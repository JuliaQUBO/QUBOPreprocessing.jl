# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Freeze raw storage rather than re-entering a normalizing model constructor.
# Tuple fields contain only immutable scalar objective data. No floating
# arithmetic, zero dropping, scale folding or relabeling occurs at this boundary.
struct _Storage
    kind::Symbol
    shape::Tuple
    values::Vector{Float64}
    indices::Vector{Int}
    pair_indices::Vector{Tuple{Int,Int}}
    pointers::Vector{Int}
end

_freeze(x::Vector{Float64}) = _Storage(:dense_linear, size(x), copy(x), Int[], Tuple{Int,Int}[], Int[])
_freeze(x::UpperTriangular{Float64,Matrix{Float64}}) =
    _Storage(:dense_quadratic, size(x), copy(vec(parent(x))), Int[], Tuple{Int,Int}[], Int[])
_freeze(x::SparseVector{Float64,Int}) =
    _Storage(:sparse_linear, size(x), copy(x.nzval), copy(x.nzind), Tuple{Int,Int}[], Int[])
_freeze(x::SparseMatrixCSC{Float64,Int}) =
    _Storage(:sparse_quadratic, size(x), copy(x.nzval), copy(x.rowval), Tuple{Int,Int}[], copy(x.colptr))
_freeze(x::Dict{Int,Float64}) =
    _Storage(:dict_linear, (), collect(Float64, values(x)), collect(Int, keys(x)), Tuple{Int,Int}[], Int[])
_freeze(x::Dict{Tuple{Int,Int},Float64}) =
    _Storage(:dict_quadratic, (), collect(Float64, values(x)), Int[], collect(Tuple{Int,Int}, keys(x)), Int[])
_freeze(x) = throw(ArgumentError("unsupported objective storage $(typeof(x))"))

function _deepcopy_tuple(@nospecialize(t::Tuple), dict::IdDict=IdDict())
    n = length(t)
    (n == 0 || isbitstype(eltype(typeof(t))) || eltype(typeof(t)) === Symbol) && return t
    out = Vector{Any}(undef, n)
    for i in 1:n
        out[i] = Base.deepcopy_internal(getfield(t, i), dict)
    end
    return Tuple(out)
end

Base.deepcopy_internal(s::_Storage, ::IdDict) = s

function _all_isfinite(vals::Vector{Float64})
    @inbounds for i in eachindex(vals)
        isfinite(vals[i]) || return false
    end
    return true
end

@inline function _foreach_linear_term(fn::F, st::_Storage) where {F}
    vals = st.values
    if st.kind === :dense_linear
        @inbounds for i in eachindex(vals)
            v = vals[i]
            !iszero(v) && fn(i, v)
        end
    else
        inds = st.indices
        @inbounds for k in eachindex(vals)
            fn(inds[k], vals[k])
        end
    end
    return nothing
end

@inline function _foreach_quadratic_term(fn::F, st::_Storage) where {F}
    vals = st.values
    if st.kind === :dense_quadratic
        n = st.shape[1]::Int
        @inbounds for i in 1:n
            for j in (i + 1):n
                v = vals[(j - 1) * n + i]
                !iszero(v) && fn(i, j, v)
            end
        end
    elseif st.kind === :sparse_quadratic
        rows = st.indices
        ptrs = st.pointers
        @inbounds for j in 1:(length(ptrs) - 1)
            for k in ptrs[j]:(ptrs[j + 1] - 1)
                fn(rows[k], j, vals[k])
            end
        end
    else
        pairs = st.pair_indices
        @inbounds for k in eachindex(vals)
            i, j = pairs[k]
            fn(i, j, vals[k])
        end
    end
    return nothing
end

function _thaw_dict_linear(indices::Vector{Int}, values::Vector{Float64})
    n = length(indices)
    d = Dict{Int,Float64}()
    sizehint!(d, n)
    @inbounds for k in 1:n
        d[indices[k]] = values[k]
    end
    return QT.DictLinearForm{Float64}(d)
end

function _thaw_dict_quadratic(indices::Vector{Tuple{Int,Int}}, values::Vector{Float64})
    n = length(indices)
    d = Dict{Tuple{Int,Int},Float64}()
    sizehint!(d, n)
    @inbounds for k in 1:n
        d[indices[k]] = values[k]
    end
    return QT.DictQuadraticForm{Float64}(d)
end

# Snapshot labels and export index sets are abstractly typed `Tuple`s with one
# parameter per variable. Indexing one through generic dispatch costs time
# proportional to its length, and iterating or comprehending over it compiles a
# new specialization for every model size. Narrow to `Tuple` and read elements
# with the `getfield` builtin so loops stay linear and compile once.
@inline _entry_at(@nospecialize(x), i::Int) = x isa Tuple ? getfield(x, i) : x[i]

_ints(@nospecialize(t)) = Int[_entry_at(t, i) for i in 1:length(t)]

function _thaw(s::_Storage)
    if s.kind === :dense_linear
        return QT.DenseLinearForm{Float64}(copy(s.values))
    elseif s.kind === :dense_quadratic
        data = reshape(copy(s.values), s.shape)
        return QT.DenseQuadraticForm{Float64}(UpperTriangular(data))
    elseif s.kind === :sparse_linear
        data = SparseVector(s.shape[1]::Int, copy(s.indices), copy(s.values))
        return QT.SparseLinearForm{Float64}(data)
    elseif s.kind === :sparse_quadratic
        data = SparseMatrixCSC(s.shape[1]::Int, s.shape[2]::Int, copy(s.pointers), copy(s.indices), copy(s.values))
        return QT.SparseQuadraticForm{Float64}(data)
    elseif s.kind === :dict_linear
        return _thaw_dict_linear(s.indices, s.values)
    else
        return _thaw_dict_quadratic(s.pair_indices, s.values)
    end
end

struct _Snapshot
    labels::Tuple
    label_type::Type
    state_type::Type
    linear::_Storage
    quadratic::_Storage
    scale::Float64
    offset::Float64
    sense::QT.Sense
    domain::QT.Domain
    perturbed::Bool
    max_perturbation::Rational{BigInt}
end

_Snapshot(
    labels::Tuple,
    label_type::Type,
    state_type::Type,
    linear::_Storage,
    quadratic::_Storage,
    scale::Float64,
    offset::Float64,
    sense::QT.Sense,
    domain::QT.Domain,
) = _Snapshot(
    labels,
    label_type,
    state_type,
    linear,
    quadratic,
    scale,
    offset,
    sense,
    domain,
    false,
    zero(Rational{BigInt}),
)

function Base.deepcopy_internal(s::_Snapshot, dict::IdDict)
    haskey(dict, s) && return dict[s]::_Snapshot
    return _Snapshot(
        _deepcopy_tuple(s.labels, dict),
        s.label_type,
        s.state_type,
        Base.deepcopy_internal(s.linear, dict),
        Base.deepcopy_internal(s.quadratic, dict),
        s.scale,
        s.offset,
        s.sense,
        s.domain,
        s.perturbed,
        Base.deepcopy_internal(s.max_perturbation, dict),
    )
end

function _labels_vector(s::_Snapshot)
    out = Vector{s.label_type}(undef, length(s.labels))
    for i in eachindex(out)
        out[i] = s.labels[i]
    end
    return _owned_labels(out)
end

function _validate_label_copy(@nospecialize(labels), @nospecialize(owned))
    for i in 1:length(labels)
        a, b = _entry_at(labels, i), _entry_at(owned, i)
        (isequal(a, b) && isequal(b, a) && hash(a) == hash(b)) ||
            throw(ArgumentError("labels must preserve equality and hash under deepcopy"))
    end
    return owned
end

_owned_labels(labels) = _validate_label_copy(labels, deepcopy(labels))

function _snapshot(model::QT.Model{V,Float64,U}) where {V,U}
    f = QT.form(model)
    f isa QT.Form || throw(ArgumentError("unsupported objective form"))
    lf, qf = QT.linear_form(f), QT.quadratic_form(f)
    lf isa Union{QT.DenseLinearForm{Float64},QT.SparseLinearForm{Float64},QT.DictLinearForm{Float64}} ||
        throw(ArgumentError("unsupported linear form"))
    qf isa Union{QT.DenseQuadraticForm{Float64},QT.SparseQuadraticForm{Float64},QT.DictQuadraticForm{Float64}} ||
        throw(ArgumentError("unsupported quadratic form"))
    n = QT.dimension(model)
    n >= 0 || throw(ArgumentError("negative model dimension"))
    labels = QT.variables(model)
    length(labels) == n && length(unique(labels)) == n ||
        throw(ArgumentError("ordered labels must cover all variables exactly once"))
    all(i -> QT.index(model, labels[i]) == i, 1:n) ||
        throw(ArgumentError("inconsistent variable mapping"))
    l, q = _freeze(QT.data(lf)), _freeze(QT.data(qf))
    (isempty(l.shape) || l.shape == (n,)) &&
        (isempty(q.shape) || q.shape == (n,n)) ||
        throw(ArgumentError("objective storage dimensions disagree with labels"))
    _all_isfinite(l.values) && _all_isfinite(q.values) &&
        isfinite(QT.scale(model)) && isfinite(QT.offset(model)) ||
        throw(ArgumentError("coefficients, scale and offset must be finite Float64 values"))
    _foreach_linear_term(l) do i, _
        1 <= i <= n || throw(ArgumentError("linear index outside model"))
    end
    _foreach_quadratic_term(q) do i, j, v
        1 <= i <= n && 1 <= j <= n && (i < j || iszero(v)) ||
            throw(ArgumentError("quadratic objective must be in strict upper triangular normal form"))
    end
    # Dense terms omit the diagonal; validate it separately without normalizing.
    if qf isa QT.DenseQuadraticForm
        all(i -> iszero(QT.data(qf)[i,i]), 1:n) ||
            throw(ArgumentError("quadratic diagonal must be zero in normal form"))
    end
    return _Snapshot(Tuple(_owned_labels(labels)), V, U, l, q,
                     QT.scale(model), QT.offset(model), QT.sense(model), QT.domain(model))
end
_snapshot(model) = throw(ArgumentError("expected a QUBOTools.Model with Float64 objective data"))

function _check_integerize_kwargs(max_decimals::Integer, atol::Real)
    (!(max_decimals isa Bool) && max_decimals >= 0) ||
        throw(ArgumentError("max_decimals must be a nonnegative integer; got $(repr(max_decimals))"))
    (!(atol isa Bool) && isfinite(atol) && atol >= 0) ||
        throw(ArgumentError("atol must be a finite nonnegative real; got $(repr(atol))"))
    return nothing
end

function _is_integer_snapshot(s::_Snapshot)::Bool
    (isfinite(s.offset) && isinteger(s.offset)) || return false
    for i in 1:length(s.linear.values)
        v = s.linear.values[i]
        (isfinite(v) && isinteger(v)) || return false
    end
    if s.quadratic.kind === :dense_quadratic
        n = s.quadratic.shape[1]::Int
        for col in 1:n, row in 1:(col - 1)
            v = s.quadratic.values[(col - 1) * n + row]
            (isfinite(v) && isinteger(v)) || return false
        end
    else
        for i in 1:length(s.quadratic.values)
            v = s.quadratic.values[i]
            (isfinite(v) && isinteger(v)) || return false
        end
    end
    return true
end

# Scaling by m = 2^a is exact in Float64 for every multiplier the search accepts,
# so rational rounding is needed only for decimal multipliers.
_scale_value(v::Float64, m_big::BigInt) =
    iszero(v) ? v : ispow2(m_big) ? v * Float64(m_big) : Float64(round(BigInt, Rational{BigInt}(v) * m_big))

function _scale_storage(st::_Storage, m_big::BigInt)::_Storage
    len = length(st.values)
    len == 0 && return st
    if st.kind === :dense_quadratic
        n = st.shape[1]::Int
        scaled = zeros(Float64, len)
        for col in 1:n, row in 1:(col - 1)
            idx = (col - 1) * n + row
            v = st.values[idx]
            scaled[idx] = _scale_value(v, m_big)
        end
        return _Storage(st.kind, st.shape, scaled, st.indices, st.pair_indices, st.pointers)
    else
        scaled = Vector{Float64}(undef, len)
        for i in 1:len
            v = st.values[i]
            scaled[i] = _scale_value(v, m_big)
        end
        return _Storage(st.kind, st.shape, scaled, st.indices, st.pair_indices, st.pointers)
    end
end

function _integerize_snapshot(s::_Snapshot; max_decimals::Integer=9, atol::Real=0.0)::_Snapshot
    _check_integerize_kwargs(max_decimals, atol)
    (_is_integer_snapshot(s) || !isfinite(s.scale) || iszero(s.scale) || !isfinite(s.offset)) && return s

    vals = Float64[]
    !iszero(s.offset) && push!(vals, s.offset)
    for i in 1:length(s.linear.values)
        v = s.linear.values[i]::Float64
        !iszero(v) && push!(vals, v)
    end
    if s.quadratic.kind === :dense_quadratic
        n = s.quadratic.shape[1]::Int
        for col in 1:n, row in 1:(col - 1)
            v = s.quadratic.values[(col - 1) * n + row]::Float64
            !iszero(v) && push!(vals, v)
        end
    else
        for i in 1:length(s.quadratic.values)
            v = s.quadratic.values[i]::Float64
            !iszero(v) && push!(vals, v)
        end
    end
    isempty(vals) && return s

    max_d = min(Int(max_decimals), 300)
    max_int = maxintfloat(Float64)
    max_int_big = BigInt(max_int)
    exact_only = iszero(atol)
    atol_rat = exact_only ? zero(Rational{BigInt}) : Rational{BigInt}(Float64(atol))
    scale_rat = Rational{BigInt}(s.scale)

    candidates = Tuple{BigInt,Int,Int}[]
    for a in 0:max_d, b in 0:max_d
        (a == 0 && b == 0) && continue
        (exact_only && b > 0) && continue
        m_big = (BigInt(2)^a) * (BigInt(5)^b)
        m_big <= max_int_big && push!(candidates, (m_big, a, b))
    end
    sort!(candidates; by = x -> (x[1], x[3], x[2]))

    rat_vals = Vector{Rational{BigInt}}(undef, length(vals))
    populated = 0

    for (m_big, a, b) in candidates
        α_new = s.scale / Float64(m_big)
        (!isfinite(α_new) || iszero(α_new) || issubnormal(α_new)) && continue
        α_new_rat = Rational{BigInt}(α_new)
        if exact_only || b == 0
            α_new_rat * m_big == scale_rat || continue
        end

        ok = true
        has_odd = false
        has_non5 = false
        max_coeff_err = zero(Rational{BigInt})
        if b == 0
            # Multiplying binary64 by 2^a is exact unless it overflows, so the
            # Float64 product decides integrality without rational arithmetic.
            m_f = Float64(m_big)
            for v in vals
                y = v * m_f
                if !(isfinite(y) && isinteger(y) && abs(y) <= max_int)
                    ok = false
                    break
                end
                has_odd |= !iszero(rem(y, 2.0))
            end
        else
            # Decimal multipliers are searched only when atol > 0.
            for k in eachindex(vals)
                if k > populated
                    populated = k
                    rat_vals[k] = Rational{BigInt}(vals[k])
                end
                v_rat = rat_vals[k]
                y_rat = v_rat * m_big
                r_big = round(BigInt, y_rat)
                if iszero(r_big) || abs(r_big) > max_int_big
                    ok = false
                    break
                end
                err_rat = abs(y_rat - r_big)
                if !(err_rat < 1 // 2 && err_rat <= atol_rat * abs(r_big))
                    ok = false
                    break
                end
                coeff_err = abs(α_new_rat * r_big - scale_rat * v_rat)
                coeff_err > max_coeff_err && (max_coeff_err = coeff_err)
                has_odd |= isodd(r_big)
                has_non5 |= !iszero(rem(r_big, 5))
            end
        end

        if ok && (a == 0 || has_odd) && (b == 0 || has_non5)
            l_new = _scale_storage(s.linear, m_big)
            q_new = _scale_storage(s.quadratic, m_big)
            offset_new = _scale_value(s.offset, m_big)
            total_pert = max(s.max_perturbation, max_coeff_err)
            return _Snapshot(s.labels, s.label_type, s.state_type, l_new, q_new,
                             α_new, offset_new, s.sense, s.domain,
                             !iszero(total_pert), total_pert)
        end
    end

    return s
end

"""
    is_integer_scaled(model_or_workspace)::Bool

Return `true` iff every linear coefficient, quadratic coefficient, and constant
offset of `model_or_workspace` is a finite exact integer (with arbitrary finite
model `scale`). On a [`Workspace`](@ref), checks the currently conditioned
residual objective (`conditioned_constant`, `effective_field`, and
`incident_couplings` over all free variables).
"""
function is_integer_scaled(model::QT.Model{V,Float64,U})::Bool where {V,U}
    return _is_integer_snapshot(_snapshot(model))
end
is_integer_scaled(model) = throw(ArgumentError("expected a QUBOTools.Model with Float64 objective data or a Workspace"))

"""
    integerize_scale(model; max_decimals::Integer=9, atol::Real=0.0)

Return an owned copy of `model` where the smallest multiplier ``m = 2^a \\cdot 5^b``
in the bounded search range ``0 \\le a, b \\le \\min(\\text{max\\_decimals}, 300)``
(with ``m \\le 2^{53}`` and all scaled integers ``|r| \\le 2^{53}``) that scales
all linear coefficients, quadratic coefficients, and `offset` to integers is
factored into `scale(model) / m`.

By default (`atol=0.0`), the rescaled snapshot is **exact**: a multiplier ``m`` is
accepted only when `Rational{BigInt}(v) * m` is an exact integer for every
coefficient and `offset` and `Rational{BigInt}(scale(model) / m) * m == Rational{BigInt}(scale(model))`,
using no tolerance and no rounding (multiplying binary64 by ``2^a`` is exact). Only exact dyadic powers (``b = 0``,
``0 \\le a \\le \\text{max\\_decimals}``) are considered under `atol=0.0`; coefficients
whose binary64 denominator exceeds ``2^{\\text{max\\_decimals}}`` (such as binary64
approximations of `0.1`, `0.3`, `0.9` under the default `max_decimals=9`) remain
unchanged.

Passing `atol > 0` explicitly opts in to tolerance-based decimal multipliers (``b \\ge 1``),
accepting irreducible ``(a, b)`` when every non-zero coefficient and `offset` satisfies
`abs(Rational{BigInt}(v) * m - r) <= Rational{BigInt}(Float64(atol)) * abs(r)` in exact
rational arithmetic. When the accepted multiplier changes any effective objective term
``\\operatorname{Rational\\{BigInt\\}}(\\alpha_{\\text{new}}) \\cdot r \\ne \\operatorname{Rational\\{BigInt\\}}(\\alpha) \\cdot \\operatorname{Rational\\{BigInt\\}}(v)``,
the rescaled model is a perturbed approximation of `model`.
"""
function integerize_scale(
    model::QT.Model{V,Float64,U};
    max_decimals::Integer=9,
    atol::Real=0.0,
) where {V,U}
    s = _integerize_snapshot(_snapshot(model); max_decimals, atol)
    labels = _labels_vector(s)
    vm = QT.VariableMap{V}(Dict{V,Int}(v => i for (i, v) in enumerate(labels)), labels)
    f = QT.Form{Float64}(length(labels), _thaw(s.linear), _thaw(s.quadratic),
                         s.scale, s.offset; sense=s.sense, domain=s.domain)
    return QT.Model{V,Float64,U,typeof(f)}(
        vm,
        f,
        deepcopy(QT.metadata(model)),
        deepcopy(QT.solution(model)),
        deepcopy(model.start),
    )
end
integerize_scale(model; max_decimals::Integer=9, atol::Real=0.0) =
    throw(ArgumentError("expected a QUBOTools.Model with Float64 objective data"))

"""
    Generation

Opaque identity for one workspace and one accepted source snapshot. Equality
matches both identities; it is neither a source hash nor an optimality proof.
"""
struct Generation
    workspace::UUID
    source::UUID
end

"""
    Workspace(model; rules=:identity, integerize_scale::Bool=false, max_decimals::Integer=9, atol::Real=0.0)

Privately snapshot a finite Float64 QUBOTools model and its ordered labels.
`:identity` performs no inference; `:dominance` prepares exact bound caches and
a deterministic queue for [`propagate!`](@ref). When `integerize_scale=true`,
the snapshot searches ``0 \\le a, b \\le \\min(\\text{max\\_decimals}, 300)`` for the
smallest common denominator ``m = 2^a \\cdot 5^b`` to factor into `scale(model) / m`
via [`integerize_scale`](@ref) before building exact integer state. With the
default `atol=0.0`, this rescaling is **exact** (`Rational{BigInt}(v) * m` must be
an integer for every coefficient and `offset` and `Rational{BigInt}(scale(model) / m) * m == Rational{BigInt}(scale(model))`,
with no rounding); passing `atol > 0` opts in to tolerance-based decimal
rounding.

`ws.max_perturbation::Rational{BigInt}` records the largest absolute change in any
effective objective coefficient or scaled offset (in objective units, including
`scale` and `offset`) between the stored snapshot and the input model:
``\\max_v |\\operatorname{Rational\\{BigInt\\}}(\\alpha_{\\text{new}}) \\cdot \\operatorname{Rational\\{BigInt\\}}(v_{\\text{new}}) - \\operatorname{Rational\\{BigInt\\}}(\\alpha) \\cdot \\operatorname{Rational\\{BigInt\\}}(v)|``
(`0 // 1` when the snapshot is exact), and `ws.perturbed::Bool` is `true` iff
`ws.max_perturbation > 0 // 1`. Both fields are also recorded on exported
certificates ([`DominanceCertificate`](@ref) / [`ReductionCertificate`](@ref))
and exports ([`ExportResult`](@ref) / [`ConditionedExport`](@ref)).

Explicit caller assumptions and certified deductions have separate provenance and
can be rolled back. Source edits never change the snapshot; use [`reset!`](@ref)
to accept a new source. Labels must have stable equality/hash semantics and
preserve equality/hash under owned deep copies. Use each workspace serially.
Model metadata, solutions and warm starts are outside the objective snapshot.
"""
mutable struct Workspace
    _snapshot::_Snapshot
    _generation::Generation
    _state::_Incremental
    # Internal staging constructor for transactional non-LIFO replay.
    Workspace(snapshot::_Snapshot, token::Generation, state::_Incremental) = new(snapshot, token, state)
    function Workspace(
        model;
        rules=:identity,
        integerize_scale::Bool=false,
        max_decimals::Integer=9,
        atol::Real=0.0,
    )
        _check_rules(rules)
        _check_integerize_kwargs(max_decimals, atol)
        raw_snapshot = _snapshot(model)
        snapshot = integerize_scale ? _integerize_snapshot(raw_snapshot; max_decimals, atol) : raw_snapshot
        state = _incremental(snapshot;rules)
        return new(snapshot, Generation(uuid4(), uuid4()), state)
    end
end
# A fresh identity workspace over the same snapshot (new generation): the original
# model a consumer can solve instead of the residual
_identity_workspace(ws::Workspace) =
    Workspace(ws._snapshot, Generation(uuid4(), uuid4()), _incremental(ws._snapshot; rules=:identity))
_check_rules(rules) = rules in (:identity,:dominance,:elimination,:relations,:mixed) ? nothing :
    throw(ArgumentError("supported rules are :identity, :dominance, :elimination, :relations and :mixed; requested $(repr(rules))"))

@inline function Base.getproperty(ws::Workspace, name::Symbol)
    name === :perturbed && return getfield(ws, :_snapshot).perturbed
    name === :max_perturbation && return getfield(ws, :_snapshot).max_perturbation
    return getfield(ws, name)
end
Base.propertynames(::Workspace, private::Bool=false) =
    private ? (:_snapshot, :_generation, :_state, :perturbed, :max_perturbation) : (:perturbed, :max_perturbation)

"""`generation(ws_or_export)` returns its immutable source/workspace identity."""
generation(ws::Workspace) = ws._generation

function is_integer_scaled(ws::Workspace)::Bool
    st = ws._state
    denominator = big(1) << st.shift
    iszero(rem(st.constant, denominator)) || return false
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        iszero(rem(st.fields[i], denominator)) || return false
        for (j, q) in st.adjacency[i]
            (st.fixed[j] == 2 && i < j) || continue
            iszero(rem(q, denominator)) || return false
        end
    end
    return true
end

"""
    reset!(ws, model; integerize_scale::Bool=false, max_decimals::Integer=9, atol::Real=0.0)

Validate a fresh snapshot before committing it. Failed validation preserves the
old workspace. Success creates a fresh generation, including for an identical
source. Owned exports remain evidence for their historical generation. With default
`atol=0.0`, `integerize_scale=true` is exact (`ws.perturbed == false`,
`ws.max_perturbation == 0 // 1`); passing `atol > 0` opts in to tolerance-based
decimal rounding and updates `ws.perturbed` and `ws.max_perturbation` from the
stored scale and coefficients/offset.
"""
function reset!(
    ws::Workspace,
    model;
    integerize_scale::Bool=false,
    max_decimals::Integer=9,
    atol::Real=0.0,
)
    _check_integerize_kwargs(max_decimals, atol)
    raw_snapshot = _snapshot(model)
    snapshot = integerize_scale ? _integerize_snapshot(raw_snapshot; max_decimals, atol) : raw_snapshot
    state = _incremental(snapshot;rules=ws._state.rules)
    token = Generation(generation(ws).workspace, uuid4())
    ws._snapshot = snapshot
    ws._generation = token
    ws._state = state
    return ws
end

"""
    ExportResult

Owned immutable identity export, with `status == :certified`, original scope
and an empty reduction chain. `certificate.unchanged_representation` is `true`
iff the snapshot was not perturbed (`result.perturbed == false`).
Obtain a separately owned mutable solver model with [`export_model`](@ref).
Private fields are implementation details, not a mutation API.
"""
struct ExportResult
    _snapshot::_Snapshot
    generation::Generation
    status::Symbol
    certificate::NamedTuple{(:scope, :reduction_chain, :unchanged_representation),Tuple{Symbol,Tuple{},Bool}}
end
generation(result::ExportResult) = result.generation

@inline function Base.getproperty(r::ExportResult, name::Symbol)
    name === :perturbed && return getfield(r, :_snapshot).perturbed
    name === :max_perturbation && return getfield(r, :_snapshot).max_perturbation
    return getfield(r, name)
end
Base.propertynames(::ExportResult, private::Bool=false) =
    private ? (:_snapshot, :generation, :status, :certificate, :perturbed, :max_perturbation) :
              (:generation, :status, :certificate, :perturbed, :max_perturbation)

"""
    materialize(ws; coefficient_type=Float64, rounding=:none, normalization=:none, map=nothing)
    materialize(ws, map::DomainGaugeMap; coefficient_type=Float64, rounding=:none, normalization=:none)

Explicitly capture an owned export. With default normalization and without fixings or a coordinate `map`, this
is the Float64 identity export (`certificate.unchanged_representation == !ws.perturbed`).
With caller assumptions, certified deductions or a [`DomainGaugeMap`](@ref), return a
[`ConditionedExport`](@ref) with the complete proof chain when present: Float64
transport must represent every conditioned/converted coefficient and constant
exactly, or the call raises `ArgumentError`; use `coefficient_type=Rational{BigInt}`
for exact transport. Materialization scans/copies the graph; it is never implicit in updates.

With `coefficient_type=Float64`, opt in to `rounding=:nearest` to round each
residual linear/quadratic coefficient and constant to its nearest finite Float64.
If any coefficient changes, the export has `status=:rounded`,
`certificate.unchanged_representation=false`, and `perturbed=true` when the
effective coefficient change is nonzero (a zero scale makes it zero).
`max_perturbation` is the maximum of the existing input perturbation and
`abs(scale) * abs(rounded - exact)` over the residual coefficients and constant,
computed exactly as `Rational{BigInt}` in original objective units. It is a
coefficient bound, not an objective-error or optimality certificate. The reduction
proof still describes the exact residual; reconstruction uses the historical
source objective rather than the rounded solver objective. The scale is never
rounded, and a nonfinite rounded coefficient still raises `ArgumentError`.

With `coefficient_type=Float64` and `rounding=:none`, `normalization=:integer`
factors all mapped coefficients, including the constant, into primitive integers
and a common positive rational factor absorbed into the scale. Every integer and
the adjusted scale must be exactly representable as finite Float64; otherwise the
call raises `ArgumentError`. An all-zero residual uses factor one and retains the
source scale. Exact normalization adds no perturbation, preserves the historical
source and proof, and sets `unchanged_representation=false` when the factor is
not one. The default `normalization=:none` retains the stored coefficients/scale.
"""
function materialize(ws::Workspace; coefficient_type=Float64, rounding=:none,
                     normalization=:none, map=nothing)
    rounding in (:none, :nearest) || throw(ArgumentError("rounding must be :none or :nearest"))
    rounding === :none || coefficient_type === Float64 ||
        throw(ArgumentError("rounding=:nearest requires coefficient_type=Float64"))
    normalization in (:none, :integer) ||
        throw(ArgumentError("normalization must be :none or :integer"))
    if normalization === :integer
        coefficient_type === Float64 ||
            throw(ArgumentError("normalization=:integer requires coefficient_type=Float64"))
        rounding === :none ||
            throw(ArgumentError("normalization=:integer requires rounding=:none"))
    end
    map === nothing || _validate_domain_map(ws, map)
    if !isempty(ws._state.fixes) || map !== nothing || normalization === :integer
        return _conditioned_export(ws, coefficient_type; map, rounding, normalization)
    end
    coefficient_type === Float64 || throw(ArgumentError("only Float64 identity transport is supported"))
    snapshot = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, snapshot.labels)
    return ExportResult(snapshot, generation(ws), :certified,
                        (scope=:original, reduction_chain=(), unchanged_representation=!snapshot.perturbed))
end

"""`original_variables(ws_or_export)` returns owned labels in original index order."""
function original_variables(x::Union{Workspace,ExportResult})
    return _labels_vector(x._snapshot)
end

"""`index_map(ws_or_export)` returns an owned original-index → residual-index vector."""
index_map(x::ExportResult) = collect(1:length(x._snapshot.labels))

"""
    export_model(result)

Return a fresh QUBOTools model with exactly the captured stored objective and
ordered labels. Each call owns all mutable data. Editing this model does not
edit the export certificate or the historical source used by reconstruction.
"""
function export_model(result::ExportResult)
    s = result._snapshot
    labels = original_variables(result)
    V, U = s.label_type, s.state_type
    vm = QT.VariableMap{V}(Dict{V,Int}(v=>i for (i,v) in enumerate(labels)), labels)
    f = QT.Form{Float64}(length(labels), _thaw(s.linear), _thaw(s.quadratic),
                         s.scale, s.offset; sense=s.sense, domain=s.domain)
    return QT.Model{V,Float64,U}(vm, f)
end

"""Ordinary Float64 energy, with `finite` and `method`; it is not an exact proof."""
struct EnergyEvaluation
    value::Float64
    finite::Bool
    method::Symbol
end

"""Complete owned original-order `state`, numerical `energy`, and historical `generation`."""
struct Reconstruction
    state::Vector{Int}
    energy::EnergyEvaluation
    generation::Generation
end

"""
    reconstruct(result, y)

Validate a complete one-based residual-domain vector (matching the original
domain for unmapped exports, or `map.target_domain` when materialized through a
[`DomainGaugeMap`](@ref)) and return an owned state in original-variable order
and original domain together with an ordinary Float64 original-energy
evaluation. Reject missing, partial, non-real, nonfinite and out-of-domain
values. Numerical overflow is reported in `energy.finite`; neither the energy
nor this reconstruction certifies optimality.
"""
function reconstruct end

function _lift_state(result::ExportResult, y::AbstractVector)
    Base.require_one_based_indexing(y)
    s = result._snapshot
    length(y) == length(s.labels) || throw(ArgumentError("state must cover every original variable"))
    state = Vector{Int}(undef, length(y))
    low = s.domain === QT.BoolDomain ? 0 : -1
    for i in eachindex(y)
        v = y[i]
        v isa Real && isfinite(v) && (v == low || v == 1) ||
            throw(ArgumentError("state value at index $i is outside the original domain"))
        state[i] = Int(v)
    end
    return state
end
function _source_evaluator(s::_Snapshot)
    return QT.Form{Float64}(length(s.labels), _thaw(s.linear), _thaw(s.quadratic),
                            s.scale, s.offset; sense=s.sense, domain=s.domain)
end
function _evaluate_state(result,state,evaluator)
    energy = QT.value(state,evaluator)
    return Reconstruction(state,EnergyEvaluation(energy,isfinite(energy),:float64),generation(result))
end
_reconstruct(result,y::AbstractVector,evaluator) = _evaluate_state(result,_lift_state(result,y),evaluator)
function reconstruct(result::ExportResult,y::AbstractVector)
    state = _lift_state(result,y)
    return _evaluate_state(result,state,_source_evaluator(result._snapshot))
end
reconstruct(::ExportResult, y) = throw(ArgumentError("state must be a complete ordered vector"))

"""No-inference report: `:quiescent` means identity completion, never solver optimality."""
struct IdentityReport
    generation::Generation
    rules::Symbol
    stop_reason::Symbol
    deductions::Int
    assumptions::Int
end

"""
    preprocess(model; rules=:identity, integerize_scale::Bool=(rules !== :identity), max_decimals::Integer=9, atol::Real=0.0, time_limit=nothing, kwargs...)

Return `(workspace, report)` using the same snapshot path as [`Workspace`](@ref).
`:identity` returns a no-inference `IdentityReport`; `:dominance` runs
[`propagate!`](@ref) with forwarded keyword limits and returns its report.
With `rules=:mixed` and a `time_limit` in seconds, every reduction family runs
under that budget through [`schedule_budgeted!`](@ref) (forwarding its keywords)
and its [`BudgetedScheduleReport`](@ref) is returned (the budget starts once the
workspace is built, and the cheap rules' capped floor can run past it); without
`time_limit`, `:mixed` runs [`schedule_reductions!`](@ref).
When `rules !== :identity`, `integerize_scale` defaults to `true` with `atol=0.0`,
so only exact dyadic denominators ``2^a`` within `0 <= a <= max_decimals` are
factored into `scale` before reduction (`ws.perturbed == false`,
`ws.max_perturbation == 0 // 1`). Passing `atol > 0` explicitly opts in to
tolerance-based decimal rounding and records any resulting effective-coefficient
or scaled-offset perturbation on `ws` and its exported certificates. No model is
materialized implicitly.
"""
function preprocess(
    model;
    rules=:identity,
    integerize_scale::Bool=(rules !== :identity),
    max_decimals::Integer=9,
    atol::Real=0.0,
    time_limit=nothing,
    kwargs...,
)
    time_limit === nothing || rules === :mixed ||
        throw(ArgumentError("time_limit requires rules=:mixed"))
    ws = Workspace(model; rules, integerize_scale, max_decimals, atol)
    time_limit === nothing || return ws, schedule_budgeted!(ws; time_limit, kwargs...)
    rules === :dominance && return ws, propagate!(ws;kwargs...)
    rules === :elimination && return ws, eliminate_low_degree!(ws;kwargs...)
    rules === :relations && return ws, contract_relations!(ws;kwargs...)
    rules === :mixed && return ws, schedule_reductions!(ws;kwargs...)
    isempty(kwargs) || throw(ArgumentError("propagation limits require rules=:dominance, rules=:elimination, rules=:relations or rules=:mixed"))
    return ws, IdentityReport(generation(ws), :identity, :quiescent, 0, 0)
end
