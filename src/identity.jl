# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Freeze raw storage rather than re-entering a normalizing model constructor.
# Tuple fields contain only immutable scalar objective data. No floating
# arithmetic, zero dropping, scale folding or relabeling occurs at this boundary.
struct _Storage
    kind::Symbol
    shape::Tuple
    values::Tuple
    indices::Tuple
    pointers::Tuple
end

_freeze(x::Vector{Float64}) = _Storage(:dense_linear, size(x), Tuple(x), (), ())
_freeze(x::UpperTriangular{Float64,Matrix{Float64}}) =
    _Storage(:dense_quadratic, size(x), Tuple(parent(x)), (), ())
_freeze(x::SparseVector{Float64,Int}) =
    _Storage(:sparse_linear, size(x), Tuple(x.nzval), Tuple(x.nzind), ())
_freeze(x::SparseMatrixCSC{Float64,Int}) =
    _Storage(:sparse_quadratic, size(x), Tuple(x.nzval), Tuple(x.rowval), Tuple(x.colptr))
_freeze(x::Dict{Int,Float64}) =
    _Storage(:dict_linear, (), Tuple(values(x)), Tuple(keys(x)), ())
_freeze(x::Dict{Tuple{Int,Int},Float64}) =
    _Storage(:dict_quadratic, (), Tuple(values(x)), Tuple(keys(x)), ())
_freeze(x) = throw(ArgumentError("unsupported objective storage $(typeof(x))"))

function _floats(@nospecialize(t::Tuple))
    out = Vector{Float64}(undef, length(t))
    for i in eachindex(out)
        out[i] = t[i]::Float64
    end
    return out
end

function _ints(@nospecialize(t::Tuple))
    out = Vector{Int}(undef, length(t))
    for i in eachindex(out)
        out[i] = Int(t[i])
    end
    return out
end

function _deepcopy_tuple(@nospecialize(t::Tuple), dict::IdDict)
    n = length(t)
    n == 0 && return ()
    out = Vector{Any}(undef, n)
    for i in 1:n
        out[i] = Base.deepcopy_internal(t[i], dict)
    end
    return Tuple(out)
end

Base.deepcopy_internal(s::_Storage, ::IdDict) = s

function _all_isfinite(@nospecialize(t::Tuple))
    for i in 1:length(t)
        isfinite(t[i]::Float64) || return false
    end
    return true
end

function _thaw_dict_linear(@nospecialize(indices::Tuple), @nospecialize(values::Tuple))
    n = length(indices)
    d = Dict{Int,Float64}()
    sizehint!(d, n)
    for k in 1:n
        d[indices[k]::Int] = values[k]::Float64
    end
    return QT.DictLinearForm{Float64}(d)
end

function _thaw_dict_quadratic(@nospecialize(indices::Tuple), @nospecialize(values::Tuple))
    n = length(indices)
    d = Dict{Tuple{Int,Int},Float64}()
    sizehint!(d, n)
    for k in 1:n
        d[indices[k]::Tuple{Int,Int}] = values[k]::Float64
    end
    return QT.DictQuadraticForm{Float64}(d)
end

function _thaw(s::_Storage)
    if s.kind === :dense_linear
        return QT.DenseLinearForm{Float64}(_floats(s.values))
    elseif s.kind === :dense_quadratic
        data = reshape(_floats(s.values), s.shape)
        return QT.DenseQuadraticForm{Float64}(UpperTriangular(data))
    elseif s.kind === :sparse_linear
        data = SparseVector(s.shape[1], _ints(s.indices), _floats(s.values))
        return QT.SparseLinearForm{Float64}(data)
    elseif s.kind === :sparse_quadratic
        data = SparseMatrixCSC(s.shape..., _ints(s.pointers), _ints(s.indices), _floats(s.values))
        return QT.SparseQuadraticForm{Float64}(data)
    elseif s.kind === :dict_linear
        return _thaw_dict_linear(s.indices, s.values)
    else
        return _thaw_dict_quadratic(s.indices, s.values)
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
end

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
        (isequal(labels[i], owned[i]) && isequal(owned[i], labels[i]) &&
         hash(labels[i]) == hash(owned[i])) ||
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
    for (i, _) in QT.linear_terms(model)
        1 <= i <= n || throw(ArgumentError("linear index outside model"))
    end
    for ((i, j), v) in QT.quadratic_terms(model)
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
        v = s.linear.values[i]::Float64
        (isfinite(v) && isinteger(v)) || return false
    end
    if s.quadratic.kind === :dense_quadratic
        n = s.quadratic.shape[1]::Int
        for col in 1:n, row in 1:(col - 1)
            v = s.quadratic.values[(col - 1) * n + row]::Float64
            (isfinite(v) && isinteger(v)) || return false
        end
    else
        for i in 1:length(s.quadratic.values)
            v = s.quadratic.values[i]::Float64
            (isfinite(v) && isinteger(v)) || return false
        end
    end
    return true
end

function _scale_storage(st::_Storage, m::Float64)::_Storage
    len = length(st.values)
    len == 0 && return st
    if st.kind === :dense_quadratic
        n = st.shape[1]::Int
        scaled = zeros(Float64, len)
        for col in 1:n, row in 1:(col - 1)
            idx = (col - 1) * n + row
            v = st.values[idx]::Float64
            scaled[idx] = iszero(v) ? 0.0 : Float64(round(v * m))
        end
        return _Storage(st.kind, st.shape, Tuple(scaled), st.indices, st.pointers)
    else
        scaled = Vector{Float64}(undef, len)
        for i in 1:len
            v = st.values[i]::Float64
            scaled[i] = iszero(v) ? 0.0 : Float64(round(v * m))
        end
        return _Storage(st.kind, st.shape, Tuple(scaled), st.indices, st.pointers)
    end
end

function _integerize_snapshot(s::_Snapshot; max_decimals::Integer=9, atol::Real=1e-12)::_Snapshot
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
    max_int = Float64(maxintfloat(Float64))
    atol_f = Float64(atol)

    candidates = Tuple{Float64,Int,Int}[]
    for a in 0:max_d, b in 0:max_d
        (a == 0 && b == 0) && continue
        m = (2.0^a) * (5.0^b)
        (isfinite(m) && m <= max_int) && push!(candidates, (m, a, b))
    end
    sort!(candidates; by = x -> (x[1], x[3], x[2]))

    for (m, a, b) in candidates
        α_new = s.scale / m
        (!isfinite(α_new) || iszero(α_new) || issubnormal(α_new)) && continue

        ok = true
        has_odd = false
        has_non5 = false
        for v in vals
            y = v * m
            if !isfinite(y)
                ok = false
                break
            end
            r = round(y)
            if iszero(r) || abs(r) > max_int
                ok = false
                break
            end
            if b == 0
                if r != y
                    ok = false
                    break
                end
            else
                err = abs(y - r)
                if !(err < 0.5 && err <= atol_f * abs(r))
                    ok = false
                    break
                end
            end
            has_odd |= !iszero(rem(r, 2))
            has_non5 |= !iszero(rem(r, 5))
        end

        if ok && (a == 0 || has_odd) && (b == 0 || has_non5)
            l_new = _scale_storage(s.linear, m)
            q_new = _scale_storage(s.quadratic, m)
            offset_new = iszero(s.offset) ? 0.0 : Float64(round(s.offset * m))
            return _Snapshot(s.labels, s.label_type, s.state_type, l_new, q_new,
                             α_new, offset_new, s.sense, s.domain)
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
    integerize_scale(model; max_decimals::Integer=9, atol::Real=1e-12)

Return an owned copy of `model` where the smallest multiplier ``m = 2^a \\cdot 5^b``
(with ``0 \\le a, b \\le \\text{max\\_decimals}``) that scales all linear coefficients,
quadratic coefficients, and `offset` to exact integers is factored into
`scale(model) / m`. Pure dyadic multipliers (``b = 0``) require exact binary
products (`v * m == round(v * m)`), preserving sub-ulp near-tie perturbations;
decimal multipliers (``b \\ge 1``) accept non-zero products within relative
tolerance `atol * abs(round(v * m))` provided ``(a, b)`` is irreducible.
"""
function integerize_scale(
    model::QT.Model{V,Float64,U};
    max_decimals::Integer=9,
    atol::Real=1e-12,
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
integerize_scale(model; max_decimals::Integer=9, atol::Real=1e-12) =
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
    Workspace(model; rules=:identity, integerize_scale::Bool=false, max_decimals::Integer=9, atol::Real=1e-12)

Privately snapshot a finite Float64 QUBOTools model and its ordered labels.
`:identity` performs no inference; `:dominance` prepares exact bound caches and
a deterministic queue for [`propagate!`](@ref). When `integerize_scale=true`,
the snapshot factors any common decimal/dyadic denominator ``m = 2^a \\cdot 5^b``
into `scale(model) / m` via [`integerize_scale`](@ref) before building exact
rational state. Explicit caller assumptions and
certified deductions have separate provenance and can be rolled back. Source edits never change the snapshot; use
[`reset!`](@ref) to accept a new source. Labels must have stable equality/hash
semantics and preserve equality/hash under owned deep copies. Use each workspace
serially. Model metadata, solutions and warm starts are outside the objective snapshot.
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
        atol::Real=1e-12,
    )
        _check_rules(rules)
        _check_integerize_kwargs(max_decimals, atol)
        raw_snapshot = _snapshot(model)
        snapshot = integerize_scale ? _integerize_snapshot(raw_snapshot; max_decimals, atol) : raw_snapshot
        state = _incremental(snapshot;rules)
        return new(snapshot, Generation(uuid4(), uuid4()), state)
    end
end
_check_rules(rules) = rules in (:identity,:dominance,:elimination,:relations,:mixed) ? nothing :
    throw(ArgumentError("supported rules are :identity, :dominance, :elimination, :relations and :mixed; requested $(repr(rules))"))

"""`generation(ws_or_export)` returns its immutable source/workspace identity."""
generation(ws::Workspace) = ws._generation

function is_integer_scaled(ws::Workspace)::Bool
    st = ws._state
    denominator(st.constant) == 1 || return false
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        denominator(st.fields[i]) == 1 || return false
        for (j, q) in st.adjacency[i]
            (st.fixed[j] == 2 && i < j) || continue
            denominator(q) == 1 || return false
        end
    end
    return true
end

"""
    reset!(ws, model; integerize_scale::Bool=false, max_decimals::Integer=9, atol::Real=1e-12)

Validate a fresh snapshot before committing it. Failed validation preserves the
old workspace. Success creates a fresh generation, including for an identical
source. Owned exports remain evidence for their historical generation.
"""
function reset!(
    ws::Workspace,
    model;
    integerize_scale::Bool=false,
    max_decimals::Integer=9,
    atol::Real=1e-12,
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
and an empty reduction chain. This certifies unchanged representation only.
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

"""
    materialize(ws; coefficient_type=Float64, map=nothing)
    materialize(ws, map::DomainGaugeMap; coefficient_type=Float64)

Explicitly capture an owned export. Without fixings or a coordinate `map`, this
is the unchanged Float64 identity export. With caller assumptions, certified
deductions or a [`DomainGaugeMap`](@ref), return a [`ConditionedExport`](@ref)
with the complete proof chain when present: Float64 transport must represent
every conditioned/converted coefficient and constant exactly, or the call raises
`ArgumentError`; use `coefficient_type=Rational{BigInt}` for exact transport.
Materialization scans/copies the graph; it is never implicit in updates.
"""
function materialize(ws::Workspace; coefficient_type=Float64, map=nothing)
    map === nothing || _validate_domain_map(ws, map)
    if !isempty(ws._state.fixes) || map !== nothing
        return _conditioned_export(ws, coefficient_type; map)
    end
    coefficient_type === Float64 || throw(ArgumentError("only Float64 identity transport is supported"))
    snapshot = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, snapshot.labels)
    return ExportResult(snapshot, generation(ws), :certified,
                        (scope=:original, reduction_chain=(), unchanged_representation=true))
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
    preprocess(model; rules=:identity, integerize_scale::Bool=(rules !== :identity), max_decimals::Integer=9, atol::Real=1e-12, kwargs...)

Return `(workspace, report)` using the same snapshot path as Workspace.
`:identity` returns a no-inference `IdentityReport`; `:dominance` runs
[`propagate!`](@ref) with forwarded keyword limits and returns its report.
When `rules !== :identity`, `integerize_scale` defaults to `true` so decimal and
dyadic floating-point denominators are factored into `scale` before reduction.
No model is materialized implicitly.
"""
function preprocess(
    model;
    rules=:identity,
    integerize_scale::Bool=(rules !== :identity),
    max_decimals::Integer=9,
    atol::Real=1e-12,
    kwargs...,
)
    ws = Workspace(model; rules, integerize_scale, max_decimals, atol)
    rules === :dominance && return ws, propagate!(ws;kwargs...)
    rules === :elimination && return ws, eliminate_low_degree!(ws;kwargs...)
    rules === :relations && return ws, contract_relations!(ws;kwargs...)
    rules === :mixed && return ws, schedule_reductions!(ws;kwargs...)
    isempty(kwargs) || throw(ArgumentError("propagation limits require rules=:dominance, rules=:elimination, rules=:relations or rules=:mixed"))
    return ws, IdentityReport(generation(ws), :identity, :quiescent, 0, 0)
end
