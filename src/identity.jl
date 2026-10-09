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

_floats(t::Tuple) = Float64[t...]
_ints(t::Tuple) = Int[t...]

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
        return QT.DictLinearForm{Float64}(Dict{Int,Float64}(zip(s.indices, s.values)))
    else
        return QT.DictQuadraticForm{Float64}(Dict{Tuple{Int,Int},Float64}(zip(s.indices, s.values)))
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

function _validate_label_copy(labels, owned)
    all(i -> isequal(labels[i], owned[i]) && isequal(owned[i], labels[i]) &&
             hash(labels[i]) == hash(owned[i]), eachindex(labels)) ||
        throw(ArgumentError("labels must preserve equality and hash under deepcopy"))
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
    all(isfinite, l.values) && all(isfinite, q.values) &&
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
    Workspace(model; rules=:identity)

Privately snapshot a finite Float64 QUBOTools model and its ordered labels.
Only `:identity` is supported. Source edits never change the snapshot; use
[`reset!`](@ref) to accept a new source. Labels must have stable equality/hash
semantics and preserve equality/hash under owned deep copies. Use each workspace
serially. Model metadata, solutions and warm starts are outside the objective snapshot.
"""
mutable struct Workspace
    _snapshot::_Snapshot
    _generation::Generation
    function Workspace(model; rules=:identity)
        _check_rules(rules)
        snapshot = _snapshot(model)
        return new(snapshot, Generation(uuid4(), uuid4()))
    end
end
_check_rules(rules) = rules === :identity ? nothing :
    throw(ArgumentError("only rules=:identity is implemented; requested $(repr(rules))"))

"""`generation(ws_or_export)` returns its immutable source/workspace identity."""
generation(ws::Workspace) = ws._generation

"""
    reset!(ws, model)

Validate a fresh snapshot before committing it. Failed validation preserves the
old workspace. Success creates a fresh generation, including for an identical
source. Owned exports remain evidence for their historical generation.
"""
function reset!(ws::Workspace, model)
    snapshot = _snapshot(model)
    token = Generation(generation(ws).workspace, uuid4())
    ws._snapshot = snapshot
    ws._generation = token
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
    materialize(ws; coefficient_type=Float64)

Explicitly capture an owned identity export. Only unchanged Float64 transport is
supported. No assumptions, deductions, deadline/work limits or alternate numeric
transport are implemented. Copies are proportional to stored source data.
"""
function materialize(ws::Workspace; coefficient_type=Float64)
    coefficient_type === Float64 || throw(ArgumentError("only Float64 identity transport is supported"))
    snapshot = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, snapshot.labels)
    return ExportResult(snapshot, generation(ws), :certified,
                        (scope=:original, reduction_chain=(), unchanged_representation=true))
end

"""`original_variables(ws_or_export)` returns owned labels in original index order."""
function original_variables(x::Union{Workspace,ExportResult})
    s = x._snapshot
    return _owned_labels(s.label_type[s.labels...])
end

"""`index_map(ws_or_export)` returns an owned original-index → residual-index vector."""
index_map(x::Union{Workspace,ExportResult}) = collect(1:length(x._snapshot.labels))

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

Validate a complete one-based original-domain vector and return an owned state
and ordinary Float64 original-energy evaluation. Reject missing, partial,
non-real, nonfinite and out-of-domain values. Numerical overflow is reported in
`energy.finite`; neither the energy nor this reconstruction certifies optimality.
"""
function reconstruct(result::ExportResult, y::AbstractVector)
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
    f = QT.Form{Float64}(length(state), _thaw(s.linear), _thaw(s.quadratic),
                         s.scale, s.offset; sense=s.sense, domain=s.domain)
    energy = QT.value(state, f)
    return Reconstruction(state, EnergyEvaluation(energy, isfinite(energy), :float64), generation(result))
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
    preprocess(model; rules=:identity)

Return `(workspace, identity_report)` using the same snapshot path as Workspace.
No model is materialized implicitly and no inference is performed.
"""
function preprocess(model; rules=:identity)
    ws = Workspace(model; rules)
    return ws, IdentityReport(generation(ws), :identity, :quiescent, 0, 0)
end
