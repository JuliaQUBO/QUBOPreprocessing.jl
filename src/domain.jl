# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

_domain_symbol(d::QT.Domain) = d === QT.BoolDomain ? :bool : :spin
function _qt_domain(s::Symbol)
    s === :bool && return QT.BoolDomain
    s === :spin && return QT.SpinDomain
    throw(ArgumentError("domain must be :bool or :spin; got $(repr(s))"))
end
_sense_symbol(s::QT.Sense) = s === QT.Min ? :min : :max

function _same_storage(a::_Storage, b::_Storage)
    return a.kind === b.kind && a.shape == b.shape && isequal(a.values, b.values) &&
           a.indices == b.indices && a.pointers == b.pointers
end
function _same_source(a::_Snapshot, b::_Snapshot)
    return a.label_type === b.label_type && a.state_type === b.state_type &&
           isequal(a.labels, b.labels) && isequal(a.scale, b.scale) && isequal(a.offset, b.offset) &&
           a.sense === b.sense && a.domain === b.domain &&
           _same_storage(a.linear, b.linear) && _same_storage(a.quadratic, b.quadratic)
end

mutable struct _GaugeConstantCursor
    epoch::UUID
    depth::Int
    tip_serial::UInt64
    constant::_Exact
    serials::Vector{UInt64}
    constants::Vector{_Exact}
end

function _source_gauged_bool_constant(s::_Snapshot, g::Tuple{Vararg{Int}})
    n = length(s.labels)
    f = QT.Form{Float64}(n, _thaw(s.linear), _thaw(s.quadratic), s.scale, s.offset;
                         sense=s.sense, domain=s.domain)
    is_bool = s.domain === QT.BoolDomain
    c = _Exact(s.offset)
    for (i, v) in QT.linear_terms(f)
        val_i = is_bool ? ((1 - g[i]) ÷ 2) : -g[i]
        val_i == 0 && continue
        c += _Exact(v) * val_i
    end
    for ((i, j), v) in QT.quadratic_terms(f)
        val_i = is_bool ? ((1 - g[i]) ÷ 2) : -g[i]
        val_j = is_bool ? ((1 - g[j]) ÷ 2) : -g[j]
        (val_i == 0 || val_j == 0) && continue
        c += _Exact(v) * (val_i * val_j)
    end
    return c
end

"""
    DomainGaugeMap

Checked coordinate bijection between a workspace's accepted source model and a
target domain (`:bool` or `:spin`) with spin gauge ``s_i = g_i t_i`` where
``g_i \\in \\{-1, +1\\}``. For binary coordinates ``x_i \\in \\{0, 1\\}`` and
canonical spin coordinates ``s_i = 2x_i - 1 \\in \\{-1, +1\\}``, the unscaled
polynomial satisfies ``J_{ij} = b_{ij}/4``,
``h_i = a_i/2 + \\sum_{j \\ne i} b_{ij}/4`` and
``c_{\\text{spin}} = c_{\\text{bool}} + \\frac{1}{2}\\sum_i a_i + \\frac{1}{4}\\sum_{i<j} b_{ij}``.
Under gauge ``g_i``, spin fields transform as ``h'_i = g_i h_i`` and couplings
as ``J'_{ij} = g_i g_j J_{ij}`` with unchanged spin constant. Target binary
coordinates relate to gauged spins by ``t_i = 2u_i - 1``.

Retains `generation`, `source_domain`, `target_domain`, `sense`, `scale`,
`offset`, `gauge` and ordered source identity. This is a bijective coordinate
map, not a variable fixing, local elimination or symmetry-breaking selection;
optional gauge selection transforms fields rather than assuming zero fields.
"""
struct DomainGaugeMap
    generation::Generation
    source_domain::Symbol
    target_domain::Symbol
    sense::Symbol
    scale::Float64
    offset::Float64
    gauge::Tuple{Vararg{Int}}
    _label_map::Dict{Any,Int}
    _source::_Snapshot
    _identity_gauge::Bool
    _validated::Bool
    _root_bool_constant::_Exact
    _cursor::_GaugeConstantCursor
    function DomainGaugeMap(
        generation::Generation,
        source_domain::Symbol,
        target_domain::Symbol,
        sense::Symbol,
        scale::Float64,
        offset::Float64,
        gauge::Tuple{Vararg{Int}},
        _label_map::Dict{Any,Int},
        _source::_Snapshot;
        _allow_unvalidated::Bool=false,
    )
        if !_allow_unvalidated
            source_domain === _domain_symbol(_source.domain) &&
                target_domain in (:bool, :spin) &&
                sense === _sense_symbol(_source.sense) &&
                isequal(scale, _source.scale) &&
                isequal(offset, _source.offset) ||
                throw(ArgumentError("DomainGaugeMap metadata does not match source snapshot"))
            length(gauge) == length(_source.labels) &&
                all(g -> g in (-1, 1), gauge) ||
                throw(ArgumentError("DomainGaugeMap gauge must contain ±1 for every source variable"))
            length(_label_map) == length(_source.labels) &&
                all(i -> get(_label_map, _source.labels[i], 0) == i, eachindex(_source.labels)) ||
                throw(ArgumentError("DomainGaugeMap label map does not match source labels"))
        end
        id_gauge = all(==(1), gauge)
        n = length(_source.labels)
        if !_allow_unvalidated && target_domain === :bool && !id_gauge
            root_c = _source_gauged_bool_constant(_source, gauge)
            cursor = _GaugeConstantCursor(UUID(UInt128(0)), 0, UInt64(0), root_c, zeros(UInt64, n), fill(_Exact(0), n))
        else
            root_c = _Exact(0)
            cursor = _GaugeConstantCursor(UUID(UInt128(0)), 0, UInt64(0), root_c, UInt64[], _Exact[])
        end
        return new(
            generation,
            source_domain,
            target_domain,
            sense,
            scale,
            offset,
            gauge,
            _label_map,
            _source,
            id_gauge,
            !_allow_unvalidated,
            root_c,
            cursor,
        )
    end
    function DomainGaugeMap(
        generation::Generation,
        source_domain::Symbol,
        target_domain::Symbol,
        sense::Symbol,
        scale::Float64,
        offset::Float64,
        gauge::Tuple{Vararg{Int}},
        _label_map::Dict{Any,Int},
        _source::_Snapshot,
        _identity_gauge::Bool,
        _validated::Bool,
        _root_bool_constant::_Exact,
        _cursor::_GaugeConstantCursor,
    )
        return new(
            generation,
            source_domain,
            target_domain,
            sense,
            scale,
            offset,
            gauge,
            _label_map,
            _source,
            _identity_gauge,
            _validated,
            _root_bool_constant,
            _cursor,
        )
    end
end
generation(m::DomainGaugeMap) = m.generation
original_variables(m::DomainGaugeMap) = _labels_vector(m._source)

function Base.deepcopy_internal(m::DomainGaugeMap, dict::IdDict)
    haskey(dict, m) && return dict[m]::DomainGaugeMap
    return DomainGaugeMap(
        m.generation,
        m.source_domain,
        m.target_domain,
        m.sense,
        m.scale,
        m.offset,
        _deepcopy_tuple(m.gauge, dict),
        Base.deepcopy_internal(m._label_map, dict),
        Base.deepcopy_internal(m._source, dict),
        m._identity_gauge,
        m._validated,
        Base.deepcopy_internal(m._root_bool_constant, dict),
        Base.deepcopy_internal(m._cursor, dict),
    )
end

function _check_gauge_scalar(v)
    !(v isa Bool) && v isa Real && isfinite(v) && (v == -1 || v == 1) ||
        throw(ArgumentError("gauge value must be -1 or +1"))
    return Int(v)
end

function _parse_gauge(ws::Workspace, gauge)
    n = length(ws._snapshot.labels)
    if gauge === nothing
        return Tuple(ones(Int, n))
    elseif gauge isa AbstractVector
        Base.require_one_based_indexing(gauge)
        length(gauge) == n || throw(ArgumentError("gauge vector must cover all $n original variables"))
        return Tuple(_check_gauge_scalar(v) for v in gauge)
    elseif gauge isa AbstractDict
        gvec = fill(1, n)
        for (label, v) in gauge
            i = _variable(ws, label)
            gvec[i] = _check_gauge_scalar(v)
        end
        return Tuple(gvec)
    else
        throw(ArgumentError("gauge must be nothing, an AbstractVector of ±1, or an AbstractDict of label => ±1"))
    end
end

"""
    domain_map(ws; domain=..., gauge=nothing)

Construct a checked [`DomainGaugeMap`](@ref) tied to `ws` and its current
[`generation`](@ref). `domain` must be `:bool` or `:spin` (defaulting to the
workspace's source domain). `gauge` may be `nothing` (all `+1`), a one-based
vector of `±1` in original variable order, or a dictionary of `label => ±1`
entries. Constructing a map validates and copies original label metadata in
`O(n)` without performing a whole-model quadratic matrix cast (or `O(n+m)` once
when precomputing the root constant offset for a non-identity binary gauge).
"""
function domain_map(ws::Workspace; domain::Symbol=_domain_symbol(ws._snapshot.domain), gauge=nothing)
    _qt_domain(domain)
    g = _parse_gauge(ws, gauge)
    source = ws._snapshot
    _validate_label_copy(source.labels, _deepcopy_tuple(source.labels, IdDict()))
    lmap = Dict{Any,Int}(v => i for (i, v) in enumerate(source.labels))
    m = DomainGaugeMap(
        generation(ws),
        _domain_symbol(source.domain),
        domain,
        _sense_symbol(source.sense),
        source.scale,
        source.offset,
        g,
        lmap,
        source,
    )
    if domain === :bool && !m._identity_gauge && !isempty(ws._state.fixes)
        _mapped_constant(ws, m)
    end
    return m
end

function _check_domain_map(ws::Workspace, m::DomainGaugeMap)
    generation(ws) == generation(m) || return (false, :stale_generation)
    s = ws._snapshot
    m.source_domain === _domain_symbol(s.domain) && m.target_domain in (:bool, :spin) &&
        m.sense === _sense_symbol(s.sense) && isequal(m.scale, s.scale) && isequal(m.offset, s.offset) ||
        return (false, :invalid_map)
    length(m.gauge) == length(s.labels) && all(g -> g in (-1, 1), m.gauge) &&
        m._identity_gauge == all(==(1), m.gauge) ||
        return (false, :invalid_gauge)
    _same_source(s, m._source) || return (false, :different_source)
    length(m._label_map) == length(s.labels) &&
        all(i -> get(m._label_map, s.labels[i], 0) == i, eachindex(s.labels)) ||
        return (false, :different_source)
    if m.target_domain === :bool && !m._identity_gauge
        m._root_bool_constant == _source_gauged_bool_constant(s, m.gauge) ||
            return (false, :invalid_map)
    end
    return (true, :verified)
end

function _validate_domain_map(ws::Workspace, m::DomainGaugeMap; full::Bool=false)
    if !full && m._validated && generation(ws) == generation(m) && m._source === ws._snapshot
        return nothing
    end
    ok, reason = _check_domain_map(ws, m)
    ok || throw(ArgumentError("invalid domain/gauge map for workspace ($reason)"))
    return nothing
end
_validate_domain_map(::Workspace, m; full::Bool=false) =
    throw(ArgumentError("expected a DomainGaugeMap; got $(typeof(m))"))

materialize(ws::Workspace, map::DomainGaugeMap; coefficient_type=Float64) =
    materialize(ws; coefficient_type, map)

function _check_domain_scalar(v, dom::Symbol)
    low = dom === :bool ? 0 : -1
    !(v isa Bool) && v isa Real && isfinite(v) && (v == low || v == 1) ||
        throw(ArgumentError("value is outside the $(repr(dom)) domain"))
    return Int(v)
end

function _map_index_value(m::DomainGaugeMap, i::Int, v::Int)
    s = m.source_domain === :bool ? (2 * v - 1) : v
    t = m.gauge[i] * s
    return m.target_domain === :bool ? ((t + 1) ÷ 2) : t
end

function _lift_index_value(m::DomainGaugeMap, i::Int, u::Int)
    t = m.target_domain === :bool ? (2 * u - 1) : u
    s = m.gauge[i] * t
    return m.source_domain === :bool ? ((s + 1) ÷ 2) : s
end

function _map_variable(m::DomainGaugeMap, label)
    i = get(m._label_map, label, 0)
    1 <= i <= length(m.gauge) && isequal(m._source.labels[i], label) ||
        throw(ArgumentError("unknown original variable label"))
    return i
end

"""
    map_value(map::DomainGaugeMap, label, value)

Map one original-domain assignment `value` for `label` into `map.target_domain`
under `map.gauge` (`x_i = (s_i + 1)/2`, `s_i = g_i t_i`).
"""
function map_value(m::DomainGaugeMap, label, value)
    i = _map_variable(m, label)
    v = _check_domain_scalar(value, m.source_domain)
    return _map_index_value(m, i, v)
end

"""
    lift_value(map::DomainGaugeMap, label, value)

Lift one target-domain assignment `value` for `label` back into
`map.source_domain` under `map.gauge` (`s_i = g_i t_i`, `x_i = (s_i + 1)/2`).
"""
function lift_value(m::DomainGaugeMap, label, value)
    i = _map_variable(m, label)
    u = _check_domain_scalar(value, m.target_domain)
    return _lift_index_value(m, i, u)
end

"""
    map_state(map::DomainGaugeMap, state::AbstractVector)

Bijectively map a complete original-order state vector from `map.source_domain`
into `map.target_domain` under `map.gauge`. Returns an owned `Vector{Int}`.
"""
function map_state(m::DomainGaugeMap, x::AbstractVector)
    Base.require_one_based_indexing(x)
    n = length(m.gauge)
    length(x) == n || throw(ArgumentError("state must cover all $n original variables"))
    out = Vector{Int}(undef, n)
    for i in 1:n
        v = _check_domain_scalar(x[i], m.source_domain)
        out[i] = _map_index_value(m, i, v)
    end
    return out
end
map_state(::DomainGaugeMap, _) = throw(ArgumentError("state must be a complete one-based vector"))

"""
    lift_state(map::DomainGaugeMap, state::AbstractVector)

Bijectively lift a complete original-order state vector from `map.target_domain`
back into `map.source_domain` under `map.gauge`. Returns an owned `Vector{Int}`.
"""
function lift_state(m::DomainGaugeMap, y::AbstractVector)
    Base.require_one_based_indexing(y)
    n = length(m.gauge)
    length(y) == n || throw(ArgumentError("state must cover all $n original variables"))
    out = Vector{Int}(undef, n)
    for i in 1:n
        u = _check_domain_scalar(y[i], m.target_domain)
        out[i] = _lift_index_value(m, i, u)
    end
    return out
end
lift_state(::DomainGaugeMap, _) = throw(ArgumentError("state must be a complete one-based vector"))

_spin_field(ws::Workspace, i::Int) =
    ws._snapshot.domain === QT.SpinDomain ? ws._state.fields[i] : ws._state.dual_fields[i]
_bool_field(ws::Workspace, i::Int) =
    ws._snapshot.domain === QT.BoolDomain ? ws._state.fields[i] : ws._state.dual_fields[i]
_spin_constant(ws::Workspace) =
    ws._snapshot.domain === QT.SpinDomain ? ws._state.constant : ws._state.dual_constant
_bool_constant(ws::Workspace) =
    ws._snapshot.domain === QT.BoolDomain ? ws._state.constant : ws._state.dual_constant
_spin_coupling(ws::Workspace, q::_Exact) =
    ws._snapshot.domain === QT.SpinDomain ? q : q // 4
_bool_coupling(ws::Workspace, q::_Exact) =
    ws._snapshot.domain === QT.BoolDomain ? q : 4 * q

function _mapped_field(ws::Workspace, i::Int, m::Union{Nothing,DomainGaugeMap})
    m === nothing && return ws._state.fields[i]
    g_i = m.gauge[i]
    if m.target_domain === :spin
        return g_i * _spin_field(ws, i)
    elseif m._identity_gauge
        return _bool_field(ws, i)
    else
        st = ws._state
        h_g = g_i * _spin_field(ws, i)
        coupling_sum = _Exact(0)
        for (j, q) in st.adjacency[i]
            st.fixed[j] == 2 || continue
            coupling_sum += (g_i * m.gauge[j]) * _spin_coupling(ws, q)
        end
        return 2 * h_g - 2 * coupling_sum
    end
end

function _mapped_coupling(ws::Workspace, i::Int, j::Int, q::_Exact, m::Union{Nothing,DomainGaugeMap})
    m === nothing && return q
    sign_ij = m.gauge[i] * m.gauge[j]
    return m.target_domain === :spin ? sign_ij * _spin_coupling(ws, q) :
                                       sign_ij * _bool_coupling(ws, q)
end

function _direct_mapped_constant(ws::Workspace, m::Union{Nothing,DomainGaugeMap})
    m === nothing && return ws._state.constant
    if m.target_domain === :spin
        return _spin_constant(ws)
    elseif m._identity_gauge
        return _bool_constant(ws)
    else
        st = ws._state
        c = _spin_constant(ws)
        for i in eachindex(st.fixed)
            st.fixed[i] == 2 || continue
            c -= m.gauge[i] * _spin_field(ws, i)
            for (j, q) in st.adjacency[i]
                i < j && st.fixed[j] == 2 || continue
                c += (m.gauge[i] * m.gauge[j]) * _spin_coupling(ws, q)
            end
        end
        return c
    end
end

function _mapped_constant(ws::Workspace, m::Union{Nothing,DomainGaugeMap})
    m === nothing && return ws._state.constant
    if m.target_domain === :spin
        return _spin_constant(ws)
    elseif m._identity_gauge
        return _bool_constant(ws)
    else
        st = ws._state
        cur = m._cursor
        k = length(st.fixes)
        tip = k == 0 ? UInt64(0) : st.trail[st.fixes[k]].serial
        if cur.epoch == st.epoch && cur.depth == k && cur.tip_serial == tip
            return cur.constant
        end
        if cur.epoch != st.epoch
            cur.epoch = st.epoch
            cur.depth = 0
            cur.tip_serial = UInt64(0)
            cur.constant = m._root_bool_constant
        end
        d = min(cur.depth, k)
        while d > 0 && cur.serials[d] != st.trail[st.fixes[d]].serial
            d -= 1
        end
        c = d == 0 ? m._root_bool_constant : cur.constants[d]
        for r in (d + 1):k
            pos = st.fixes[r]
            raw_entry = st.trail[pos]
            if raw_entry isa _UndoFix
                entry = raw_entry
                i = entry.index
                u_i = _map_index_value(m, i, entry.value)
                if u_i != 0
                    g_i = m.gauge[i]
                    h_i = _spin_field(ws, i)
                    csum = _Exact(0)
                    for (j, q) in st.adjacency[i]
                        (st.fixed[j] == 2 || st.entries[j] > pos) || continue
                        csum += (g_i * m.gauge[j]) * _spin_coupling(ws, q)
                    end
                    c += (2 * g_i * h_i - 2 * csum) * u_i
                end
                cur.serials[r] = entry.serial
            else
                red = raw_entry::_UndoReduction
                c += red.spin_const_delta
                for (w, dh) in red.spin_field_deltas
                    c -= m.gauge[w] * dh
                end
                for (j, l, dJ) in red.spin_coupling_deltas
                    c += (m.gauge[j] * m.gauge[l]) * dJ
                end
                cur.serials[r] = red.serial
            end
            cur.constants[r] = c
        end
        cur.depth = k
        cur.tip_serial = tip
        cur.constant = c
        return c
    end
end

"""
    degree(ws::Workspace, label)

Return the number of remaining nonzero quadratic interactions incident to
`label` among currently free variables, in `O(1)`. Fixed variables have degree
`0`. Stored zero quadratic entries do not count toward degree, and linear fields
are tracked separately via [`effective_field`](@ref).
"""
function degree(ws::Workspace, label)
    i = _variable(ws, label)
    return ws._state.fixed[i] == 2 ? ws._state.degrees[i] : 0
end

"""
    effective_field(ws::Workspace, label; map=nothing)

Return the exact `Rational{BigInt}` conditioned linear/field coefficient for a
currently free original `label`, either in the workspace's source domain
(`map=nothing`) or transported through a validated [`DomainGaugeMap`](@ref).
Requires no whole-model cast (`O(1)` in spin coordinates and identity-gauge
binary coordinates; `O(degree)` in gauged binary coordinates).
"""
function effective_field(ws::Workspace, label; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    ws._state.fixed[i] == 2 || throw(ArgumentError("effective_field requires a currently free variable"))
    return deepcopy(_mapped_field(ws, i, map))
end

"""
    incident_couplings(ws::Workspace, label; map=nothing)

Return owned `neighbor_label => Rational{BigInt}` pairs for remaining nonzero
interactions incident to a currently free `label`, either in the source domain
(`map=nothing`) or transported through a validated [`DomainGaugeMap`](@ref).
Costs `O(source degree)` without scanning the rest of the graph.
"""
function incident_couplings(ws::Workspace, label; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws, label)
    st, s = ws._state, ws._snapshot
    st.fixed[i] == 2 || throw(ArgumentError("incident_couplings requires a currently free variable"))
    V = s.label_type
    out = Pair{V,_Exact}[]
    for (j, q) in st.adjacency[i]
        st.fixed[j] == 2 || continue
        lbl = _owned_labels(V[s.labels[j]])[1]
        push!(out, lbl => deepcopy(_mapped_coupling(ws, i, j, q, map)))
    end
    return out
end

"""
    conditioned_constant(ws::Workspace; map=nothing)

Return the exact `Rational{BigInt}` unscaled conditioned constant offset of `ws`,
either in the source domain (`map=nothing`) or transported through a validated
[`DomainGaugeMap`](@ref). Spin constants are invariant under spin gauge `s_i = g_i t_i`
and are read in `O(1)` from the workspace's incremental state.
"""
function conditioned_constant(ws::Workspace; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map)
    return deepcopy(_mapped_constant(ws, map))
end

function _validate_nonneg_atol(atol)
    !(atol isa Bool) && atol isa Real && !isnan(atol) && atol >= 0 ||
        throw(ArgumentError("atol must be a nonnegative real number; got $(repr(atol))"))
    return nothing
end

"""
    coercive_fields(ws::Workspace; map=nothing) -> Vector{Rational{BigInt}}

Return the exact conditioned Ising local fields ``h_i`` for all currently free
variables in ascending `free_variables` order. In `:bool` workspaces,
``h_i = \\frac{1}{2} L_i + \\frac{1}{4} \\sum_{j \\in \\text{free}} Q_{i,j}``;
in `:spin` workspaces, ``h_i = L_i``. When a validated [`DomainGaugeMap`](@ref)
is supplied, each field is multiplied by its spin gauge ``g_i \\in \\{-1, +1\\}``.
"""
function coercive_fields(ws::Workspace; map::Union{Nothing,DomainGaugeMap}=nothing)
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    out = _Exact[]
    sizehint!(out, count(==(2), st.fixed))
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        g_i = map === nothing ? 1 : map.gauge[i]
        push!(out, deepcopy(g_i * _spin_field(ws, i)))
    end
    return out
end

function _ws_coercive_ratios_and_active(ws::Workspace; norm::Real=2)
    !(norm isa Bool) && norm > 0 && !isnan(norm) ||
        throw(ArgumentError("norm must be positive; got $(repr(norm))"))
    st = ws._state
    n_free = count(==(2), st.fixed)
    ratios = Vector{Float64}(undef, n_free)
    active = falses(n_free)
    n_free == 0 && return ratios, active

    setprecision(BigFloat, 256) do
        pos = 0
        for i in eachindex(st.fixed)
            st.fixed[i] == 2 || continue
            pos += 1
            abs_h = abs(_spin_field(ws, i))
            abs_js = _Exact[]
            for (j, q) in st.adjacency[i]
                (st.fixed[j] == 2 && !iszero(q)) || continue
                push!(abs_js, abs(_spin_coupling(ws, q)))
            end
            if isempty(abs_js)
                ratios[pos] = iszero(abs_h) ? 0.0 : Inf
                active[pos] = false
            else
                j_norm = if isinf(norm)
                    BigFloat(maximum(abs_js))
                elseif norm == 1
                    BigFloat(sum(abs_js))
                elseif norm == 2
                    max_j = maximum(abs_js)
                    s2 = sum((r = c / max_j; r * r) for c in abs_js)
                    BigFloat(max_j) * sqrt(BigFloat(s2))
                else
                    max_j = BigFloat(maximum(abs_js))
                    p_bf = BigFloat(norm)
                    sp = sum((BigFloat(c) / max_j)^p_bf for c in abs_js)
                    max_j * (sp^(inv(p_bf)))
                end
                ratios[pos] = Float64(BigFloat(abs_h) / j_norm)
                active[pos] = true
            end
        end
    end
    return ratios, active
end

"""
    coercive_field_ratios(ws::Workspace; norm::Real=2, map=nothing) -> Vector{Float64}

Return the per-free-variable coercive-field-to-coupling ratios
``|h_i| / \\|J_{i,\\cdot}\\|_p`` on the conditioned residual graph of `ws` in
ascending `free_variables` order. Isolated free variables with ``\\|J_{i,\\cdot}\\|_p = 0``
yield `0.0` when ``h_i = 0`` and `Inf` when ``h_i \\neq 0``.
"""
function coercive_field_ratios(
    ws::Workspace;
    norm::Real=2,
    map::Union{Nothing,DomainGaugeMap}=nothing,
)
    map === nothing || _validate_domain_map(ws, map)
    return first(_ws_coercive_ratios_and_active(ws; norm))
end

"""
    coercive_field_ratio(ws::Workspace; norm::Real=2, map=nothing) -> Float64

Return the arithmetic mean of [`coercive_field_ratios`](@ref) over all currently
free variables with at least one active incident coupling (`NaN` if no free
variable has an active coupling).
"""
function coercive_field_ratio(
    ws::Workspace;
    norm::Real=2,
    map::Union{Nothing,DomainGaugeMap}=nothing,
)
    map === nothing || _validate_domain_map(ws, map)
    ratios, active = _ws_coercive_ratios_and_active(ws; norm)
    k = count(active)
    k == 0 && return NaN
    return setprecision(BigFloat, 256) do
        s = zero(BigFloat)
        for idx in eachindex(ratios)
            active[idx] && (s += BigFloat(ratios[idx]))
        end
        return Float64(s / k)
    end
end

"""
    is_gauge_invariant(ws::Workspace; atol::Real=0//1, map=nothing) -> Bool

Return `true` iff every currently free variable in `ws` satisfies ``|h_i| \\le \\text{atol}``
(so the conditioned residual Ising Hamiltonian is ``\\mathbb{Z}_2`` spin-flip
invariant up to `atol`).
"""
function is_gauge_invariant(
    ws::Workspace;
    atol::Real=0//1,
    map::Union{Nothing,DomainGaugeMap}=nothing,
)
    _validate_nonneg_atol(atol)
    map === nothing || _validate_domain_map(ws, map)
    isinf(atol) && return true
    atol_ex = _Exact(atol)
    st = ws._state
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        abs(_spin_field(ws, i)) <= atol_ex || return false
    end
    return true
end

"""
    zero_field_fraction(ws::Workspace; atol::Real=0//1, map=nothing) -> Float64

Return the fraction of currently free variables in `ws` whose conditioned Ising
local field satisfies ``|h_i| \\le \\text{atol}`` (`NaN` when `free_count(ws) == 0`).
"""
function zero_field_fraction(
    ws::Workspace;
    atol::Real=0//1,
    map::Union{Nothing,DomainGaugeMap}=nothing,
)
    _validate_nonneg_atol(atol)
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    n_free = 0
    z_cnt = 0
    atol_ex = isinf(atol) ? _Exact(0) : _Exact(atol)
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        n_free += 1
        (isinf(atol) || abs(_spin_field(ws, i)) <= atol_ex) && (z_cnt += 1)
    end
    n_free == 0 && return NaN
    return z_cnt / n_free
end

"""
    trivial_dominance_fraction(ws::Workspace; atol::Real=0//1, map=nothing) -> Float64

Return the fraction of currently free variables in `ws` whose conditioned Ising
local field strictly dominates its incident coupling ``\\ell_1`` norm by more than
`atol` (``|h_i| > \\sum_{j \\in N(i)} |J_{i,j}| + \\text{atol}``; `NaN` when
`free_count(ws) == 0`).
"""
function trivial_dominance_fraction(
    ws::Workspace;
    atol::Real=0//1,
    map::Union{Nothing,DomainGaugeMap}=nothing,
)
    _validate_nonneg_atol(atol)
    map === nothing || _validate_domain_map(ws, map)
    st = ws._state
    n_free = count(==(2), st.fixed)
    n_free == 0 && return NaN
    isinf(atol) && return 0.0
    atol_ex = _Exact(atol)
    dom_cnt = 0
    for i in eachindex(st.fixed)
        st.fixed[i] == 2 || continue
        abs_h = abs(_spin_field(ws, i))
        l1 = _Exact(0)
        for (j, q) in st.adjacency[i]
            (st.fixed[j] == 2 && !iszero(q)) || continue
            l1 += abs(_spin_coupling(ws, q))
        end
        abs_h > l1 + atol_ex && (dom_cnt += 1)
    end
    return dom_cnt / n_free
end
