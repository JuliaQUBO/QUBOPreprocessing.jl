# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""
    DominanceStep

Compact strong-persistency witness. Bounds enclose the normalized derivative
of the unscaled objective: normalization multiplies by the sign of scale and
objective sense, never by a potentially overflowing magnitude. `predecessors`
is the number of preceding steps in the ordered certificate prefix; every
preceding deduction is therefore explicit without copying the chain per step.
`constant` binds the exact conditioned offset. Indices refer to original order.
"""
struct DominanceStep <: _ProofRecord
    variable::Int
    value::Int
    lower::_Exact
    upper::_Exact
    constant::_Exact
    predecessors::Int
    method::Symbol
    scope_length::Int
end
DominanceStep(i,v,lo,hi,c,p,m) = DominanceStep(i,v,lo,hi,c,p,m,-1)

"""
    DominanceCertificate

Owned source/generation, explicit caller scope and ordered strict-dominance
steps. Every step retains all scoped optima. This is a proof of restrictions,
not a certificate that a supplied solver state is optimal. Source, scope and
step capture are explicit export work; the propagation layer can retain compact
`DominanceStep` records without copying the source at each inference.
"""
struct DominanceCertificate
    generation::Generation
    _scope_checkpoint::Checkpoint
    assumptions::Tuple
    steps::Tuple
    _source::_Snapshot
    _map::Union{Nothing,DomainGaugeMap}
end
DominanceCertificate(g,cp,a,s,src) = DominanceCertificate(g,cp,a,s,src,nothing)
generation(c::DominanceCertificate) = c.generation

"""Proof attempt with optional `certificate`, `stop_reason`, numeric `method`,
adjacency `edge_visits`, and explicit `exact_fallbacks`/`exact_work` counters."""
struct DominanceAttempt
    certificate::Union{Nothing,DominanceCertificate}
    stop_reason::Symbol
    method::Symbol
    edge_visits::Int
    exact_fallbacks::Int
    exact_work::Int
end

"""Read-only verification result: `valid`, `stop_reason` and charged `term_visits`.
A budget/deadline stop is not verification success."""
struct VerificationResult
    valid::Bool
    stop_reason::Symbol
    term_visits::Int
end

_caller_scope(ws::Workspace) = Tuple(ws._state.trail[p].index=>ws._state.trail[p].value
                                    for p in ws._state.callers)
_direction(s::_Snapshot) = iszero(s.scale) ? 0 :
    (s.sense === QT.Min ? 1 : -1) * (signbit(s.scale) ? -1 : 1)

# Check the enclosure against the exact cached field rather than assuming a
# rational-to-float conversion is correctly rounded. No global rounding mode.
function _enclose(q::_Exact)
    v = Float64(q)
    isfinite(v) || return (-Inf,Inf)
    exact = _Exact(v)
    lo = exact > q ? prevfloat(v) : v
    hi = exact < q ? nextfloat(v) : v
    isfinite(lo) && isfinite(hi) && _Exact(lo) <= q <= _Exact(hi) || return (-Inf,Inf)
    return lo,hi
end

function _strict_value(lower, upper, domain)
    lower > 0 && return domain === QT.BoolDomain ? 0 : -1
    upper < 0 && return 1
    return nothing
end

# Internal numeric seam for #4 and #13: no model copy, proof export or assumption scan.
# Caller supplies predecessor count and persists the returned compact step.
function _dominance_witness(ws::Workspace, i::Int; map::Union{Nothing,DomainGaugeMap}=nothing,
                            max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing,
                            predecessors=0,scope_length=-1)
    _limits(max_work,deadline_ns)
    _limits(max_exact_work,deadline_ns)
    map === nothing || _validate_domain_map(ws, map)
    st, s = ws._state, ws._snapshot
    st.fixed[i] == 2 || return (nothing,:already_fixed,:none,0,0,0)
    direction = _direction(s)
    direction != 0 || return (nothing,:zero_scale,:none,0,0,0)
    degree = length(st.adjacency[i])
    degree <= max_work || return (nothing,:work_limit,:none,0,0,0)
    _expired(deadline_ns) && return (nothing,:deadline,:none,0,0,0)
    target_dom = map === nothing ? s.domain : _qt_domain(map.target_domain)
    gauged_bool = map !== nothing && map.target_domain === :bool && !all(==(1), map.gauge)
    init_field = if map === nothing
        direction * st.fields[i]
    elseif map.target_domain === :spin
        direction * map.gauge[i] * _spin_field(ws, i)
    elseif !gauged_bool
        direction * _bool_field(ws, i)
    else
        2 * direction * map.gauge[i] * _spin_field(ws, i)
    end
    lo, hi = _enclose(init_field)
    visits = 0
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
        visits += 1
        st.fixed[j] == 2 || continue
        if map === nothing
            # Adjacency coefficients are unchanged exact source Float64 values.
            coefficient = direction*Float64(q)
            a,b = s.domain === QT.BoolDomain ? (min(0.0,coefficient),max(0.0,coefficient)) :
                                                 (-abs(coefficient),abs(coefficient))
        elseif map.target_domain === :spin
            c_lo, c_hi = _enclose(direction * _mapped_coupling(ws, i, j, q, map))
            m = max(abs(c_lo), abs(c_hi))
            a, b = -m, m
        elseif !gauged_bool
            c_lo, c_hi = _enclose(direction * _bool_coupling(ws, q))
            a, b = min(0.0, c_lo), max(0.0, c_hi)
        else
            c_lo, c_hi = _enclose(2 * _spin_coupling(ws, q))
            m = max(abs(c_lo), abs(c_hi))
            a, b = -m, m
        end
        lo = prevfloat(lo + a)
        hi = nextfloat(hi + b)
    end
    mapped_val = isfinite(lo) && isfinite(hi) ? _strict_value(lo,hi,target_dom) : nothing
    _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
    if mapped_val !== nothing
        value = map === nothing ? mapped_val : _lift_index_value(map, i, mapped_val)
        c_val = _mapped_constant(ws, map)
        step = DominanceStep(i,value,_Exact(lo),_Exact(hi),deepcopy(c_val),predecessors,:interval,scope_length)
        return (step,:proved,:interval,visits,0,0)
    end
    # Reserve the complete fallback before doing it. Exact work counts the
    # initial field and each free coefficient addition; adjacency visits include
    # both passes, including fixed neighbors skipped by arithmetic.
    degree <= max_work - visits || return (nothing,:work_limit,:interval,visits,0,0)
    degree < max_exact_work || return (nothing,:verification_limit,:interval,visits,0,0)
    lower = init_field
    upper = lower
    exact_work = 1
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
        visits += 1
        st.fixed[j] == 2 || continue
        if map === nothing
            a = direction*q
            lower += s.domain === QT.BoolDomain ? min(0,a) : -abs(a)
            upper += s.domain === QT.BoolDomain ? max(0,a) : abs(a)
        elseif map.target_domain === :spin
            c = abs(_mapped_coupling(ws, i, j, q, map))
            lower -= c
            upper += c
        elseif !gauged_bool
            c = direction * _bool_coupling(ws, q)
            lower += min(0, c)
            upper += max(0, c)
        else
            c = 2 * abs(_spin_coupling(ws, q))
            lower -= c
            upper += c
        end
        exact_work += 1
    end
    _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
    mapped_val = _strict_value(lower,upper,target_dom)
    mapped_val === nothing && return (nothing,:not_strict,:exact,visits,1,exact_work)
    value = map === nothing ? mapped_val : _lift_index_value(map, i, mapped_val)
    c_val = _mapped_constant(ws, map)
    step = DominanceStep(i,value,deepcopy(lower),deepcopy(upper),deepcopy(c_val),predecessors,:exact,scope_length)
    return (step,:proved,:exact,visits,1,exact_work)
end

function _convert_step_bounds(s::_Snapshot, step::DominanceStep,
                              from_map::Union{Nothing,DomainGaugeMap},
                              to_map::Union{Nothing,DomainGaugeMap})
    i = step.variable
    from_dom = from_map === nothing ? _domain_symbol(s.domain) : from_map.target_domain
    from_g = from_map === nothing ? 1 : from_map.gauge[i]
    lo_g = from_dom === :bool ? (step.lower // 2) : step.lower
    hi_g = from_dom === :bool ? (step.upper // 2) : step.upper
    lo_spin, hi_spin = from_g == 1 ? (lo_g, hi_g) : (-hi_g, -lo_g)
    to_dom = to_map === nothing ? _domain_symbol(s.domain) : to_map.target_domain
    to_g = to_map === nothing ? 1 : to_map.gauge[i]
    lo_to_g, hi_to_g = to_g == 1 ? (lo_spin, hi_spin) : (-hi_spin, -lo_spin)
    new_lo = to_dom === :bool ? (2 * lo_to_g) : lo_to_g
    new_hi = to_dom === :bool ? (2 * hi_to_g) : hi_to_g
    return deepcopy(new_lo), deepcopy(new_hi)
end

function _root_spin_polynomial(s::_Snapshot, adjacency::Vector{Vector{Pair{Int,_Exact}}})
    n = length(s.labels)
    src_fields = fill(_Exact(0), n)
    f = QT.Form{Float64}(n, _thaw(s.linear), _thaw(s.quadratic), s.scale, s.offset;
                         sense=s.sense, domain=s.domain)
    for (i, v) in QT.linear_terms(f)
        src_fields[i] = _Exact(v)
    end
    if s.domain === QT.SpinDomain
        return src_fields, _Exact(s.offset)
    end
    spin_fields = Vector{_Exact}(undef, n)
    quad_sum = _Exact(0)
    for i in 1:n
        csum = _Exact(0)
        for (j, q) in adjacency[i]
            csum += q
            i < j && (quad_sum += q)
        end
        spin_fields[i] = src_fields[i] // 2 + csum // 4
    end
    spin_const = _Exact(s.offset) + sum(src_fields; init=_Exact(0)) // 2 + quad_sum // 4
    return spin_fields, spin_const
end

function _step_constant_at(ws::Workspace, fixed::Dict{Int,Int},
                           spin_fields::Vector{_Exact}, spin_const::_Exact,
                           to_map::Union{Nothing,DomainGaugeMap})
    s, st = ws._snapshot, ws._state
    target_dom = to_map === nothing ? _domain_symbol(s.domain) : to_map.target_domain
    target_dom === :spin && return deepcopy(spin_const)
    gauge = to_map === nothing ? ntuple(_ -> 1, length(s.labels)) : to_map.gauge
    c = spin_const
    for i in eachindex(s.labels)
        haskey(fixed, i) && continue
        c -= gauge[i] * spin_fields[i]
        for (j, q) in st.adjacency[i]
            i < j && !haskey(fixed, j) || continue
            J_ij = _spin_coupling(ws, q)
            c += (gauge[i] * gauge[j]) * J_ij
        end
    end
    return deepcopy(c)
end

function _transport_steps(ws::Workspace, assumptions::Tuple, steps::Tuple,
                          from_map::Union{Nothing,DomainGaugeMap},
                          to_map::Union{Nothing,DomainGaugeMap})
    isempty(steps) && return ()
    s, st = ws._snapshot, ws._state
    spin_fields, spin_const = _root_spin_polynomial(s, st.adjacency)
    fixed = Dict{Int,Int}()
    function apply_fix!(idx::Int, val::Int)
        s_val = s.domain === QT.BoolDomain ? (2 * val - 1) : val
        spin_const += spin_fields[idx] * s_val
        for (nbr, q) in st.adjacency[idx]
            haskey(fixed, nbr) && continue
            spin_fields[nbr] += _spin_coupling(ws, q) * s_val
        end
        fixed[idx] = val
    end
    introduced = 0
    out = Vector{DominanceStep}(undef, length(steps))
    for (k, step) in enumerate(steps)
        count = step.scope_length == -1 ? length(assumptions) : step.scope_length
        for p in introduced+1:count
            idx, val = assumptions[p]
            apply_fix!(idx, val)
        end
        introduced = count
        new_lo, new_hi = _convert_step_bounds(s, step, from_map, to_map)
        new_c = _step_constant_at(ws, fixed, spin_fields, spin_const, to_map)
        out[k] = DominanceStep(step.variable, step.value, new_lo, new_hi, new_c,
                               step.predecessors, step.method, step.scope_length)
        apply_fix!(step.variable, step.value)
    end
    return Tuple(out)
end

"""
    prove_dominance(ws, label; map=nothing, max_work=typemax(Int),
                    max_exact_work=typemax(Int), deadline_ns=nothing)

Prove one strong strict-dominance restriction without changing the workspace,
optionally operating in the coordinate system of `map::DomainGaugeMap`.
Use signed derivative bounds under the current explicit caller assumptions,
with conservative floating enclosures and budgeted exact fallback. Ties, zero
scale, work/deadline exhaustion and unresolved signs yield no certificate.
`edge_visits` includes both passes; fallback work/allocations remain explicit.

The numeric check touches incident adjacency. Successful public proof export
additionally copies O(n+m) source data and O(k) assumptions; it is an explicit
verification/export boundary, not an inner-loop propagation API. No deduction
is installed here. Select `rules=:dominance` and call `propagate!` to commit
a bounded cascade using the workspace's exact caches.
"""
function prove_dominance(ws::Workspace, label; map::Union{Nothing,DomainGaugeMap}=nothing,
                         max_work=typemax(Int), max_exact_work=typemax(Int), deadline_ns=nothing)
    map === nothing || _validate_domain_map(ws, map)
    i = _variable(ws,label)
    step, reason, method, visits, fallbacks, exact_work = _dominance_witness(ws,i;
        map,max_work,max_exact_work,deadline_ns,predecessors=ws._state.proof_count,
        scope_length=length(ws._state.callers))
    certificate = if step === nothing
        nothing
    else
        source = deepcopy(ws._snapshot)
        _validate_label_copy(ws._snapshot.labels,source.labels)
        owned_map = map === nothing ? nothing : deepcopy(map)
        prefix = _proof_steps(ws; map=owned_map)
        _expired(deadline_ns) && return DominanceAttempt(nothing,:deadline,method,visits,fallbacks,exact_work)
        DominanceCertificate(generation(ws),checkpoint(ws),_caller_scope(ws),(prefix...,step),source,owned_map)
    end
    return DominanceAttempt(certificate,reason,method,visits,fallbacks,exact_work)
end

"""
    transport_certificate(ws::Workspace, cert::DominanceCertificate, map::DomainGaugeMap)

Transport a valid [`DominanceCertificate`](@ref) for `ws` into the coordinate
representation of `map` while preserving its `generation`, branch checkpoint,
explicit caller `assumptions` and lifted original-domain deductions. Rejects
stale generations, mismatched source/variable ordering, invalid gauges or
stale branch scopes with `ArgumentError`.
"""
function transport_certificate(ws::Workspace, cert::DominanceCertificate, map::DomainGaugeMap)
    _validate_domain_map(ws, map)
    generation(ws) == generation(cert) || throw(ArgumentError("certificate belongs to a stale generation"))
    _same_source(ws._snapshot, cert._source) || throw(ArgumentError("certificate source does not match workspace"))
    cert.assumptions == _caller_scope(ws) && cert._scope_checkpoint._depth == length(ws._state.trail) ||
        throw(ArgumentError("certificate scope does not match current workspace trail"))
    _validate_checkpoint(ws, cert._scope_checkpoint)
    cert._map === nothing || _validate_domain_map(ws, cert._map)
    isempty(cert.steps) && throw(ArgumentError("certificate contains no proof steps"))
    source = deepcopy(ws._snapshot)
    _validate_label_copy(ws._snapshot.labels, source.labels)
    owned_map = deepcopy(map)
    steps = _transport_steps(ws, cert.assumptions, cert.steps, cert._map, owned_map)
    return DominanceCertificate(generation(ws), checkpoint(ws), cert.assumptions, steps, source, owned_map)
end

# Independent verifier: re-read the original represented polynomial on each
# step and substitute a dictionary of explicit assumptions/validated prefix
# deductions. Do not read cached boundary fields, adjacency, constant or queue,
# and do not call the producer's bound or conditioning helper.
function _verify_polynomial(s::_Snapshot, fixed, step::DominanceStep,
                            active_map::Union{Nothing,DomainGaugeMap}, remaining, deadline)
    n = length(s.labels)
    1 <= step.variable <= n && !haskey(fixed,step.variable) || return (false,:invalid_step,0)
    low = s.domain === QT.BoolDomain ? 0 : -1
    step.value in (low,1) || return (false,:invalid_value,0)
    step.method in (:interval,:exact) || return (false,:invalid_method,0)
    direction = _direction(s)
    direction != 0 || return (false,:zero_scale,0)
    # Storage reconstruction and iteration are charged before allocating it.
    cost = length(s.linear.values) + length(s.quadratic.values)
    cost <= remaining || return (false,:work_limit,0)
    _expired(deadline) && return (false,:deadline,0)
    f = QT.Form{Float64}(n,_thaw(s.linear),_thaw(s.quadratic),s.scale,s.offset;
                         sense=s.sense,domain=s.domain)
    if active_map === nothing
        lower,upper,constant = _Exact(0),_Exact(0),_Exact(s.offset)
        visits = 0
        for (i,v) in QT.linear_terms(f)
            _expired(deadline) && return (false,:deadline,cost)
            visits += 1
            haskey(fixed,i) && (constant += _Exact(v)*fixed[i])
            if i == step.variable
                lower += direction*_Exact(v)
                upper += direction*_Exact(v)
            end
        end
        for ((i,j),v) in QT.quadratic_terms(f)
            _expired(deadline) && return (false,:deadline,cost)
            visits += 1
            if haskey(fixed,i) && haskey(fixed,j)
                constant += _Exact(v)*fixed[i]*fixed[j]
            end
            (i == step.variable || j == step.variable) || continue
            other = i == step.variable ? j : i
            coefficient = direction*_Exact(v)
            if haskey(fixed,other)
                lower += coefficient*fixed[other]
                upper += coefficient*fixed[other]
            elseif s.domain === QT.BoolDomain
                lower += min(0,coefficient)
                upper += max(0,coefficient)
            else
                lower -= abs(coefficient)
                upper += abs(coefficient)
            end
        end
        _expired(deadline) && return (false,:deadline,cost)
        constant == step.constant || return (false,:invalid_constant,cost)
        enclosure = step.method === :exact ? step.lower == lower && step.upper == upper :
                                             step.lower <= lower <= upper <= step.upper
        enclosure && _strict_value(step.lower,step.upper,s.domain) == step.value ||
            return (false,:invalid_bound,cost)
        return (true,:verified,cost)
    end
    # Independent domain/gauge polynomial verification from raw source storage:
    # 1. Substitute fixed variables in original coordinates.
    src_fields = fill(_Exact(0), n)
    src_constant = _Exact(s.offset)
    free_couplings = Tuple{Int,Int,_Exact}[]
    for (i,v) in QT.linear_terms(f)
        _expired(deadline) && return (false,:deadline,cost)
        ev = _Exact(v)
        if haskey(fixed,i)
            src_constant += ev * fixed[i]
        else
            src_fields[i] += ev
        end
    end
    for ((i,j),v) in QT.quadratic_terms(f)
        _expired(deadline) && return (false,:deadline,cost)
        ev = _Exact(v)
        if haskey(fixed,i) && haskey(fixed,j)
            src_constant += ev * fixed[i] * fixed[j]
        elseif haskey(fixed,i)
            src_fields[j] += ev * fixed[i]
        elseif haskey(fixed,j)
            src_fields[i] += ev * fixed[j]
        elseif !iszero(ev)
            push!(free_couplings, (min(i,j), max(i,j), ev))
        end
    end
    # 2. Convert free polynomial to canonical spin: J_ij = b_ij/4, h_i = a_i/2 + sum_j b_ij/4,
    #    c_spin = c_bool + sum_i a_i/2 + sum_{i<j} b_ij/4.
    h_spin = fill(_Exact(0), n)
    c_spin = src_constant
    if s.domain === QT.BoolDomain
        for i in 1:n
            haskey(fixed,i) && continue
            h_spin[i] = src_fields[i] // 2
            c_spin += src_fields[i] // 2
        end
        for (i,j,b_ij) in free_couplings
            J_ij = b_ij // 4
            h_spin[i] += J_ij
            h_spin[j] += J_ij
            c_spin += J_ij
        end
    else
        for i in 1:n
            haskey(fixed,i) && continue
            h_spin[i] = src_fields[i]
        end
    end
    # 3. Apply spin gauge s_i = g_i * t_i: h'_i = g_i * h_i, J'_{ij} = g_i * g_j * J_ij.
    g = active_map.gauge
    h_gauged = fill(_Exact(0), n)
    for i in 1:n
        haskey(fixed,i) && continue
        h_gauged[i] = g[i] * h_spin[i]
    end
    J_gauged = Tuple{Int,Int,_Exact}[
        (i, j, g[i] * g[j] * (s.domain === QT.BoolDomain ? (q // 4) : q))
        for (i, j, q) in free_couplings
    ]
    u = step.variable
    if active_map.target_domain === :spin
        constant = c_spin
        lower = direction * h_gauged[u]
        upper = lower
        for (i, j, J_ij) in J_gauged
            (i == u || j == u) || continue
            c = abs(direction * J_ij)
            lower -= c
            upper += c
        end
    else
        # 4. Inverse spin -> bool on gauged spins t_i = 2*u_i - 1:
        #    b'_{ij} = 4*J'_{ij}, a'_i = 2*h'_i - 2*sum_j J'_{ij},
        #    c_bool = c_spin - sum_i h'_i + sum_{i<j} J'_{ij}.
        a_bool = fill(_Exact(0), n)
        constant = c_spin
        for i in 1:n
            haskey(fixed,i) && continue
            a_bool[i] = 2 * h_gauged[i]
            constant -= h_gauged[i]
        end
        for (i, j, J_ij) in J_gauged
            a_bool[i] -= 2 * J_ij
            a_bool[j] -= 2 * J_ij
            constant += J_ij
        end
        lower = direction * a_bool[u]
        upper = lower
        for (i, j, J_ij) in J_gauged
            (i == u || j == u) || continue
            b_ij = direction * (4 * J_ij)
            lower += min(0, b_ij)
            upper += max(0, b_ij)
        end
    end
    _expired(deadline) && return (false,:deadline,cost)
    constant == step.constant || return (false,:invalid_constant,cost)
    enclosure = step.method === :exact ? step.lower == lower && step.upper == upper :
                                         step.lower <= lower <= upper <= step.upper
    target_dom = _qt_domain(active_map.target_domain)
    mapped_val = _strict_value(step.lower, step.upper, target_dom)
    enclosure && mapped_val !== nothing && _lift_index_value(active_map, u, mapped_val) == step.value ||
        return (false,:invalid_bound,cost)
    return (true,:verified,cost)
end

"""
    verify_certificate(ws, certificate; map=nothing, max_work=typemax(Int), deadline_ns=nothing)

Independently recheck source identity, current caller scope, optional
[`DomainGaugeMap`](@ref) provenance and the complete ordered strong-dominance
chain using exact original-coefficient substitution and domain/gauge conversion.
Never trust cached workspace fields or an authenticated identifier alone.
Undoing/changing assumptions, changing gauge/domain or resetting the model
invalidates applicability. Source/label validation costs O(n+m); each step scans
source storage, so this explicit verifier can cost O(steps*(n+m)). Dense storage
costs O(n²) per scan. Work is reserved before scans; exhausted work/deadline
yields `valid=false`. This does not validate a solver optimum or certify a
rounded residual export.
"""
function verify_certificate(ws::Workspace, cert::DominanceCertificate;
                            map::Union{Nothing,DomainGaugeMap}=nothing,
                            max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work,deadline_ns)
    generation(ws) == generation(cert) || return VerificationResult(false,:stale_generation,0)
    _expired(deadline_ns) && return VerificationResult(false,:deadline,0)
    s = ws._snapshot
    cost = length(s.labels) + length(s.linear.values) + length(s.quadratic.values)
    cost <= max_work || return VerificationResult(false,:work_limit,0)
    _same_source(s,cert._source) || return VerificationResult(false,:different_source,cost)
    if cert._map !== nothing
        ok, reason = _check_domain_map(ws, cert._map)
        ok || return VerificationResult(false, reason, cost)
    end
    if map !== nothing
        ok, reason = _check_domain_map(ws, map)
        ok || return VerificationResult(false, reason, cost)
        if cert._map === nothing
            map.target_domain === _domain_symbol(s.domain) ||
                return VerificationResult(false, :invalid_map, cost)
            all(==(1), map.gauge) ||
                return VerificationResult(false, :invalid_gauge, cost)
        else
            map.target_domain === cert._map.target_domain ||
                return VerificationResult(false, :invalid_map, cost)
            map.gauge == cert._map.gauge ||
                return VerificationResult(false, :invalid_gauge, cost)
        end
    end
    active_map = cert._map !== nothing ? cert._map : map
    cert.assumptions == _caller_scope(ws) || return VerificationResult(false,:stale_scope,cost)
    # A valid ancestor alone cannot bind the complete current scope. Requiring
    # the tip depth lets lineage validation below check its generation, epoch
    # and exact serial, including after an identical branch is reapplied.
    cert._scope_checkpoint._depth == length(ws._state.trail) ||
        return VerificationResult(false,:stale_scope,cost)
    try
        _validate_checkpoint(ws,cert._scope_checkpoint)
    catch error
        error isa ArgumentError || rethrow()
        return VerificationResult(false,:stale_scope,cost)
    end
    _expired(deadline_ns) && return VerificationResult(false,:deadline,cost)
    isempty(cert.steps) && return VerificationResult(false,:empty_proof,cost)
    fixed = Dict{Int,Int}()
    seen = Set{Int}()
    low = s.domain === QT.BoolDomain ? 0 : -1
    for assumption in cert.assumptions
        assumption isa Pair{Int,Int} || return VerificationResult(false,:invalid_scope,cost)
        i,v = assumption
        1 <= i <= length(s.labels) && !(i in seen) && v in (low,1) ||
            return VerificationResult(false,:invalid_scope,cost)
        push!(seen,i)
    end
    introduced = 0
    for (k,step) in enumerate(cert.steps)
        step isa DominanceStep && step.predecessors == k-1 ||
            return VerificationResult(false,:invalid_predecessors,cost)
        # Scope prefixes preserve the actual interleaving of caller assumptions
        # and strong deductions. Later assumptions constrain only variables
        # that were free when earlier uniform derivative bounds were proved.
        count = step.scope_length == -1 ? length(cert.assumptions) : step.scope_length
        introduced <= count <= length(cert.assumptions) ||
            return VerificationResult(false,:invalid_scope,cost)
        for p in introduced+1:count
            i,v = cert.assumptions[p]
            haskey(fixed,i) && return VerificationResult(false,:invalid_scope,cost)
            fixed[i] = v
        end
        introduced = count
        valid, reason, visits = _verify_polynomial(s,fixed,step,active_map,max_work-cost,deadline_ns)
        cost += visits
        valid || return VerificationResult(false,reason,cost)
        fixed[step.variable] = step.value
    end
    for p in introduced+1:length(cert.assumptions)
        i,v = cert.assumptions[p]
        haskey(fixed,i) && return VerificationResult(false,:invalid_scope,cost)
        fixed[i] = v
    end
    return _expired(deadline_ns) ? VerificationResult(false,:deadline,cost) :
                                   VerificationResult(true,:verified,cost)
end
