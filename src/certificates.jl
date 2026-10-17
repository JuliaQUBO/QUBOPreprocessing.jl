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
end
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

# Internal numeric seam for #4: no model copy, proof export or assumption scan.
# Caller supplies predecessor count and persists the returned compact step.
function _dominance_witness(ws::Workspace, i::Int; max_work=typemax(Int),
                            max_exact_work=typemax(Int), deadline_ns=nothing,
                            predecessors=0,scope_length=-1)
    _limits(max_work,deadline_ns)
    _limits(max_exact_work,deadline_ns)
    st, s = ws._state, ws._snapshot
    st.fixed[i] == 2 || return (nothing,:already_fixed,:none,0,0,0)
    direction = _direction(s)
    direction != 0 || return (nothing,:zero_scale,:none,0,0,0)
    degree = length(st.adjacency[i])
    degree <= max_work || return (nothing,:work_limit,:none,0,0,0)
    _expired(deadline_ns) && return (nothing,:deadline,:none,0,0,0)
    lo, hi = _enclose(direction*st.fields[i])
    visits = 0
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
        visits += 1
        st.fixed[j] == 2 || continue
        # Adjacency coefficients are unchanged exact source Float64 values.
        # Conditioning changes fields/constants only; topology edits are not supported.
        coefficient = direction*Float64(q)
        a,b = s.domain === QT.BoolDomain ? (min(0.0,coefficient),max(0.0,coefficient)) :
                                             (-abs(coefficient),abs(coefficient))
        lo = prevfloat(lo + a)
        hi = nextfloat(hi + b)
    end
    value = isfinite(lo) && isfinite(hi) ? _strict_value(lo,hi,s.domain) : nothing
    _expired(deadline_ns) && return (nothing,:deadline,:interval,visits,0,0)
    if value !== nothing
        step = DominanceStep(i,value,_Exact(lo),_Exact(hi),deepcopy(st.constant),predecessors,:interval,scope_length)
        return (step,:proved,:interval,visits,0,0)
    end
    # Reserve the complete fallback before doing it. Exact work counts the
    # initial field and each free coefficient addition; adjacency visits include
    # both passes, including fixed neighbors skipped by arithmetic.
    degree <= max_work - visits || return (nothing,:work_limit,:interval,visits,0,0)
    degree < max_exact_work || return (nothing,:verification_limit,:interval,visits,0,0)
    lower = direction*st.fields[i]
    upper = lower
    exact_work = 1
    for (j,q) in st.adjacency[i]
        _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
        visits += 1
        st.fixed[j] == 2 || continue
        a = direction*q
        lower += s.domain === QT.BoolDomain ? min(0,a) : -abs(a)
        upper += s.domain === QT.BoolDomain ? max(0,a) : abs(a)
        exact_work += 1
    end
    _expired(deadline_ns) && return (nothing,:deadline,:exact,visits,1,exact_work)
    value = _strict_value(lower,upper,s.domain)
    value === nothing && return (nothing,:not_strict,:exact,visits,1,exact_work)
    step = DominanceStep(i,value,deepcopy(lower),deepcopy(upper),deepcopy(st.constant),predecessors,:exact,scope_length)
    return (step,:proved,:exact,visits,1,exact_work)
end

"""
    prove_dominance(ws, label; max_work=typemax(Int),
                    max_exact_work=typemax(Int), deadline_ns=nothing)

Prove one strong strict-dominance restriction without changing the workspace.
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
function prove_dominance(ws::Workspace, label; max_work=typemax(Int),
                         max_exact_work=typemax(Int), deadline_ns=nothing)
    i = _variable(ws,label)
    step, reason, method, visits, fallbacks, exact_work = _dominance_witness(ws,i;
        max_work,max_exact_work,deadline_ns,predecessors=ws._state.proof_count,
        scope_length=length(ws._state.callers))
    certificate = if step === nothing
        nothing
    else
        source = deepcopy(ws._snapshot)
        _validate_label_copy(ws._snapshot.labels,source.labels)
        _expired(deadline_ns) && return DominanceAttempt(nothing,:deadline,method,visits,fallbacks,exact_work)
        DominanceCertificate(generation(ws),checkpoint(ws),_caller_scope(ws),(_proof_steps(ws)...,step),source)
    end
    return DominanceAttempt(certificate,reason,method,visits,fallbacks,exact_work)
end

function _same_storage(a::_Storage,b::_Storage)
    return a.kind === b.kind && a.shape == b.shape && isequal(a.values,b.values) &&
           a.indices == b.indices && a.pointers == b.pointers
end
function _same_source(a::_Snapshot,b::_Snapshot)
    return a.label_type === b.label_type && a.state_type === b.state_type &&
           isequal(a.labels,b.labels) && isequal(a.scale,b.scale) && isequal(a.offset,b.offset) &&
           a.sense === b.sense && a.domain === b.domain &&
           _same_storage(a.linear,b.linear) && _same_storage(a.quadratic,b.quadratic)
end

# Independent verifier: re-read the original represented polynomial on each
# step and substitute a dictionary of explicit assumptions/validated prefix
# deductions. Do not read cached boundary fields, adjacency, constant or queue,
# and do not call the producer's bound or conditioning helper.
function _verify_polynomial(s::_Snapshot, fixed, step::DominanceStep, remaining, deadline)
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

"""
    verify_certificate(ws, certificate; max_work=typemax(Int), deadline_ns=nothing)

Independently recheck source identity, current caller scope and the complete
ordered strong-dominance chain using exact original-coefficient substitution.
Never trust cached workspace fields or an authenticated identifier alone.
Undoing/changing assumptions or resetting the model invalidates applicability.
Source/label validation costs O(n+m); each step scans source storage, so this
explicit verifier can cost O(steps*(n+m)). Dense storage costs O(n²) per scan.
Work is reserved before scans; exhausted work/deadline yields `valid=false`.
This does not validate a solver optimum or certify a rounded residual export.
"""
function verify_certificate(ws::Workspace, cert::DominanceCertificate;
                            max_work=typemax(Int), deadline_ns=nothing)
    _limits(max_work,deadline_ns)
    generation(ws) == generation(cert) || return VerificationResult(false,:stale_generation,0)
    _expired(deadline_ns) && return VerificationResult(false,:deadline,0)
    s = ws._snapshot
    cost = length(s.labels) + length(s.linear.values) + length(s.quadratic.values)
    cost <= max_work || return VerificationResult(false,:work_limit,0)
    _same_source(s,cert._source) || return VerificationResult(false,:different_source,cost)
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
        valid, reason, visits = _verify_polynomial(s,fixed,step,max_work-cost,deadline_ns)
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
