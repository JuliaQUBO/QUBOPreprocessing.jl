# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

function check_integer_payload(ws)
    st = ws._state
    I = eltype(st.fields)
    @test I in (Int128, BigInt)
    @test st.fields isa Vector{I}
    @test st.dual_fields isa Vector{I}
    @test st.adjacency isa Vector{Vector{Pair{Int,I}}}
    @test st.trail isa Vector{QUBOPreprocessing._UndoEntry{I}}
    @test st.constant isa I && st.dual_constant isa I
    @test st.lower === nothing || st.lower isa Vector{I}
    @test st.upper === nothing || st.upper isa Vector{I}
    R = Rational{BigInt}
    physical(v) = R(v) / (big(1) << st.shift)
    is_bool = ws._snapshot.domain === QT.BoolDomain
    free = findall(==(2), st.fixed)
    total_f = sum((physical(st.fields[i]) for i in free); init=R(0))
    total_q = sum((physical(q) for i in free for (j,q) in st.adjacency[i]
                   if i < j && st.fixed[j] == 2); init=R(0))
    for i in free
        f = physical(st.fields[i])
        qs = R[physical(q) for (j,q) in st.adjacency[i] if st.fixed[j] == 2]
        @test st.degrees[i] == length(qs)
        @test physical(st.dual_fields[i]) == (is_bool ? f/2 + sum(qs; init=R(0))/4 : 2*f - 2*sum(qs; init=R(0)))
        if st.lower !== nothing
            lo = f + sum((is_bool ? min(R(0),q) : -abs(q) for q in qs); init=R(0))
            hi = f + sum((is_bool ? max(R(0),q) : abs(q) for q in qs); init=R(0))
            @test physical(st.lower[i]) == lo
            @test physical(st.upper[i]) == hi
        end
    end
    @test physical(st.dual_constant) == (is_bool ? physical(st.constant) + total_f/2 + total_q/4 :
        physical(st.constant) - total_f + total_q)
    for e in st.trail
        e isa QUBOPreprocessing._UndoQueue && continue
        @test e.constant isa I && e.dual_constant isa I
        @test e.fields isa Vector{QUBOPreprocessing._NeighborRecord{I}}
    end
end

function check_integer_objective(ws, L, Q, scale, offset, domain)
    R = Rational{BigInt}
    # Use a coordinate map to request rational output even for an identity
    # workspace, whose default no-map identity API remains Float64-only.
    map = domain_map(ws; domain)
    result = materialize(ws, map; coefficient_type=R)
    model = export_model(result)
    n = QT.dimension(model)
    n <= 8 || throw(ArgumentError("integer-state oracle accepts at most eight free variables"))
    for y in states(n, domain)
        rec = reconstruct(result, y)
        energy = QT.offset(model)
        for i in 1:n
            energy += linear(model)[i]*y[i]
            for j in i+1:n
                energy += quadratic(model)[i,j]*y[i]*y[j]
            end
        end
        @test R(QT.scale(model))*energy == reference(L,Q,scale,offset,rec.state,R)
    end
    proof = export_certificate(ws)
    proof === nothing || @test verify_certificate(ws, proof).valid
    check_integer_payload(ws)
end

@testset "persistent integer payload across represented decimal conditioning" begin
    for domain in (:bool,:spin), sense in (:min,:max), scale in (-2.0,0.0,0.5),
        unit in (0.1,1/512)
        L = [-3unit, unit, 2unit]
        Q = [0.0 unit -2unit; 0.0 0.0 3unit; 0.0 0.0 0.0]
        ws = Workspace(fixture([:x,:y,:z],L,Q; domain,sense,scale,offset=unit);
                       rules=:mixed, integerize_scale=false)
        @test eltype(ws._state.fields) === Int128
        check_integer_objective(ws,L,Q,scale,unit,domain)
        root = checkpoint(ws)
        low = domain === :bool ? 0 : -1
        assume!(ws,:x,low)
        assume!(ws,:z,1)
        check_integer_objective(ws,L,Q,scale,unit,domain)
        unfix!(ws,:x)
        @test assumptions(ws) == [:z=>1]
        @test_throws ArgumentError rollback!(ws,root)
        check_integer_objective(ws,L,Q,scale,unit,domain)
    end
end

@testset "exponent extension rescales live state and old undo records" begin
    L = [1.0,0.0,0.0,2.0]
    Q = [0.0 1.0 1.0 0.0; zeros(3,4)]
    ws = Workspace(fixture([:x,:y,:z,:isolate],L,Q; domain=:spin); rules=:mixed)
    root = checkpoint(ws)
    assume!(ws,:isolate,1)
    cp = checkpoint(ws)
    gauge = domain_map(ws; domain=:bool,gauge=[-1,1,-1,1])
    before_map_constant = conditioned_constant(ws; map=gauge)
    @test ws._state.shift == 0
    @test eliminate_variable!(ws,:x).stop_reason === :applied
    @test ws._state.shift == 1
    @test ws._state.extensions == 1
    @test eltype(ws._state.fields) === Int128
    @test conditioned_constant(ws; map=gauge) == QUBOPreprocessing._direct_mapped_constant(ws,gauge)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,cp)
    @test ws._state.shift == 1 # rollback retains a valid finer integer grid
    @test conditioned_constant(ws; map=gauge) == before_map_constant
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "promotion precedes integer overflow and preserves checkpoints" begin
    L = [0.0,0.0,1.0]
    Q = [0.0 2.0^125 0.0; zeros(2,3)]
    ws = Workspace(fixture([:x,:y,:isolate],L,Q; domain=:spin); rules=:mixed)
    @test eltype(ws._state.fields) === BigInt
    root = checkpoint(ws)
    assume!(ws,:isolate,1)
    # Exercise the guarded update at the actual Int128 boundary. All live and
    # historical numerators fit Int128 here; the constructor conservatively
    # chooses BigInt because it reserves headroom for future arithmetic.
    ws._state.numeric = QUBOPreprocessing._regrid(ws._state,Int128,ws._state.shift)
    @test eltype(ws._state.fields) === Int128
    cp = checkpoint(ws)
    @test assume!(ws,:x,-1).stop_reason === :applied
    @test eltype(ws._state.fields) === BigInt
    @test ws._state.promotions == 1
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,cp)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)

    # A large exponent extension preserves the polynomial in the wide backend.
    # Rollback restores old values under the new denominator.
    assume!(ws,:isolate,1)
    original_constant = conditioned_constant(ws)
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+1076)
    @test conditioned_constant(ws) == original_constant
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "integer reductions, maps and local block reconstruction" begin
    for domain in (:bool,:spin), sense in (:min,:max), scale in (-0.5,0.5)
        L = domain === :bool ? [-0.5,-0.5,0.0,0.0] : [0.5,-0.5,0.0,0.0]
        Q = [0.0 0.5 0.25 0.0; 0.0 0.0 0.0 -0.25; zeros(2,4)]
        ws = Workspace(fixture([:a,:b,:c,:d],L,Q; domain,sense,scale,offset=0.125);rules=:mixed)
        root = checkpoint(ws)
        @test eliminate_block!(ws,[:a,:b]).stop_reason === :applied
        check_integer_objective(ws,L,Q,scale,0.125,domain)
        rollback!(ws,root)
        check_integer_objective(ws,L,Q,scale,0.125,domain)
    end
    L = zeros(3)
    Q = [0.0 -4.0 2.0; 0.0 0.0 1.0; 0.0 0.0 0.0]
    ws = Workspace(fixture([:x,:y,:z],L,Q;domain=:spin);rules=:mixed)
    root = checkpoint(ws)
    @test contract_relation!(ws,:x,:y;sign=1).stop_reason === :applied
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    gauge = domain_map(ws;domain=:bool,gauge=[-1,1,-1])
    before_constant = conditioned_constant(ws;map=gauge)
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+124)
    @test eltype(ws._state.fields) === BigInt
    @test ws._state.promotions == 1
    @test conditioned_constant(ws;map=gauge) == before_constant
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)

    for value in (nextfloat(0.0),floatmax(Float64))
        L = [value,-value]
        Q = [0.0 value;0.0 0.0]
        ws = Workspace(fixture([:x,:y],L,Q;offset=value,domain=:spin);rules=:mixed)
        check_integer_objective(ws,L,Q,1.0,value,:spin)
        @test eliminate_variable!(ws,:x).stop_reason === :applied
        check_integer_objective(ws,L,Q,1.0,value,:spin)
    end
end

@testset "integer no-progress path preserves payload and policy" begin
    ws = Workspace(fixture([:x,:y,:z],zeros(3),[0.0 1.0 1.0;0.0 0.0 1.0;0.0 0.0 0.0];domain=:spin);
                   rules=:dominance)
    numeric = ws._state.numeric
    report = propagate!(ws)
    @test report.deductions == 0
    @test report.stop_reason === :quiescent
    @test ws._state.numeric === numeric
    @test ws._state.promotions == ws._state.extensions == 0
    @test isempty(deductions(ws))
end

@testset "integer relation screening and complete schedules" begin
    n = 8 # guarded complete-state oracle limit
    L = zeros(n)
    Q = [i<j ? 4.0 : 0.0 for i in 1:n,j in 1:n]
    Q[1,2] = -4.0
    ws = Workspace(fixture(collect(1:n),L,Q;domain=:spin);rules=:mixed)
    st = ws._state
    raw12 = st.adjacency[1][st.adj_pos[1][2]].second
    raw34 = st.adjacency[3][st.adj_pos[3][4]].second
    @test QUBOPreprocessing._can_possibly_contract(ws,1,2,raw12,1,nothing)
    @test !QUBOPreprocessing._can_possibly_contract(ws,3,4,raw34,1,nothing)
    @test QUBOPreprocessing._can_possibly_contract(ws,1,2,Rational{BigInt}(-4),1,nothing)
    report = schedule_reductions!(ws;allow_weak_dominance=true,allow_weak_relations=true)
    @test report.deductions > 0
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "interrupted reductions do not commit grid extension" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([:x,:y,:z],[1.0,0.0,0.0],
        [0.0 1.0 1.0;zeros(2,3)];domain=:spin);rules=:mixed)
    attempt = prove_elimination(ws,:x)
    @test attempt.stop_reason === :proved
    step = last(attempt.certificate.steps)
    numeric = ws._state.numeric
    cp = checkpoint(ws)
    result = QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,step.constant_delta,
        Pair{Int,R}[p for p in step.linear_deltas],
        Tuple{Int,Int,R}[t for t in step.quadratic_deltas];max_work=0)
    @test result.stop_reason === :work_limit
    @test ws._state.numeric === numeric
    @test ws._state.shift == ws._state.extensions == 0
    @test isempty(reductions(ws))
    @test_throws ArgumentError QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,R(1//3),
        Pair{Int,R}[],Tuple{Int,Int,R}[])
    @test ws._state.numeric === numeric
    rollback!(ws,cp)
    check_integer_payload(ws)
end

@testset "direct dyadic intervals enclose exact values" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([:x],zeros(1),zeros(1,1)))
    values = [big(0),big(1),-big(1),big(2)^53+1,big(2)^128-1,
              -(big(2)^127),big(2)^2098-1,-(big(2)^2098-1)]
    for shift in (0,54,1074,1076,2100), q in values,
        numerator in (typemin(Int128) <= q <= typemax(Int128) ? (Int128(q),q) : (q,))
        ws._state.shift = shift # the zero polynomial is unchanged on every grid
        lo,hi = QUBOPreprocessing._enclose_grid(ws._state,numerator)
        exact = R(q)/(big(1)<<shift)
        @test !isnan(lo) && !isnan(hi)
        @test lo != Inf && hi != -Inf
        @test lo <= hi
        @test !isfinite(lo) || R(lo) <= exact
        @test !isfinite(hi) || exact <= R(hi)
    end
end

# A test-owned clock observes per-entry deadline polls independently of the
# returned work count. Promotion may add one safety poll after copying the
# payload; it must not repeat the local adjacency preparation.
mutable struct IntegerPromotionPolls
    calls::Int
end
function Base.:>=(::UInt64, deadline::IntegerPromotionPolls)
    deadline.calls += 1
    return false
end

@testset "promotion reuses local work within the original adjacency budget" begin
    R = Rational{BigInt}
    for degree in 1:3
        n = degree + 1
        L, Q = zeros(n), zeros(n,n)
        Q[1,2:n] .= 2.0^123
        function fixing_workspace(I)
            ws = Workspace(fixture(collect(1:n),L,Q;domain=:spin);rules=:mixed)
            I === Int128 && (ws._state.numeric = QUBOPreprocessing._regrid(ws._state,I,ws._state.shift))
            return ws
        end
        promoted, wide = fixing_workspace(Int128), fixing_workspace(BigInt)
        promoted_clock, wide_clock = IntegerPromotionPolls(0), IntegerPromotionPolls(0)
        cp = checkpoint(promoted)
        # Every incident edge is visited once, including at the exact budget.
        refused = QUBOPreprocessing._fix!(promoted,1,-1;max_work=degree-1)
        @test refused.stop_reason === :work_limit
        @test refused.edge_visits == 0
        @test eltype(promoted._state.fields) === Int128
        result = QUBOPreprocessing._fix!(promoted,1,-1;max_work=degree,deadline_ns=promoted_clock)
        control = QUBOPreprocessing._fix!(wide,1,-1;max_work=degree,deadline_ns=wide_clock)
        @test result.stop_reason === control.stop_reason === :applied
        @test result.edge_visits == control.edge_visits == degree
        @test promoted_clock.calls <= wide_clock.calls + 1
        @test promoted._state.promotions == 1
        check_integer_objective(promoted,L,Q,1.0,0.0,:spin)
        rollback!(promoted,cp)
        check_integer_objective(promoted,L,Q,1.0,0.0,:spin)
    end

    # Eliminating x from Q*x*(y+z) creates one coupling between y and z.
    # The budget is the two original edges plus two directed endpoint updates,
    # with an explicit precharge that must survive promotion unchanged.
    L = zeros(3)
    Q = [0.0 2.0^123 2.0^123;zeros(2,3)]
    function reduction_workspace(I)
        ws = Workspace(fixture(collect(1:3),L,Q;domain=:spin);rules=:mixed)
        I === Int128 && (ws._state.numeric = QUBOPreprocessing._regrid(ws._state,I,ws._state.shift))
        return ws
    end
    promoted, wide = reduction_workspace(Int128), reduction_workspace(BigInt)
    step = only(prove_elimination(promoted,1).certificate.steps)
    @test step.constant_delta == -R(2.0^123)
    @test step.quadratic_deltas == ((2,3,-R(2.0^123)),)
    promoted_clock, wide_clock = IntegerPromotionPolls(0), IntegerPromotionPolls(0)
    cp = checkpoint(promoted)
    function apply_boundary(ws, clock; max_work)
        QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,step.constant_delta,
            Pair{Int,R}[p for p in step.linear_deltas],
            Tuple{Int,Int,R}[t for t in step.quadratic_deltas];
            max_work,precharged_visits=7,deadline_ns=clock)
    end
    refused = apply_boundary(promoted,IntegerPromotionPolls(0);max_work=10)
    @test refused.stop_reason === :work_limit
    @test refused.edge_visits == 9
    @test eltype(promoted._state.fields) === Int128
    result = apply_boundary(promoted,promoted_clock;max_work=11)
    control = apply_boundary(wide,wide_clock;max_work=11)
    @test result.stop_reason === control.stop_reason === :applied
    @test result.edge_visits == control.edge_visits == 11
    @test promoted_clock.calls <= wide_clock.calls + 1
    @test promoted._state.promotions == 1
    check_integer_objective(promoted,L,Q,1.0,0.0,:spin)
    rollback!(promoted,cp)
    check_integer_objective(promoted,L,Q,1.0,0.0,:spin)
end

# A test-owned clock injects a failure only after a real numeric replacement.
# It does not depend on how many adjacency polls a kernel uses.
mutable struct IntegerReplacementFailure
    workspace::Workspace
    original::Any
    observed::Any
    failure::Exception
end
function Base.:>=(::UInt64, clock::IntegerReplacementFailure)
    if clock.workspace._state.numeric !== clock.original
        clock.observed = clock.workspace._state.numeric
        throw(clock.failure)
    end
    return false
end

@testset "failed integer transactions restore payload identity and original states" begin
    R=Rational{BigInt}
    # Both kernels replace their payload before committing. Exercise the
    # exception boundary with an existing caller undo entry still live.
    for operation in (:fix_promotion,:reduction_extension,:reduction_promotion)
        if operation===:fix_promotion
            L=[0.0,0.0,1.0]
            Q=[0.0 2.0^125 0.0;zeros(2,3)]
        elseif operation===:reduction_extension
            L=[1.0,0.0,0.0,2.0]
            Q=[0.0 1.0 1.0 0.0;zeros(3,4)]
        else
            L=[0.0,0.0,0.0,1.0]
            Q=[0.0 2.0^123 2.0^123 0.0;zeros(3,4)]
        end
        n=length(L);@test n<=4
        labels=collect(1:n)
        ws=Workspace(fixture(labels,L,Q;domain=:spin);rules=:mixed)
        root=checkpoint(ws)
        assume!(ws,n,1)
        # The conservative constructor reserves more headroom than needed for
        # these current values. Narrow only after proving every value fits.
        if eltype(ws._state.fields)===BigInt
            ws._state.numeric=QUBOPreprocessing._regrid(ws._state,Int128,ws._state.shift)
        end
        @test eltype(ws._state.fields)===Int128
        cp=checkpoint(ws);original=ws._state.numeric
        failure=ErrorException("injected failure after $operation payload replacement")
        clock=IntegerReplacementFailure(ws,original,nothing,failure)
        step=operation===:fix_promotion ? nothing : only(prove_elimination(ws,1).certificate.steps)
        function commit_with_clock(deadline)
            if operation===:fix_promotion
                return QUBOPreprocessing._fix!(ws,1,-1;deadline_ns=deadline)
            end
            return QUBOPreprocessing._apply_reduction!(ws,1,Int8(4),step,step.constant_delta,
                Pair{Int,R}[p for p in step.linear_deltas],
                Tuple{Int,Int,R}[t for t in step.quadratic_deltas];deadline_ns=deadline)
        end
        caught=try
            commit_with_clock(clock)
            nothing
        catch err
            err
        end
        @test caught===failure
        @test clock.observed!==nothing
        @test ws._state.numeric===original
        @test checkpoint(ws)==cp
        @test assumptions(ws)==[n=>1]
        @test isempty(reductions(ws))
        if operation===:reduction_extension
            @test clock.observed.shift>original.shift
            @test eltype(clock.observed.fields)===Int128
        else
            @test eltype(clock.observed.fields)===BigInt
        end
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
        # The rejected attempt leaves both normal commit and historical rollback
        # available; check all original-state energies through both operations.
        @test commit_with_clock(nothing).stop_reason===:applied
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
        rollback!(ws,cp)
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
        rollback!(ws,root)
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    end
end

@testset "overflowing grid extension preserves live and historical physical units" begin
    L=[1.0,0.0,0.0,2.0]
    Q=[0.0 1.0 1.0 0.0;zeros(3,4)]
    ws=Workspace(fixture(collect(1:4),L,Q;domain=:spin);rules=:mixed)
    root=checkpoint(ws);assume!(ws,4,1);conditioned=checkpoint(ws)
    @test eliminate_variable!(ws,1).stop_reason===:applied
    @test eltype(ws._state.fields)===Int128
    @test any(e isa QUBOPreprocessing._UndoFix for e in ws._state.trail)
    @test any(e isa QUBOPreprocessing._UndoReduction for e in ws._state.trail)
    proof=export_certificate(ws)
    gauge=domain_map(ws;domain=:bool,gauge=[-1,1,-1,1])
    constant=conditioned_constant(ws;map=gauge)
    old=ws._state.numeric
    shift=old.shift+130
    # No Int128 conversion can represent even the old unit coefficient on this
    # grid. The operation must fall back from InexactError without partial edits.
    @test_throws InexactError QUBOPreprocessing._regrid(ws._state,Int128,shift)
    @test ws._state.numeric===old
    QUBOPreprocessing._ensure_grid!(ws._state,shift)
    @test eltype(ws._state.fields)===BigInt
    @test ws._state.shift==shift
    @test ws._state.promotions==1
    @test conditioned_constant(ws;map=gauge)==constant
    @test verify_certificate(ws,proof).valid
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,conditioned)
    @test assumptions(ws)==[4=>1]
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    @test isempty(assumptions(ws))
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "integer coordinate adapters and uncached MaxCut weights match source rationals" begin
    R=Rational{BigInt}
    L=[-0.3,0.1,0.2]
    Q=[0.0 0.1 -0.3;0.0 0.0 0.2;0.0 0.0 0.0]
    for domain in (:bool,:spin),wide in (false,true)
        ws=Workspace(fixture(collect(1:3),L,Q;domain);rules=:identity)
        @test ws._state.lower===nothing && ws._state.upper===nothing
        wide && QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+130)
        @test (eltype(ws._state.fields)===BigInt)==wide
        for i in 1:3,(j,q) in ws._state.adjacency[i]
            input=R(Q[min(i,j),max(i,j)])
            @test QUBOPreprocessing._physical(q,ws._state.shift)==input
            @test QUBOPreprocessing._spin_coupling(ws,q)==(domain===:bool ? input/4 : input)
            @test QUBOPreprocessing._bool_coupling(ws,q)==(domain===:bool ? input : 4input)
        end
        for fixed in (false,true)
            fixed && assume!(ws,3,1)
            for i in (1,2),direction in (-1,1)
                # Expand the original polynomial directly in canonical spin
                # coordinates; no package field/cache supplies expected weights.
                f=R(L[i])+(fixed ? R(Q[i,3]) : R(0))
                active_q=[R(Q[min(i,j),max(i,j)]) for j in 1:3 if j!=i && !(fixed && j==3)]
                h=domain===:bool ? f/2+sum(active_q;init=R(0))/4 : f
                expected=abs(h)+sum(abs,active_q;init=R(0))/(domain===:bool ? 4 : 1)
                result=QUBOPreprocessing._ws_mc_total_abs_weight(ws,i,direction)
                @test result[1:2]==(true,:ok)
                @test result[3]==expected
            end
            check_integer_objective(ws,L,Q,1.0,0.0,domain)
        end
    end
end

@testset "constant-only integer workspace has coherent empty-state metadata" begin
    for offset in (0.0,0.3,nextfloat(0.0)),domain in (:bool,:spin)
        ws=Workspace(fixture(Int[],Float64[],zeros(0,0);offset,domain);rules=:mixed)
        @test isempty(ws._state.fields) && isempty(ws._state.adjacency)
        # The stable topology owner must expose numeric payload properties even
        # for empty models, so diagnostics can distinguish bounds from no bounds.
        @test all(name in propertynames(ws._state) for name in
                  (:numeric,:fields,:constant,:lower,:upper,:trail,:shift))
        @test conditioned_constant(ws)==Rational{BigInt}(offset)
        check_integer_objective(ws,Float64[],zeros(0,0),1.0,offset,domain)
    end
end

@testset "workspace physical denominators are exact, reused and owned" begin
    R = Rational{BigInt}
    L = [3/16,-5/16,7/16]
    Q = [0.0 -3/32 5/32; zeros(2,3)]
    for domain in (:bool,:spin)
        model = fixture(collect(1:3),L,Q;domain,offset=1/32)
        ws = Workspace(model;rules=:mixed)
        st = ws._state
        a = QUBOPreprocessing._physical(st,Int128(3))
        b = QUBOPreprocessing._physical(st,Int128(-5))
        @test denominator(a) === denominator(b)
        for q in (typemin(Int128),typemax(Int128),Int128(0),Int128(1),Int128(-1),Int128(12))
            value = QUBOPreprocessing._physical(st,q)
            @test value == R(q)/(big(1)<<st.shift)
            @test denominator(value) > 0 && gcd(numerator(value),denominator(value)) == 1
        end
        unit = R(1,big(1)<<st.shift)
        @test (a+b,a-b,a*b,a//b,-a,abs(b)) ==
            (-2unit,8unit,-15unit^2,R(-3,5),-3unit,5unit)
        @test a == R(3)/(big(1)<<st.shift) && b == R(-5)/(big(1)<<st.shift)
        copy_ws = deepcopy(ws)
        other = Workspace(model;rules=:mixed)
        copies = (copy_ws,other)
        for owned in copies
            c = QUBOPreprocessing._physical(owned._state,Int128(3))
            @test c == a
            @test owned._state.denominators !== st.denominators
            @test denominator(c) !== denominator(a)
        end
        # Public rationals may be mutated by their owner without changing any
        # workspace's cached powers, integer state, exports or reconstruction.
        values = (effective_field(ws,1),last(first(incident_couplings(ws,1))),conditioned_constant(ws))
        for value in values
            Base.GMP.MPZ.set!(denominator(value),BigInt(7))
        end
        @test denominator(a) == big(1)<<st.shift
        for owned in (ws,copies...)
            check_integer_objective(owned,L,Q,1.0,1/32,domain)
        end
    end
end

@testset "physical denominator cache survives finer grids and rollback" begin
    R = Rational{BigInt}
    L = [1.0,0.0,0.0,2.0]
    Q = [0.0 1.0 1.0 0.0; zeros(3,4)]
    ws = Workspace(fixture(collect(1:4),L,Q;domain=:spin);rules=:mixed)
    st = ws._state
    root = checkpoint(ws)
    assume!(ws,4,1)
    conditioned = checkpoint(ws)
    cache = st.denominators
    one = denominator(QUBOPreprocessing._physical(st,Int128(1)))
    @test eliminate_variable!(ws,1).stop_reason === :applied
    @test st.shift == 1
    proof = export_certificate(ws)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    # A finer grid need not allocate any new denominator until an adapter
    # actually requests it; old rational/proof values remain in physical units.
    for shift in (4,6)
        old_length = length(cache)
        QUBOPreprocessing._ensure_grid!(st,shift)
        @test eltype(st.fields) === Int128
        @test st.denominators === cache && length(cache) == old_length
        value = QUBOPreprocessing._physical(st,Int128(1))
        @test value == R(1,big(1)<<shift)
        @test length(cache) >= 2old_length
        @test cache[1] === one && one == 1
        @test all(x === nothing || ispow2(x) for x in cache)
        @test verify_certificate(ws,proof).valid
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    end
    rollback!(ws,conditioned)
    @test st.denominators === cache && st.shift == 6
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    # Promotion keeps the workspace cache but preserves the general BigInt
    # adapter, rather than trying to narrow wide live or historical numerators.
    QUBOPreprocessing._ensure_grid!(st,st.shift+130)
    @test eltype(st.fields) === BigInt && st.denominators === cache
    @test conditioned_constant(ws) == 2
    @test QUBOPreprocessing._physical(st,st.fields[1]) == 1
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    for domain in (:bool,:spin)
        tiny = nextfloat(0.0)
        subnormal = Workspace(fixture([1],[tiny],zeros(1,1);domain);rules=:mixed)
        @test eltype(subnormal._state.fields) === Int128
        @test effective_field(subnormal,1) == R(1,big(1)<<1074)
        check_integer_objective(subnormal,[tiny],zeros(1,1),1.0,0.0,domain)
    end
end

@testset "filtered rational adapters preserve network values and work limits" begin
    R = Rational{BigInt}
    L = [0.25,-0.5,1.0]
    Q = [0.0 -0.5 0.25; 0.0 0.0 -0.25; zeros(1,3)]
    capacities(net) = Dict((u,e.to)=>e.cap for (u,edges) in enumerate(net.adj)
                           for e in edges if !iszero(e.cap))
    for domain in (:bool,:spin)
        ws = Workspace(fixture(collect(1:3),L,Q;domain);rules=:mixed)
        assume!(ws,3,1)
        result = QUBOPreprocessing._build_implication_network(ws)
        @test result[1:2] == (true,:ok)
        @test result[5:6] == (6,4) # two free vertices, four adjacency entries;
        h1,h2,j = domain === :bool ? (R(1,8),R(1,2),R(1,8)) : (R(1,2),R(3,4),R(1,2))
        expected = Dict((7,2)=>h1,(1,8)=>h1,(7,3)=>h2,(4,8)=>h2,
                        (1,3)=>j,(3,1)=>j,(2,4)=>j,(4,2)=>j)
        @test capacities(result[3]) == expected
        @test result[4] == (domain === :bool ? R(0) : R(-3,4))
        @test QUBOPreprocessing._can_use_float_spin_heuristic(ws,[1,2])
        for (budget,reason,graph,exact) in ((0,:work_limit,0,1),(2,:work_limit,2,3),
                                           (3,:work_limit,3,3),(5,:work_limit,5,4),(6,:ok,6,4))
            bounded = QUBOPreprocessing._build_implication_network(ws;max_work=budget)
            @test (bounded[2],bounded[5],bounded[6]) == (reason,graph,exact)
        end
        for (budget,reason,graph,exact) in ((0,:verification_limit,0,0),(1,:verification_limit,1,1),
                                           (2,:verification_limit,2,2),(3,:verification_limit,4,3),(4,:ok,6,4))
            bounded = QUBOPreprocessing._build_implication_network(ws;max_exact_work=budget)
            @test (bounded[2],bounded[5],bounded[6]) == (reason,graph,exact)
        end
        expired = QUBOPreprocessing._build_implication_network(ws;deadline_ns=UInt64(0))
        @test (expired[2],expired[5],expired[6]) == (:deadline,0,1)
        check_integer_objective(ws,L,Q,1.0,0.0,domain)
        # Explicit stored zero edges are algebraically empty, but keep their
        # original traversal/admission charges. Fixed and reverse edges also
        # remain in this tiny graph, exercising all skipped-adapter filters.
        zero_Q = copy(Q); zero_Q[1,2] = 0.0
        zero_ws = Workspace(fixture(collect(1:3),L,zero_Q;domain);rules=:identity)
        assume!(zero_ws,3,1)
        before = QUBOPreprocessing._build_implication_network(zero_ws)
        for (i,k) in ((1,2),(2,1))
            push!(zero_ws._state.adjacency[i],k=>Int128(0))
        end
        after = QUBOPreprocessing._build_implication_network(zero_ws)
        @test before[5:6] == (4,3) && after[5:6] == (6,4)
        @test before[4] == after[4] && capacities(before[3]) == capacities(after[3])
        @test QUBOPreprocessing._can_use_float_spin_heuristic(zero_ws,[1,2])
    end
end

@testset "physical scalar interning is lazy and exact on every dyadic grid" begin
    R = Rational{BigInt}
    ws = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
    st = ws._state
    @test length(st.physical_constants) == 31 && all(isnothing,st.physical_constants)
    constants = Tuple(QUBOPreprocessing._physical(st,Int128(k)) for k in (-1,0,1))
    @test constants == (R(-1),R(0),R(1))
    for shift in (0,1,2,63,126,127,128,1074)
        QUBOPreprocessing._ensure_grid!(st,shift) # zero live state fits every grid
        @test eltype(st.fields) === Int128 && st.shift == shift
        @test QUBOPreprocessing._physical(st,Int128(0)) === constants[2]
        for q in (typemin(Int128),typemax(Int128),Int128(-3),Int128(-1),Int128(0),Int128(1),Int128(3))
            actual = QUBOPreprocessing._physical(st,q)
            @test actual == R(q)/(big(1)<<shift)
            @test denominator(actual)>0 && gcd(numerator(actual),denominator(actual))==1
        end
        if shift < 127
            unit = Int128(1)<<shift
            @test QUBOPreprocessing._physical(st,-unit) === constants[1]
            @test QUBOPreprocessing._physical(st,unit) === constants[3]
        elseif shift == 127
            minus_one = QUBOPreprocessing._physical(st,typemin(Int128))
            @test minus_one == -1
            @test minus_one === constants[1] # canonical physical value on the finer grid
        end
        @test constants == (R(-1),R(0),R(1))
        check_integer_objective(ws,[0.0],zeros(1,1),1.0,0.0,:spin)
    end
    @test QUBOPreprocessing._physical(st,Int128(1)) == R(nextfloat(0.0))
    # The BigInt adapter keeps its previous behavior, including physical units.
    for q in (big(0),big(1)<<1074,-(big(1)<<1074),big(3))
        @test QUBOPreprocessing._physical(st,q) == R(q)/(big(1)<<st.shift)
    end
end

@testset "physical constants survive elimination, finer grids, promotion and rollback" begin
    R = Rational{BigInt}
    L = [1.0,0.0,0.0,2.0]
    Q = [0.0 1.0 1.0 0.0; zeros(3,4)]
    ws = Workspace(fixture(collect(1:4),L,Q;domain=:spin);rules=:mixed)
    st = ws._state
    constants = Tuple(QUBOPreprocessing._physical(st,Int128(k)) for k in (-1,0,1))
    expanded = Dict(R(k)=>QUBOPreprocessing._physical(st,Int128(k)) for k in (-4,-2,2,4))
    pool = st.physical_constants
    root = checkpoint(ws)
    assume!(ws,4,1)
    conditioned = checkpoint(ws)
    @test eliminate_variable!(ws,1).stop_reason === :applied
    @test st.shift == 1
    proof = export_certificate(ws)
    for shift in (3,6)
        QUBOPreprocessing._ensure_grid!(st,shift)
        @test st.physical_constants === pool
        for k in (-1,0,1)
            @test QUBOPreprocessing._physical(st,Int128(k)*(Int128(1)<<shift)) === constants[k+2]
        end
        for value in (R(-4),R(-2),R(-1,2),R(-1,4),R(1,4),R(1,2),R(2),R(4))
            actual = QUBOPreprocessing._physical(st,Int128(value*(big(1)<<shift)))
            @test actual == value
            if haskey(expanded,value)
                @test actual === expanded[value]
            else
                expanded[value] = actual
            end
        end
        @test verify_certificate(ws,proof).valid
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    end
    rollback!(ws,conditioned)
    @test st.physical_constants === pool && constants == (R(-1),R(0),R(1))
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    QUBOPreprocessing._ensure_grid!(st,st.shift+130)
    @test eltype(st.fields) === BigInt && st.physical_constants === pool
    @test QUBOPreprocessing._physical(st,Int128(0)) === constants[2]
    @test QUBOPreprocessing._physical(st,st.constant) == 2
    rollback!(ws,root)
    @test all(value==key for (key,value) in expanded)
    @test constants == (R(-1),R(0),R(1))
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
end

@testset "public rationals cannot mutate interned scalars or another workspace" begin
    R = Rational{BigInt}
    poison_owned!(q) = (Base.GMP.MPZ.set!(numerator(q),BigInt(777));
                        Base.GMP.MPZ.set!(denominator(q),BigInt(7)))
    for domain in (:bool,:spin),gain in (1.0,2.0,4.0,0.5,0.25)
        L = [0.0,0.0,0.0,-gain]
        Q = [0.0 gain -gain 0.0; zeros(3,4)]
        model = fixture(collect(1:4),L,Q;domain,offset=gain)
        ws = Workspace(model;rules=:dominance)
        st = ws._state
        unit = Int128(R(gain)*(big(1)<<st.shift))
        constants = Tuple(QUBOPreprocessing._physical(st,Int128(k)*unit) for k in (-1,0,1))
        @test constants == (-R(gain),R(0),R(gain))
        other = Workspace(model;rules=:dominance)
        copied = deepcopy(ws)
        for owner in (other,copied),k in (-1,0,1)
            q = QUBOPreprocessing._physical(owner._state,Int128(k)*unit)
            @test q == constants[k+2]
            @test owner._state.physical_constants !== st.physical_constants
            @test numerator(q) !== numerator(constants[k+2])
            @test denominator(q) !== denominator(constants[k+2])
        end
        # A public proof attempt owns both mutable BigInts in its rationals.
        attempt = prove_dominance(ws,4)
        @test attempt.certificate !== nothing && verify_certificate(ws,attempt.certificate).valid
        poison_owned!(only(attempt.certificate.steps).lower)
        @test verify_certificate(ws,prove_dominance(ws,4).certificate).valid
        @test constants == (-R(gain),R(0),R(gain))
        report = propagate!(ws)
        @test report.deductions == 1
        raw = st.trail[only(st.fixes)].proof
        @test numerator(raw.lower) === numerator(constants[1])
        @test denominator(raw.lower) === denominator(constants[1])
        for q in (effective_field(ws,1),conditioned_constant(ws),
                  (last(edge) for edge in incident_couplings(ws,1))...)
            poison_owned!(q)
        end
        result = materialize(ws;coefficient_type=R)
        exported = export_model(result)
        for q in (linear(exported)[1],quadratic(exported)[1,2],quadratic(exported)[1,3],
                  QT.offset(exported),QT.scale(exported))
            poison_owned!(q)
        end
        fresh = export_model(result)
        @test linear(fresh)[1] == 0 && quadratic(fresh)[1,2] == gain && quadratic(fresh)[1,3] == -gain
        @test QT.offset(fresh) == 0 && QT.scale(fresh) == 1
        # Certificate exports, materialized proof chains and reduction queries
        # all pass through owned-copy paths, even when raw trail bounds intern.
        certificate = export_certificate(ws)
        @test numerator(only(certificate.steps).lower) !== numerator(constants[1])
        @test denominator(only(certificate.steps).lower) !== denominator(constants[1])
        for step in (only(certificate.steps),only(result.certificate.proof.steps),only(reductions(ws)))
            for q in (step.lower,step.upper,step.constant)
                poison_owned!(q)
            end
        end
        @test verify_certificate(ws,export_certificate(ws)).valid
        @test constants == (-R(gain),R(0),R(gain))
        check_integer_objective(ws,L,Q,1.0,gain,domain)
        for owner in (other,copied)
            check_integer_objective(owner,L,Q,1.0,gain,domain)
        end
        pool = st.physical_constants
        reset!(ws,model)
        @test ws._state.physical_constants !== pool && all(isnothing,ws._state.physical_constants)
        @test numerator(QUBOPreprocessing._physical(ws._state,unit)) !== numerator(constants[3])
        check_integer_objective(ws,L,Q,1.0,gain,domain)
    end
end

@testset "canonical small dyadic membership and normalization share physical keys" begin
    R = Rational{BigInt}
    values = R[R(n,big(1)<<d) for d in 0:2 for n in -7:7 if d==0 || isodd(n)]
    @test length(unique(values)) == 31
    ws = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
    st = ws._state
    @test length(st.physical_constants) == 31 && all(isnothing,st.physical_constants)
    QUBOPreprocessing._ensure_grid!(st,2)
    interned = Dict(value=>QUBOPreprocessing._physical(st,Int128(4value)) for value in values)
    @test count(!isnothing,st.physical_constants) == 31
    @test Set(st.physical_constants) == Set(values)
    for shift in (2,3,20,120,126,127,128,129,130,1074)
        QUBOPreprocessing._ensure_grid!(st,shift) # zero state stays Int128
        @test eltype(st.fields) === Int128
        for value in values
            numerator_on_grid = value*(big(1)<<shift)
            if denominator(numerator_on_grid)==1 && typemin(Int128)<=numerator(numerator_on_grid)<=typemax(Int128)
                actual = QUBOPreprocessing._physical(st,Int128(numerator_on_grid))
                @test actual == value
                @test actual === interned[value]
                @test gcd(numerator(actual),denominator(actual)) == 1
            end
        end
        for q in (typemin(Int128),typemax(Int128),Int128(-8),Int128(8),Int128(-1),Int128(1))
            expected = R(q)/(big(1)<<shift)
            first = QUBOPreprocessing._physical(st,q)
            second = QUBOPreprocessing._physical(st,q)
            @test first == second == expected
            if expected in values
                @test first === interned[expected]
            else
                @test numerator(first) !== numerator(second)
            end
        end
        if shift in (127,128,129)
            expected = R(-1,big(1)<<(shift-127))
            @test QUBOPreprocessing._physical(st,typemin(Int128)) === interned[expected]
        elseif shift == 130
            first = QUBOPreprocessing._physical(st,typemin(Int128))
            second = QUBOPreprocessing._physical(st,typemin(Int128))
            @test first == second == R(-1,8)
            @test numerator(first) !== numerator(second)
        end
        @test all(value==key for (key,value) in interned)
    end
    # Integer and half grids admit only the corresponding subset, including
    # representations whose raw numerator exceeds7 but normalizes into S.
    for shift in (0,1)
        low = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
        QUBOPreprocessing._ensure_grid!(low._state,shift)
        for q in Int128.(-16:16)
            expected = R(q)/(big(1)<<shift)
            first = QUBOPreprocessing._physical(low._state,q)
            second = QUBOPreprocessing._physical(low._state,q)
            @test first == second == expected
            @test (numerator(first) === numerator(second)) == (expected in values)
        end
    end
    # Denominator and numerator bounds are exact: represented0.1, eighths and
    # integers8 stay on the previous conversion path, with no approximation.
    for coefficient in (0.1,-0.1,0.125,-0.125,8.0,-8.0)
        fallback = Workspace(fixture([1],[coefficient],zeros(1,1);domain=:spin);rules=:mixed)
        q = only(fallback._state.fields)
        first = QUBOPreprocessing._physical(fallback._state,q)
        second = QUBOPreprocessing._physical(fallback._state,q)
        @test first == second == R(coefficient)
        @test numerator(first) !== numerator(second)
        @test all(isnothing,fallback._state.physical_constants)
        check_integer_objective(fallback,[coefficient],zeros(1,1),1.0,0.0,:spin)
    end
    copied = deepcopy(ws)
    @test copied._state.physical_constants !== st.physical_constants
    for value in values
        position = findfirst(==(value),st.physical_constants)
        other = copied._state.physical_constants[position]
        @test other == value
        @test numerator(other) !== numerator(interned[value])
        @test denominator(other) !== denominator(interned[value])
    end
    # Generic BigInt dispatch remains exact without populating the small pool.
    wide = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
    for q in (big(0),big(2),big(-4),big(1)<<200)
        @test QUBOPreprocessing._physical(wide._state,q) == R(q)
    end
    @test all(isnothing,wide._state.physical_constants)
end


@testset "physical Float view preserves rational conversion bits in public contexts" begin
    R = Rational{BigInt}
    bits(x) = reinterpret(UInt64,x)
    bound = Int128(1) << 53
    # Explicit numerical boundaries: exactly represented normals, precision
    # loss, typemin normalization, subnormals, overflow and represented0.1.
    samples = Tuple{Int128,Int}[
        (0,0),(0,1075),(1,0),(-1,0),(3,1),(-7,2),
        (bound-1,0),(bound,53),(bound+1,0),(-bound-1,53),
        (typemax(Int128),0),(typemin(Int128),0),
        (typemin(Int128),127),(typemin(Int128),128),
        (typemin(Int128),129),(typemin(Int128),130),
        (typemin(Int128),1202),(1,1021),(-1,1021),
        (1,1022),(-1,1022),(3,1074),(-3,1074),
        (1,1075),(-1,1075),(1,1200),(-1,1200),
        (Int128(numerator(R(0.1))),55),(bound+11,1075),
    ]
    saved_ftz = get_zero_subnormals()
    try
        for ftz in (false,true)
            set_zero_subnormals(ftz)
            @test get_zero_subnormals() == ftz
            for p in (24,32,53,64,256), mode in (RoundNearest,RoundUp,RoundDown,RoundToZero)
                setprecision(BigFloat,p) do
                    setrounding(BigFloat,mode) do
                        ws = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
                        st = ws._state
                        for shift in sort!(unique(last.(samples)))
                            QUBOPreprocessing._ensure_grid!(st,shift)
                            for (q,s) in samples
                                s == shift || continue
                                exact = R(BigInt(q),big(1)<<s)
                                expected = Float64(exact)
                                actual = QUBOPreprocessing._physical_float(st,q)
                                @test bits(actual) == bits(expected)
                                # BigInt and exact inputs retain the general
                                # rational conversion, including context rounding.
                                @test bits(QUBOPreprocessing._physical_float(st,BigInt(q))) == bits(expected)
                                @test bits(QUBOPreprocessing._physical_float(st,exact)) == bits(expected)
                                if typemin(Int64) <= q <= typemax(Int64)
                                    @test bits(QUBOPreprocessing._physical_float(st,Int64(q))) == bits(expected)
                                end
                            end
                        end
                        for (q,shift) in ((big(1)<<1100,0),(-(big(1)<<1100),0),
                                          (big(1),20000),(big(-1),20000))
                            wide = Workspace(fixture([1],[0.0],zeros(1,1);domain=:spin);rules=:mixed)
                            QUBOPreprocessing._ensure_grid!(wide._state,shift)
                            @test wide._state.shift == shift
                            @test bits(QUBOPreprocessing._physical_float(wide._state,q)) == bits(Float64(R(q,big(1)<<shift)))
                        end
                    end
                end
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
    @test get_zero_subnormals() == saved_ftz
end

@testset "integer Float coupling keeps raw conversion before Bool quarter scaling" begin
    R = Rational{BigInt}
    bits(x) = reinterpret(UInt64,x)
    saved_ftz = get_zero_subnormals()
    try
        for ftz in (false,true)
            set_zero_subnormals(ftz)
            for p in (24,32,53,64,256), mode in (RoundNearest,RoundUp,RoundDown,RoundToZero)
                setprecision(BigFloat,p) do
                    setrounding(BigFloat,mode) do
                        for domain in (:bool,:spin)
                            ws = Workspace(fixture([1],[0.0],zeros(1,1);domain);rules=:mixed)
                            for (q,shift) in ((Int128(0),2),(Int128(-3),2),
                                              (Int128(numerator(R(0.1))),55),
                                              (Int128(9007199254741003),1075),
                                              (typemin(Int128),1202))
                                QUBOPreprocessing._ensure_grid!(ws._state,shift)
                                raw = R(q,big(1)<<ws._state.shift)
                                expected = domain === :bool ? 0.25*Float64(raw) : Float64(raw)
                                @test bits(QUBOPreprocessing._float_spin_coupling(ws,q)) == bits(expected)
                                @test bits(QUBOPreprocessing._float_spin_coupling(ws,BigInt(q))) == bits(expected)
                                @test bits(QUBOPreprocessing._float_spin_coupling(ws,raw)) == bits(expected)
                            end
                        end
                    end
                end
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
    @test get_zero_subnormals() == saved_ftz
    # These two expressions differ by one subnormal unit: do not commute
    # Bool scaling with the raw Float64 conversion.
    try
        set_zero_subnormals(false)
        setprecision(BigFloat,256) do
            setrounding(BigFloat,RoundNearest) do
                raw = R(9007199254741003,big(1)<<1075)
                @test bits(0.25*Float64(raw)) != bits(Float64(raw/4))
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
end

@testset "Float consumers agree with original three-variable objectives and undo" begin
    R = Rational{BigInt}
    bits(x) = reinterpret(UInt64,x)
    L = [0.0,1.0,-2.0]
    Q = [0.0 1.0 -0.5; 0.0 0.0 0.25; 0.0 0.0 0.0]
    for domain in (:bool,:spin), sense in (:min,:max)
        ws = Workspace(fixture([1,2,3],L,Q;domain,sense);rules=:mixed)
        cp = checkpoint(ws)
        initial = (copy(ws._state.fields),copy(ws._state.dual_fields),ws._state.constant)
        for conditioned in (false,true)
            conditioned && assume!(ws,3,1)
            free = conditioned ? [1,2] : [1,2,3]
            witness = domain === :bool ? [0,1,conditioned ? 1 : 0] : [-1,1,conditioned ? 1 : -1]
            @test QUBOPreprocessing._can_use_float_spin_heuristic(ws,free)
            actual = QUBOPreprocessing._try_build_float_spin_subproblem(ws,free)
            @test actual !== nothing
            h,adj,l1 = actual
            for i in 1:3
                if i in free
                    # Condition the original scalar polynomial independently,
                    # then apply x=(s+1)/2 only for a native Bool objective.
                    field = R(L[i]) + (conditioned ? R(Q[i,3]) : R(0))
                    neighbors = [(j,R(Q[min(i,j),max(i,j)])) for j in free if j != i && !iszero(Q[min(i,j),max(i,j)])]
                    spinfield = domain === :bool ? field/2 + sum((q/4 for (_,q) in neighbors);init=R(0)) : field
                    expected_adj = [(j,domain === :bool ? 0.25*Float64(q) : Float64(q)) for (j,q) in neighbors]
                    @test bits(h[i]) == bits(Float64(spinfield))
                    @test [(j,bits(q)) for (j,q) in adj[i]] == [(j,bits(q)) for (j,q) in expected_adj]
                    expected_l1 = 0.0
                    for (_,q) in expected_adj
                        expected_l1 += abs(q)
                    end
                    @test bits(l1[i]) == bits(expected_l1)
                else
                    @test iszero(h[i]) && isempty(adj[i]) && iszero(l1[i])
                end
            end
            # Ratios from this polynomial give distinct rankings, including
            # the zero conditioned Bool field and min/max sign placement.
            coercive = conditioned ? [2,1] : [3,2,1]
            extremal = sense === :min ? copy(free) : reverse(free)
            @test QUBOPreprocessing._order_probing_candidates!(ws,copy(free),witness,:coercive) == coercive
            @test QUBOPreprocessing._order_probing_candidates!(ws,copy(free),witness,:extremal) == extremal
            feasible = [x for x in states(3,domain) if !conditioned || x[3] == 1]
            energies = [reference(L,Q,1.0,0.0,x,R) for x in feasible]
            optimum = (sense === :min ? minimum : maximum)(energies)
            for gauge in (-1,1)
                map = domain_map(ws;domain=:spin,gauge=fill(gauge,3))
                mapped = coercive_field_witness(ws;map,polish=true,sequential=true,max_flips=8)
                original = lift_state(map,mapped)
                @test original in feasible
                @test reference(L,Q,1.0,0.0,original,R) == optimum
            end
            check_integer_objective(ws,L,Q,1.0,0.0,domain)
        end
        rollback!(ws,cp)
        @test isempty(assumptions(ws))
        @test (ws._state.fields,ws._state.dual_fields,ws._state.constant) == initial
        check_integer_objective(ws,L,Q,1.0,0.0,domain)
    end
end

@testset "Float eligibility rejects underflowed nonzero fields before conversion" begin
    R = Rational{BigInt}
    saved_ftz = get_zero_subnormals()
    try
        # Construct native subnormal inputs before enabling FTZ: fixture
        # creation must not erase a coefficient before the consumer sees it.
        set_zero_subnormals(false)
        fixtures = [begin
            coefficient = sign*nextfloat(0.0)
            ws = Workspace(fixture([1],[coefficient],zeros(1,1);domain);rules=:mixed)
            exactfield = domain === :bool ? R(coefficient)/2 : R(coefficient)
            (ws,exactfield)
        end for domain in (:bool,:spin) for sign in (-1,1)]
        for ftz in (false,true)
            set_zero_subnormals(ftz)
            for p in (24,53,256), mode in (RoundNearest,RoundUp,RoundDown,RoundToZero)
                setprecision(BigFloat,p) do
                    setrounding(BigFloat,mode) do
                        for (ws,exactfield) in fixtures
                            @test !iszero(exactfield)
                            @test !QUBOPreprocessing._can_use_float_spin_heuristic(ws,[1])
                            @test QUBOPreprocessing._try_build_float_spin_subproblem(ws,[1]) === nothing
                        end
                    end
                end
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
    @test get_zero_subnormals() == saved_ftz
end


@testset "direct exact coordinate couplings match independent dyadic oracles" begin
    R = Rational{BigInt}
    vals = Int128[0,1,-1,2,-2,4,-4,7,-7,8,-8,17,-17,12345,-12345,
        typemin(Int128),typemax(Int128),typemin(Int128)÷4-1,
        typemin(Int128)÷4,typemax(Int128)÷4,typemax(Int128)÷4+1,
        typemin(Int128)÷2-1,typemin(Int128)÷2,typemax(Int128)÷2+1]
    for domain in (:bool,:spin)
        ws = Workspace(fixture([1],[0.0],zeros(1,1);domain);rules=:mixed)
        st = ws._state
        for shift in (0,1,2,3,55,127,140,1074,65536)
            shift < st.shift && continue
            QUBOPreprocessing._ensure_grid!(st,shift)
            for q in vals
                original = R(BigInt(q),big(1)<<shift)
                spin = domain === :bool ? original/4 : original
                bool = domain === :spin ? 4original : original
                @test QUBOPreprocessing._spin_coupling(ws,q) == spin
                @test QUBOPreprocessing._bool_coupling(ws,q) == bool
                @test QUBOPreprocessing._physical_at_shift(st,q,shift) == original
                @test gcd(numerator(QUBOPreprocessing._spin_coupling(ws,q)),denominator(QUBOPreprocessing._spin_coupling(ws,q))) == 1
            end
            for q in (big(0),big(17),-(big(1)<<200),(big(1)<<200)+12345)
                before = deepcopy(q)
                original = R(q,big(1)<<shift)
                @test QUBOPreprocessing._spin_coupling(ws,q) == (domain === :bool ? original/4 : original)
                @test QUBOPreprocessing._bool_coupling(ws,q) == (domain === :spin ? 4original : original)
                @test q == before
            end
        end
        # _Exact overloads retain arbitrary rationals and same-domain identity.
        for exact in (R(0),R(1,3),R(-17,64),R(0.1))
            @test QUBOPreprocessing._spin_coupling(ws,exact) == (domain === :bool ? exact/4 : exact)
            @test QUBOPreprocessing._bool_coupling(ws,exact) == (domain === :spin ? 4exact : exact)
            @test (domain === :bool ? QUBOPreprocessing._bool_coupling(ws,exact) : QUBOPreprocessing._spin_coupling(ws,exact)) === exact
        end
        @test_throws ArgumentError QUBOPreprocessing._physical_at_shift(st,Int128(1),-1)
        @test_throws ArgumentError QUBOPreprocessing._physical_at_shift(st,big(1),-1)
    end
    # Zero is meaningful without allocating a denominator on an impossible
    # exponent; nonzero quarter conversion must detect Int exponent overflow.
    overflow = Workspace(fixture([1],[0.0],zeros(1,1);domain=:bool))
    for shift in (typemax(Int)-1,typemax(Int))
        overflow._state.shift = shift # zero state, scalar context only
        @test QUBOPreprocessing._spin_coupling(overflow,Int128(0)) == 0
        @test QUBOPreprocessing._spin_coupling(overflow,big(0)) == 0
        @test_throws OverflowError QUBOPreprocessing._spin_coupling(overflow,Int128(1))
        @test_throws OverflowError QUBOPreprocessing._spin_coupling(overflow,big(1))
    end
end

@testset "exact coordinate and Float expression order survive public precision contexts" begin
    R = Rational{BigInt}
    bits(x) = reinterpret(UInt64,x)
    saved = get_zero_subnormals()
    try
        for ftz in (false,true)
            set_zero_subnormals(ftz)
            for precision_bits in (8,24,53,256), mode in (RoundNearest,RoundUp,RoundDown,RoundToZero)
                setprecision(BigFloat,precision_bits) do
                    setrounding(BigFloat,mode) do
                        for domain in (:bool,:spin)
                            ws = Workspace(fixture([1],[0.0],zeros(1,1);domain))
                            for shift in (2,55,127,1075), q in Int128[0,17,-12345,typemin(Int128),typemax(Int128)]
                                QUBOPreprocessing._ensure_grid!(ws._state,shift)
                                raw = R(q,big(1)<<shift)
                                exact_spin = domain === :bool ? raw/4 : raw
                                exact_bool = domain === :spin ? 4raw : raw
                                @test bits(Float64(QUBOPreprocessing._spin_coupling(ws,q))) == bits(Float64(exact_spin))
                                @test bits(Float64(QUBOPreprocessing._bool_coupling(ws,q))) == bits(Float64(exact_bool))
                                # Float consumers keep conversion before Bool's
                                # factor0.25, unlike the exact coordinate view.
                                old_float = domain === :bool ? 0.25*Float64(raw) : Float64(raw)
                                @test bits(QUBOPreprocessing._float_spin_coupling(ws,q)) == bits(old_float)
                            end
                        end
                    end
                end
            end
        end
    finally
        set_zero_subnormals(saved)
    end
    @test get_zero_subnormals() == saved
end

@testset "direct coordinates remain exact across grid extension promotion and rollback" begin
    L = [1.0,0.0,0.0]
    Q = [0.0 1.0 1.0;0.0 0.0 0.0;0.0 0.0 0.0]
    ws = Workspace(fixture([1,2,3],L,Q;domain=:spin);rules=:mixed)
    root = checkpoint(ws)
    old = QUBOPreprocessing._bool_coupling(ws,first(ws._state.adjacency[1]).second)
    @test old == 4
    @test eliminate_variable!(ws,1).stop_reason === :applied
    @test ws._state.shift == 1
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    for i in (2,3),(_,q) in ws._state.adjacency[i]
        @test QUBOPreprocessing._bool_coupling(ws,q) == 4Rational{BigInt}(q)/(big(1)<<ws._state.shift)
    end
    QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+130)
    @test eltype(ws._state.fields) === BigInt
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    rollback!(ws,root)
    @test old == 4
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    for i in 1:3,(_,q) in ws._state.adjacency[i]
        @test QUBOPreprocessing._bool_coupling(ws,q) == 4
    end
end

@testset "public cross-domain quarter exports own both mutable BigInts" begin
    R = Rational{BigInt}
    poison(q) = (Base.GMP.MPZ.set!(numerator(q),big(777));Base.GMP.MPZ.set!(denominator(q),big(7)))
    for domain in (:bool,:spin),sense in (:min,:max),scale in (-2.0,0.5),gauged in (false,true)
        # Both transformations have final J=1/4: Bool1/4 and Spin(1/16)*4.
        nativeq = domain === :bool ? 1.0 : 1/16
        L = [0.1,-0.3,2.0];Q=[0.0 nativeq 0.0;0.0 0.0 0.0;0.0 0.0 0.0]
        model=fixture([1,2,3],L,Q;domain,sense,scale)
        ws=Workspace(model;rules=:mixed,integerize_scale=false)
        other=Workspace(model;rules=:mixed,integerize_scale=false)
        target=domain===:bool ? :spin : :bool
        gauge=gauged ? [-1,1,-1] : [1,1,1]
        map=domain_map(ws;domain=target,gauge)
        raw=first(ws._state.adjacency[1]).second
        borrowed=domain===:bool ? QUBOPreprocessing._spin_coupling(ws,raw) : QUBOPreprocessing._bool_coupling(ws,raw)
        @test borrowed == R(1,4)
        copied=deepcopy(ws)
        owned=last(only(incident_couplings(ws,1;map)))
        @test owned == gauge[1]*gauge[2]*R(1,4)
        @test numerator(owned) !== numerator(borrowed)
        @test denominator(owned) !== denominator(borrowed)
        poison(owned)
        @test borrowed == R(1,4)
        @test last(only(incident_couplings(ws,1;map))) == gauge[1]*gauge[2]*R(1,4)
        result=materialize(ws,map;coefficient_type=R)
        out=export_model(result)
        for y in states(3,target)
            expected=domain===:bool ? [(gauge[i]*y[i]+1)÷2 for i in 1:3] : [gauge[i]*(2*y[i]-1) for i in 1:3]
            @test reconstruct(result,y).state == expected
            @test exact_model_energy(out,y) == reference(L,Q,scale,0.0,expected,R)
        end
        for q in (linear(out)[1],quadratic(out)[1,2],QT.offset(out),QT.scale(out))
            poison(q)
        end
        fresh=export_model(result)
        @test quadratic(fresh)[1,2] == gauge[1]*gauge[2]*R(1,4)
        @test borrowed == R(1,4)
        # Public MaxCut graph and certificates also promise owned rationals.
        graph=maxcut_graph(ws)
        for (_,q) in graph.reference_weights
            poison(q)
        end
        for (_,_,q) in graph.edge_weights
            poison(q)
        end
        poison(graph.cut_constant);poison(graph.scale)
        @test borrowed == R(1,4)
        attempt=prove_dominance(ws,3)
        @test attempt.certificate !== nothing && verify_certificate(ws,attempt.certificate).valid
        for step in attempt.certificate.steps,q in (step.lower,step.upper,step.constant)
            poison(q)
        end
        @test verify_certificate(ws,prove_dominance(ws,3).certificate).valid
        @test apply_dominance!(ws,3).stop_reason === :applied
        exported=export_certificate(ws)
        for step in exported.steps,q in (step.lower,step.upper,step.constant)
            poison(q)
        end
        @test verify_certificate(ws,export_certificate(ws)).valid
        @test borrowed == R(1,4)
        check_integer_objective(ws,L,Q,scale,0.0,domain)
        check_integer_objective(other,L,Q,scale,0.0,domain)
        check_integer_objective(copied,L,Q,scale,0.0,domain)
        reset!(ws,model;integerize_scale=false)
        check_integer_objective(ws,L,Q,scale,0.0,domain)
    end
end

@testset "physical enclosures preserve exact endpoint bits across numeric contexts" begin
    R = Rational{BigInt}
    bits(x) = reinterpret(UInt64,x)
    pairbits(x) = map(bits,x)
    function exact_float_bits(x)
        b=bits(x);e=Int((b>>52)&0x7ff);m=b&0x000fffffffffffff
        e==0x7ff && error("finite endpoint required")
        e==0 || (m|=UInt64(1)<<52)
        n=BigInt(m);(b>>63)!=0 && (n=-n)
        p=e==0 ? -1074 : e-1075
        return p>=0 ? R(n<<p,1) : R(n,big(1)<<(-p))
    end
    vals=Int128[0,1,-1,17,-17,3602879701896397,-3602879701896397,
        (Int128(1)<<53)-1,(Int128(1)<<53)+1,-((Int128(1)<<53)+1),
        (Int128(1)<<63)+1024,-((Int128(1)<<63)+1025),
        (Int128(1)<<126)+(Int128(1)<<73)+1,
        -((Int128(1)<<126)+(Int128(1)<<73)+1),typemin(Int128),typemax(Int128)]
    shifts=(0,1,2,55,74,127,129,1021,1022,1074)
    ws=Workspace(fixture([1,2,3],zeros(3),zeros(3,3));rules=:mixed)
    st=ws._state;saved_ftz=get_zero_subnormals()
    try
        for p in (8,24,53,128,256),round in (RoundNearest,RoundUp,RoundDown,RoundToZero),ftz in (false,true)
            set_zero_subnormals(ftz)
            setprecision(BigFloat,p) do
                setrounding(BigFloat,round) do
                    for q in vals,shift in shifts
                        # Scalar conversion context only, never a live update.
                        st.shift=shift
                        old=QUBOPreprocessing._enclose(QUBOPreprocessing._physical(st,q))
                        enclosed=QUBOPreprocessing._enclose_physical(st,q)
                        @test pairbits(enclosed)==pairbits(old)
                        if iszero(q)
                            @test pairbits(enclosed)==(UInt64(0),UInt64(0))
                        elseif p>=53
                            common=min(trailing_zeros(q),shift)
                            num=q>>common;d=shift-common
                            eligible=d<=1021 && (p>=128 || -(Int128(1)<<53)<=num<=(Int128(1)<<53))
                            if eligible
                                exact=R(BigInt(q),big(1)<<shift)
                                lo=exact_float_bits(enclosed[1]);hi=exact_float_bits(enclosed[2])
                                @test lo<=exact<=hi
                                if lo==exact
                                    @test lo==hi
                                    @test bits(enclosed[1])==bits(enclosed[2])
                                else
                                    @test lo<exact<hi
                                    @test bits(nextfloat(enclosed[1]))==bits(enclosed[2])
                                end
                            end
                        end
                    end
                end
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
    @test get_zero_subnormals()==saved_ftz
    for q in (BigInt(0),big(1)<<200,-(big(1)<<200)+1),shift in (0,2,55,1074,65536)
        st.shift=shift;before=deepcopy(q)
        @test pairbits(QUBOPreprocessing._enclose_physical(st,q))==pairbits(QUBOPreprocessing._enclose(QUBOPreprocessing._physical(st,q)))
        @test q==before
    end
    for q in (R(0),R(1,3),R(-1,3),R(1,10)),shift in (-1,55,65536)
        st.shift=shift;before=deepcopy(q)
        @test pairbits(QUBOPreprocessing._enclose_physical(st,q))==pairbits(QUBOPreprocessing._enclose(q))
        @test q==before
    end
    st.shift=-1
    @test_throws ArgumentError QUBOPreprocessing._enclose_physical(st,Int128(0))
    @test_throws ArgumentError QUBOPreprocessing._enclose_physical(st,Int128(1))
    st.shift=typemax(Int)
    @test pairbits(QUBOPreprocessing._enclose_physical(st,Int128(0)))==(UInt64(0),UInt64(0))
    @test pairbits(QUBOPreprocessing._enclose_physical(st,BigInt(0)))==(UInt64(0),UInt64(0))
    for q in (Int128(1),typemin(Int128),typemax(Int128))
        st.shift=65536
        @test pairbits(QUBOPreprocessing._enclose_physical(st,q))==pairbits(QUBOPreprocessing._enclose(QUBOPreprocessing._physical(st,q)))
    end
    # Preserve raw-coordinate enclosure before the existing outward quarter.
    try
        set_zero_subnormals(false)
        setprecision(BigFloat,256) do
            setrounding(BigFloat,RoundNearest) do
                st.shift=2
                lo,hi=QUBOPreprocessing._enclose_physical(st,Int128(1))
                @test pairbits((prevfloat(0.25*lo),nextfloat(0.25*hi)))!=pairbits(QUBOPreprocessing._enclose(R(1,16)))
            end
        end
    finally
        set_zero_subnormals(saved_ftz)
    end
    @test get_zero_subnormals()==saved_ftz
end

@testset "physical enclosures survive productive regridding promotion and rollback" begin
    L=[1.0,0.0,0.0]
    Q=[0.0 1.0 1.0;0.0 0.0 0.0;0.0 0.0 0.0]
    ws=Workspace(fixture([1,2,3],L,Q;domain=:spin);rules=:mixed)
    root=checkpoint(ws)
    @test QUBOPreprocessing._enclose_physical(ws._state,Int128(1))==(1.0,1.0)
    @test eliminate_variable!(ws,1).stop_reason===:applied
    @test ws._state.shift==1
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    for promoted in (false,true)
        promoted && QUBOPreprocessing._ensure_grid!(ws._state,ws._state.shift+130)
        @test eltype(ws._state.fields)==(promoted ? BigInt : Int128)
        st=ws._state
        for q in vcat(st.fields,st.dual_fields,st.lower,st.upper,[q for ns in st.adjacency for (_,q) in ns])
            @test map(x->reinterpret(UInt64,x),QUBOPreprocessing._enclose_physical(st,q))==map(x->reinterpret(UInt64,x),QUBOPreprocessing._enclose(QUBOPreprocessing._physical(st,q)))
        end
        check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    end
    rollback!(ws,root)
    check_integer_objective(ws,L,Q,1.0,0.0,:spin)
    st=ws._state
    for q in st.fields
        @test map(x->reinterpret(UInt64,x),QUBOPreprocessing._enclose_physical(st,q))==map(x->reinterpret(UInt64,x),QUBOPreprocessing._enclose(QUBOPreprocessing._physical(st,q)))
    end
end
