using QUBOPreprocessing
import QUBOTools as QT

# A bounded exact depth-first caller. The search chooses branches; the workspace
# certifies only strict deductions within them. No heuristic optimum claim.
function branch_search(model)
    n = QT.dimension(model)
    0 <= n <= 8 || throw(ArgumentError("example search requires n<=8 before sizing the tree"))
    QT.domain(model) === QT.BoolDomain && QT.sense(model) === QT.Min ||
        throw(ArgumentError("example search supports binary minimization"))
    maxnodes = (1<<(n+1))-1
    nodes,calls,removed = 0,0,0
    best,beststate = nothing,Int[]
    ws = Workspace(model;rules=:dominance)
    original = original_variables(ws)
    root = checkpoint(ws)
    function visit()
        nodes < maxnodes || error("example node allowance exhausted")
        nodes += 1
        while true
            calls < 8192 || error("example propagation allowance exhausted")
            calls += 1
            r = propagate!(ws;max_work=32,max_exact_work=128,max_deductions=1)
            r.stop_reason === :quiescent && break
            r.stop_reason === :deduction_limit || error("unexpected propagation stop")
        end
        # Explicit O(n) algorithm query; no full graph/model export per decision.
        i = findfirst(!=(0),index_map(ws))
        if i === nothing
            result = materialize(ws) # tiny dyadic fixture has safe Float64 transport
            result.certificate.proof === nothing ||
                verify_certificate(ws,result.certificate.proof).valid || error("invalid branch proof")
            state = reconstruct(result,Int[]).state
            # Exact original scalar audit at leaves, including scale and offset.
            energy = Rational{BigInt}(QT.offset(model))
            for (j,a) in QT.linear_terms(model); energy += Rational{BigInt}(a)*state[j]; end
            for ((j,k),b) in QT.quadratic_terms(model); energy += Rational{BigInt}(b)*state[j]*state[k]; end
            energy *= Rational{BigInt}(QT.scale(model))
            if best === nothing || energy < best;best,beststate=energy,state;end
            return
        end
        cp = checkpoint(ws)
        for value in (0,1)
            assume!(ws,original[i],value)
            visit()
            undo = rollback!(ws,cp;report=true)
            @assert undo.caller_unfixed == [i=>value]
            removed += length(undo.deduction_unfixed)
        end
    end
    visit()
    rollback!(ws,root)
    @assert isempty(assumptions(ws)) && isempty(deductions(ws))
    return (;energy=best,state=beststate,nodes,propagation_calls=calls,removed_deductions=removed)
end

model = QT.Model(Dict(1=>1.0,2=>0.0,3=>2.0,4=>0.0,5=>0.0,6=>0.0),
                 Dict((1,2)=>-2.0,(3,4)=>-3.0,(5,6)=>1.0);offset=0.5)
solved = branch_search(model)
@assert solved.energy == -3//2
@assert solved.state[1:4] == [1,1,1,1]
@assert solved.removed_deductions > 0
@assert solved.nodes <= 127
println(solved)
