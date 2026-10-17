# Tiny CPU pilot, not an adoption envelope. No external solver/dependencies.
# Run from a clean producing commit, with one Julia/OpenBLAS thread:
# julia --startup-file=no --threads=1 --project=. scripts/dominance_pilot.jl > pilot.tsv
using QUBOPreprocessing
import QUBOTools as QT

const R = Rational{BigInt}
const MAX_N = 8
const REPS = 5

function coefficients(model)
    n = QT.dimension(model)
    0 <= n <= MAX_N || throw(ArgumentError("pilot child requires 0<=n<=8 before exponentiation"))
    l = [i=>R(v) for (i,v) in QT.linear_terms(model)]
    q = [(i,j)=>R(v) for ((i,j),v) in QT.quadratic_terms(model)]
    return (;n,l,q,scale=R(QT.scale(model)),offset=R(QT.offset(model)))
end
function scalar(c,x)
    v = c.offset
    for (i,a) in c.l; v += a*x[i]; end
    for ((i,j),b) in c.q; v += b*x[i]*x[j]; end
    return c.scale*v
end
function child(model)
    c = coefficients(model) # guard precedes shift/allocation, including original controls
    QT.domain(model) === QT.BoolDomain || throw(ArgumentError("pilot child is binary"))
    low = QT.sense(model) === QT.Min
    best,state = nothing,Int[]
    for mask in 0:(1<<c.n)-1
        x = [(mask>>(i-1))&1 for i in 1:c.n]
        e = scalar(c,x)
        if best === nothing || (low ? e<best : e>best)
            best,state = e,x
        end
    end
    return (;state,energy=best,assignments=1<<c.n)
end
function cases()
    return [
        "cascade"=>QT.Model(Dict(1=>3.0,2=>1.0,3=>0.0,4=>0.0),Dict((1,2)=>-2.0);offset=0.5),
        "all_fixed"=>QT.Model(Dict(i=>Float64(i) for i in 1:8),Dict{Tuple{Int,Int},Float64}();offset=-0.5),
        "tie_chain"=>QT.Model(Dict(i=>0.0 for i in 1:8),Dict((i,i+1)=>1.0 for i in 1:7)),
        "small_no_reduction"=>QT.Model(Dict(1=>0.0,2=>0.0),Dict((1,2)=>-1.0)),
    ]
end
function runmode(model,on)
    start = time_ns()
    setup=prop=proof=material=0.0
    candidates=edges=exact=removed=0
    childmodel=model
    result=nothing
    if on
        t = @timed Workspace(model;rules=:dominance)
        ws,setup = t.value,t.time
        t = @timed propagate!(ws;max_work=512,max_exact_work=2048,max_deductions=MAX_N)
        report,prop = t.value,t.time
        report.stop_reason === :quiescent || error("unexpected bounded pilot interruption")
        candidates,edges,exact = report.candidates,report.edge_visits,report.exact_work
        t = @timed begin
            certificate = export_certificate(ws)
            certificate === nothing || verify_certificate(ws,certificate).valid || error("invalid pilot proof")
        end
        proof = t.time
        t = @timed begin
            result = materialize(ws)
            childmodel = export_model(result)
        end
        material = t.time
        removed = QT.dimension(model)-QT.dimension(childmodel)
    end
    t = @timed child(childmodel)
    solved,solve = t.value,t.time
    t = @timed begin
        restored = on ? reconstruct(result,solved.state).state : copy(solved.state)
        # Independent exact original-energy audit is inside both total timings.
        original = scalar(coefficients(model),restored)
        original == solved.energy || error("pilot energy identity failed")
    end
    lift = t.time
    total = Float64(time_ns()-start)/1e9
    original_edges = count(p->!iszero(last(p)),QT.quadratic_terms(model))
    residual_edges = count(p->!iszero(last(p)),QT.quadratic_terms(childmodel))
    return (;total,setup,prop,proof,material,solve,lift,removed,
            removed_edges=original_edges-residual_edges,n=QT.dimension(childmodel),
            assignments=solved.assignments,energy=solved.energy,candidates,edges,exact)
end

function main()
    root = normpath(joinpath(@__DIR__,".."))
    producing_sha = readchomp(Cmd(["git","rev-parse","HEAD"];dir=root))
    isempty(readchomp(Cmd(["git","status","--porcelain","--untracked-files=normal"];dir=root))) ||
        error("pilot provenance requires a clean checkout")
    # Verify oversize rejection without constructing its state space.
    oversized = QT.Model(Dict(i=>0.0 for i in 1:MAX_N+1),Dict{Tuple{Int,Int},Float64}())
    try
        child(oversized)
        error("oversize guard failed")
    catch e
        e isa ArgumentError || rethrow()
    end
    fixtures=cases()
    for (_,model) in fixtures, _ in 1:2, on in (false,true); runmode(model,on); end
    println("# producing_sha=",producing_sha)
    println("# Julia=",VERSION," QUBOTools=",pkgversion(QT)," threads=",Threads.nthreads(),
            " cpu=",Sys.CPU_NAME," kernel=",Sys.KERNEL," arch=",Sys.ARCH,
            " repetitions=",REPS," max_n=",MAX_N," child=exact_scalar_enumeration")
    names=(:total,:setup,:prop,:proof,:material,:solve,:lift,:removed,:removed_edges,:n,
           :assignments,:energy,:candidates,:edges,:exact)
    println(join(("case","rep","mode",string.(names)...),'\t'))
    for (name,model) in fixtures, rep in 1:REPS
        results=Dict{Bool,Any}()
        for on in (isodd(rep) ? (false,true) : (true,false))
            r=runmode(model,on)
            results[on]=r
            println(join((name,rep,on ? "on" : "off",(getproperty(r,k) for k in names)...),'\t'))
        end
        results[false].energy == results[true].energy || error("pilot optimum mismatch")
    end
end
main()
