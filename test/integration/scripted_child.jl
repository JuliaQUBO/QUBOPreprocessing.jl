module ScriptedChild
import QUBODrivers
import QUBODrivers: MOI, Sample, SampleSet
import QUBOTools
const R = Rational{BigInt}
const calls = Ref(0)
const limits = Ref{Any}(nothing)

QUBODrivers.@setup Optimizer begin
    name = "Guarded exact / scripted test child"
    version = v"0.1.0"
    attributes = begin
        Mode["mode"]::Symbol = :exact
    end
end
function scalar(model,x)
    v = R(QUBOTools.offset(model))
    for (i,a) in QUBOTools.linear_terms(model); v += R(a)*x[i]; end
    for ((i,j),b) in QUBOTools.quadratic_terms(model);v += R(b)*x[i]*x[j];end
    return R(QUBOTools.scale(model))*v
end
function QUBODrivers.sample(opt::Optimizer{Float64})
    calls[] += 1
    model = QUBOTools.backend(opt)
    n = QUBOTools.dimension(model)
    0 <= n <= 8 || throw(ArgumentError("test child requires n<=8 before exponentiation"))
    limits[] = MOI.get(opt,MOI.TimeLimitSec())
    mode = MOI.get(opt,Mode())
    low = QUBOTools.domain(model) === QUBOTools.BoolDomain ? 0 : -1
    states = [[isodd(mask>>(i-1)) ? 1 : low for i in 1:n] for mask in 0:(1<<n)-1]
    energies = [scalar(model,x) for x in states]
    order = sortperm(energies;rev=QUBOTools.sense(model) === QUBOTools.Max)
    samples = Sample{Float64,Int}[
        Sample{Float64,Int}(states[k],Float64(energies[k]),1) for k in order]
    term = MOI.OPTIMAL
    if mode === :heuristic
        samples = [Sample{Float64,Int}(fill(low,n),Float64(scalar(model,fill(low,n))),1)]
        term = MOI.LOCALLY_SOLVED
    elseif mode === :empty
        empty!(samples);term=MOI.OTHER_ERROR
    elseif mode === :partial
        samples = [Sample{Float64,Int}(fill(low,max(0,n-1)),0.0,1)]
    elseif mode === :invalid
        samples = [Sample{Float64,Int}(fill(2,n),0.0,1)]
    elseif mode === :invalid_first
        samples = [Sample{Float64,Int}(fill(2,n),-1000.0,1),
                   Sample{Float64,Int}(fill(low,n),1000.0,1)]
    elseif mode === :timeout
        samples = samples[1:1];term=MOI.TIME_LIMIT
    elseif mode === :failure_incumbent
        samples = samples[1:1];term=MOI.OTHER_ERROR
    end
    metadata = Dict{String,Any}(
        "origin"=>"guarded test child","status"=>string(term),"termination_status"=>term,
        "algorithm"=>Dict("name"=>"exact scalar enumeration"),
        "backend"=>Dict("name"=>"test","version"=>"0.1.0"),
        "reads"=>Dict("number_of_reads"=>length(samples),"final_number_of_reads"=>length(samples)),
        "seeds"=>Dict{String,Any}(),"time"=>Dict("total"=>1e-9,"effective"=>1e-9))
    out = SampleSet{Float64}(samples,metadata;sense=QUBOTools.sense(model),domain=QUBOTools.domain(model))
    if mode === :failure_incumbent
        QUBOTools.attach!(opt,out)
        error("scripted failure after a complete incumbent")
    end
    return out
end
MOI.get(opt::Optimizer,::MOI.TerminationStatus) =
    get(QUBOTools.metadata(QUBOTools.solution(opt)),"termination_status",MOI.OPTIMIZE_NOT_CALLED)
function factory(mode=:exact)
    return () -> begin
        opt=Optimizer()
        MOI.set(opt,Mode(),mode)
        opt
    end
end
end
