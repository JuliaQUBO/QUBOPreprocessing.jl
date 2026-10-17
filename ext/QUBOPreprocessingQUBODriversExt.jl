# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.
module QUBOPreprocessingQUBODriversExt

import QUBOPreprocessing
import QUBOTools
import QUBODrivers
import QUBODrivers: MOI, Sample, SampleSet
const QP = QUBOPreprocessing
const QT = QUBOTools
const VI = MOI.VariableIndex

mutable struct _Budget
    remaining::Int
    used::Int
    deadline::Union{Nothing,UInt64}
end
function _charge!(b,n)
    QP._expired(b.deadline) && return :deadline
    n <= b.remaining || return :work_limit
    b.remaining -= n
    b.used += n
    return nothing
end
_stored(x::Union{QT.SparseLinearForm,QT.SparseQuadraticForm}) = length(QT.data(x).nzval)
_stored(x) = length(QT.data(x))
function _units(model)
    f = QT.form(model)
    return Base.checked_add(QT.dimension(model)+1,
        Base.checked_add(_stored(QT.linear_form(f)),_stored(QT.quadratic_form(f))))
end
function _units(s::QP._Snapshot)
    return Base.checked_add(length(s.labels)+1,
        Base.checked_add(length(s.linear.values),length(s.quadratic.values)))
end
_passes(n,k) = Base.checked_mul(n,k)

function _child_model(model)
    # Relabel only: retain the already checked raw form, sense, domain and scale.
    # A normalizing constructor or Float64 summation is not needed here.
    labels = VI.(1:QT.dimension(model))
    vm = QT.VariableMap{VI}(Dict(v=>i for (i,v) in enumerate(labels)),labels)
    return QT.Model{VI,Float64,Int}(vm,deepcopy(QT.form(model)))
end
function _child_bound(child,model,remaining,deadline,custom)
    if custom !== nothing
        bound = custom(child,model,remaining,deadline)
        QP._limits(bound,nothing)
        return Int(bound)
    elseif child isa QUBODrivers.ExactSampler.Optimizer
        n = QT.dimension(model)
        n <= 20 || return nothing # before shift or backend exponential allocation
        return Base.checked_add(_passes(_units(model),8),_passes(1<<n,_units(model)))
    end
    return nothing
end

function QP.sample_preprocessed(input,child_factory;rules=nothing,max_work=typemax(Int),
        max_deductions=typemax(Int),max_exact_work=typemax(Int),deadline_ns=nothing,
        max_child_variables=16,max_results=1024,child_work_bound=nothing)
    QP._limits(max_work,deadline_ns)
    QP._limits(max_deductions,deadline_ns)
    QP._limits(max_exact_work,deadline_ns)
    QP._limits(max_child_variables,deadline_ns)
    QP._limits(max_results,deadline_ns)
    max_results <= 1_000_000 || throw(ArgumentError("max_results must be <=1000000"))
    begin_ns = time_ns()
    budget = _Budget(Int(max_work),0,deadline_ns)
    ws = input isa QP.Workspace ? input : nothing
    exported = nothing
    samples,reads = QP.Reconstruction[],Int[]
    child_status = :not_called
    child_called = false
    child_allowance = nothing
    rejected = 0
    phase = :setup
    timings = Dict{Symbol,Float64}()
    propagation = nothing
    child_variables = 0
    function finish(reason;scope_optimal=false)
        scope = exported === nothing ? :unknown : exported.certificate.scope
        expired = QP._expired(deadline_ns)
        expired && (reason=:deadline;scope_optimal=false)
        scope_optimal && scope === :assumptions && reason === :optimal && (reason=:scope_optimal)
        source = ws === nothing ? nothing : ws._snapshot
        metadata = (total_seconds=0.0,phases=copy(timings),
            work_used=budget.used,work_remaining=budget.remaining,child_work_reserved=child_allowance,
            child_called=child_called,child_variables=child_variables,rejected_results=rejected,
            propagation=propagation,stopped_phase=phase,
            labels=exported === nothing ? [] : QP.original_variables(exported),
            caller_assumptions=exported isa QP.ConditionedExport ? exported.certificate.assumptions : (),
            reduction_chain=exported === nothing ? () : exported.certificate.reduction_chain,
            sense=source === nothing ? nothing : source.sense,
            domain=source === nothing ? nothing : source.domain,
            scale=source === nothing ? nothing : source.scale,
            offset=source === nothing ? nothing : source.offset)
        metadata = merge(metadata,(total_seconds=Float64(time_ns()-begin_ns)/1e9,))
        return QP.SolverResult(ws,ws === nothing ? nothing : QP.generation(ws),scope,reason,
            samples,reads,scope_optimal && scope === :original,scope_optimal,child_status,exported,metadata)
    end
    stop = _charge!(budget,0)
    stop === nothing || return finish(stop)
    t = time_ns()
    if ws === nothing
        selected = rules === nothing ? :dominance : rules
        stop = _charge!(budget,_passes(_units(input),8))
        stop === nothing || return finish(stop)
        ws = QP.Workspace(input;rules=selected)
    elseif rules !== nothing && rules !== ws._state.rules
        throw(ArgumentError("rules must match the existing workspace; construct a new one to change rules"))
    end
    timings[:setup] = Float64(time_ns()-t)/1e9
    phase = :propagation
    t = time_ns()
    if ws._state.rules === :dominance
        propagation = QP.propagate!(ws;max_work=budget.remaining,max_deductions,max_exact_work,deadline_ns)
        # Producer work was already bounded by this same remaining allowance.
        used = propagation.candidates+propagation.edge_visits
        budget.remaining -= used
        budget.used += used
        timings[:propagation] = Float64(time_ns()-t)/1e9
        propagation.stop_reason === :deadline && return finish(:deadline)
        # Every other interruption leaves a sound prefix that can be solved.
    end
    phase = :materialization
    t = time_ns()
    # Reserve source/proof capture, residual construction/relabeling and one
    # shared original-energy evaluator, before any of these graph-copy boundaries.
    units = _units(ws._snapshot)
    stop = _charge!(budget,_passes(units+ws._state.proof_count,8))
    stop === nothing || return finish(stop)
    try
        exported = QP.materialize(ws)
    catch err
        err isa ArgumentError || rethrow()
        return finish(:unsafe_export)
    end
    model = QP.export_model(exported)
    evaluator = QP._source_evaluator(exported._snapshot)
    timings[:materialization] = Float64(time_ns()-t)/1e9
    phase = :verification
    t = time_ns()
    proof = exported isa QP.ExportResult ? nothing : exported.certificate.proof
    if proof !== nothing
        verified = QP.verify_certificate(ws,proof;max_work=budget.remaining,deadline_ns)
        budget.remaining -= verified.term_visits
        budget.used += verified.term_visits
        verified.valid || return finish(verified.reason === :deadline ? :deadline : :verification_limit)
    end
    timings[:verification] = Float64(time_ns()-t)/1e9
    child_variables = QT.dimension(model)
    if child_variables == 0
        phase = :reconstruction
        t = time_ns()
        stop = _charge!(budget,units)
        stop === nothing || return finish(stop)
        restored = QP._reconstruct(exported,Int[],evaluator)
        restored.energy.finite || return finish(:nonfinite_energy)
        push!(samples,restored);push!(reads,1)
        timings[:reconstruction] = Float64(time_ns()-t)/1e9
        return finish(:optimal;scope_optimal=true)
    end
    child_variables <= max_child_variables || return finish(:capacity_limit)
    max_results > 0 || return finish(:result_limit)
    phase = :child
    t = time_ns()
    child = try
        child_factory()
    catch err
        err isa InterruptException && rethrow()
        return finish(:child_failure)
    end
    child isa QUBODrivers.AbstractSampler{Float64} ||
        throw(ArgumentError("factory must return a fresh Float64 QUBODrivers sampler"))
    QT.dimension(child) == 0 && isempty(QT.solution(child)) ||
        throw(ArgumentError("child factory must return a fresh empty sampler"))
    child_allowance = _child_bound(child,model,budget.remaining,deadline_ns,child_work_bound)
    child_allowance === nothing && max_work != typemax(Int) && return finish(:unsupported_work_limit)
    child isa QUBODrivers.ExactSampler.Optimizer && child_variables > 20 && return finish(:capacity_limit)
    stop = _charge!(budget,something(child_allowance,0))
    stop === nothing || return finish(stop)
    QUBODrivers.set_model!(child,_child_model(model))
    if deadline_ns !== nothing
        now = time_ns()
        now < deadline_ns || return finish(:deadline)
        remaining_seconds = Float64(deadline_ns-now)/1e9
        remaining_seconds > 0 || return finish(:deadline)
        # QUBODrivers0.6.5 supplies this public setter even though its generic
        # supports query is conservative. Exercise the setter itself.
        try
            MOI.set(child,MOI.TimeLimitSec(),remaining_seconds)
        catch err
            err isa Union{MOI.UnsupportedAttribute,MOI.SetAttributeNotAllowed} || rethrow()
            return finish(:unsupported_deadline)
        end
    end
    failed = false
    try
        child_called = true
        MOI.optimize!(child)
    catch err
        err isa InterruptException && rethrow()
        failed = true
    end
    timings[:child] = Float64(time_ns()-t)/1e9
    term = try MOI.get(child,MOI.TerminationStatus()) catch; MOI.OTHER_ERROR end
    child_status = Symbol(string(term))
    count = try MOI.get(child,MOI.ResultCount()) catch; 0 end
    count isa Integer && 0 <= count <= typemax(Int) || return finish(:malformed_child)
    phase = :reconstruction
    t = time_ns()
    first_valid = false
    for rank in 1:min(count,max_results)
        stop = _charge!(budget,units)
        stop === nothing || return finish(stop)
        restored = try
            y = [MOI.get(child,MOI.VariablePrimal(rank),VI(i)) for i in 1:child_variables]
            QP._reconstruct(exported,y,evaluator)
        catch err
            err isa InterruptException && rethrow()
            rejected += 1
            continue
        end
        if !restored.energy.finite
            rejected += 1
            continue
        end
        push!(samples,restored)
        # Keep actual sample multiplicity when available; unknown means1.
        multiplicity = try QT.reads(QT.solution(child),rank) catch; 1 end
        push!(reads,multiplicity isa Integer && 0 < multiplicity <= typemax(Int) ? Int(multiplicity) : 1)
        rank == 1 && (first_valid=true)
    end
    timings[:reconstruction] = Float64(time_ns()-t)/1e9
    failed && return finish(:child_failure)
    isempty(samples) && return finish(count == 0 ? :empty_child : :malformed_child)
    term === MOI.TIME_LIMIT && return finish(:child_timeout)
    certified = term === MOI.OPTIMAL && first_valid
    return finish(certified ? :optimal : :feasible;scope_optimal=certified)
end

QUBODrivers.@setup SamplerOptimizer begin
    name = "Certified Preprocessing Sampler"
    version = Base.pkgversion(QP)
    attributes = begin
        ChildFactory["child_factory"]::Any = QUBODrivers.ExactSampler.Optimizer
        Options["preprocessing_options"]::NamedTuple = NamedTuple()
        LastResult["preprocessing_result"]::Any = nothing
    end
end
QUBODrivers.honors_final_reads(::Type{<:SamplerOptimizer}) = false
QUBODrivers.enforces_time_limit(::Type{<:SamplerOptimizer}) = false
MOI.supports(::SamplerOptimizer,::MOI.TimeLimitSec) = true

function QP.Optimizer(child_factory;kwargs...)
    opt = SamplerOptimizer{Float64}()
    MOI.set(opt,ChildFactory(),child_factory)
    MOI.set(opt,Options(),(;kwargs...))
    return opt
end

function QUBODrivers.sample(opt::SamplerOptimizer{Float64})
    start = time_ns()
    options = MOI.get(opt,Options())
    limit = MOI.get(opt,MOI.TimeLimitSec())
    if limit !== nothing
        isfinite(limit) && 0 <= limit <= Float64(typemax(UInt64)÷2)/1e9 ||
            throw(ArgumentError("finite supported TimeLimitSec required"))
        own_deadline = Base.checked_add(start,UInt64(floor(limit*1e9)))
        prior = get(options,:deadline_ns,nothing)
        options = merge(options,(deadline_ns=prior === nothing ? own_deadline : min(own_deadline,prior),))
    end
    result = QP.sample_preprocessed(QT.backend(opt),MOI.get(opt,ChildFactory());options...)
    MOI.set(opt,LastResult(),result)
    s = QT.backend(opt)
    samples = Sample{Float64,Int}[Sample{Float64,Int}(copy(r.state),r.energy.value,k)
                                for (r,k) in zip(result.samples,result.reads)]
    termination = result.optimal ? MOI.OPTIMAL :
        result.stop_reason in (:deadline,:child_timeout) ? MOI.TIME_LIMIT :
        !isempty(samples) ? MOI.LOCALLY_SOLVED :
        result.stop_reason in (:work_limit,:verification_limit,:capacity_limit,:result_limit,
                               :unsupported_work_limit,:unsupported_deadline) ? MOI.OTHER_LIMIT : MOI.OTHER_ERROR
    elapsed = Float64(time_ns()-start)/1e9
    metadata = Dict{String,Any}(
        "origin"=>"QUBOPreprocessing.jl", "status"=>String(result.stop_reason),
        "termination_status"=>termination,
        "algorithm"=>Dict("name"=>"Certified strict dominance + supplied child"),
        "backend"=>Dict("name"=>"QUBOPreprocessing.jl","version"=>string(Base.pkgversion(QP))),
        "reads"=>Dict("number_of_reads"=>sum(result.reads),"final_number_of_reads"=>sum(result.reads)),
        "seeds"=>Dict{String,Any}(),"time"=>Dict("total"=>elapsed,"effective"=>elapsed),
        "preprocessing"=>Dict("scope"=>String(result.scope),"scope_optimal"=>result.scope_optimal,
            "work_used"=>result.metadata.work_used,"child_called"=>result.metadata.child_called,
            "child_variables"=>result.metadata.child_variables,"child_status"=>String(result.child_status)))
    return SampleSet{Float64}(samples,metadata;sense=QT.sense(s),domain=QT.domain(s))
end
function MOI.get(opt::SamplerOptimizer,::MOI.TerminationStatus)
    metadata = QT.metadata(QT.solution(opt))
    isempty(metadata) && return MOI.OPTIMIZE_NOT_CALLED
    # Explicit post-sample transformations cannot retain the upstream proof.
    callback = get(get(metadata,"postprocess",Dict()),"callback",Dict())
    get(callback,"transformed",false) && return MOI.LOCALLY_SOLVED
    return get(metadata,"termination_status",MOI.OTHER_ERROR)
end

end
