# Bounded microbenchmark; prints measurements, never a CI wall-time threshold.
# Run with julia --project=. --startup-file=no scripts/workspace_costs.jl
using QUBOPreprocessing
import QUBOTools as QT

function chain(n)
    labels = collect(1:n)
    vm = QT.VariableMap{Int}(Dict(i=>i for i in labels),labels)
    L = QT.DictLinearForm{Float64}(Dict{Int,Float64}())
    Q = QT.DictQuadraticForm{Float64}(Dict{Tuple{Int,Int},Float64}((i,i+1)=>0.5 for i in 1:n-1))
    return QT.Model{Int,Float64,Int}(vm,QT.Form{Float64}(n,L,Q))
end

function cycles(ws, cp, repetitions)
    for _ in 1:repetitions
        assume!(ws,1,1)
        rollback!(ws,cp)
    end
end

function measure(n)
    model = chain(n)
    Workspace(model) # symmetric construction warmup
    setup = @timed Workspace(model)
    ws = setup.value
    cp = checkpoint(ws)
    cycles(ws,cp,10)
    updates = @timed cycles(ws,cp,1000)
    changes(ws,cp)
    nochange = @timed for _ in 1:1000; changes(ws,cp); end
    assume!(ws,1,1)
    materialize(ws)
    export_measurement = @timed materialize(ws)
    return (; n, setup_seconds=setup.time, setup_bytes=setup.bytes,
            fix_rollback_seconds_per_call=updates.time/1000,
            fix_rollback_bytes_per_call=updates.bytes/1000,
            nochange_seconds_per_call=nochange.time/1000,
            nochange_bytes_per_call=nochange.bytes/1000,
            materialize_seconds=export_measurement.time, materialize_bytes=export_measurement.bytes)
end

measure(10) # warm code shared by the two reported sizes
println("Julia ",VERSION,"; QUBOTools ",pkgversion(QT),"; repetitions=1000; one-thread recommended")
for n in (10,2000)
    println(measure(n))
end
