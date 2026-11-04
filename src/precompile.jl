# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Deterministic, corpus-independent fixtures. The largest graph has 20 vertices;
# the only explicit block has five (32 assignments). Keep construction separate
# from the captured workload so fixture-building code need not enter the cache.
function _precompile_models()
    model(L, Q; domain=:spin) = QT.Model{Int,Float64,Int}(L, Q; domain, sense=:min)
    glass_h = Dict(i => Float64(((i * 31) % 5) - 2) for i in 1:20)
    glass_J = Dict{Tuple{Int,Int},Float64}()
    for i in 1:20, j in (i + 1):20
        w = ((i * 7919 + j * 104729) % 7) - 3
        abs(w) >= 2 && (glass_J[(i, j)] = Float64(w))
    end
    glass_L = Dict(i => 2glass_h[i] - 2sum((v for ((a, b), v) in glass_J if a == i || b == i); init=0.0) for i in 1:20)
    glass_Q = Dict(edge => 4v for (edge, v) in glass_J)
    cheap_L = Dict(i => h for (i, h) in enumerate([5.0, 0.5, 0.25, -0.25, 0.0, 0.25, -0.5]))
    cheap_Q = Dict((1,2)=>1.0, (2,3)=>-0.5, (3,4)=>-6.0, (3,5)=>0.5,
                   (3,6)=>0.5, (4,5)=>0.5, (4,6)=>0.5, (4,7)=>1.0,
                   (5,6)=>1.0, (5,7)=>1.0, (6,7)=>1.0)
    probe_L = Dict(1=>4.0, 2=>1.5, 3=>1.5)
    probe_Q = Dict((1,2)=>2.5, (1,3)=>2.5, (2,3)=>-1.0)
    tiny = ldexp(1.0, -1020)
    return (
        cheap=model(cheap_L, cheap_Q),
        glass=model(glass_L, glass_Q; domain=:bool),
        scc=model(Dict(i=>0.0 for i in 1:16), Dict((i,j)=>-1.0 for i in 1:8 for j in 9:16)),
        roof=model(Dict(1=>2.0, 2=>0.0, 3=>0.0), Dict((1,2)=>-2.0, (1,3)=>-2.0, (2,3)=>-2.0)),
        submodular=model(Dict(1=>1.5, 2=>1.25, 3=>1.0, 4=>-1.5, 5=>-1.25, 6=>-0.75),
                          Dict((i,j)=>2.0 for i in 1:3 for j in 4:6)),
        maxcut=model(Dict(i=>0.0 for i in 1:4),
                     Dict((1,2)=>-2.0, (1,3)=>2.0, (2,3)=>2.0, (1,4)=>0.5, (2,4)=>0.5, (3,4)=>0.5)),
        block=model(Dict(i=>0.0 for i in 1:5), Dict((i,j)=>1.0 for i in 1:5 for j in (i+1):5)),
        probing=model(probe_L, probe_Q),
        exact_witness=model(Dict(i=>tiny*v for (i,v) in probe_L), Dict(e=>tiny*v for (e,v) in probe_Q)),
    )
end

# A large allowance avoids compiling just the cheap floor when a first-use JIT
# cost consumes a small scheduler share. Work is bounded by the tiny fixtures,
# the scheduler's twelve-vertex block cap and the explicit five-vertex block.
# This is not a latency promise and does not change any public runtime default.
function _precompile_budgeted_workload(models)
    deadline = typemax(UInt64)
    schedules = BudgetedScheduleReport[]
    for allow_weak in (false, true)
        ws = Workspace(models.glass; rules=:mixed, integerize_scale=false)
        push!(schedules, schedule_budgeted!(ws; time_limit=3600.0, allow_weak))
        for m in (models.cheap, models.scc)
            _, report = preprocess(m; rules=:mixed, time_limit=3600.0, allow_weak)
            push!(schedules, report)
        end
    end

    _, default_report = preprocess(models.cheap; rules=:mixed, time_limit=3600.0)

    # Calling every family on a glass is insufficient: productive calls enter
    # proof creation and exact workspace updates that a no-change call misses.
    ws_roof = Workspace(models.roof; rules=:mixed)
    roof = apply_roof_duality!(ws_roof; deadline_ns=deadline)
    submodular = map((false, true)) do allow_weak
        ws = Workspace(models.submodular; rules=:mixed)
        apply_submodular_cut!(ws; allow_weak, deadline_ns=deadline)
    end
    maxcut = map((false, true)) do allow_weak
        ws = Workspace(models.maxcut; rules=:mixed)
        apply_maxcut!(ws, 1, 2; allow_weak, deadline_ns=deadline)
    end
    ws_block = Workspace(models.block; rules=:mixed)
    block = eliminate_block!(ws_block, collect(1:5); deadline_ns=deadline)
    ws_probe = Workspace(models.probing; rules=:mixed)
    probing = probe_variables!(ws_probe; order=:coercive, max_rounds=2, deadline_ns=deadline)

    # Small finite binary64 coefficients force exact-rational witness fallback;
    # the ordinary fixture uses Float64 preparation. Both call signatures occur
    # in public standalone and deadline-aware budgeted consumers.
    witnesses = map((models.probing, models.exact_witness)) do m
        ws = Workspace(m; rules=:mixed, integerize_scale=false)
        plain = coercive_field_witness(ws; max_flips=16)
        limited = _coercive_field_witness_orig(ws; max_flips=16, deadline_ns=deadline)
        (plain, limited)
    end
    return (; schedules, default_report, roof, submodular, maxcut, block, probing, witnesses)
end

@setup_workload begin
    let models = _precompile_models()
        @compile_workload begin
            _precompile_budgeted_workload(models)
        end
    end
end
