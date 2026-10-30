using Random

function _fuzz_randmodel(rng, n)
    dom = rand(rng, (:bool, :spin))
    sense = rand(rng, (:min, :min, :max))
    coef() = rand(rng, (rand(rng, -4:4), rand(rng, -8:8) / 2, rand(rng, -3:3) / 4, rand(rng, -3:3) / 3 * 1.0))
    L = Dict{Int,Float64}()
    Q = Dict{Tuple{Int,Int},Float64}()
    p = rand(rng, (0.3, 0.5, 0.8))
    for i in 1:n
        rand(rng) < 0.7 && (L[i] = Float64(coef()))
        for j in (i + 1):n
            rand(rng) < p && (Q[(i, j)] = Float64(coef()))
        end
    end
    off = rand(rng, (0.0, 0.0, 1.5, -2.0))
    m = QT.Model{Int,Float64,Int}(L, Q; domain=dom, sense=sense, offset=off)
    return m, dom, sense
end

function _fuzz_states(n, dom)
    low = dom === :bool ? 0 : -1
    return (Int[((k >> (i - 1)) & 1) == 1 ? 1 : low for i in 1:n] for k in 0:(2^n - 1))
end

_fuzz_best(sense, vals) = sense === :min ? minimum(vals) : maximum(vals)

const _FUZZ_CONFIGS = (
    (name="strong", kw=(;)),
    (name="star", kw=(enable_star_triangle=true,)),
    (name="blocks", kw=(enable_star_triangle=true, enable_blocks=true)),
    (name="weak", kw=(enable_star_triangle=true, enable_blocks=true, allow_weak_dominance=true, allow_weak_relations=true)),
    (name="weak-nofb", kw=(allow_weak_dominance=true, allow_weak_relations=true, allow_exact_fallback=false)),
)

function _check_scheduler_fuzz_case(rng, n, cfg)
    m, dom, sense = _fuzz_randmodel(rng, n)
    n_dim = QT.dimension(m)
    ws = Workspace(m; rules=:mixed)
    rep = schedule_reductions!(ws; cfg.kw...)
    orig = [QT.value(x, QT.form(m)) for x in _fuzz_states(n_dim, dom)]
    obest = _fuzz_best(sense, orig)
    cert = export_certificate(ws)
    if cert !== nothing
        vr = verify_certificate(ws, cert)
        vr.valid || return (:verify_failed, vr.stop_reason)
    end
    res = materialize(ws; coefficient_type=(cert === nothing ? Float64 : Rational{BigInt}))
    rm = export_model(res)
    nr = QT.dimension(rm)
    rdom = QT.domain(rm) === QT.BoolDomain ? :bool : :spin
    rvals = Float64[]
    for y in _fuzz_states(nr, rdom)
        rv = Float64(QT.value(y, QT.form(rm)))
        rec = reconstruct(res, y)
        abs(rec.energy.value - rv) <= 1e-9 * (1 + abs(rv)) || return (:lift_mismatch, (rv, rec.energy.value))
        ov = QT.value(rec.state, QT.form(m))
        abs(ov - rv) <= 1e-9 * (1 + abs(rv)) || return (:lift_state_mismatch, (rv, ov))
        push!(rvals, rv)
    end
    rbest = _fuzz_best(sense, rvals)
    abs(rbest - obest) <= 1e-9 * (1 + abs(obest)) || return (:optimum_lost, (obest, rbest, rep.stop_reason))
    return (:ok, nr < n_dim)
end

function _check_sequence_fuzz_case(rng, n0)
    m, dom, sense = _fuzz_randmodel(rng, n0)
    n = QT.dimension(m)
    labels = QT.variables(m)
    n == 0 && return (:ok, false)
    ws = Workspace(m; rules=:mixed)
    map = nothing
    if rand(rng) < 0.5
        tdom = rand(rng, (:bool, :spin))
        g = rand(rng) < 0.5 ? nothing : rand(rng, (-1, 1), n)
        map = domain_map(ws; domain=tdom, gauge=g)
    end
    assumed = Dict{Int,Int}()
    low = dom === :bool ? 0 : -1
    cp = nothing
    for _ in 1:rand(rng, 2:6)
        r = rand(rng, 1:9)
        lab = rand(rng, labels)
        try
            if r == 1
                schedule_reductions!(ws; map, enable_star_triangle=rand(rng, Bool), enable_blocks=rand(rng, Bool),
                    allow_weak_dominance=rand(rng, Bool), allow_weak_relations=rand(rng, Bool))
            elseif r == 2
                apply_probing!(ws, lab; map, double_probe=rand(rng, Bool))
            elseif r == 3
                apply_roof_duality!(ws; map, contract_scc=rand(rng, Bool))
            elseif r == 4
                apply_submodular_cut!(ws; map, allow_weak=rand(rng, Bool))
            elseif r == 5
                apply_maxcut!(ws, lab; map, allow_weak=rand(rng, Bool))
            elseif r == 6 && length(assumed) < n - 1
                v = rand(rng, (low, 1))
                assume!(ws, lab, v)
                assumed[lab] = v
            elseif r == 7 && cp === nothing
                cp = (checkpoint(ws), copy(assumed))
            elseif r == 8 && cp !== nothing
                rollback!(ws, cp[1])
                assumed = copy(cp[2])
                cp = nothing
            end
        catch err
            err isa ArgumentError || rethrow()
        end
    end
    cert = export_certificate(ws; map)
    if cert !== nothing
        vr = verify_certificate(ws, cert; map)
        vr.valid || return (:verify_failed, vr.stop_reason)
    end
    idx = Dict(l => i for (i, l) in enumerate(labels))
    orig = Float64[]
    for x in _fuzz_states(n, dom)
        all(x[idx[l]] == v for (l, v) in assumed) || continue
        push!(orig, QT.value(x, QT.form(m)))
    end
    obest = _fuzz_best(sense, orig)
    res = materialize(ws; coefficient_type=(cert === nothing && map === nothing && isempty(assumed) ? Float64 : Rational{BigInt}), map)
    rm = export_model(res)
    nr = QT.dimension(rm)
    rdom = QT.domain(rm) === QT.BoolDomain ? :bool : :spin
    rsense = QT.sense(rm) === QT.Min ? :min : :max
    rvals = Float64[]
    for y in _fuzz_states(nr, rdom)
        rv = Float64(QT.value(y, QT.form(rm)))
        rec = reconstruct(res, y)
        ov = QT.value(rec.state, QT.form(m))
        abs(rec.energy.value - ov) <= 1e-9 * (1 + abs(ov)) || return (:energy_report_mismatch, (ov, rec.energy.value))
        all(rec.state[idx[l]] == v for (l, v) in assumed) || return (:assumption_violated, (rec.state, assumed))
        abs(ov - rv) <= 1e-9 * (1 + abs(rv)) || return (:lift_state_mismatch, (rv, ov))
        push!(rvals, rv)
    end
    rbest = _fuzz_best(rsense, rvals)
    abs(rbest - obest) <= 1e-9 * (1 + abs(obest)) || return (:optimum_lost, (obest, rbest))
    return (:ok, nr < n)
end

function _fuzz_with_field(x, k, newval)
    T = typeof(x)
    vals = Any[getfield(x, i) for i in 1:fieldcount(T)]
    vals[k] = newval
    return T(vals...)
end

_fuzz_mutations(v::Int) = unique((v + 1, v - 1, -v, 1 - v))
_fuzz_mutations(v::Rational{BigInt}) = (v + 1, v - 1 // 2, -v, v * 2 + 1)
function _fuzz_mutations(v::Tuple)
    out = Any[]
    for i in eachindex(v), m in _fuzz_mutations(v[i])
        try
            push!(out, Base.setindex(v, m, i))
        catch
        end
    end
    return out
end
_fuzz_mutations(p::Pair) = [p.first => m for m in _fuzz_mutations(p.second)]
_fuzz_mutations(_) = ()

function _check_tamper_fuzz_case(rng, n)
    m, dom, sense = _fuzz_randmodel(rng, n)
    n_dim = QT.dimension(m)
    n_dim == 0 && return (:ok, 0, 0)
    labels = QT.variables(m)
    ws = Workspace(m; rules=:mixed)
    init_op = rand(rng, 1:5)
    try
        if init_op == 1
            apply_roof_duality!(ws; contract_scc=true)
        elseif init_op == 2
            apply_submodular_cut!(ws; allow_weak=rand(rng, Bool))
        elseif init_op == 3
            apply_maxcut!(ws, rand(rng, labels); allow_weak=rand(rng, Bool))
        elseif init_op == 4
            apply_probing!(ws, rand(rng, labels); double_probe=rand(rng, Bool))
        end
    catch err
        err isa ArgumentError || rethrow()
    end
    schedule_reductions!(ws; enable_star_triangle=true, enable_blocks=true,
        allow_weak_dominance=rand(rng, Bool), allow_weak_relations=rand(rng, Bool))
    cert = export_certificate(ws)
    cert === nothing && return (:ok, 0, 0)
    verify_certificate(ws, cert).valid || return (:base_invalid, 0, 0)
    orig_all = [QT.value(x, QT.form(m)) for x in _fuzz_states(n_dim, dom)]
    obest = _fuzz_best(sense, orig_all)
    res = materialize(ws; coefficient_type=Rational{BigInt})
    rm = export_model(res)
    nr = QT.dimension(rm)
    rdom = QT.domain(rm) === QT.BoolDomain ? :bool : :spin
    checked = 0
    rejected = 0
    for (k, step) in enumerate(cert.steps)
        T = typeof(step)
        for f in 1:fieldcount(T)
            fname = fieldname(T, f)
            fname in (:predecessors, :scope_length, :method) && continue
            for mv in _fuzz_mutations(getfield(step, f))
                isequal(mv, getfield(step, f)) && continue
                newstep = try
                    _fuzz_with_field(step, f, mv)
                catch
                    continue
                end
                steps = Base.setindex(cert.steps, newstep, k)
                c2 = QUBOPreprocessing.DominanceCertificate(
                    cert.generation,
                    cert._scope_checkpoint,
                    cert.assumptions,
                    steps,
                    cert._source,
                    cert._map,
                )
                checked += 1
                ok = try
                    verify_certificate(ws, c2).valid
                catch
                    false
                end
                if !ok
                    rejected += 1
                else
                    # Every accepted tampered certificate must lift all residual states
                    # with exact energy agreement and preserve the brute-force global optimum.
                    lifted_vals = Float64[]
                    for y in _fuzz_states(nr, rdom)
                        rv = Float64(QT.value(y, QT.form(rm)))
                        st = QUBOPreprocessing._lift_state_impl(res, y, res._free, steps)
                        ov = QT.value(st, QT.form(m))
                        abs(ov - rv) <= 1e-9 * (1 + abs(rv)) || return (:unsound_tamper_lift_mismatch, (rv, ov))
                        push!(lifted_vals, ov)
                    end
                    lbest = _fuzz_best(sense, lifted_vals)
                    abs(lbest - obest) <= 1e-9 * (1 + abs(obest)) || return (:unsound_tamper_accepted, (obest, lbest))
                end
            end
        end
    end
    return (:ok, checked, rejected)
end

@testset "Brute-Force Scheduler, Sequence, and Certificate-Tampering Fuzzing (#80)" begin
    @testset "Brute-force scheduler fuzzing across 5 configurations" begin
        rng = MersenneTwister(20261030)
        reduced_count = 0
        for t in 1:150
            n = rand(rng, 1:8)
            cfg = _FUZZ_CONFIGS[mod1(t, length(_FUZZ_CONFIGS))]
            sub = MersenneTwister(10_000 + t)
            status, info = _check_scheduler_fuzz_case(sub, n, cfg)
            @test status === :ok
            status === :ok && info && (reduced_count += 1)
        end
        @test reduced_count >= 50
    end

    @testset "Interleaved operation-sequence, gauge-map, assumption & rollback fuzzing" begin
        rng = MersenneTwister(20261031)
        reduced_count = 0
        for t in 1:150
            n = rand(rng, 1:8)
            sub = MersenneTwister(20_000 + t)
            status, info = _check_sequence_fuzz_case(sub, n)
            @test status === :ok
            status === :ok && info && (reduced_count += 1)
        end
        @test reduced_count >= 40

        # Explicit 8-variable regression sequence from #71 (repro94) with and without gauge map
        L = Dict(5 => 1 / 3, 4 => 1.0, 6 => 2.0, 2 => -4.0, 3 => 1.0, 1 => 1 / 3)
        Q = Dict(
            (4, 5) => 3.0, (1, 2) => -0.25, (6, 8) => 4.0, (2, 5) => 2.0,
            (1, 3) => 2 / 3, (3, 8) => 4.0, (2, 6) => -1.0, (7, 8) => -0.25,
            (4, 7) => 0.5, (3, 4) => -2.0, (5, 6) => -1.0, (2, 7) => 4.0,
            (2, 8) => 0.75, (5, 7) => -2 / 3, (1, 6) => -0.5, (3, 5) => -1 / 3,
            (5, 8) => -2 / 3, (2, 4) => -0.5, (1, 7) => 3.5, (3, 6) => 0.75,
            (6, 7) => -3.0, (1, 8) => 4.0,
        )
        gauge = [-1, -1, 1, 1, 1, 1, -1, 1]
        for seq in (
            [:roof, :schedule, (1 => 0), :schedule, (2 => 1)],
            [:schedule, (1 => 0), :schedule, (2 => 1)],
            [(1 => 0), :schedule, (2 => 1)],
            [(1 => 0), (2 => 1)],
        ), usemap in (true, false)
            m = QT.Model{Int,Float64,Int}(L, Q; domain=:bool, sense=:min)
            ws = Workspace(m; rules=:mixed)
            map = usemap ? domain_map(ws; domain=:bool, gauge=gauge) : nothing
            assumed = Dict{Int,Int}()
            for op in seq
                if op === :roof
                    apply_roof_duality!(ws; map)
                elseif op === :schedule
                    schedule_reductions!(ws; map)
                else
                    (l, v) = op
                    assume!(ws, l, v)
                    assumed[l] = v
                end
                cert_step = export_certificate(ws; map)
                if cert_step !== nothing
                    @test verify_certificate(ws, cert_step; map).valid
                end
                ctype = (cert_step === nothing && map === nothing && isempty(assumptions(ws))) ? Float64 : Rational{BigInt}
                res = materialize(ws; coefficient_type=ctype, map)
                rm = export_model(res)
                nr = QT.dimension(rm)
                for y in _fuzz_states(nr, :bool)
                    st = reconstruct(res, y).state
                    @test all(st[l] == v for (l, v) in assumed)
                end
            end
        end
    end

    @testset "Certificate-tampering soundness verification" begin
        rng = MersenneTwister(20261101)
        total_checked = 0
        total_rejected = 0
        for t in 1:60
            n = rand(rng, 2:7)
            status, checked, rejected = _check_tamper_fuzz_case(MersenneTwister(30_000 + t), n)
            @test status === :ok
            total_checked += checked
            total_rejected += rejected
        end
        @test total_checked >= 500
        @test total_rejected >= 450
    end
end

