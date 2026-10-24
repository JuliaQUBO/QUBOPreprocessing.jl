# Bounded CPU ablation pilot for mixed exact reduction pass scheduling (issue #20),
# not an ecosystem adoption envelope (owned by QUBOBenchmarks #30).
# Run from a clean producing commit, with one Julia/OpenBLAS thread:
# OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/scheduler_pilot.jl > /tmp/scheduler-pilot.tsv && cp /tmp/scheduler-pilot.tsv docs/evidence/scheduler-pilot.tsv
using QUBOPreprocessing
import QUBOTools as QT

const R = Rational{BigInt}
const MAX_N = 10
const REPS = 5

function coefficients(model)
    n = QT.dimension(model)
    0 <= n <= MAX_N || throw(ArgumentError("pilot child requires 0<=n<=10 before exponentiation"))
    l = [i => R(v) for (i, v) in QT.linear_terms(model)]
    q = [(i, j) => R(v) for ((i, j), v) in QT.quadratic_terms(model)]
    return (; n, l, q, scale=R(QT.scale(model)), offset=R(QT.offset(model)))
end

function scalar(c, s)
    v = c.offset
    for (i, a) in c.l; v += a * s[i]; end
    for ((i, j), b) in c.q; v += b * s[i] * s[j]; end
    return c.scale * v
end

function child(model)
    c = coefficients(model)
    QT.domain(model) === QT.SpinDomain || throw(ArgumentError("pilot child is spin"))
    low = QT.sense(model) === QT.Min
    best, state = nothing, Int[]
    s = fill(-1, c.n)
    for mask in 0:(1 << c.n) - 1
        for i in 1:c.n
            s[i] = ((mask >> (i - 1)) & 1) == 1 ? 1 : -1
        end
        e = scalar(c, s)
        if best === nothing || (low ? e < best : e > best)
            best, state = e, copy(s)
        end
    end
    return (; state, energy=best, assignments=1 << c.n)
end

function build_sparse_mixed_cascade_10()
    # 10-vertex sparse model:
    # - 1, 2: strongly dominated leaves fixing into 3, 4
    # - 5, 6: degree-2 chain vertices eliminated by :elimination
    # - 7, 8: strongly coupled pair (J = -6.0) contracted by :relations
    # - 9, 10: residual core coupled to 3, 4, 8
    L = Dict(
        1 => 5.0, 2 => -5.0, 3 => 0.5, 4 => -0.5,
        5 => 0.25, 6 => -0.25, 7 => 0.0, 8 => 0.25,
        9 => 0.5, 10 => -0.75,
    )
    Q = Dict(
        (1, 3) => 1.0, (2, 4) => -1.0,
        (3, 5) => 1.25, (5, 6) => -1.5, (6, 7) => 1.0,
        (7, 8) => -6.0, (7, 9) => 0.5, (8, 9) => 0.5,
        (4, 8) => -1.0, (8, 10) => 1.25, (9, 10) => -0.75,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_dense_no_reduction_8()
    # Dense K_8 with frustrated couplings where no strict dominance, low-degree elimination,
    # star-triangle, or pair relation holds:
    L = Dict(i => (isodd(i) ? 0.25 : -0.25) for i in 1:8)
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:8, j in (i+1):8
        Q[(i, j)] = ((i + j) % 2 == 0) ? 1.0 : -1.0
    end
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_zero_field_star_gadget_10()
    # 4-clique core (1..4) with two zero-field degree-3 star gadgets (5..8) and two degree-2 bridges (9, 10):
    L = Dict(
        1 => 0.5, 2 => -0.75, 3 => 0.25, 4 => -0.5,
        5 => 0.0, 6 => 0.0, 7 => 0.0, 8 => 0.0,
        9 => 0.25, 10 => -0.5,
    )
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:4, j in (i+1):4
        Q[(i, j)] = (i + j) % 2 == 0 ? 1.0 : -1.25
    end
    Q[(1, 5)] = 1.0; Q[(2, 5)] = -1.5; Q[(5, 6)] = 2.0
    Q[(2, 6)] = 1.25; Q[(3, 6) ] = -1.0
    Q[(1, 7)] = -1.0; Q[(3, 7)] = 1.5; Q[(7, 8)] = -2.0
    Q[(2, 8)] = -1.25; Q[(4, 8)] = 1.0
    Q[(1, 9)] = 1.5; Q[(2, 9)] = -1.0
    Q[(3, 10)] = -1.5; Q[(4, 10)] = 1.0
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_nonzero_field_relations_10()
    # 10-vertex model with nonzero fields, 3 strong signed relations (5~1, 6~2, 7~3) and 2 degree-2 whiskers (9, 10):
    L = Dict(
        1 => 0.5, 2 => -0.75, 3 => 0.25, 4 => -0.5,
        5 => 0.25, 6 => -0.25, 7 => 0.5, 8 => -0.5,
        9 => 0.25, 10 => -0.5,
    )
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:4, j in (i+1):4
        Q[(i, j)] = (i + j) % 2 == 0 ? 1.0 : -1.25
    end
    Q[(1, 8)] = 1.0; Q[(2, 8)] = -1.0; Q[(3, 8)] = 1.0; Q[(4, 8)] = -1.0
    Q[(1, 5)] = -6.0; Q[(2, 5)] = 0.5
    Q[(2, 6)] = 6.0;  Q[(3, 6)] = -0.5
    Q[(3, 7)] = -6.0; Q[(4, 7)] = 0.5
    Q[(1, 9)] = 1.5;  Q[(2, 9)] = -1.0
    Q[(3, 10)] = -1.5; Q[(4, 10)] = 1.0
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_high_dynamic_range_8()
    # Dynamic range from 1e6 down to 2^-52 near-tie requiring exact Rational{BigInt} fallback:
    L = Dict(
        1 => 1.0,
        2 => 1000000.0,
        3 => -0.5,
        4 => 0.25,
        5 => -0.75,
        6 => 0.5,
        7 => -0.25,
        8 => 0.5,
    )
    Q = Dict(
        (1, 3) => -0.5,
        (1, 4) => -0.5 + 2.0^-52,
        (2, 3) => 100.0,
        (3, 5) => -1.5,
        (4, 6) => 1.25,
        (5, 6) => -6.0,
        (5, 7) => 0.5,
        (6, 7) => 0.5,
        (7, 8) => -1.0,
        (4, 8) => 0.75,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_degenerate_optima_8()
    # Frustrated cycle + zero-field ties with degenerate global optima:
    L = Dict(i => 0.0 for i in 1:8)
    Q = Dict(
        (1, 2) => -1.0, (2, 3) => -1.0, (3, 4) => -1.0, (1, 4) => 1.0,
        (4, 5) => -4.0, (5, 6) => -1.0, (6, 7) => -1.0, (7, 8) => -1.0, (5, 8) => 1.0,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_repeated_fix_unfix_8()
    # 8-vertex sparse graph for repeated branch/unfix/rollback cycles + root reduction:
    L = Dict(1 => 4.0, 2 => 0.5, 3 => -0.25, 4 => 0.0, 5 => 0.25, 6 => -0.5, 7 => 0.5, 8 => -0.25)
    Q = Dict(
        (1, 2) => 1.0, (2, 3) => -1.5, (3, 4) => -5.0,
        (3, 5) => 0.5, (4, 5) => 0.5,  (5, 6) => -1.25,
        (6, 7) => 1.0, (7, 8) => -1.0, (5, 8) => 0.75,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_gauge_equivalent_cascade_8()
    # Gauge-transformed counterpart of build_repeated_fix_unfix_8 under g = [-1, 1, -1, 1, -1, 1, -1, 1]:
    g = [-1, 1, -1, 1, -1, 1, -1, 1]
    base = build_repeated_fix_unfix_8()
    L = Dict(i => g[i] * v for (i, v) in QT.linear_terms(base))
    Q = Dict((i, j) => g[i] * g[j] * v for ((i, j), v) in QT.quadratic_terms(base))
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function cases()
    return [
        "sparse_mixed_cascade_10" => build_sparse_mixed_cascade_10(),
        "dense_no_reduction_8" => build_dense_no_reduction_8(),
        "zero_field_star_gadget_10" => build_zero_field_star_gadget_10(),
        "nonzero_field_relations_10" => build_nonzero_field_relations_10(),
        "high_dynamic_range_8" => build_high_dynamic_range_8(),
        "degenerate_optima_8" => build_degenerate_optima_8(),
        "repeated_fix_unfix_8" => build_repeated_fix_unfix_8(),
        "gauge_equivalent_cascade_8" => build_gauge_equivalent_cascade_8(),
    ]
end

const MODES = (:off, :dominance, :elimination, :relations, :mixed_cheap, :mixed_star)

function runmode(name::String, model, mode::Symbol)
    start = time_ns()
    setup = disc = proof = material = 0.0
    candidates = edges = exact = fallbacks = removed = fill_edges = 0
    childmodel = model
    result = nothing
    t_all = @timed begin
        if mode !== :off
            w_rules = mode in (:mixed_cheap, :mixed_star) ? :mixed : mode
            t = @timed Workspace(model; rules=w_rules)
            ws, setup = t.value, t.time
            gmap = name == "gauge_equivalent_cascade_8" ?
                domain_map(ws; domain=:spin, gauge=[-1, 1, -1, 1, -1, 1, -1, 1]) : nothing
            if name == "repeated_fix_unfix_8"
                cp0 = checkpoint(ws)
                assume!(ws, 7, 1)
                assume!(ws, 8, -1)
                unfix!(ws, 7)
                unfix!(ws, 8)
                @assert isempty(assumptions(ws))
                cp1 = checkpoint(ws)
                assume!(ws, 7, -1)
                rollback!(ws, cp1)
            end
            t = @timed begin
                if mode === :dominance
                    propagate!(ws; map=gmap, max_work=2048, max_exact_work=4096, max_deductions=MAX_N + 1)
                elseif mode === :elimination
                    eliminate_low_degree!(ws; map=gmap, max_degree=2, max_work=2048, max_exact_work=4096, max_deductions=MAX_N + 1)
                elseif mode === :relations
                    contract_relations!(ws; map=gmap, max_work=2048, max_exact_work=4096, max_deductions=MAX_N + 1)
                elseif mode === :mixed_cheap
                    schedule_reductions!(ws; map=gmap, enable_star_triangle=false, max_work=2048, max_exact_work=4096, max_deductions=MAX_N + 1)
                else
                    schedule_reductions!(ws; map=gmap, enable_star_triangle=true, max_work=2048, max_exact_work=4096, max_deductions=MAX_N + 1)
                end
            end
            report, disc = t.value, t.time
            report.stop_reason === :quiescent || error("unexpected pilot interruption: $(report.stop_reason)")
            candidates, edges, exact = report.candidates, report.edge_visits, report.exact_work
            if report isa ScheduleReport
                fallbacks = report.exact_fallbacks
                fill_edges = report.fill_edges
            end
            t = @timed begin
                certificate = export_certificate(ws; map=gmap)
                certificate === nothing || verify_certificate(ws, certificate; map=gmap).valid || error("invalid pilot proof")
            end
            proof = t.time
            t = @timed begin
                ctype = (isempty(ws._state.fixes) && gmap === nothing) ? Float64 : R
                result = materialize(ws; coefficient_type=ctype, map=gmap)
                childmodel = export_model(result)
            end
            material = t.time
            removed = QT.dimension(model) - QT.dimension(childmodel)
        end
        t = @timed child(childmodel)
        solved, solve = t.value, t.time
        t = @timed begin
            restored = mode !== :off ? reconstruct(result, solved.state).state : copy(solved.state)
            original = scalar(coefficients(model), restored)
            original == solved.energy || error("pilot energy identity failed")
        end
        lift = t.time
        (; solved, solve, lift)
    end
    total = Float64(time_ns() - start) / 1e9
    m_in = count(p -> !iszero(last(p)), QT.quadratic_terms(model))
    m_out = count(p -> !iszero(last(p)), QT.quadratic_terms(childmodel))
    return (;
        n_in=QT.dimension(model),
        m_in,
        n_out=QT.dimension(childmodel),
        m_out,
        removed,
        removed_edges=m_in - m_out,
        fill_edges,
        candidates,
        edges,
        exact,
        fallbacks,
        assignments=t_all.value.solved.assignments,
        energy=t_all.value.solved.energy,
        setup_ns=round(Int, setup * 1e9),
        disc_ns=round(Int, disc * 1e9),
        proof_ns=round(Int, proof * 1e9),
        material_ns=round(Int, material * 1e9),
        solve_ns=round(Int, t_all.value.solve * 1e9),
        lift_ns=round(Int, t_all.value.lift * 1e9),
        total_ns=round(Int, total * 1e9),
        bytes=t_all.bytes,
    )
end

function main()
    root = normpath(joinpath(@__DIR__, ".."))
    producing_sha = readchomp(Cmd(Cmd(["git", "rev-parse", "HEAD"]); dir=root))
    isempty(readchomp(Cmd(Cmd(["git", "status", "--porcelain", "--untracked-files=normal"]); dir=root))) ||
        error("pilot provenance requires a clean checkout")
    oversized = QT.Model{Int,Float64,Int}(Dict(i => 0.0 for i in 1:MAX_N+1), Dict{Tuple{Int,Int},Float64}(); domain=:spin)
    try
        child(oversized)
        error("oversize guard failed")
    catch e
        e isa ArgumentError || rethrow()
    end
    fixtures = cases()
    for (name, model) in fixtures, _ in 1:2, m in MODES
        runmode(name, model, m)
    end
    println("# producing_sha=", producing_sha)
    println("# Julia=", VERSION, " QUBOTools=", pkgversion(QT), " threads=", Threads.nthreads(),
            " cpu=", Sys.CPU_NAME, " kernel=", Sys.KERNEL, " arch=", Sys.ARCH,
            " repetitions=", REPS, " max_n=", MAX_N, " child=exact_spin_scalar_enumeration")
    cols = (
        :n_in, :m_in, :n_out, :m_out, :removed, :removed_edges, :fill_edges,
        :candidates, :edges, :exact, :fallbacks, :assignments,
        :setup_ns, :disc_ns, :proof_ns, :material_ns, :solve_ns, :lift_ns, :total_ns, :bytes,
    )
    println(join(("case", "rep", "mode", string.(cols)...), '\t'))
    for (name, model) in fixtures, rep in 1:REPS
        order = isodd(rep) ? MODES : reverse(MODES)
        results = Dict{Symbol,Any}()
        for m in order
            r = runmode(name, model, m)
            results[m] = r
            println(join((name, rep, m, (getproperty(r, k) for k in cols)...), '\t'))
        end
        ref_e = results[:off].energy
        for m in MODES
            results[m].energy == ref_e || error("pilot optimum mismatch on $name mode $m")
        end
    end
end
main()

