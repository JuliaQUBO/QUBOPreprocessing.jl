# Bounded CPU pilot for guarded zero-field degree-3 Ising star-triangle reduction
# (issue #17), not an ecosystem adoption envelope (owned by QUBOBenchmarks #30).
# Run from a clean producing commit, with one Julia/OpenBLAS thread:
# OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/star_triangle_pilot.jl > /tmp/star-triangle-pilot.tsv && cp /tmp/star-triangle-pilot.tsv docs/evidence/star-triangle-pilot.tsv
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

function build_k4_zero_field()
    L = Dict(1 => 0.0, 2 => 0.25, 3 => -0.5, 4 => 0.75)
    Q = Dict((1, 2) => 1.0, (1, 3) => -1.5, (1, 4) => 2.0, (2, 3) => 0.5, (2, 4) => -0.75, (3, 4) => 1.25)
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_wheel_w6()
    # 6-vertex graph: hub 6 connected to 1..4, plus cycle/chord edges so vertices 1, 2 have degree 3 and zero field:
    L = Dict(1 => 0.0, 2 => 0.0, 3 => 0.5, 4 => -0.75, 5 => 0.25, 6 => -0.5)
    Q = Dict(
        (1, 2) => -1.0, (1, 3) => 1.5, (1, 6) => -1.25,
        (2, 4) => 1.0,  (2, 6) => 1.5,
        (3, 4) => -0.75, (3, 5) => 1.25, (3, 6) => -1.0,
        (4, 5) => -1.5, (4, 6) => 0.5,
        (5, 6) => 1.0,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_subdivided_10()
    # 4-clique core (1..4) with two zero-field degree-3 star gadgets (5, 6, 7, 8) and two degree-2 bridges (9, 10):
    L = Dict(
        1 => 0.5, 2 => -0.75, 3 => 0.25, 4 => -0.5,
        5 => 0.0, 6 => 0.0, 7 => 0.0, 8 => 0.0,
        9 => 0.25, 10 => -0.5,
    )
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:4, j in (i+1):4
        Q[(i, j)] = (i + j) % 2 == 0 ? 1.0 : -1.25
    end
    # Zero-field degree-3 stars on 5..8 attached to core 1..3:
    Q[(1, 5)] = 1.0; Q[(2, 5)] = -1.5; Q[(5, 6)] = 2.0
    Q[(2, 6)] = 1.25; Q[(3, 6)] = -1.0
    Q[(1, 7)] = -1.0; Q[(3, 7)] = 1.5; Q[(7, 8)] = -2.0
    Q[(2, 8)] = -1.25; Q[(4, 8)] = 1.0
    # Two degree-2 bridges 9, 10:
    Q[(1, 9)] = 1.5; Q[(2, 9)] = -1.0
    Q[(3, 10)] = -1.5; Q[(4, 10)] = 1.0
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_conditioned_field(cancel::Bool)
    # 8-vertex graph: core K_4 (1..4), vertex 5 has degree 4 (neighbors 1, 2, 3 and dominant leaf 8),
    # vertices 6, 7 are degree-3 zero-field hubs connected to 5, 1, 2.
    # Leaf 8 has strong field L[8] = -5.0 and coupling Q[(5, 8)] = 1.0, so dominance fixes s_8 = +1,
    # inducing field shift +1.0 on vertex 5!
    # When cancel=false, L[5] = 0.0 -> conditioned field becomes +1.0 != 0 (invalidates degree-3 on 5).
    # When cancel=true,  L[5] = -1.0 -> conditioned field becomes 0.0 (unlocks degree-3 on 5 and cascades 6, 7)!
    L = Dict(
        1 => 0.5, 2 => -0.75, 3 => 0.25, 4 => -0.5,
        5 => (cancel ? -1.0 : 0.0),
        6 => 0.0, 7 => 0.0,
        8 => -5.0,
    )
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:4, j in (i+1):4
        Q[(i, j)] = (i + j) % 2 == 0 ? 1.0 : -1.25
    end
    Q[(1, 5)] = 1.5; Q[(5, 6)] = -1.0; Q[(5, 7)] = 2.0; Q[(5, 8)] = 1.0
    Q[(1, 6)] = -1.25; Q[(2, 6)] = 1.5; Q[(6, 7)] = -1.0
    Q[(2, 7)] = 1.25; Q[(3, 7)] = -1.5
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_no_benefit_cubic_8()
    # 8-vertex 3-regular cube graph where every vertex has degree 3 and nonzero field:
    L = Dict(i => (isodd(i) ? 0.5 : -0.75) for i in 1:8)
    Q = Dict(
        (1, 2) => 1.0, (2, 3) => -1.25, (3, 4) => 1.5, (1, 4) => -1.0,
        (5, 6) => -1.0, (6, 7) => 1.25, (7, 8) => -1.5, (5, 8) => 1.0,
        (1, 5) => 0.75, (2, 6) => -0.75, (3, 7) => 1.25, (4, 8) => -1.25,
    )
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function cases()
    return [
        ("zero_field_k4", build_k4_zero_field(), false),
        ("zero_field_wheel_w6", build_wheel_w6(), false),
        ("zero_field_subdivided_10", build_subdivided_10(), false),
        ("conditioned_invalidated_8", build_conditioned_field(false), true),
        ("conditioned_unlocked_8", build_conditioned_field(true), true),
        ("no_benefit_cubic_8", build_no_benefit_cubic_8(), false),
    ]
end

function runmode(model, mode::Symbol, cascade::Bool)
    start = time_ns()
    setup = elim = proof = material = 0.0
    candidates = edges = exact = removed = 0
    childmodel = model
    result = nothing
    t_all = @timed begin
        if mode !== :off
            md = mode === :deg3 ? 3 : 2
            t = @timed Workspace(model; rules=:elimination)
            ws, setup = t.value, t.time
            t = @timed eliminate_low_degree!(
                ws; max_degree=md, cascade_dominance=cascade,
                max_work=512, max_exact_work=2048, max_deductions=MAX_N,
            )
            report, elim = t.value, t.time
            report.stop_reason === :quiescent || error("unexpected bounded pilot interruption: $(report.stop_reason)")
            candidates, edges, exact = report.candidates, report.edge_visits, report.exact_work
            t = @timed begin
                certificate = export_certificate(ws)
                certificate === nothing || verify_certificate(ws, certificate).valid || error("invalid pilot proof")
            end
            proof = t.time
            t = @timed begin
                result = materialize(ws)
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
    return (;
        n_in=QT.dimension(model),
        m_in=length(QT.quadratic_terms(model)),
        n_out=QT.dimension(childmodel),
        m_out=length(QT.quadratic_terms(childmodel)),
        removed,
        candidates,
        edges,
        exact,
        assignments=t_all.value.solved.assignments,
        energy=t_all.value.solved.energy,
        setup_ns=round(Int, setup * 1e9),
        elim_ns=round(Int, elim * 1e9),
        proof_ns=round(Int, proof * 1e9),
        material_ns=round(Int, material * 1e9),
        solve_ns=round(Int, t_all.value.solve * 1e9),
        lift_ns=round(Int, t_all.value.lift * 1e9),
        total_ns=round(Int, total * 1e9),
        bytes=t_all.bytes,
    )
end

println(join([
    "case", "rep", "mode", "n_in", "m_in", "n_out", "m_out", "removed",
    "candidates", "edges", "exact", "assignments",
    "setup_ns", "elim_ns", "proof_ns", "material_ns", "solve_ns", "lift_ns", "total_ns", "bytes",
], '\t'))

for (name, model, cascade) in cases()
    for _ in 1:2, mode in (:off, :deg2, :deg3)
        runmode(model, mode, cascade)
    end
    for rep in 1:REPS
        modes = isodd(rep) ? (:off, :deg2, :deg3) : (:deg3, :deg2, :off)
        results = Dict(m => runmode(model, m, cascade) for m in modes)
        results[:off].energy == results[:deg2].energy == results[:deg3].energy || error("energy mismatch on $name")
        for mode in (:off, :deg2, :deg3)
            r = results[mode]
            println(join([
                name, rep, mode, r.n_in, r.m_in, r.n_out, r.m_out, r.removed,
                r.candidates, r.edges, r.exact, r.assignments,
                r.setup_ns, r.elim_ns, r.proof_ns, r.material_ns, r.solve_ns, r.lift_ns, r.total_ns, r.bytes,
            ], '\t'))
        end
    end
end

