# Bounded CPU pilot for degree-0/1/2 local elimination (issue #15), not an
# ecosystem adoption envelope (owned by QUBOBenchmarks #30).
# Run from a clean producing commit, with one Julia/OpenBLAS thread:
# OPENBLAS_NUM_THREADS=1 julia --startup-file=no --threads=1 --project=. scripts/elimination_pilot.jl > /tmp/elimination-pilot.tsv && cp /tmp/elimination-pilot.tsv docs/evidence/elimination-pilot.tsv
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

function build_whisker_core(n_core::Int, n_whisker::Int)
    n = n_core + n_whisker
    L = Dict(i => (isodd(i) ? 0.5 : -0.75) for i in 1:n)
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:n_core, j in (i+1):n_core
        Q[(i, j)] = (i + j) % 2 == 0 ? 1.0 : -1.25
    end
    for k in 1:n_whisker
        u = n_core + k
        v = k == 1 ? 1 : (n_core + k - 1)
        Q[(min(u, v), max(u, v))] = isodd(k) ? -1.5 : 2.0
    end
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function build_cycle(n::Int)
    L = Dict(i => (isodd(i) ? 0.25 : -0.75) for i in 1:n)
    Q = Dict{Tuple{Int,Int},Float64}()
    for i in 1:n
        j = i == n ? 1 : i + 1
        Q[(min(i, j), max(i, j))] = isodd(i) ? -1.5 : 2.0
    end
    return QT.Model{Int,Float64,Int}(L, Q; domain=:spin, sense=:min)
end

function cases()
    return [
        "dense_k5" => QT.Model{Int,Float64,Int}(
            Dict(i => 0.25 * i for i in 1:5),
            Dict((i, j) => 1.0 for i in 1:5 for j in (i+1):5);
            domain=:spin, sense=:min,
        ),
        "whisker_5" => build_whisker_core(4, 1),
        "whisker_7" => build_whisker_core(4, 3),
        "whisker_10" => build_whisker_core(4, 6),
        "cycle_8" => build_cycle(8),
    ]
end

function runmode(model, on)
    start = time_ns()
    setup = elim = proof = material = 0.0
    candidates = edges = exact = removed = 0
    childmodel = model
    result = nothing
    t_all = @timed begin
        if on
            t = @timed Workspace(model; rules=:elimination)
            ws, setup = t.value, t.time
            t = @timed eliminate_low_degree!(ws; max_work=512, max_exact_work=2048, max_deductions=MAX_N)
            report, elim = t.value, t.time
            report.stop_reason === :quiescent || error("unexpected bounded pilot interruption")
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
            restored = on ? reconstruct(result, solved.state).state : copy(solved.state)
            original = scalar(coefficients(model), restored)
            original == solved.energy || error("pilot energy identity failed")
        end
        lift = t.time
        (; solved, solve, lift)
    end
    total = Float64(time_ns() - start) / 1e9
    original_edges = count(p -> !iszero(last(p)), QT.quadratic_terms(model))
    residual_edges = count(p -> !iszero(last(p)), QT.quadratic_terms(childmodel))
    return (; total, bytes=t_all.bytes, setup, elim, proof, material,
            solve=t_all.value.solve, lift=t_all.value.lift, removed,
            removed_edges=original_edges - residual_edges, n=QT.dimension(childmodel),
            assignments=t_all.value.solved.assignments, energy=t_all.value.solved.energy,
            candidates, edges, exact)
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
    for (_, model) in fixtures, _ in 1:2, on in (false, true); runmode(model, on); end
    println("# producing_sha=", producing_sha)
    println("# Julia=", VERSION, " QUBOTools=", pkgversion(QT), " threads=", Threads.nthreads(),
            " cpu=", Sys.CPU_NAME, " kernel=", Sys.KERNEL, " arch=", Sys.ARCH,
            " repetitions=", REPS, " max_n=", MAX_N, " child=exact_spin_scalar_enumeration")
    names = (:total, :bytes, :setup, :elim, :proof, :material, :solve, :lift,
             :removed, :removed_edges, :n, :assignments, :energy, :candidates, :edges, :exact)
    println(join(("case", "rep", "mode", string.(names)...), '\t'))
    for (name, model) in fixtures, rep in 1:REPS
        results = Dict{Bool,Any}()
        for on in (isodd(rep) ? (false, true) : (true, false))
            r = runmode(model, on)
            results[on] = r
            println(join((name, rep, on ? "on" : "off", (getproperty(r, k) for k in names)...), '\t'))
        end
        results[false].energy == results[true].energy || error("pilot optimum mismatch")
    end
end
main()

