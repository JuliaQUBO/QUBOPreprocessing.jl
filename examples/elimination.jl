using QUBOPreprocessing
import QUBOTools as QT

# Example: Degree-0/1/2 exact local elimination on a cycle and a whisker-core
# family, plus a no-benefit high-degree control.

# 1. 6-vertex Ising cycle with nonzero local fields where strict dominance makes 0 deductions:
L_cycle = [0.25, -0.75, 1.25, -0.5, 0.5, -1.0]
Q_cycle = Dict(
    (1, 2) => -1.5, (2, 3) => 2.0, (3, 4) => -1.0,
    (4, 5) => 1.5,  (5, 6) => -2.0, (1, 6) => 1.25,
)
m_cycle = QT.Model{Int,Float64,Int}(Dict(i => L_cycle[i] for i in 1:6), Q_cycle; domain=:spin, sense=:min)

ws_dom = Workspace(m_cycle; rules=:dominance)
@assert propagate!(ws_dom).deductions == 0

ws_elim, rep_elim = preprocess(m_cycle; rules=:elimination)
@assert rep_elim.stop_reason === :quiescent
@assert rep_elim.deductions == 6
@assert verify_certificate(ws_elim, export_certificate(ws_elim)).valid
res_cycle = materialize(ws_elim; coefficient_type=Rational{BigInt})
@assert QT.dimension(export_model(res_cycle)) == 0
rec_cycle = reconstruct(res_cycle, Int[])
@assert rec_cycle.energy.finite

# 2. Dense 4-regular control (K_5): no degree <= 3 vertices exist, so
# eliminate_low_degree! examines 0 candidates in O(1) without scanning the graph.
Q_k5 = Dict((i, j) => 1.0 for i in 1:5 for j in (i+1):5)
m_k5 = QT.Model{Int,Float64,Int}(Dict(i => 0.0 for i in 1:5), Q_k5; domain=:spin, sense=:min)
ws_k5, rep_k5 = preprocess(m_k5; rules=:elimination)
@assert rep_k5.candidates == 0
@assert rep_k5.edge_visits == 0
@assert rep_k5.deductions == 0

# 3. Warmed, repeated paired end-to-end comparison (including construction,
# elimination, certificate verification, materialization, child solve, and lifting):
const R = Rational{BigInt}

function exact_coeffs(model)
    n = QT.dimension(model)
    l = [i => R(v) for (i, v) in QT.linear_terms(model)]
    q = [(i, j) => R(v) for ((i, j), v) in QT.quadratic_terms(model)]
    return (; n, l, q, scale=R(QT.scale(model)), offset=R(QT.offset(model)))
end

function eval_exact(c, s)
    v = c.offset
    for (i, a) in c.l; v += a * s[i]; end
    for ((i, j), b) in c.q; v += b * s[i] * s[j]; end
    return c.scale * v
end

function exhaustive_spin_min(model)
    c = exact_coeffs(model)
    best_e = nothing
    best_s = zeros(Int, c.n)
    s = fill(-1, c.n)
    for mask in 0:((1 << c.n) - 1)
        for i in 1:c.n
            s[i] = ((mask >> (i - 1)) & 1) == 1 ? 1 : -1
        end
        e = eval_exact(c, s)
        if best_e === nothing || e < best_e
            best_e = e
            copyto!(best_s, s)
        end
    end
    return best_e, best_s, (1 << c.n)
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

function run_paired_mode(model, on::Bool)
    t = @timed begin
        if on
            ws, rep = preprocess(model; rules=:elimination)
            @assert rep.stop_reason === :quiescent
            cert = export_certificate(ws)
            @assert cert === nothing || verify_certificate(ws, cert).valid
            res = materialize(ws)
            child_model = export_model(res)
            e_red, s_red, states_red = exhaustive_spin_min(child_model)
            rec = reconstruct(res, s_red)
            e_orig = eval_exact(exact_coeffs(model), rec.state)
            @assert e_orig == e_red
            (; energy=e_red, states=states_red, n_res=QT.dimension(child_model), eliminated=rep.deductions)
        else
            e_raw, s_raw, states_raw = exhaustive_spin_min(model)
            e_orig = eval_exact(exact_coeffs(model), copy(s_raw))
            @assert e_orig == e_raw
            (; energy=e_raw, states=states_raw, n_res=QT.dimension(model), eliminated=0)
        end
    end
    return (; val=t.value, us=t.time * 1e6, bytes=t.bytes)
end

med(v) = sort(collect(v))[(length(v) + 1) ÷ 2]

for (label, n_core, n_whisker) in ((:tiny_no_payoff, 4, 1), (:break_even, 4, 3), (:sparse_payoff, 4, 6))
    m = build_whisker_core(n_core, n_whisker)
    for _ in 1:2, on in (false, true)
        run_paired_mode(m, on)
    end
    off_us, on_us, diff_us = Float64[], Float64[], Float64[]
    off_b, on_b = Int[], Int[]
    r_off = r_on = nothing
    for rep in 1:5
        r_off = run_paired_mode(m, false)
        r_on  = run_paired_mode(m, true)
        @assert r_off.val.energy == r_on.val.energy
        push!(off_us, r_off.us)
        push!(on_us, r_on.us)
        push!(diff_us, r_on.us - r_off.us)
        push!(off_b, r_off.bytes)
        push!(on_b, r_on.bytes)
    end
    println((
        regime=label,
        n_orig=n_core + n_whisker,
        n_residual=r_on.val.n_res,
        eliminated=r_on.val.eliminated,
        raw_states=r_off.val.states,
        residual_states=r_on.val.states,
        median_off_us=round(med(off_us); digits=1),
        median_on_us=round(med(on_us); digits=1),
        median_paired_diff_us=round(med(diff_us); digits=1),
        median_off_bytes=med(off_b),
        median_on_bytes=med(on_b),
    ))
end

println((
    cycle_eliminated=rep_elim.deductions,
    cycle_energy=rec_cycle.energy.value,
    cycle_state=rec_cycle.state,
    dense_k5_candidates=rep_k5.candidates,
    dense_k5_edge_visits=rep_k5.edge_visits,
))
