using QUBOPreprocessing
import QUBOTools as QT

# Example: Degree-0/1/2 exact local elimination on a cycle and an alternating
# dominance/elimination cascade, plus a no-benefit high-degree control.

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

# 3. Paired exhaustive solve cost comparison (sparse benefit vs tiny/dense overhead and break-even):
function exhaustive_spin_min(model)
    n = QT.dimension(model)
    f = QT.form(model)
    best_e = Inf
    best_s = zeros(Int, n)
    s = fill(-1, n)
    for mask in 0:((1 << n) - 1)
        for i in 1:n
            s[i] = ((mask >> (i - 1)) & 1) == 1 ? 1 : -1
        end
        e = QT.value(s, f)
        if e < best_e
            best_e = e
            copyto!(best_s, s)
        end
    end
    return best_e, best_s, (1 << n)
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

for (label, n_core, n_whisker) in ((:tiny_no_payoff, 4, 2), (:break_even, 4, 6), (:sparse_payoff, 4, 10))
    m = build_whisker_core(n_core, n_whisker)
    e_raw, _, states_raw = exhaustive_spin_min(m)
    ws, rep = preprocess(m; rules=:elimination)
    res = materialize(ws)
    e_red, s_red, states_red = exhaustive_spin_min(export_model(res))
    rec = reconstruct(res, s_red)
    @assert isapprox(rec.energy.value, e_raw; atol=1e-12)
    @assert isapprox(e_red, e_raw; atol=1e-12)
    println((
        regime=label,
        n_orig=n_core + n_whisker,
        n_residual=QT.dimension(export_model(res)),
        eliminated=rep.deductions,
        raw_states=states_raw,
        residual_states=states_red,
    ))
end

println((
    cycle_eliminated=rep_elim.deductions,
    cycle_energy=rec_cycle.energy.value,
    cycle_state=rec_cycle.state,
    dense_k5_candidates=rep_k5.candidates,
    dense_k5_edge_visits=rep_k5.edge_visits,
))

