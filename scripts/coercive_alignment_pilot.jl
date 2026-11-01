# Cross-corpus coercive local-field alignment and coercive_field_witness benchmark.
# Reproduces the 611-instance OR/spin-glass alignment and witness quality table in
# docs/src/benchmarks.md from QUBOLib.jl (v0.2.4-data+8) using the production
# QUBOPreprocessing.Workspace + coercive_field_witness path.
#
# Usage (from an environment with QUBOLib, QUBOTools, SQLite, and HDF5):
#   julia --startup-file=no --threads=1 --project=/path/to/qubo-preprocessing-benchmarks scripts/coercive_alignment_pilot.jl
pushfirst!(LOAD_PATH, joinpath(@__DIR__, ".."))
using QUBOPreprocessing
import QUBOTools as QT
using QUBOLib
using SQLite
using HDF5
using Statistics
using Printf

const ACTIVE_FIELD_TOL = 1e-12

function read_qubin_tuple(h5::HDF5.File, instance_id::Int)
    fg = h5["instances/$(instance_id)/model/form"]
    n = Int(read(fg["dimension"]))
    sense = Symbol(read(fg["sense"]))
    domain = Symbol(read(fg["domain"]))
    α = Float64(read(fg["scale"]))
    β = Float64(read(fg["offset"]))
    li = read(fg["linear/i"])
    lv = read(fg["linear/v"])
    qi = read(fg["quadratic/i"])
    qj = read(fg["quadratic/j"])
    qv = read(fg["quadratic/v"])

    L = zeros(Float64, n)
    @inbounds for k in eachindex(li)
        L[Int(li[k])] += Float64(lv[k])
    end
    Q = Dict{Tuple{Int,Int},Float64}()
    @inbounds for k in eachindex(qi)
        u = Int(qi[k])
        v = Int(qj[k])
        w = Float64(qv[k])
        if u == v
            L[u] += w
        else
            a, b = u < v ? (u, v) : (v, u)
            Q[(a, b)] = get(Q, (a, b), 0.0) + w
        end
    end
    return (n = n, L = L, Q = Q, scale = α, offset = β, sense = sense, domain = domain)
end

function eval_bool_tuple(
    L::Vector{Float64},
    Q::Dict{Tuple{Int,Int},Float64},
    scale::Float64,
    offset::Float64,
    x::Vector{Int},
)
    acc = offset
    @inbounds for i in eachindex(L)
        x[i] != 0 && (acc += L[i])
    end
    for ((u, v), w) in Q
        (x[u] != 0 && x[v] != 0) && (acc += w)
    end
    return scale * acc
end

function build_spin_subproblem(raw)
    n = raw.n
    direction = if raw.scale == 0.0
        0
    elseif (raw.sense === :min) == (raw.scale > 0.0)
        1
    else
        -1
    end
    h_f = zeros(Float64, n)
    l1_f = zeros(Float64, n)
    adj_f = [Tuple{Int,Float64}[] for _ in 1:n]
    @inbounds for i in 1:n
        h_f[i] = 0.5 * raw.L[i]
    end
    n_pos_q = 0
    n_neg_q = 0
    for ((u, v), w) in raw.Q
        iszero(w) && continue
        w_min = direction * w
        if w_min > ACTIVE_FIELD_TOL
            n_pos_q += 1
        elseif w_min < -ACTIVE_FIELD_TOL
            n_neg_q += 1
        end
        j_ij = 0.25 * w
        h_f[u] += j_ij
        h_f[v] += j_ij
        push!(adj_f[u], (v, j_ij))
        push!(adj_f[v], (u, j_ij))
        l1_f[u] += abs(j_ij)
        l1_f[v] += abs(j_ij)
    end
    for i in 1:n
        sort!(adj_f[i]; by = first)
    end
    n_tot_q = max(1, n_pos_q + n_neg_q)
    return (
        h_f = h_f,
        adj_f = adj_f,
        l1_f = l1_f,
        direction = direction,
        frac_pos_off = n_pos_q / n_tot_q,
    )
end

function spin_field_alignment_counts(h_f::Vector{Float64}, l1_f::Vector{Float64}, direction::Int, x_bool::Vector{Int})
    aligned = 0
    active = 0
    @inbounds for i in eachindex(h_f)
        tol_i = max(ACTIVE_FIELD_TOL, 1e-12 * l1_f[i])
        abs(h_f[i]) <= tol_i && continue
        active += 1
        s_i = (x_bool[i] == 1) ? 1 : -1
        direction * s_i * h_f[i] < 0.0 && (aligned += 1)
    end
    return aligned, active
end

function build_identity_workspace(raw)
    model = QT.Model{Int,Float64,Int}(
        Dict(i => raw.L[i] for i in 1:raw.n),
        raw.Q;
        scale = raw.scale,
        offset = raw.offset,
        sense = raw.sense,
        domain = raw.domain,
    )
    return Workspace(model; rules = :identity, integerize_scale = false)
end

# Calls the production QUBOPreprocessing.Workspace + _coercive_field_witness_pair path.
function run_coercive_field_witness(raw; max_flips::Int = max(500, raw.n), tie_break::Symbol = :low)
    ws = build_identity_workspace(raw)
    x_par, x_cfw = QUBOPreprocessing._coercive_field_witness_pair(
        ws;
        max_flips = max_flips,
        tie_break = tie_break,
    )
    v_par = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_par)
    v_cfw = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_cfw)
    return x_par, v_par, x_cfw, v_cfw
end

function verify_production_equivalence!(h5::HDF5.File)
    # 1. Verify exact equivalence on the 2^-50 scaled 6-variable zero-field fixture:
    scale_tiny = 2.0^-50
    Q_zf = Dict(
        (1, 2) => -4.0 * scale_tiny, (1, 3) => -4.0 * scale_tiny, (2, 3) => -4.0 * scale_tiny,
        (4, 5) => -8.0 * scale_tiny, (4, 6) => -8.0 * scale_tiny, (5, 6) => -8.0 * scale_tiny,
        (3, 4) => 2.0 * scale_tiny,  (2, 5) => 2.0 * scale_tiny,
    )
    L_zf = zeros(Float64, 6)
    for ((u, v), w) in Q_zf
        L_zf[u] -= 0.5 * w
        L_zf[v] -= 0.5 * w
    end
    raw_zf = (n = 6, L = L_zf, Q = Q_zf, scale = 1.0, offset = 0.0, sense = :min, domain = :bool)
    x_par_zf, _, x_cfw_zf, _ = run_coercive_field_witness(raw_zf)
    ws_zf = build_identity_workspace(raw_zf)
    w_par_zf = coercive_field_witness(ws_zf; sequential = false, max_flips = max(500, 6), tie_break = :low)
    w_prod_zf = coercive_field_witness(ws_zf; sequential = true, max_flips = max(500, 6), tie_break = :low)
    (x_par_zf == w_par_zf && x_cfw_zf == w_prod_zf == [0, 0, 0, 1, 1, 1]) ||
        error("Pilot/production mismatch on 2^-50 fixture: $(x_cfw_zf) vs $(w_prod_zf)")

    # 2. Verify exact equivalence on the unscaled 6-variable fixture with L[1] -= 2^-40
    #    (non-zero exact field below 1e-12 * l1_f[1] plus near-tied sequential vs parallel energy):
    Q_nt = Dict(
        (1, 2) => -4.0, (1, 3) => -4.0, (2, 3) => -4.0,
        (4, 5) => -8.0, (4, 6) => -8.0, (5, 6) => -8.0,
        (3, 4) => 2.0,  (2, 5) => 2.0,
    )
    L_nt = zeros(Float64, 6)
    for ((u, v), w) in Q_nt
        L_nt[u] -= 0.5 * w
        L_nt[v] -= 0.5 * w
    end
    L_nt[1] -= 2.0^-40
    raw_nt = (n = 6, L = L_nt, Q = Q_nt, scale = 1.0, offset = 0.0, sense = :min, domain = :bool)
    x_par_nt, _, x_cfw_nt, _ = run_coercive_field_witness(raw_nt)
    ws_nt = build_identity_workspace(raw_nt)
    w_par_nt = coercive_field_witness(ws_nt; sequential = false, max_flips = max(500, 6), tie_break = :low)
    w_prod_nt = coercive_field_witness(ws_nt; sequential = true, max_flips = max(500, 6), tie_break = :low)
    (x_par_nt == w_par_nt && x_cfw_nt == w_prod_nt == [1, 1, 1, 0, 0, 0]) ||
        error("Pilot/production mismatch on L[1] -= 2^-40 fixture: $(x_cfw_nt) vs $(w_prod_nt)")

    # 3. Verify exact equivalence on archived instance 6233 (farm.qs.xz):
    raw_6233 = read_qubin_tuple(h5, 6233)
    x_par_6233, _, x_cfw_6233, _ = run_coercive_field_witness(raw_6233)
    ws_6233 = build_identity_workspace(raw_6233)
    w_par_6233 = coercive_field_witness(ws_6233; sequential = false, max_flips = max(500, raw_6233.n), tie_break = :low)
    w_prod_6233 = coercive_field_witness(ws_6233; sequential = true, max_flips = max(500, raw_6233.n), tie_break = :low)
    (x_par_6233 == w_par_6233 && x_cfw_6233 == w_prod_6233) ||
        error("Pilot/production mismatch on instance 6233: $(x_cfw_6233) vs $(w_prod_6233)")
    return nothing
end

function subfam(col, fam, act_cnt)
    col == "mqlib" && return ("1. MQLib (OR)", fam)
    col == "qoblib" && return ("4. QOBLIB", fam)
    if col == "qplib"
        return act_cnt > 0 ?
            ("2. QPLIB (h!=0)", "BiqMac OR Random (5875..5922)") :
            ("2. QPLIB (h=0)", "sporttournament (15) + Ising (3)")
    elseif col == "minlplib"
        return ("3. MINLPLib (h=0)", "sporttournament / chimera / autocorr")
    end
    return (col, fam)
end

function main()
    db = SQLite.DB(QUBOLib.database_path())
    q = """
    SELECT
        i.instance AS instance_id,
        i.collection AS collection,
        coalesce(i.problem_class, json_extract(i.metadata, '\$.problem_class'), json_extract(i.metadata, '\$.family'), i.collection) AS family,
        i.name AS name,
        coalesce(json_extract(i.metadata, '\$.original_name'), i.name) AS sname,
        i.dimension AS n_orig,
        b.qubo_value AS best_val,
        coalesce(b.proven_optimal, 0) AS proven_opt,
        b.bitstring AS bitstring
    FROM Instances i
    LEFT JOIN BestSolutions b ON b.instance = i.instance
    WHERE i.collection IN ('qplib', 'minlplib', 'qoblib')
       OR (i.collection = 'mqlib' AND coalesce(json_extract(i.metadata, '\$.family'), '') IN ('Beasley', 'GKA', 'Palubeckis'))
    ORDER BY i.collection, i.instance
    """
    rows = [
        (
            instance_id = Int(r.instance_id),
            collection  = String(r.collection),
            family      = String(r.family),
            name        = String(r.name),
            sname       = String(r.sname),
            n_orig      = Int(r.n_orig),
            proven_opt  = Int(r.proven_opt),
            bitstring   = ismissing(r.bitstring) ? nothing : String(r.bitstring),
        )
        for r in SQLite.DBInterface.execute(db, q)
    ]
    close(db)

    stats = Dict{Tuple{String,String},Any}()
    h5open(QUBOLib.archive_path(), "r") do h5
        verify_production_equivalence!(h5)
        for r in rows
            id = r.instance_id
            raw = read_qubin_tuple(h5, id)
            sp = build_spin_subproblem(raw)
            act_cnt = count(i -> abs(sp.h_f[i]) > max(ACTIVE_FIELD_TOL, 1e-12 * sp.l1_f[i]), 1:raw.n)
            key = subfam(r.collection, r.family, act_cnt)
            st = get!(stats, key) do
                (
                    n_inst = Ref(0),
                    n_prov = Ref(0),
                    n_nz_h = Ref(0),
                    n_sol = Ref(0),
                    opt_align = Float64[],
                    spin_al = Ref(0),
                    spin_act = Ref(0),
                    wit_align = Float64[],
                    gap_greedy = Float64[],
                    gap_cfw = Float64[],
                    ov_cfw = Float64[],
                    ov_z2 = Float64[],
                    pos_q = Float64[],
                )
            end
            st.n_inst[] += 1
            r.proven_opt != 0 && (st.n_prov[] += 1)
            push!(st.pos_q, 100.0 * sp.frac_pos_off)
            act_cnt > 0 && (st.n_nz_h[] += 1)

            x_gr, v_gr, x_cfw, v_cfw = run_coercive_field_witness(raw; max_flips = max(500, raw.n))

            al_w, act_w = spin_field_alignment_counts(sp.h_f, sp.l1_f, sp.direction, x_cfw)
            act_w > 0 && push!(st.wit_align, 100.0 * al_w / act_w)

            x_opt = if r.bitstring !== nothing && ncodeunits(r.bitstring) == raw.n
                [codeunit(r.bitstring, i) == UInt8('1') ? 1 : 0 for i in 1:raw.n]
            else
                nothing
            end

            if x_opt !== nothing
                v_opt = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_opt)
                st.n_sol[] += 1
                al_o, act_o = spin_field_alignment_counts(sp.h_f, sp.l1_f, sp.direction, x_opt)
                if act_o > 0
                    push!(st.opt_align, 100.0 * al_o / act_o)
                    st.spin_al[] += al_o
                    st.spin_act[] += act_o
                end
                ov = 100.0 * count(i -> x_opt[i] == x_cfw[i], 1:raw.n) / raw.n
                push!(st.ov_cfw, ov)
                push!(st.ov_z2, max(ov, 100.0 - ov))
                denom = abs(v_opt) > 1e-9 ? abs(v_opt) : max(1.0, abs(raw.scale * raw.offset))
                g_gr = 100.0 * max(0.0, (raw.sense == :min ? (v_gr - v_opt) : (v_opt - v_gr)) / denom)
                g_cfw = 100.0 * max(0.0, (raw.sense == :min ? (v_cfw - v_opt) : (v_opt - v_cfw)) / denom)
                push!(st.gap_greedy, g_gr)
                push!(st.gap_cfw, g_cfw)
            end
        end
    end

    @printf(
        "%-17s | %-34s | %4s | %4s | %4s | %4s | %-15s | %-8s | %-10s | %-10s | %-10s | %-8s | %-8s | %-7s\n",
        "Collection", "Sub-Family", "Inst", "Ref", "Prov", "h!=0", "Ref Align±SD", "SpinWtd",
        "CFW Align", "Gr1F Gap", "CFW Gap", "CFW Ovlp", "Z2 Ovlp", "Q>0(%)",
    )
    println(repeat("-", 182))
    for k in sort(collect(keys(stats)))
        s = stats[k]
        ra = isempty(s.opt_align) ? "h=0 (symm)" : @sprintf("%.2f±%.2f%%", mean(s.opt_align), length(s.opt_align) > 1 ? std(s.opt_align) : 0.0)
        sw = s.spin_act[] == 0 ? "h=0" : @sprintf("%.2f%%", 100.0 * s.spin_al[] / s.spin_act[])
        wa = isempty(s.wit_align) ? "h=0 (symm)" : @sprintf("%.2f%%", mean(s.wit_align))
        gg = isempty(s.gap_greedy) ? "n/a" : @sprintf("%.2f%%", median(s.gap_greedy))
        gc = isempty(s.gap_cfw) ? "n/a" : @sprintf("%.2f%%", median(s.gap_cfw))
        ov = isempty(s.ov_cfw) ? "n/a" : @sprintf("%.2f%%", mean(s.ov_cfw))
        oz = isempty(s.ov_z2) ? "n/a" : @sprintf("%.2f%%", mean(s.ov_z2))
        pq = @sprintf("%.1f%%", mean(s.pos_q))
        @printf(
            "%-17s | %-34s | %4d | %4d | %4d | %4d | %-15s | %-8s | %-10s | %-10s | %-10s | %-8s | %-8s | %-7s\n",
            k[1], k[2], s.n_inst[], s.n_sol[], s.n_prov[], s.n_nz_h[], ra, sw, wa, gg, gc, ov, oz, pq,
        )
    end
end

main()
