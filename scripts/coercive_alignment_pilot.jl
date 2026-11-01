# Cross-corpus coercive local-field alignment and coercive_field_witness benchmark.
# Reproduces the 611-instance OR/spin-glass alignment and witness quality table in
# docs/src/benchmarks.md from QUBOLib.jl (v0.2.4-data+8).
#
# Usage (from an environment with QUBOPreprocessing, QUBOLib, SQLite, HDF5, and MQLib):
#   julia --startup-file=no --threads=1 scripts/coercive_alignment_pilot.jl
using QUBOLib
using MQLib
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

function compute_ising_fields_and_bond_signs(raw)
    # Normalize to equivalent minimization spin Hamiltonian H(s) = const + sum_i h_i s_i + sum_{i<j} J_{ij} s_i s_j
    sign_mult = (raw.sense == :max) ? -1.0 : 1.0
    h = zeros(Float64, raw.n)
    @inbounds for i in 1:raw.n
        h[i] = 0.5 * sign_mult * raw.L[i]
    end
    n_pos_q = 0
    n_neg_q = 0
    for ((u, v), w) in raw.Q
        w_min = sign_mult * w
        if w_min > ACTIVE_FIELD_TOL
            n_pos_q += 1
        elseif w_min < -ACTIVE_FIELD_TOL
            n_neg_q += 1
        end
        h[u] += 0.25 * w_min
        h[v] += 0.25 * w_min
    end
    n_tot_q = max(1, n_pos_q + n_neg_q)
    return (h = h, frac_pos_off = n_pos_q / n_tot_q)
end

function spin_field_alignment_counts(h::Vector{Float64}, x_bool::Vector{Int})
    aligned = 0
    active = 0
    @inbounds for i in eachindex(h)
        abs(h[i]) <= ACTIVE_FIELD_TOL && continue
        active += 1
        s_i = (x_bool[i] == 1) ? 1 : -1
        s_i * h[i] < 0.0 && (aligned += 1)
    end
    return aligned, active
end

# Float64 implementation matching QUBOPreprocessing.coercive_field_witness
# (with tie_break = :low, max_flips = max(500, n), l1_J tie-breaking, and
# zero-field anchor symmetry breaking s_u = +1 on the first h_u == 0 variable).
function run_coercive_field_witness(raw, h::Vector{Float64}; max_flips::Int = max(500, raw.n))
    n = raw.n
    sign_mult = (raw.sense == :max) ? -1.0 : 1.0
    adj = [Tuple{Int,Float64}[] for _ in 1:n]
    l1_J = zeros(Float64, n)
    for ((u, v), w) in raw.Q
        w_min = sign_mult * w
        push!(adj[u], (v, w_min))
        push!(adj[v], (u, w_min))
        j_abs = 0.25 * abs(w_min)
        l1_J[u] += j_abs
        l1_J[v] += j_abs
    end

    function polish_1flip!(x::Vector{Int})
        grad = Vector{Float64}(undef, n)
        @inbounds for i in 1:n
            g = sign_mult * raw.L[i]
            for (j, w_min) in adj[i]
                x[j] == 1 && (g += w_min)
            end
            grad[i] = g
        end
        for _ in 1:max_flips
            best_i = 0
            best_delta = -1e-12
            @inbounds for i in 1:n
                delta = (x[i] == 0) ? grad[i] : -grad[i]
                if delta < best_delta
                    best_delta = delta
                    best_i = i
                end
            end
            best_i == 0 && break
            new_x = 1 - x[best_i]
            x[best_i] = new_x
            step_dir = (new_x == 1) ? 1.0 : -1.0
            @inbounds for (j, w_min) in adj[best_i]
                grad[j] += step_dir * w_min
            end
        end
        return x
    end

    # Candidate 1 (Gr1F): Parallel field alignment + 1-flip polish
    x_par = [(h[i] < 0.0) ? 1 : 0 for i in 1:n]
    polish_1flip!(x_par)

    # Candidate 2 (CFW): Sequential coercive-ordered conditioned field alignment + 1-flip polish
    order = sortperm(
        1:n;
        by = i -> (
            l1_J[i] == 0.0 ? (abs(h[i]) == 0.0 ? 0 : 2) : 1,
            l1_J[i] == 0.0 ? abs(h[i]) : abs(h[i]) / l1_J[i],
            abs(h[i]),
            l1_J[i],
            -i,
        ),
        rev = true,
    )
    h_cond = copy(h)
    fixed = falses(n)
    x_seq = zeros(Int, n)
    broke_zero_symmetry = false
    @inbounds for u in order
        s_u = if h_cond[u] < -ACTIVE_FIELD_TOL
            1
        elseif h_cond[u] > ACTIVE_FIELD_TOL
            -1
        elseif !broke_zero_symmetry
            broke_zero_symmetry = true
            1
        else
            -1
        end
        x_seq[u] = (s_u == 1) ? 1 : 0
        fixed[u] = true
        for (v, w_min) in adj[u]
            !fixed[v] && (h_cond[v] += 0.25 * w_min * s_u)
        end
    end
    polish_1flip!(x_seq)

    v_par = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_par)
    v_seq = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_seq)
    better_seq = (raw.sense == :max) ? (v_seq > v_par) : (v_seq < v_par)
    return x_par, v_par, (better_seq ? x_seq : x_par), (better_seq ? v_seq : v_par)
end

function solve_mqlib_quick(raw, time_limit::Float64 = 0.2)
    sign_mult = (raw.sense == :max) ? 1.0 : -1.0
    linear = Cdouble.(sign_mult .* raw.L)
    m = length(raw.Q)
    qi = Vector{Int32}(undef, m)
    qj = Vector{Int32}(undef, m)
    qv = Vector{Cdouble}(undef, m)
    idx = 0
    for ((u, v), w) in raw.Q
        idx += 1
        qi[idx] = Int32(u)
        qj[idx] = Int32(v)
        qv[idx] = Cdouble(0.5 * sign_mult * w)
    end
    res = MQLib._mqlib_solve_qubo(
        raw.n, linear, qi, qj, qv;
        heuristic = "BURER2002", random_seed = Int32(1001), run_time_limit = time_limit,
    )
    return Int.(res.solution)
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
        for r in rows
            id = r.instance_id
            raw = read_qubin_tuple(h5, id)
            info = compute_ising_fields_and_bond_signs(raw)
            act_cnt = count(x -> abs(x) > ACTIVE_FIELD_TOL, info.h)
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
            push!(st.pos_q, 100.0 * info.frac_pos_off)
            act_cnt > 0 && (st.n_nz_h[] += 1)

            x_gr, v_gr, x_cfw, v_cfw = run_coercive_field_witness(raw, info.h; max_flips = max(500, raw.n))

            al_w, act_w = spin_field_alignment_counts(info.h, x_cfw)
            act_w > 0 && push!(st.wit_align, 100.0 * al_w / act_w)

            x_opt = if r.bitstring !== nothing && ncodeunits(r.bitstring) == raw.n
                [codeunit(r.bitstring, i) == UInt8('1') ? 1 : 0 for i in 1:raw.n]
            elseif r.collection == "minlplib"
                solve_mqlib_quick(raw, 0.2)
            else
                nothing
            end

            if x_opt !== nothing
                v_opt = eval_bool_tuple(raw.L, raw.Q, raw.scale, raw.offset, x_opt)
                st.n_sol[] += 1
                al_o, act_o = spin_field_alignment_counts(info.h, x_opt)
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
        "%-14s | %-34s | %4s | %4s | %4s | %-15s | %-8s | %-10s | %-10s | %-10s | %-8s | %-8s | %-7s\n",
        "Collection", "Sub-Family", "Inst", "Prov", "h!=0", "Ref Align±SD", "SpinWtd",
        "CFW Align", "Gr1F Gap", "CFW Gap", "CFW Ovlp", "Z2 Ovlp", "Q>0(%)",
    )
    println(repeat("-", 172))
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
            "%-14s | %-34s | %4d | %4d | %4d | %-15s | %-8s | %-10s | %-10s | %-10s | %-8s | %-8s | %-7s\n",
            k[1], k[2], s.n_inst[], s.n_prov[], s.n_nz_h[], ra, sw, wa, gg, gc, ov, oz, pq,
        )
    end
end

main()

