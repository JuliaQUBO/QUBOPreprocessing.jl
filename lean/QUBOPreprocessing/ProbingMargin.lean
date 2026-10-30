import Mathlib
import QUBOPreprocessing.GaugeCoercive
import QUBOPreprocessing.CompositionRepair
import QUBOPreprocessing.CoflipCancellation

/-!
# Theorem 7: Sequential Trial-Dominance Probing Margin, Double Probing, and 2-SAT Pair Probing

This module formalizes Theorem 7 of `QUBOPreprocessing.jl` (`_dominance_step_spin_margin`,
`_branch_steps_spin_margin`, `_double_probe_witness_for_var`, `_probing_relation_witness`,
`_verify_probing_step`, and `_verify_relation_step` in
`src/certificates.jl:1658-1703, 1834-1871, 2288-2400, 4794-4837, 5352-5387`):
1. **Single-Step Spin Margin & Boolean-to-Spin Normalization (`_dominance_step_spin_margin`)**:
   Defines `domSpinMargin lo hi = max lo (-hi)` and
   `boolToSpinMargin lo_bool hi_bool = domSpinMargin (lo_bool / 2) (hi_bool / 2)` and proves that
   when a spin variable $z \in \{-1, +1\}$ has effective local field $L \in [\text{lo}, \text{hi}]$
   certified to fix $z^* = -1$ ($\text{lo} > 0$) or $z^* = +1$ ($\text{hi} < 0$), flipping the
   violating assignment $z = -z^*$ to $z^*$ changes the energy by
   $\Delta E \le -2\,\mathrm{domSpinMargin}(\text{lo}, \text{hi}) < 0$.
2. **Sequential Branch Cascade & First-Divergence / Telescoping Repair (`_branch_steps_spin_margin`)**:
   Formalizes a sequential trial-dominance branch `ValidCascade` under initial assumption $P_0(s)$,
   defines `branchSpinMargin m₁ ms = ms.foldl min m₁`, and proves both the **First-Divergence
   Repair Theorem** (any state satisfying $P_0$ and violating the cascade admits a single-step
   repair at the first diverging step $r^*$ lowering energy by at least
   $2 m_{r^*} \ge 2 M_{\mathrm{branch}}$) and the **Full-Cascade Telescoping Repair Theorem**
   (sequentially repairing all diverging steps produces a feasible state satisfying
   $P_0 \land P_1 \land \dots \land P_k$ with cumulative energy drop at least
   $2 \sum_{r \in \text{repaired}} m_r \ge 2 M_{\mathrm{branch}}$).
3. **Witness-Free Double Probing (`:double_probe`)**:
   Proves that if both branches $s_p = -1$ and $s_p = +1$ of a probed spin $s_p \in \{-1, +1\}$
   refute $s_u \neq u^*$ with branch spin margins $M_{\mathrm{low}}, M_{\mathrm{high}} > 0$, then
   every feasible configuration violating $s_u = u^*$ admits a feasible repair lowering energy by at
   least $2 \min(M_{\mathrm{low}}, M_{\mathrm{high}}) > 0$, and instantiates `ReductionStep` and
   `StrongReductionStep` from `QUBOPreprocessing.CompositionRepair`.
4. **Two-Branch 2-SAT Pair Equivalence Probing (`:probing_pair`)**:
   Proves the exact spin violation partition
   $s_u \neq \sigma s_v \iff (s_u = -1 \land s_v = \sigma) \lor (s_u = 1 \land s_v = -\sigma)$,
   formalizes all four witness branch patterns verified by `ok_pat_1` and `ok_pat_2` in
   `_verify_relation_step`, proves that $\mathrm{lo}_p = \min(M_1, M_2) > 0$ certifies a strict
   energy repair on every violating configuration, and instantiates `ReductionStep` and
   `StrongReductionStep` for `:probing_pair` pair contraction.
-/

namespace QUBOPreprocessing

/-!
### Part 1: Single-Step Spin Margin & Boolean-to-Spin Normalization
-/

/-- Spin-domain dominance margin (`_dominance_step_spin_margin` in `src/certificates.jl:1658-1667`):
$\mathrm{domSpinMargin}(\text{lo}, \text{hi}) = \max(\text{lo}, -\text{hi})$. -/
noncomputable def domSpinMargin (lo hi : ℝ) : ℝ :=
  max lo (-hi)

/-- Boolean-to-spin normalized dominance margin (`dom_sym === :bool` in
`_dominance_step_spin_margin`): divides Boolean gradient bounds by $2$ before taking
$\max(\text{lo}_s, -\text{hi}_s)$. -/
noncomputable def boolToSpinMargin (lo_bool hi_bool : ℝ) : ℝ :=
  domSpinMargin (lo_bool / 2) (hi_bool / 2)

/-- Exact homogeneity identity for `boolToSpinMargin`:
$\mathrm{boolToSpinMargin}(\text{lo}_{\mathrm{bool}}, \text{hi}_{\mathrm{bool}})
  = \max(\text{lo}_{\mathrm{bool}}, -\text{hi}_{\mathrm{bool}}) / 2$. -/
theorem boolToSpinMargin_eq (lo_bool hi_bool : ℝ) :
    boolToSpinMargin lo_bool hi_bool = max lo_bool (-hi_bool) / 2 := by
  unfold boolToSpinMargin domSpinMargin
  have hneg : -(hi_bool / 2) = -hi_bool / 2 := by ring
  rw [hneg]
  rcases le_total lo_bool (-hi_bool) with h | h
  · have h2 : lo_bool / 2 ≤ -hi_bool / 2 := by linarith
    rw [max_eq_right h, max_eq_right h2]
  · have h2 : -hi_bool / 2 ≤ lo_bool / 2 := by linarith
    rw [max_eq_left h, max_eq_left h2]

/-- Single-spin flip energy change $\Delta E = (-z) L - z L = -2 z L$ for a spin $z \in \{-1, +1\}$
subject to effective local field $L$. -/
noncomputable def singleSpinFlipDelta (z L : ℝ) : ℝ :=
  (-z) * L - z * L

/-- Explicit factoring $\Delta E = -2 z L$ for flipping spin $z \mapsto -z$. -/
theorem singleSpinFlipDelta_eq (z L : ℝ) :
    singleSpinFlipDelta z L = -2 * z * L := by
  unfold singleSpinFlipDelta
  ring

/-- When $\text{lo} \le \text{hi}$ and $\text{lo} > 0$, `domSpinMargin lo hi = lo > 0`. -/
theorem domSpinMargin_eq_left_of_lo_pos {lo hi : ℝ} (h_le : lo ≤ hi) (h_lo : 0 < lo) :
    domSpinMargin lo hi = lo ∧ 0 < domSpinMargin lo hi := by
  unfold domSpinMargin
  have h : -hi ≤ lo := by linarith
  rw [max_eq_left h]
  exact ⟨rfl, h_lo⟩

/-- When $\text{lo} \le \text{hi}$ and $\text{hi} < 0$, `domSpinMargin lo hi = -hi > 0`. -/
theorem domSpinMargin_eq_right_of_hi_neg {lo hi : ℝ} (h_le : lo ≤ hi) (h_hi : hi < 0) :
    domSpinMargin lo hi = -hi ∧ 0 < domSpinMargin lo hi := by
  unfold domSpinMargin
  have h : lo ≤ -hi := by linarith
  rw [max_eq_right h]
  exact ⟨rfl, by linarith⟩

/-- **Theorem 7 (Part 1A — Positive Lower Bound Spin Margin)**:
If $L \in [\text{lo}, \text{hi}]$ with $\text{lo} > 0$ (certifying $z^* = -1$), then on the
violating state $z = +1 = -z^*$, flipping $z \mapsto -1$ changes the energy by
$\Delta E = -2 L \le -2\,\text{lo} = -2\,\mathrm{domSpinMargin}(\text{lo}, \text{hi}) < 0$. -/
theorem single_step_spin_margin_pos_lo {lo hi L : ℝ}
    (h_lo_L : lo ≤ L) (h_L_hi : L ≤ hi) (h_lo_pos : 0 < lo) :
    singleSpinFlipDelta 1 L = -2 * L ∧
      singleSpinFlipDelta 1 L ≤ -2 * lo ∧
      -2 * lo = -2 * domSpinMargin lo hi ∧
      -2 * domSpinMargin lo hi < 0 := by
  have h_le : lo ≤ hi := le_trans h_lo_L h_L_hi
  have hdom := (domSpinMargin_eq_left_of_lo_pos h_le h_lo_pos).1
  rw [singleSpinFlipDelta_eq]
  refine ⟨by ring, by linarith, by rw [hdom], by linarith⟩

/-- **Theorem 7 (Part 1B — Negative Upper Bound Spin Margin)**:
If $L \in [\text{lo}, \text{hi}]$ with $\text{hi} < 0$ (certifying $z^* = +1$), then on the
violating state $z = -1 = -z^*$, flipping $z \mapsto +1$ changes the energy by
$\Delta E = 2 L \le 2\,\text{hi} = -2\,\mathrm{domSpinMargin}(\text{lo}, \text{hi}) < 0$. -/
theorem single_step_spin_margin_neg_hi {lo hi L : ℝ}
    (h_lo_L : lo ≤ L) (h_L_hi : L ≤ hi) (h_hi_neg : hi < 0) :
    singleSpinFlipDelta (-1) L = 2 * L ∧
      singleSpinFlipDelta (-1) L ≤ 2 * hi ∧
      2 * hi = -2 * domSpinMargin lo hi ∧
      -2 * domSpinMargin lo hi < 0 := by
  have h_le : lo ≤ hi := le_trans h_lo_L h_L_hi
  have hdom := (domSpinMargin_eq_right_of_hi_neg h_le h_hi_neg).1
  rw [singleSpinFlipDelta_eq]
  refine ⟨by ring, by linarith, by rw [hdom]; ring, by linarith⟩

/-- **Theorem 7 (Part 1C — Unified Single-Step Spin Margin Soundness)**:
Whether a dominance step fixes $z^* = -1$ via $\text{lo} > 0$ or $z^* = +1$ via $\text{hi} < 0$,
flipping the violating spin assignment $z = -z^*$ to $z^*$ strictly reduces energy by at least
$2\,\mathrm{domSpinMargin}(\text{lo}, \text{hi}) > 0$. -/
theorem single_step_spin_margin_sound {lo hi L z_star : ℝ}
    (h_lo_L : lo ≤ L) (h_L_hi : L ≤ hi)
    (h_cert : (0 < lo ∧ z_star = -1) ∨ (hi < 0 ∧ z_star = 1)) :
    singleSpinFlipDelta (-z_star) L ≤ -2 * domSpinMargin lo hi ∧
      -2 * domSpinMargin lo hi < 0 := by
  rcases h_cert with ⟨h_lo, rfl⟩ | ⟨h_hi, rfl⟩
  · have h := single_step_spin_margin_pos_lo h_lo_L h_L_hi h_lo
    norm_num
    norm_num at h
    exact ⟨by linarith [h.2.1, h.2.2.1], h.2.2.2⟩
  · have h := single_step_spin_margin_neg_hi h_lo_L h_L_hi h_hi
    exact ⟨by linarith [h.2.1, h.2.2.1], h.2.2.2⟩

/-!
### Part 2: Sequential Branch Cascade & First-Divergence / Telescoping Repair
-/

/-- Branch spin margin across a non-empty sequence of dominance steps with step margins
`m₁ :: ms` (`_branch_steps_spin_margin` in `src/certificates.jl:1669-1681`):
$\mathrm{branchSpinMargin}(m_1, \mathrm{ms}) = \mathrm{ms.foldl}\ \min\ m_1$. -/
noncomputable def branchSpinMargin (m₁ : ℝ) (ms : List ℝ) : ℝ :=
  ms.foldl min m₁

/-- Helper lemma: `List.foldl min a ms` is bounded above by the initial accumulator `a`. -/
theorem foldl_min_le_init (a : ℝ) (ms : List ℝ) :
    ms.foldl min a ≤ a := by
  induction ms generalizing a with
  | nil => exact le_rfl
  | cons m rest ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (min a m)) (min_le_left a m)

/-- Helper lemma: `List.foldl min a ms` is bounded above by every element `m ∈ ms`. -/
theorem foldl_min_le_of_mem {a m : ℝ} {ms : List ℝ} (hm : m ∈ ms) :
    ms.foldl min a ≤ m := by
  induction ms generalizing a with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | htl
    · exact le_trans (foldl_min_le_init (min a m) tl) (min_le_right a m)
    · exact ih htl

/-- `branchSpinMargin m₁ ms` is bounded above by every step margin `m ∈ m₁ :: ms`. -/
theorem branchSpinMargin_le_of_mem {m₁ m : ℝ} {ms : List ℝ} (hm : m ∈ m₁ :: ms) :
    branchSpinMargin m₁ ms ≤ m := by
  unfold branchSpinMargin
  rcases List.mem_cons.mp hm with rfl | hms
  · exact foldl_min_le_init m ms
  · exact foldl_min_le_of_mem hms

/-- `branchSpinMargin m₁ ms` is strictly positive if and only if every step margin in `m₁ :: ms`
is strictly positive. -/
theorem branchSpinMargin_pos_iff (m₁ : ℝ) (ms : List ℝ) :
    0 < branchSpinMargin m₁ ms ↔ ∀ m ∈ m₁ :: ms, 0 < m := by
  unfold branchSpinMargin
  induction ms generalizing m₁ with
  | nil =>
    simp
  | cons m₂ rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, forall_eq_or_imp, lt_min_iff]
    tauto

/-- `branchSpinMargin m₁ ms` is non-negative if and only if every step margin in `m₁ :: ms`
is non-negative. -/
theorem branchSpinMargin_nonneg_iff (m₁ : ℝ) (ms : List ℝ) :
    0 ≤ branchSpinMargin m₁ ms ↔ ∀ m ∈ m₁ :: ms, 0 ≤ m := by
  unfold branchSpinMargin
  induction ms generalizing m₁ with
  | nil =>
    simp
  | cons m₂ rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, forall_eq_or_imp, le_min_iff]
    tauto

/-- A single step in a sequential trial-dominance cascade on state space `S`, carrying its target
fixing predicate `pred`, spin margin `margin`, and single-step repair map `repair`. -/
structure CascadeStep (S : Type*) where
  pred : S → Prop
  margin : ℝ
  repair : S → S

/-- Conjunction of all step predicates $P_1(s) \land \dots \land P_k(s)$ in a cascade. -/
def allCascadePreds {S : Type*} : List (CascadeStep S) → S → Prop
  | [], _ => True
  | st :: rest, s => st.pred s ∧ allCascadePreds rest s

/-- If a state satisfies `allCascadePreds steps s`, it satisfies `st.pred s` for every
`st ∈ steps`. -/
theorem allCascadePreds_imp_mem {S : Type*} {steps : List (CascadeStep S)} {s : S}
    (hall : allCascadePreds steps s) {st : CascadeStep S} (hst : st ∈ steps) :
    st.pred s := by
  induction steps with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hall with ⟨hhd, htl⟩
    rcases List.mem_cons.mp hst with rfl | hmem
    · exact hhd
    · exact ih htl hmem

/-- Validity of a sequential trial-dominance cascade `steps` on feasible set `Ω` with objective
`E` under initial assumption prefix `P₀`: each step `st` repairs any state `s ∈ Ω` satisfying the
accumulated prefix `P₀` and violating `¬ st.pred s` into a feasible state `st.repair s ∈ Ω`
preserving `P₀`, establishing `st.pred`, and lowering energy by at least `2 * st.margin`. -/
def ValidCascade {S : Type*} (Ω : Set S) (E : S → ℝ) :
    (S → Prop) → List (CascadeStep S) → Prop
  | _, [] => True
  | P₀, st :: rest =>
      (∀ s ∈ Ω, P₀ s → ¬ st.pred s →
        st.repair s ∈ Ω ∧ P₀ (st.repair s) ∧ st.pred (st.repair s) ∧
          E (st.repair s) ≤ E s - 2 * st.margin) ∧
      ValidCascade Ω E (fun s => P₀ s ∧ st.pred s) rest

/-- **Theorem 7 (Part 2A — First-Divergence Cascade Repair Theorem)**:
In any valid non-empty cascade `st₁ :: rest` under assumption `P₀`, if a feasible state `s ∈ Ω`
satisfies `P₀ s` and violates at least one step (`¬ allCascadePreds (st₁ :: rest) s`), then at the
first diverging step `st ∈ st₁ :: rest`, the single-step repair `s' = st.repair s ∈ Ω` satisfies:
$$E(s') \le E(s) - 2\,\mathrm{st.margin} \le E(s) - 2 M_{\mathrm{branch}}.$$ -/
theorem cascade_first_divergence_repair {S : Type*}
    {Ω : Set S} {E : S → ℝ} {P₀ : S → Prop}
    (st₁ : CascadeStep S) (rest : List (CascadeStep S))
    (hvalid : ValidCascade Ω E P₀ (st₁ :: rest))
    {s : S} (hs : s ∈ Ω) (hP₀ : P₀ s)
    (hviol : ¬ allCascadePreds (st₁ :: rest) s) :
    ∃ st ∈ st₁ :: rest, ∃ s' ∈ Ω,
      ¬ st.pred s ∧ st.pred s' ∧
      E s' ≤ E s - 2 * st.margin ∧
      E s' ≤ E s - 2 * branchSpinMargin st₁.margin (rest.map CascadeStep.margin) := by
  suffices hgen :
      ∃ st ∈ st₁ :: rest, ∃ s' ∈ Ω,
        ¬ st.pred s ∧ st.pred s' ∧ E s' ≤ E s - 2 * st.margin by
    rcases hgen with ⟨st, hst_mem, s', hs', hnot, hpred, hE⟩
    have hmem_margin : st.margin ∈ st₁.margin :: rest.map CascadeStep.margin := by
      have hmap := List.mem_map_of_mem (f := CascadeStep.margin) hst_mem
      simpa using hmap
    have hle_margin := branchSpinMargin_le_of_mem hmem_margin
    exact ⟨st, hst_mem, s', hs', hnot, hpred, hE, by linarith⟩
  induction rest generalizing P₀ st₁ with
  | nil =>
    rcases hvalid with ⟨hst₁, _⟩
    have hnot₁ : ¬ st₁.pred s := by
      intro hp₁
      exact hviol ⟨hp₁, trivial⟩
    rcases hst₁ s hs hP₀ hnot₁ with ⟨hs', _, hpred', hE'⟩
    exact ⟨st₁, List.mem_cons_self, st₁.repair s, hs', hnot₁, hpred', hE'⟩
  | cons st₂ tl ih =>
    rcases hvalid with ⟨hst₁, hrest⟩
    by_cases hp₁ : st₁.pred s
    · have hviol₂ : ¬ allCascadePreds (st₂ :: tl) s := by
        intro hall₂
        exact hviol ⟨hp₁, hall₂⟩
      rcases ih st₂ hrest ⟨hP₀, hp₁⟩ hviol₂ with ⟨st, hst_mem, s', hs', hnot, hpred, hE⟩
      exact ⟨st, List.mem_cons_of_mem st₁ hst_mem, s', hs', hnot, hpred, hE⟩
    · rcases hst₁ s hs hP₀ hp₁ with ⟨hs', _, hpred', hE'⟩
      exact ⟨st₁, List.mem_cons_self, st₁.repair s, hs', hp₁, hpred', hE'⟩

/-- **Corollary (Terminal-Step Refutation along a Cascade)**:
If `st_target ∈ st₁ :: rest` is any step in a valid cascade (in particular, the terminal step
fixing a target variable) and `s ∈ Ω` satisfies `P₀ s` but violates `¬ st_target.pred s`, then
there exists a repaired feasible state `s' ∈ Ω` with
$E(s') \le E(s) - 2 M_{\mathrm{branch}}$. -/
theorem cascade_terminal_refutation {S : Type*}
    {Ω : Set S} {E : S → ℝ} {P₀ : S → Prop}
    (st₁ : CascadeStep S) (rest : List (CascadeStep S))
    (hvalid : ValidCascade Ω E P₀ (st₁ :: rest))
    {st_target : CascadeStep S} (htarget : st_target ∈ st₁ :: rest)
    {s : S} (hs : s ∈ Ω) (hP₀ : P₀ s) (hviol_target : ¬ st_target.pred s) :
    ∃ s' ∈ Ω,
      E s' ≤ E s - 2 * branchSpinMargin st₁.margin (rest.map CascadeStep.margin) := by
  have hviol_all : ¬ allCascadePreds (st₁ :: rest) s := by
    intro hall
    exact hviol_target (allCascadePreds_imp_mem hall htarget)
  rcases cascade_first_divergence_repair st₁ rest hvalid hs hP₀ hviol_all with
    ⟨_, _, s', hs', _, _, _, hE⟩
  exact ⟨s', hs', hE⟩

/-- Full-cascade sequential repair operator: traverses the cascade from step $1$ to step $k$,
applying `st.repair` whenever the current state violates `st.pred`. -/
noncomputable def cascadeFullRepair {S : Type*} : List (CascadeStep S) → S → S
  | [], s => s
  | st :: rest, s =>
      open Classical in
      cascadeFullRepair rest (if st.pred s then s else st.repair s)

/-- Exact cumulative sum of step margins $\sum_{r \in \text{repaired}} m_r$ along all steps
repaired by `cascadeFullRepair`. -/
noncomputable def cascadeTelescopingMargin {S : Type*} : List (CascadeStep S) → S → ℝ
  | [], _ => 0
  | st :: rest, s =>
      open Classical in
      (if st.pred s then 0 else st.margin) +
        cascadeTelescopingMargin rest (if st.pred s then s else st.repair s)

/-- **Theorem 7 (Part 2B — Full-Cascade Telescoping Repair Theorem)**:
Given any `ValidCascade Ω E P₀ steps` and any feasible state `s ∈ Ω` satisfying `P₀ s`, the
full-cascade repaired state `s_final = cascadeFullRepair steps s` belongs to `Ω`, satisfies both
`P₀ s_final` and the entire conjunction `allCascadePreds steps s_final`, and satisfies the exact
telescoping energy bound:
$$E(s_{\mathrm{final}}) \le E(s) - 2\,\mathrm{cascadeTelescopingMargin}(\mathrm{steps}, s).$$ -/
theorem cascadeFullRepair_satisfies_and_telescopes {S : Type*}
    {Ω : Set S} {E : S → ℝ} {P₀ : S → Prop}
    (steps : List (CascadeStep S))
    (hvalid : ValidCascade Ω E P₀ steps)
    {s : S} (hs : s ∈ Ω) (hP₀ : P₀ s) :
    cascadeFullRepair steps s ∈ Ω ∧
      P₀ (cascadeFullRepair steps s) ∧
      allCascadePreds steps (cascadeFullRepair steps s) ∧
      E (cascadeFullRepair steps s) ≤ E s - 2 * cascadeTelescopingMargin steps s := by
  classical
  induction steps generalizing P₀ s with
  | nil =>
    simp [cascadeFullRepair, allCascadePreds, cascadeTelescopingMargin, hs, hP₀]
  | cons st rest ih =>
    rcases hvalid with ⟨hst, hrest⟩
    simp only [cascadeFullRepair, cascadeTelescopingMargin]
    by_cases hp : st.pred s
    · simp only [if_pos hp]
      rcases ih hrest hs ⟨hP₀, hp⟩ with ⟨hΩ_f, ⟨hP₀_f, hst_f⟩, hall_f, hE_f⟩
      refine ⟨hΩ_f, hP₀_f, ⟨hst_f, hall_f⟩, ?_⟩
      linarith
    · simp only [if_neg hp]
      rcases hst s hs hP₀ hp with ⟨hs₁, hP₀₁, hst₁, hE₁⟩
      rcases ih hrest hs₁ ⟨hP₀₁, hst₁⟩ with ⟨hΩ_f, ⟨hP₀_f, hst_f⟩, hall_f, hE_f⟩
      refine ⟨hΩ_f, hP₀_f, ⟨hst_f, hall_f⟩, ?_⟩
      linarith

/-- If all step margins in a cascade `steps` are non-negative, `cascadeTelescopingMargin steps s`
is non-negative for every state `s`. -/
theorem cascadeTelescopingMargin_nonneg {S : Type*}
    (steps : List (CascadeStep S))
    (hnonneg : ∀ st ∈ steps, 0 ≤ st.margin) (s : S) :
    0 ≤ cascadeTelescopingMargin steps s := by
  classical
  induction steps generalizing s with
  | nil => simp [cascadeTelescopingMargin]
  | cons st rest ih =>
    rw [cascadeTelescopingMargin]
    have hst : 0 ≤ st.margin := hnonneg st List.mem_cons_self
    have hrest : ∀ st' ∈ rest, 0 ≤ st'.margin :=
      fun st' hmem => hnonneg st' (List.mem_cons_of_mem st hmem)
    by_cases hp : st.pred s
    · simp only [if_pos hp]
      have hih := ih hrest s
      linarith
    · simp only [if_neg hp]
      have hih := ih hrest (st.repair s)
      linarith

/-- Helper lemma: when all step margins in `st₁ :: rest` are non-negative and `s` violates at least
one step (`¬ allCascadePreds (st₁ :: rest) s`), the telescoping margin sum is at least the margin
of the first diverging step `st ∈ st₁ :: rest`. -/
theorem exists_le_cascadeTelescopingMargin {S : Type*}
    (st₁ : CascadeStep S) (rest : List (CascadeStep S))
    (hall_nonneg : ∀ st ∈ st₁ :: rest, 0 ≤ st.margin)
    {s : S} (hviol : ¬ allCascadePreds (st₁ :: rest) s) :
    ∃ st ∈ st₁ :: rest, st.margin ≤ cascadeTelescopingMargin (st₁ :: rest) s := by
  classical
  induction rest generalizing st₁ s with
  | nil =>
    have hnot₁ : ¬ st₁.pred s := fun hp₁ => hviol ⟨hp₁, trivial⟩
    refine ⟨st₁, List.mem_cons_self, ?_⟩
    rw [cascadeTelescopingMargin]
    simp [if_neg hnot₁, cascadeTelescopingMargin]
  | cons st₂ tl ih =>
    by_cases hp₁ : st₁.pred s
    · have hviol₂ : ¬ allCascadePreds (st₂ :: tl) s := fun hall₂ => hviol ⟨hp₁, hall₂⟩
      have hall₂ : ∀ st ∈ st₂ :: tl, 0 ≤ st.margin :=
        fun st hst => hall_nonneg st (List.mem_cons_of_mem st₁ hst)
      rcases ih st₂ hall₂ hviol₂ with ⟨st, hst, hle⟩
      refine ⟨st, List.mem_cons_of_mem st₁ hst, ?_⟩
      rw [cascadeTelescopingMargin]
      simp only [if_pos hp₁, zero_add]
      exact hle
    · refine ⟨st₁, List.mem_cons_self, ?_⟩
      rw [cascadeTelescopingMargin]
      simp only [if_neg hp₁]
      have htail_nonneg : 0 ≤ cascadeTelescopingMargin (st₂ :: tl) (st₁.repair s) :=
        cascadeTelescopingMargin_nonneg (st₂ :: tl)
          (fun st hst => hall_nonneg st (List.mem_cons_of_mem st₁ hst)) (st₁.repair s)
      linarith

/-- When all step margins in `st₁ :: rest` are non-negative and `s` violates at least one step
(`¬ allCascadePreds (st₁ :: rest) s`), the telescoping margin sum is at least
`branchSpinMargin st₁.margin (rest.map CascadeStep.margin)`, so `cascadeFullRepair` reduces
energy by at least $2 M_{\mathrm{branch}}$. -/
theorem cascadeFullRepair_drop_ge_branchSpinMargin {S : Type*}
    {Ω : Set S} {E : S → ℝ} {P₀ : S → Prop}
    (st₁ : CascadeStep S) (rest : List (CascadeStep S))
    (hvalid : ValidCascade Ω E P₀ (st₁ :: rest))
    (hnonneg : 0 ≤ branchSpinMargin st₁.margin (rest.map CascadeStep.margin))
    {s : S} (hs : s ∈ Ω) (hP₀ : P₀ s)
    (hviol : ¬ allCascadePreds (st₁ :: rest) s) :
    branchSpinMargin st₁.margin (rest.map CascadeStep.margin) ≤
        cascadeTelescopingMargin (st₁ :: rest) s ∧
      E (cascadeFullRepair (st₁ :: rest) s) ≤
        E s - 2 * branchSpinMargin st₁.margin (rest.map CascadeStep.margin) := by
  have htele := cascadeFullRepair_satisfies_and_telescopes (st₁ :: rest) hvalid hs hP₀
  have hall_nonneg : ∀ st ∈ st₁ :: rest, 0 ≤ st.margin := by
    intro st hst
    have hmem : st.margin ∈ st₁.margin :: rest.map CascadeStep.margin := by
      have hmap := List.mem_map_of_mem (f := CascadeStep.margin) hst
      simpa using hmap
    exact (branchSpinMargin_nonneg_iff st₁.margin (rest.map CascadeStep.margin)).mp hnonneg
      st.margin hmem
  rcases exists_le_cascadeTelescopingMargin st₁ rest hall_nonneg hviol with ⟨st, hst, hle⟩
  have hmem : st.margin ∈ st₁.margin :: rest.map CascadeStep.margin := by
    have hmap := List.mem_map_of_mem (f := CascadeStep.margin) hst
    simpa using hmap
  have hbr := branchSpinMargin_le_of_mem hmem
  refine ⟨le_trans hbr hle, ?_⟩
  linarith [htele.2.2.2, hbr, hle]

/-!
### Part 3: Witness-Free Double Probing (`:double_probe`)
-/

/-- Worst-case spin margin across the low ($s_p = -1$) and high ($s_p = +1$) probing branches:
$\mathrm{doubleProbeMargin}(M_{\mathrm{low}}, M_{\mathrm{high}})
  = \min(M_{\mathrm{low}}, M_{\mathrm{high}})$. -/
noncomputable def doubleProbeMargin (M_low M_high : ℝ) : ℝ :=
  min M_low M_high

/-- `doubleProbeMargin M_low M_high > 0` holds iff both branch margins are strictly positive
(`M_low > 0 && M_high > 0` in `_verify_probing_step`, `src/certificates.jl:5383`). -/
theorem doubleProbeMargin_pos_iff (M_low M_high : ℝ) :
    0 < doubleProbeMargin M_low M_high ↔ 0 < M_low ∧ 0 < M_high :=
  lt_min_iff

/-- **Theorem 7 (Part 3A — Witness-Free `:double_probe` Soundness)**:
Suppose every state $s \in \Omega$ has $s_p(s) \in \{-1, +1\}$, the low branch ($s_p = -1$)
repairs any state with $s_u(s) \neq u^*$ by at least $2 M_{\mathrm{low}}$, and the high branch
($s_p = +1$) repairs any state with $s_u(s) \neq u^*$ by at least $2 M_{\mathrm{high}}$. Then
every state $s \in \Omega$ with $s_u(s) \neq u^*$ admits a feasible repair $s' \in \Omega$ with
$$E(s') \le E(s) - 2\,\mathrm{doubleProbeMargin}(M_{\mathrm{low}}, M_{\mathrm{high}}).$$ -/
theorem double_probe_sound {S : Type*}
    (Ω : Set S) (E : S → ℝ) (sp su : S → ℝ) (u_star M_low M_high : ℝ)
    (hsp : ∀ s ∈ Ω, isSpin (sp s))
    (hlow : ∀ s ∈ Ω, sp s = -1 → su s ≠ u_star → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M_low)
    (hhigh : ∀ s ∈ Ω, sp s = 1 → su s ≠ u_star → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M_high)
    {s : S} (hs : s ∈ Ω) (hviol : su s ≠ u_star) :
    ∃ s' ∈ Ω, E s' ≤ E s - 2 * doubleProbeMargin M_low M_high := by
  unfold doubleProbeMargin
  rcases hsp s hs with hsp_neg | hsp_pos
  · rcases hlow s hs hsp_neg hviol with ⟨s', hs', hE⟩
    refine ⟨s', hs', ?_⟩
    have hmin : min M_low M_high ≤ M_low := min_le_left _ _
    linarith
  · rcases hhigh s hs hsp_pos hviol with ⟨s', hs', hE⟩
    refine ⟨s', hs', ?_⟩
    have hmin : min M_low M_high ≤ M_high := min_le_right _ _
    linarith

/-- **Corollary (`:double_probe` Global-Minimum Persistence)**:
Under the hypotheses of `double_probe_sound` with $M_{\mathrm{low}} > 0$ and $M_{\mathrm{high}} > 0$,
every global minimizer $s^*$ of $E$ on $\Omega$ satisfies $s_u(s^*) = u^*$. -/
theorem double_probe_global_min_fixes_target {S : Type*}
    (Ω : Set S) (E : S → ℝ) (sp su : S → ℝ) (u_star M_low M_high : ℝ)
    (hsp : ∀ s ∈ Ω, isSpin (sp s))
    (hlow : ∀ s ∈ Ω, sp s = -1 → su s ≠ u_star → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M_low)
    (hhigh : ∀ s ∈ Ω, sp s = 1 → su s ≠ u_star → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M_high)
    (hM_low : 0 < M_low) (hM_high : 0 < M_high)
    {s : S} (hs_min : IsGlobalMin Ω E s) :
    su s = u_star := by
  by_contra hviol
  rcases double_probe_sound Ω E sp su u_star M_low M_high hsp hlow hhigh hs_min.1 hviol with
    ⟨s', hs', hE⟩
  have hpos : 0 < doubleProbeMargin M_low M_high :=
    (doubleProbeMargin_pos_iff M_low M_high).mpr ⟨hM_low, hM_high⟩
  have hmin := hs_min.2 s' hs'
  linarith

/-- **Cascade-Instantiated `:double_probe` Soundness**:
If `st_low₁ :: rest_low` is a valid cascade under assumption $s_p(s) = -1$ containing a step
fixing $s_u(s) = u^*$, and `st_high₁ :: rest_high` is a valid cascade under assumption
$s_p(s) = +1$ containing a step fixing $s_u(s) = u^*$, then every feasible state $s \in \Omega$
with $s_u(s) \neq u^*$ admits a feasible repair lowering energy by at least
$2 \min(M_{\mathrm{low}}, M_{\mathrm{high}})$. -/
theorem double_probe_cascade_sound {S : Type*}
    (Ω : Set S) (E : S → ℝ) (sp su : S → ℝ) (u_star : ℝ)
    (st_low₁ : CascadeStep S) (rest_low : List (CascadeStep S))
    (st_high₁ : CascadeStep S) (rest_high : List (CascadeStep S))
    (st_target_low st_target_high : CascadeStep S)
    (hsp : ∀ s ∈ Ω, isSpin (sp s))
    (hvalid_low : ValidCascade Ω E (fun s => sp s = -1) (st_low₁ :: rest_low))
    (hvalid_high : ValidCascade Ω E (fun s => sp s = 1) (st_high₁ :: rest_high))
    (htarget_low : st_target_low ∈ st_low₁ :: rest_low)
    (htarget_high : st_target_high ∈ st_high₁ :: rest_high)
    (hpred_low : ∀ s, st_target_low.pred s ↔ su s = u_star)
    (hpred_high : ∀ s, st_target_high.pred s ↔ su s = u_star)
    {s : S} (hs : s ∈ Ω) (hviol : su s ≠ u_star) :
    ∃ s' ∈ Ω,
      E s' ≤ E s - 2 * doubleProbeMargin
        (branchSpinMargin st_low₁.margin (rest_low.map CascadeStep.margin))
        (branchSpinMargin st_high₁.margin (rest_high.map CascadeStep.margin)) := by
  refine double_probe_sound Ω E sp su u_star
    (branchSpinMargin st_low₁.margin (rest_low.map CascadeStep.margin))
    (branchSpinMargin st_high₁.margin (rest_high.map CascadeStep.margin))
    hsp ?_ ?_ hs hviol
  · intro s₀ hs₀ hsp₀ hviol₀
    have hnot : ¬ st_target_low.pred s₀ := by
      rw [hpred_low]
      exact hviol₀
    exact cascade_terminal_refutation st_low₁ rest_low hvalid_low htarget_low hs₀ hsp₀ hnot
  · intro s₀ hs₀ hsp₀ hviol₀
    have hnot : ¬ st_target_high.pred s₀ := by
      rw [hpred_high]
      exact hviol₀
    exact cascade_terminal_refutation st_high₁ rest_high hvalid_high htarget_high hs₀ hsp₀ hnot

/-- Reconstruction map $y \mapsto (y, u^*)$ for `:double_probe` variable fixing $s_u = u^*$. -/
def doubleProbeReconstruct {Y : Type*} (u_star : ℝ) : Y → Y × ℝ :=
  reconstruct (fun _ => u_star)

/-- **Theorem 7 (Part 3B — Compositional `ReductionStep` Bridge for `:double_probe`)**:
When both the low branch ($s_p = -1$) and high branch ($s_p = +1$) repair any state
$(y, s_u) \in S_{\mathrm{rest}} \times^s \{-1, +1\}$ with $s_u \neq u^*$ to a state
$(y', u^*) \in S_{\mathrm{rest}} \times^s \{-1, +1\}$ with energy drop at least
$2 M_{\mathrm{low}} \ge 0$ (resp. $2 M_{\mathrm{high}} \ge 0$), variable fixing $s_u = u^*$ defines
a valid `ReductionStep`. -/
theorem double_probe_reductionStep {Y : Type*}
    (S_rest : Set Y) (F : Y × ℝ → ℝ) (sp : Y → ℝ) (u_star M_low M_high : ℝ)
    (hu_star : isSpin u_star)
    (hsp : ∀ y ∈ S_rest, isSpin (sp y))
    (hlow : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = -1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_low)
    (hhigh : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = 1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_high)
    (hM_low : 0 ≤ M_low) (hM_high : 0 ≤ M_high) :
    ReductionStep (S_rest ×ˢ {s_u | isSpin s_u}) F
      S_rest (reducedObj F (fun _ => u_star)) (doubleProbeReconstruct u_star) where
  maps_into y hy := ⟨hy, hu_star⟩
  energy_eq _ _ := rfl
  weak_dom := by
    rintro ⟨y, s_u⟩ ⟨hy, hs_u⟩
    by_cases hrel : s_u = u_star
    · refine ⟨y, hy, ?_⟩
      unfold reducedObj
      rw [hrel]
    · rcases hsp y hy with hneg | hpos
      · rcases hlow y hy s_u hs_u hneg hrel with ⟨y', hy', hE⟩
        refine ⟨y', hy', ?_⟩
        unfold reducedObj
        linarith
      · rcases hhigh y hy s_u hs_u hpos hrel with ⟨y', hy', hE⟩
        refine ⟨y', hy', ?_⟩
        unfold reducedObj
        linarith

/-- **Theorem 7 (Part 3C — Compositional `StrongReductionStep` Bridge for `:double_probe`)**:
When $M_{\mathrm{low}} > 0$ and $M_{\mathrm{high}} > 0$, `:double_probe` variable fixing
$s_u = u^*$ defines a `StrongReductionStep` whose reconstruction map `doubleProbeReconstruct u_star`
is surjective onto all global minimizers of $F$ on $S_{\mathrm{rest}} \times^s \{-1, +1\}$. -/
theorem double_probe_strongReductionStep {Y : Type*}
    (S_rest : Set Y) (F : Y × ℝ → ℝ) (sp : Y → ℝ) (u_star M_low M_high : ℝ)
    (hu_star : isSpin u_star)
    (hsp : ∀ y ∈ S_rest, isSpin (sp y))
    (hlow : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = -1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_low)
    (hhigh : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = 1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_high)
    (hM_low : 0 < M_low) (hM_high : 0 < M_high) :
    StrongReductionStep (S_rest ×ˢ {s_u | isSpin s_u}) F
      S_rest (reducedObj F (fun _ => u_star)) (doubleProbeReconstruct u_star) where
  toReductionStep :=
    double_probe_reductionStep S_rest F sp u_star M_low M_high hu_star hsp hlow hhigh
      (le_of_lt hM_low) (le_of_lt hM_high)
  surj_on_min := by
    rintro ⟨y, s_u⟩ ⟨⟨hy, hs_u⟩, hmin⟩
    by_cases hrel : s_u = u_star
    · refine ⟨y, ⟨hy, ?_⟩, ?_⟩
      · intro y' hy'
        have hx' : (y', u_star) ∈ S_rest ×ˢ {s_u | isSpin s_u} := ⟨hy', hu_star⟩
        have hle := hmin (y', u_star) hx'
        unfold reducedObj
        dsimp
        rw [hrel] at hle
        exact hle
      · unfold doubleProbeReconstruct reconstruct
        rw [hrel]
    · exfalso
      rcases hsp y hy with hneg | hpos
      · rcases hlow y hy s_u hs_u hneg hrel with ⟨y', hy', hE⟩
        have hx' : (y', u_star) ∈ S_rest ×ˢ {s_u | isSpin s_u} := ⟨hy', hu_star⟩
        have hle := hmin (y', u_star) hx'
        linarith
      · rcases hhigh y hy s_u hs_u hpos hrel with ⟨y', hy', hE⟩
        have hx' : (y', u_star) ∈ S_rest ×ˢ {s_u | isSpin s_u} := ⟨hy', hu_star⟩
        have hle := hmin (y', u_star) hx'
        linarith

/-- **Corollary (Global Minimum Preservation under `:double_probe`)**:
Under the hypotheses of `double_probe_reductionStep`, any global minimizer of
`reducedObj F (fun _ => u_star)` on `S_rest` reconstructs via `doubleProbeReconstruct u_star` to
a global minimizer of `F` on `S_rest ×ˢ {s_u | isSpin s_u}` with identical objective value. -/
theorem double_probe_preserves_global_min {Y : Type*}
    (S_rest : Set Y) (F : Y × ℝ → ℝ) (sp : Y → ℝ) (u_star M_low M_high : ℝ)
    (hu_star : isSpin u_star)
    (hsp : ∀ y ∈ S_rest, isSpin (sp y))
    (hlow : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = -1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_low)
    (hhigh : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = 1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_high)
    (hM_low : 0 ≤ M_low) (hM_high : 0 ≤ M_high)
    {y : Y} (hy : IsGlobalMin S_rest (reducedObj F (fun _ => u_star)) y) :
    IsGlobalMin (S_rest ×ˢ {s_u | isSpin s_u}) F (doubleProbeReconstruct u_star y) ∧
      F (doubleProbeReconstruct u_star y) = reducedObj F (fun _ => u_star) y :=
  (double_probe_reductionStep S_rest F sp u_star M_low M_high
    hu_star hsp hlow hhigh hM_low hM_high).preserves_global_min hy

/-- **Corollary (Exact Bijection on Global Minimizers under Strong `:double_probe`)**:
When $M_{\mathrm{low}} > 0$ and $M_{\mathrm{high}} > 0$, the set of global minimizers of `F` on
`S_rest ×ˢ {s_u | isSpin s_u}` is the exact image under `doubleProbeReconstruct u_star` of the
global minimizers of `reducedObj F (fun _ => u_star)` on `S_rest`. -/
theorem double_probe_strong_image_global_min_eq {Y : Type*}
    (S_rest : Set Y) (F : Y × ℝ → ℝ) (sp : Y → ℝ) (u_star M_low M_high : ℝ)
    (hu_star : isSpin u_star)
    (hsp : ∀ y ∈ S_rest, isSpin (sp y))
    (hlow : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = -1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_low)
    (hhigh : ∀ y ∈ S_rest, ∀ s_u, isSpin s_u → sp y = 1 → s_u ≠ u_star →
      ∃ y' ∈ S_rest, F (y', u_star) ≤ F (y, s_u) - 2 * M_high)
    (hM_low : 0 < M_low) (hM_high : 0 < M_high) :
    {x | IsGlobalMin (S_rest ×ˢ {s_u | isSpin s_u}) F x} =
      doubleProbeReconstruct u_star ''
        {y | IsGlobalMin S_rest (reducedObj F (fun _ => u_star)) y} :=
  (double_probe_strongReductionStep S_rest F sp u_star M_low M_high
    hu_star hsp hlow hhigh hM_low hM_high).image_global_min_eq

/-!
### Part 4: Two-Branch 2-SAT Pair Equivalence Probing (`:probing_pair`)
-/

/-- **Theorem 7 (Part 4A — Exact 2-SAT Spin Violation Partition)**:
For any spins $s_u, s_v \in \{-1, +1\}$ and relation sign $\sigma \in \{-1, +1\}$, violating the
signed relation $s_u = \sigma s_v$ is equivalent to the two-clause partition
$$(s_u = -1 \land s_v = \sigma) \lor (s_u = 1 \land s_v = -\sigma).$$ -/
theorem probing_pair_violation_iff {s_u s_v σ : ℝ}
    (hs_u : isSpin s_u) (hs_v : isSpin s_v) (hσ : isSpin σ) :
    s_u ≠ σ * s_v ↔ (s_u = -1 ∧ s_v = σ) ∨ (s_u = 1 ∧ s_v = -σ) := by
  rcases hs_u with rfl | rfl <;> rcases hs_v with rfl | rfl <;> rcases hσ with rfl | rfl <;>
    norm_num

/-- Equivalent form of the 2-SAT spin violation partition using $s_u = -\sigma s_v$. -/
theorem probing_pair_viol_eq_iff {s_u s_v σ : ℝ}
    (hs_u : isSpin s_u) (hs_v : isSpin s_v) (hσ : isSpin σ) :
    s_u = -σ * s_v ↔ (s_u = -1 ∧ s_v = σ) ∨ (s_u = 1 ∧ s_v = -σ) := by
  rcases hs_u with rfl | rfl <;> rcases hs_v with rfl | rfl <;> rcases hσ with rfl | rfl <;>
    norm_num

/-- Witness Pattern 1 (`ok_pat_1` in `_verify_relation_step`, `src/certificates.jl:4803-4806`):
refutes the Clause-1 violation $(s_u = -1 \land s_v = \sigma)$ with branch margin $M_1$ either:
- via Pattern 1A (`assume_u_low`): assuming $s_u = -1$ derives $s_v = -\sigma$, or
- via Pattern 1B (`assume_v_xv1`): assuming $s_v = \sigma$ derives $s_u = 1$. -/
def OkPat1 {S : Type*} (Ω : Set S) (E : S → ℝ) (su sv : S → ℝ) (σ M₁ : ℝ) : Prop :=
  (∀ s ∈ Ω, su s = -1 → sv s ≠ -σ → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₁) ∨
  (∀ s ∈ Ω, sv s = σ → su s ≠ 1 → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₁)

/-- Witness Pattern 2 (`ok_pat_2` in `_verify_relation_step`, `src/certificates.jl:4807-4810`):
refutes the Clause-2 violation $(s_u = 1 \land s_v = -\sigma)$ with branch margin $M_2$ either:
- via Pattern 2A (`assume_u_high`): assuming $s_u = 1$ derives $s_v = \sigma$, or
- via Pattern 2B (`assume_v_xv2`): assuming $s_v = -\sigma$ derives $s_u = -1$. -/
def OkPat2 {S : Type*} (Ω : Set S) (E : S → ℝ) (su sv : S → ℝ) (σ M₂ : ℝ) : Prop :=
  (∀ s ∈ Ω, su s = 1 → sv s ≠ σ → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₂) ∨
  (∀ s ∈ Ω, sv s = -σ → su s ≠ -1 → ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₂)

/-- Both sub-patterns of `OkPat1` refute any Clause-1 violating state $(s_u = -1 \land s_v = \sigma)$
with energy drop at least $2 M_1$. -/
theorem okPat1_refutes_clause1 {S : Type*}
    {Ω : Set S} {E : S → ℝ} {su sv : S → ℝ} {σ M₁ : ℝ}
    (hσ : isSpin σ) (hpat1 : OkPat1 Ω E su sv σ M₁)
    {s : S} (hs : s ∈ Ω) (hu : su s = -1) (hv : sv s = σ) :
    ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₁ := by
  have hσ_ne : σ ≠ -σ := by
    rcases hσ with rfl | rfl <;> norm_num
  rcases hpat1 with h1A | h1B
  · refine h1A s hs hu ?_
    rw [hv]
    exact hσ_ne
  · refine h1B s hs hv ?_
    rw [hu]
    norm_num

/-- Both sub-patterns of `OkPat2` refute any Clause-2 violating state $(s_u = 1 \land s_v = -\sigma)$
with energy drop at least $2 M_2$. -/
theorem okPat2_refutes_clause2 {S : Type*}
    {Ω : Set S} {E : S → ℝ} {su sv : S → ℝ} {σ M₂ : ℝ}
    (hσ : isSpin σ) (hpat2 : OkPat2 Ω E su sv σ M₂)
    {s : S} (hs : s ∈ Ω) (hu : su s = 1) (hv : sv s = -σ) :
    ∃ s' ∈ Ω, E s' ≤ E s - 2 * M₂ := by
  have hσ_ne : -σ ≠ σ := by
    rcases hσ with rfl | rfl <;> norm_num
  rcases hpat2 with h2A | h2B
  · refine h2A s hs hu ?_
    rw [hv]
    exact hσ_ne
  · refine h2B s hs hv ?_
    rw [hu]
    norm_num

/-- Lower bound of a `:probing_pair` step (`lo_p = min(M_1, M_2)` in `src/certificates.jl:1695, 4832`). -/
noncomputable def probingPairLower (M₁ M₂ : ℝ) : ℝ :=
  min M₁ M₂

/-- Upper bound of a `:probing_pair` step (`hi_p = max(M_1, M_2)` in `src/certificates.jl:1695, 4832`). -/
noncomputable def probingPairUpper (M₁ M₂ : ℝ) : ℝ :=
  max M₁ M₂

/-- **Theorem 7 (Part 4B — Two-Branch `:probing_pair` Soundness)**:
Whenever `OkPat1 Ω E su sv σ M₁` and `OkPat2 Ω E su sv σ M₂` hold on a spin state space $\Omega$,
every feasible state $s \in \Omega$ violating $s_u(s) = \sigma s_v(s)$ admits a repaired feasible
state $s' \in \Omega$ with:
$$E(s') \le E(s) - 2\,\mathrm{probingPairLower}(M_1, M_2).$$ -/
theorem probing_pair_sound {S : Type*}
    (Ω : Set S) (E : S → ℝ) (su sv : S → ℝ) (σ M₁ M₂ : ℝ)
    (hsu : ∀ s ∈ Ω, isSpin (su s))
    (hsv : ∀ s ∈ Ω, isSpin (sv s))
    (hσ : isSpin σ)
    (hpat1 : OkPat1 Ω E su sv σ M₁)
    (hpat2 : OkPat2 Ω E su sv σ M₂)
    {s : S} (hs : s ∈ Ω) (hviol : su s ≠ σ * sv s) :
    ∃ s' ∈ Ω, E s' ≤ E s - 2 * probingPairLower M₁ M₂ := by
  unfold probingPairLower
  have hpart := (probing_pair_violation_iff (hsu s hs) (hsv s hs) hσ).mp hviol
  rcases hpart with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rcases okPat1_refutes_clause1 hσ hpat1 hs hu hv with ⟨s', hs', hE⟩
    refine ⟨s', hs', ?_⟩
    have hmin : min M₁ M₂ ≤ M₁ := min_le_left _ _
    linarith
  · rcases okPat2_refutes_clause2 hσ hpat2 hs hu hv with ⟨s', hs', hE⟩
    refine ⟨s', hs', ?_⟩
    have hmin : min M₁ M₂ ≤ M₂ := min_le_right _ _
    linarith

/-- **Corollary (`:probing_pair` Global-Minimum Persistence)**:
Under the hypotheses of `probing_pair_sound` with `0 < probingPairLower M₁ M₂` (`M₁ > 0` and
`M₂ > 0`), every global minimizer $s^*$ of $E$ on $\Omega$ satisfies the relation
$s_u(s^*) = \sigma s_v(s^*)$. -/
theorem probing_pair_global_min_satisfies_relation {S : Type*}
    (Ω : Set S) (E : S → ℝ) (su sv : S → ℝ) (σ M₁ M₂ : ℝ)
    (hsu : ∀ s ∈ Ω, isSpin (su s))
    (hsv : ∀ s ∈ Ω, isSpin (sv s))
    (hσ : isSpin σ)
    (hpat1 : OkPat1 Ω E su sv σ M₁)
    (hpat2 : OkPat2 Ω E su sv σ M₂)
    (hlo : 0 < probingPairLower M₁ M₂)
    {s : S} (hs_min : IsGlobalMin Ω E s) :
    su s = σ * sv s := by
  by_contra hviol
  rcases probing_pair_sound Ω E su sv σ M₁ M₂ hsu hsv hσ hpat1 hpat2 hs_min.1 hviol with
    ⟨s', hs', hE⟩
  have hmin := hs_min.2 s' hs'
  linarith

/-- **Theorem 7 (Part 4C — Compositional `ReductionStep` Bridge for `:probing_pair`)**:
When Clause-1 violations $(s_u = -1 \land s_v = \sigma)$ and Clause-2 violations
$(s_u = 1 \land s_v = -\sigma)$ on `pairFullSet W` can be repaired to relation-satisfying states
`coflipReconstruct σ y'` (`y' ∈ pairReducedSet W`) with margins $M_1 \ge 0$ and $M_2 \ge 0$,
pair contraction $s_u = \sigma s_v$ defines a valid `ReductionStep`. -/
theorem probing_pair_reductionStep {W : Type*}
    (F : (ℝ × (W → ℝ)) × ℝ → ℝ) (σ M₁ M₂ : ℝ)
    (hσ : isSpin σ)
    (hclause1 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((σ, s_W), -1) - 2 * M₁)
    (hclause2 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((-σ, s_W), 1) - 2 * M₂)
    (hlo : 0 ≤ probingPairLower M₁ M₂) :
    ReductionStep (pairFullSet W) F
      (pairReducedSet W) (reducedObj F (fun y => σ * y.1)) (coflipReconstruct σ) where
  maps_into y hy := ⟨hy, isSpin_mul hσ hy.1⟩
  energy_eq _ _ := rfl
  weak_dom := by
    rintro ⟨⟨s_v, s_W⟩, s_u⟩ ⟨⟨hs_v, hs_W⟩, hs_u⟩
    dsimp at hs_v hs_W hs_u
    by_cases hrel : s_u = σ * s_v
    · refine ⟨(s_v, s_W), ⟨hs_v, hs_W⟩, ?_⟩
      unfold reducedObj
      dsimp
      rw [← hrel]
    · have hpart := (probing_pair_violation_iff hs_u hs_v hσ).mp hrel
      unfold probingPairLower at hlo
      have hM₁ : 0 ≤ M₁ := le_trans hlo (min_le_left _ _)
      have hM₂ : 0 ≤ M₂ := le_trans hlo (min_le_right _ _)
      rcases hpart with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rcases hclause1 s_W hs_W with ⟨y', hy', hE⟩
        refine ⟨y', hy', ?_⟩
        unfold coflipReconstruct reconstruct at hE
        unfold reducedObj
        dsimp at hE ⊢
        rw [hu, hv]
        linarith
      · rcases hclause2 s_W hs_W with ⟨y', hy', hE⟩
        refine ⟨y', hy', ?_⟩
        unfold coflipReconstruct reconstruct at hE
        unfold reducedObj
        dsimp at hE ⊢
        rw [hu, hv]
        linarith

/-- **Theorem 7 (Part 4D — Compositional `StrongReductionStep` Bridge for `:probing_pair`)**:
When `0 < probingPairLower M₁ M₂` (`M₁ > 0` and `M₂ > 0`), `:probing_pair` pair contraction
$s_u = \sigma s_v$ defines a `StrongReductionStep` whose reconstruction map `coflipReconstruct σ`
is surjective onto all global minimizers of $F$ on `pairFullSet W`. -/
theorem probing_pair_strongReductionStep {W : Type*}
    (F : (ℝ × (W → ℝ)) × ℝ → ℝ) (σ M₁ M₂ : ℝ)
    (hσ : isSpin σ)
    (hclause1 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((σ, s_W), -1) - 2 * M₁)
    (hclause2 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((-σ, s_W), 1) - 2 * M₂)
    (hlo : 0 < probingPairLower M₁ M₂) :
    StrongReductionStep (pairFullSet W) F
      (pairReducedSet W) (reducedObj F (fun y => σ * y.1)) (coflipReconstruct σ) where
  toReductionStep :=
    probing_pair_reductionStep F σ M₁ M₂ hσ hclause1 hclause2 (le_of_lt hlo)
  surj_on_min := by
    rintro ⟨⟨s_v, s_W⟩, s_u⟩ ⟨⟨⟨hs_v, hs_W⟩, hs_u⟩, hmin⟩
    dsimp at hs_v hs_W hs_u
    by_cases hrel : s_u = σ * s_v
    · refine ⟨(s_v, s_W), ⟨⟨hs_v, hs_W⟩, ?_⟩, ?_⟩
      · intro y' hy'
        have hx' : coflipReconstruct σ y' ∈ pairFullSet W :=
          ⟨hy', isSpin_mul hσ hy'.1⟩
        have hle := hmin (coflipReconstruct σ y') hx'
        unfold coflipReconstruct reconstruct at hle
        unfold reducedObj
        dsimp
        rw [← hrel]
        exact hle
      · unfold coflipReconstruct reconstruct
        dsimp
        rw [← hrel]
    · exfalso
      have hpart := (probing_pair_violation_iff hs_u hs_v hσ).mp hrel
      unfold probingPairLower at hlo
      have hM₁ : 0 < M₁ := lt_of_lt_of_le hlo (min_le_left _ _)
      have hM₂ : 0 < M₂ := lt_of_lt_of_le hlo (min_le_right _ _)
      rcases hpart with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rcases hclause1 s_W hs_W with ⟨y', hy', hE⟩
        have hx' : coflipReconstruct σ y' ∈ pairFullSet W :=
          ⟨hy', isSpin_mul hσ hy'.1⟩
        have hle := hmin (coflipReconstruct σ y') hx'
        rw [hu, hv] at hle
        linarith
      · rcases hclause2 s_W hs_W with ⟨y', hy', hE⟩
        have hx' : coflipReconstruct σ y' ∈ pairFullSet W :=
          ⟨hy', isSpin_mul hσ hy'.1⟩
        have hle := hmin (coflipReconstruct σ y') hx'
        rw [hu, hv] at hle
        linarith

/-- **Corollary (Global Minimum Preservation under `:probing_pair`)**:
Under the hypotheses of `probing_pair_reductionStep`, any global minimizer of
`reducedObj F (fun y => σ * y.1)` on `pairReducedSet W` reconstructs via `coflipReconstruct σ` to
a global minimizer of `F` on `pairFullSet W` with identical objective value. -/
theorem probing_pair_preserves_global_min {W : Type*}
    (F : (ℝ × (W → ℝ)) × ℝ → ℝ) (σ M₁ M₂ : ℝ)
    (hσ : isSpin σ)
    (hclause1 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((σ, s_W), -1) - 2 * M₁)
    (hclause2 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((-σ, s_W), 1) - 2 * M₂)
    (hlo : 0 ≤ probingPairLower M₁ M₂)
    {y : ℝ × (W → ℝ)}
    (hy : IsGlobalMin (pairReducedSet W) (reducedObj F (fun y => σ * y.1)) y) :
    IsGlobalMin (pairFullSet W) F (coflipReconstruct σ y) ∧
      F (coflipReconstruct σ y) = reducedObj F (fun y => σ * y.1) y :=
  (probing_pair_reductionStep F σ M₁ M₂ hσ hclause1 hclause2 hlo).preserves_global_min hy

/-- **Corollary (Exact Bijection on Global Minimizers under Strong `:probing_pair`)**:
When `0 < probingPairLower M₁ M₂`, the set of global minimizers of `F` on `pairFullSet W` is the
exact image under `coflipReconstruct σ` of the set of global minimizers of
`reducedObj F (fun y => σ * y.1)` on `pairReducedSet W`. -/
theorem probing_pair_strong_image_global_min_eq {W : Type*}
    (F : (ℝ × (W → ℝ)) × ℝ → ℝ) (σ M₁ M₂ : ℝ)
    (hσ : isSpin σ)
    (hclause1 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((σ, s_W), -1) - 2 * M₁)
    (hclause2 : ∀ s_W : W → ℝ, (∀ w, isSpin (s_W w)) →
      ∃ y' ∈ pairReducedSet W,
        F (coflipReconstruct σ y') ≤ F ((-σ, s_W), 1) - 2 * M₂)
    (hlo : 0 < probingPairLower M₁ M₂) :
    {x | IsGlobalMin (pairFullSet W) F x} =
      coflipReconstruct σ ''
        {y | IsGlobalMin (pairReducedSet W) (reducedObj F (fun y => σ * y.1)) y} :=
  (probing_pair_strongReductionStep F σ M₁ M₂ hσ hclause1 hclause2 hlo).image_global_min_eq

end QUBOPreprocessing
