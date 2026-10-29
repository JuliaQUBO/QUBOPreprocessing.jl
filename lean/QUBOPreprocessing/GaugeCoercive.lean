import Mathlib

/-!
# Proposition 1: Gauge Invariance and Ising Coercive-Field Dominance

This module formalizes Proposition 1 of `QUBOPreprocessing.jl` (`docs/src/dominance.md`):
1. The exact affine bijection $s_i = 2 x_i - 1$ ($x_i = (s_i + 1)/2$) between Boolean variables
   $x_i \in \{0, 1\}$ and Ising spins $s_i \in \{-1, +1\}$.
2. The exact algebraic identity connecting the QUBO objective
   $F_{\mathrm{bool}}(x) = c_{\mathrm{bool}} + \sum_i a_i x_i + \frac{1}{2}\sum_{i, j} B_{ij} x_i x_j$
   and the Ising spin Hamiltonian
   $E_{\mathrm{spin}}(s) = c_{\mathrm{spin}} + \sum_i h_i s_i + \frac{1}{2}\sum_{i, j} J_{ij} s_i s_j$
   under $J_{ij} = B_{ij} / 4$, $h_i = a_i / 2 + \sum_j B_{ij} / 4$, and
   $c_{\mathrm{spin}} = c_{\mathrm{bool}} + \sum_i a_i / 2 + \frac{1}{8}\sum_{i, j} B_{ij}$.
3. Invariance of the Ising Hamiltonian, field magnitudes $|h_i|$, coupling magnitudes $|J_{ij}|$,
   $\ell_1$ interaction norms $\sum_{j \neq i} |J_{ij}|$, and coercive-field ratios
   $\rho_i = |h_i| / \sum_{j \neq i} |J_{ij}|$ under arbitrary spin-flip gauge transformations
   $s_i = g_i t_i$ with $g_i \in \{-1, +1\}$.
4. Exact equivalence between the Hammer–Hansen–Simeone (1984) QUBO first-order persistence criteria
   and the Ising coercive-field criteria $\pm h_i > \sum_{j \neq i} |J_{ij}|$, together with the
   soundness theorem showing that a coercive field strictly fixes $s_i^* = -\operatorname{sgn}(h_i)$
   across all neighbor spin configurations.
-/

open scoped BigOperators

namespace QUBOPreprocessing

/-- A real number lies in the Boolean domain $\{0, 1\}$. -/
def isBool (x : ℝ) : Prop := x = 0 ∨ x = 1

/-- A real number lies in the Ising spin domain $\{-1, +1\}$. -/
def isSpin (s : ℝ) : Prop := s = -1 ∨ s = 1

/-- Affine map from Boolean $x \in \{0, 1\}$ to Ising spin $s = 2x - 1 \in \{-1, +1\}$. -/
noncomputable def boolToSpin (x : ℝ) : ℝ := 2 * x - 1

/-- Inverse affine map from Ising spin $s \in \{-1, +1\}$ to Boolean $x = (s + 1) / 2 \in \{0, 1\}$. -/
noncomputable def spinToBool (s : ℝ) : ℝ := (s + 1) / 2

@[simp]
theorem spinToBool_boolToSpin (x : ℝ) : spinToBool (boolToSpin x) = x := by
  unfold spinToBool boolToSpin
  ring

@[simp]
theorem boolToSpin_spinToBool (s : ℝ) : boolToSpin (spinToBool s) = s := by
  unfold boolToSpin spinToBool
  ring

theorem isSpin_boolToSpin_iff (x : ℝ) : isSpin (boolToSpin x) ↔ isBool x := by
  unfold isSpin isBool boolToSpin
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · left; ring
    · right; ring

theorem isBool_spinToBool_iff (s : ℝ) : isBool (spinToBool s) ↔ isSpin s := by
  unfold isBool isSpin spinToBool
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · left; ring
    · right; ring

theorem isSpin_sq_eq_one {s : ℝ} (hs : isSpin s) : s ^ 2 = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem isSpin_mul_self {s : ℝ} (hs : isSpin s) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem abs_of_isSpin {s : ℝ} (hs : isSpin s) : |s| = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem isSpin_neg {s : ℝ} (hs : isSpin s) : isSpin (-s) := by
  rcases hs with rfl | rfl
  · right; ring
  · left; ring

theorem isSpin_mul {g s : ℝ} (hg : isSpin g) (hs : isSpin s) : isSpin (g * s) := by
  rcases hg with rfl | rfl <;> rcases hs with rfl | rfl
  · right; ring
  · left; ring
  · left; ring
  · right; ring

/-- Single-variable linear term conversion under $x = (s + 1) / 2$. -/
theorem linear_term_spin_eq (a s : ℝ) :
    a * spinToBool s = (a / 2) * s + a / 2 := by
  unfold spinToBool
  ring

/-- Pairwise bilinear term conversion under $x_i = (s_i + 1) / 2$ and $x_j = (s_j + 1) / 2$. -/
theorem quadratic_term_spin_eq (b s_i s_j : ℝ) :
    b * spinToBool s_i * spinToBool s_j =
      (b / 4) * s_i * s_j + (b / 4) * s_i + (b / 4) * s_j + b / 4 := by
  unfold spinToBool
  ring

/-- Finite-dimensional QUBO objective with symmetric off-diagonal interaction matrix $B$:
$F_{\mathrm{bool}}(x) = c + \sum_i a_i x_i + \frac{1}{2}\sum_{i,j} B_{ij} x_i x_j$. -/
noncomputable def quboEnergy {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  c + (∑ i, a i * x i) + (1 / 2) * ∑ i, ∑ j, B i j * x i * x j

/-- Finite-dimensional Ising Hamiltonian:
$E_{\mathrm{spin}}(s) = c_{\mathrm{spin}} + \sum_i h_i s_i + \frac{1}{2}\sum_{i,j} J_{ij} s_i s_j$. -/
noncomputable def isingEnergy {n : ℕ} (c_spin : ℝ) (h : Fin n → ℝ) (J : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) : ℝ :=
  c_spin + (∑ i, h i * s i) + (1 / 2) * ∑ i, ∑ j, J i j * s i * s j

/-- Ising coupling induced by QUBO interaction matrix: $J_{ij} = B_{ij} / 4$. -/
noncomputable def isingJ {n : ℕ} (B : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  B i j / 4

/-- Ising external field induced by QUBO coefficients: $h_i = a_i / 2 + \sum_j B_{ij} / 4$. -/
noncomputable def isingH {n : ℕ} (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  a i / 2 + ∑ j, B i j / 4

/-- Ising constant offset induced by QUBO coefficients:
$c_{\mathrm{spin}} = c + \sum_i a_i / 2 + \frac{1}{8}\sum_{i,j} B_{ij}$. -/
noncomputable def isingOffset {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ) : ℝ :=
  c + (∑ i, a i / 2) + (1 / 8) * ∑ i, ∑ j, B i j

/-- Exact QUBO-to-Ising objective equivalence across $\mathbb{R}^n$ for any symmetric matrix $B$. -/
theorem quboEnergy_eq_isingEnergy {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ)
    (hSym : ∀ i j, B i j = B j i) (s : Fin n → ℝ) :
    quboEnergy c a B (fun i => spinToBool (s i)) =
      isingEnergy (isingOffset c a B) (isingH a B) (isingJ B) s := by
  unfold quboEnergy isingEnergy isingOffset isingH isingJ spinToBool
  have hlin :
      (∑ i, a i * ((s i + 1) / 2)) = (∑ i, (a i / 2) * s i) + ∑ i, a i / 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hquad_inner :
      ∀ i, (∑ j, B i j * ((s i + 1) / 2) * ((s j + 1) / 2)) =
        (∑ j, (B i j / 4) * s i * s j) +
        ((∑ j, (B i j / 4) * s i) +
        ((∑ j, (B i j / 4) * s j) +
        (∑ j, B i j / 4))) := by
    intro i
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hquad :
      (∑ i, ∑ j, B i j * ((s i + 1) / 2) * ((s j + 1) / 2)) =
        (∑ i, ∑ j, (B i j / 4) * s i * s j) +
        ((∑ i, ∑ j, (B i j / 4) * s i) +
        ((∑ i, ∑ j, (B i j / 4) * s j) +
        (∑ i, ∑ j, B i j / 4))) := by
    simp only [hquad_inner, Finset.sum_add_distrib]
  have hswap :
      (∑ i, ∑ j, (B i j / 4) * s j) = ∑ i, ∑ j, (B i j / 4) * s i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hSym j i]
  have hfield :
      (∑ i, (a i / 2 + ∑ j, B i j / 4) * s i) =
        (∑ i, (a i / 2) * s i) + ∑ i, ∑ j, (B i j / 4) * s i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [add_mul, Finset.sum_mul]
  have hconst :
      (1 / 2 : ℝ) * (∑ i, ∑ j, B i j / 4) = (1 / 8) * ∑ i, ∑ j, B i j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hlin, hquad, hswap, hfield, ← hconst]
  ring

/-- Gauge-transformed spin vector $(g \odot s)_i = g_i s_i$. -/
def gaugeSpin {n : ℕ} (g s : Fin n → ℝ) (i : Fin n) : ℝ := g i * s i

/-- Gauge-transformed field vector $h'_i = g_i h_i$. -/
def gaugeH {n : ℕ} (g h : Fin n → ℝ) (i : Fin n) : ℝ := g i * h i

/-- Gauge-transformed coupling matrix $J'_{ij} = g_i g_j J_{ij}$. -/
def gaugeJ {n : ℕ} (g : Fin n → ℝ) (J : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  g i * g j * J i j

/-- The Ising Hamiltonian is strictly invariant under any spin-flip gauge transformation
$g \in \{-1, +1\}^n$. -/
theorem isingEnergy_gauge_invariant {n : ℕ} (c_spin : ℝ) (h : Fin n → ℝ)
    (J : Fin n → Fin n → ℝ) (g s : Fin n → ℝ) (hg : ∀ i, isSpin (g i)) :
    isingEnergy c_spin (gaugeH g h) (gaugeJ g J) (gaugeSpin g s) =
      isingEnergy c_spin h J s := by
  unfold isingEnergy gaugeH gaugeJ gaugeSpin
  have h1 : (∑ i, g i * h i * (g i * s i)) = ∑ i, h i * s i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hgi : g i * g i = 1 := isSpin_mul_self (hg i)
    calc
      g i * h i * (g i * s i) = (g i * g i) * (h i * s i) := by ring
      _ = h i * s i := by rw [hgi, one_mul]
  have h2 :
      (∑ i, ∑ j, g i * g j * J i j * (g i * s i) * (g j * s j)) =
        ∑ i, ∑ j, J i j * s i * s j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hgi : g i * g i = 1 := isSpin_mul_self (hg i)
    have hgj : g j * g j = 1 := isSpin_mul_self (hg j)
    calc
      g i * g j * J i j * (g i * s i) * (g j * s j)
        = (g i * g i) * (g j * g j) * (J i j * s i * s j) := by ring
      _ = J i j * s i * s j := by rw [hgi, hgj, one_mul, one_mul]
  rw [h1, h2]

theorem abs_gaugeH_eq {n : ℕ} (g h : Fin n → ℝ) (i : Fin n) (hg : isSpin (g i)) :
    |gaugeH g h i| = |h i| := by
  unfold gaugeH
  rw [abs_mul, abs_of_isSpin hg, one_mul]

theorem abs_gaugeJ_eq {n : ℕ} (g : Fin n → ℝ) (J : Fin n → Fin n → ℝ) (i j : Fin n)
    (hgi : isSpin (g i)) (hgj : isSpin (g j)) :
    |gaugeJ g J i j| = |J i j| := by
  unfold gaugeJ
  rw [abs_mul, abs_mul, abs_of_isSpin hgi, abs_of_isSpin hgj, one_mul, one_mul]

/-- The $\ell_1$ interaction norm $\sum_{j \neq i} |J_{ij}|$ at spin $i$. -/
noncomputable def couplingNorm1 {n : ℕ} (J : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, |J i j|

/-- The coercive-field dominance ratio $\rho_i = |h_i| / \sum_{j \neq i} |J_{ij}|$. -/
noncomputable def coerciveRatio {n : ℕ} (h : Fin n → ℝ) (J : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |h i| / couplingNorm1 J i

/-- Gauge invariance of the $\ell_1$ interaction norm $\sum_{j \neq i} |J_{ij}|$. -/
theorem couplingNorm1_gauge_invariant {n : ℕ} (g : Fin n → ℝ) (J : Fin n → Fin n → ℝ)
    (i : Fin n) (hg : ∀ j, isSpin (g j)) :
    couplingNorm1 (gaugeJ g J) i = couplingNorm1 J i := by
  unfold couplingNorm1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact abs_gaugeJ_eq g J i j (hg i) (hg j)

/-- Gauge invariance of the coercive-field ratio $\rho_i = |h_i| / \sum_{j \neq i} |J_{ij}|$. -/
theorem coerciveRatio_gauge_invariant {n : ℕ} (g h : Fin n → ℝ) (J : Fin n → Fin n → ℝ)
    (i : Fin n) (hg : ∀ j, isSpin (g j)) :
    coerciveRatio (gaugeH g h) (gaugeJ g J) i = coerciveRatio h J i := by
  unfold coerciveRatio
  rw [abs_gaugeH_eq g h i (hg i), couplingNorm1_gauge_invariant g J i hg]

/-- Exact identity relating $\min(0, b)$ to $b/4 - |b/4|$. -/
theorem min_zero_eq_two_mul_quarter_sub_abs (b : ℝ) :
    min 0 b = 2 * (b / 4 - |b / 4|) := by
  rcases le_total 0 b with hb | hb
  · have hb4 : 0 ≤ b / 4 := by linarith
    rw [min_eq_left hb, abs_of_nonneg hb4]
    ring
  · have hb4 : b / 4 ≤ 0 := by linarith
    rw [min_eq_right hb, abs_of_nonpos hb4]
    ring

/-- Exact identity relating $\max(0, b)$ to $b/4 + |b/4|$. -/
theorem max_zero_eq_two_mul_quarter_add_abs (b : ℝ) :
    max 0 b = 2 * (b / 4 + |b / 4|) := by
  rcases le_total 0 b with hb | hb
  · have hb4 : 0 ≤ b / 4 := by linarith
    rw [max_eq_right hb, abs_of_nonneg hb4]
    ring
  · have hb4 : b / 4 ≤ 0 := by linarith
    rw [max_eq_left hb, abs_of_nonpos hb4]
    ring

/-- Decomposition of $h_i$ over $j \neq i$ when $B_{ii} = 0$. -/
theorem isingH_eq_erase {n : ℕ} (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ) (i : Fin n)
    (hDiag : B i i = 0) :
    isingH a B i = a i / 2 + ∑ j ∈ Finset.univ.erase i, B i j / 4 := by
  unfold isingH
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hDiag]
  ring

/-- The Hammer–Hansen–Simeone lower gradient bound $\underline{g}_i = a_i + \sum_{j \neq i} \min(0, B_{ij})$
equals $2 (h_i - \sum_{j \neq i} |J_{ij}|)$. -/
theorem qubo_lower_grad_eq_two_mul_ising_margin {n : ℕ} (a : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ) (i : Fin n) (hDiag : B i i = 0) :
    a i + (∑ j ∈ Finset.univ.erase i, min 0 (B i j)) =
      2 * (isingH a B i - couplingNorm1 (isingJ B) i) := by
  rw [isingH_eq_erase a B i hDiag]
  unfold couplingNorm1 isingJ
  have hsum :
      (∑ j ∈ Finset.univ.erase i, min 0 (B i j)) =
        2 * ((∑ j ∈ Finset.univ.erase i, B i j / 4) -
          ∑ j ∈ Finset.univ.erase i, |B i j / 4|) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact min_zero_eq_two_mul_quarter_sub_abs (B i j)
  rw [hsum]
  ring

/-- The Hammer–Hansen–Simeone upper gradient bound $\overline{g}_i = a_i + \sum_{j \neq i} \max(0, B_{ij})$
equals $2 (h_i + \sum_{j \neq i} |J_{ij}|)$. -/
theorem qubo_upper_grad_eq_two_mul_ising_margin {n : ℕ} (a : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ) (i : Fin n) (hDiag : B i i = 0) :
    a i + (∑ j ∈ Finset.univ.erase i, max 0 (B i j)) =
      2 * (isingH a B i + couplingNorm1 (isingJ B) i) := by
  rw [isingH_eq_erase a B i hDiag]
  unfold couplingNorm1 isingJ
  have hsum :
      (∑ j ∈ Finset.univ.erase i, max 0 (B i j)) =
        2 * ((∑ j ∈ Finset.univ.erase i, B i j / 4) +
          ∑ j ∈ Finset.univ.erase i, |B i j / 4|) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact max_zero_eq_two_mul_quarter_add_abs (B i j)
  rw [hsum]
  ring

/-- **Proposition 1 (Part A)**: The QUBO zero-fixing persistence condition
$a_i + \sum_{j \neq i} \min(0, B_{ij}) > 0$ is equivalent to the positive Ising coercive-field
condition $h_i > \sum_{j \neq i} |J_{ij}|$. -/
theorem qubo_persist_zero_iff_ising_coercive_pos {n : ℕ} (a : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ) (i : Fin n) (hDiag : B i i = 0) :
    a i + (∑ j ∈ Finset.univ.erase i, min 0 (B i j)) > 0 ↔
      isingH a B i > couplingNorm1 (isingJ B) i := by
  rw [qubo_lower_grad_eq_two_mul_ising_margin a B i hDiag]
  constructor <;> intro h <;> linarith

/-- **Proposition 1 (Part B)**: The QUBO one-fixing persistence condition
$a_i + \sum_{j \neq i} \max(0, B_{ij}) < 0$ is equivalent to the negative Ising coercive-field
condition $-h_i > \sum_{j \neq i} |J_{ij}|$. -/
theorem qubo_persist_one_iff_ising_coercive_neg {n : ℕ} (a : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ) (i : Fin n) (hDiag : B i i = 0) :
    a i + (∑ j ∈ Finset.univ.erase i, max 0 (B i j)) < 0 ↔
      -isingH a B i > couplingNorm1 (isingJ B) i := by
  rw [qubo_upper_grad_eq_two_mul_ising_margin a B i hDiag]
  constructor <;> intro h <;> linarith

/-- Effective local field acting on spin $i$: $h_i + \sum_{j \neq i} J_{ij} s_j$. -/
noncomputable def localField {n : ℕ} (h : Fin n → ℝ) (J : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  h i + ∑ j ∈ Finset.univ.erase i, J i j * s j

/-- Triangle inequality bound on neighbor interactions when all neighbor spins lie in $\{-1, +1\}$. -/
theorem abs_neighbor_sum_le_couplingNorm1 {n : ℕ} (J : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) (hs : ∀ j ∈ Finset.univ.erase i, isSpin (s j)) :
    |∑ j ∈ Finset.univ.erase i, J i j * s j| ≤ couplingNorm1 J i := by
  unfold couplingNorm1
  calc
    |∑ j ∈ Finset.univ.erase i, J i j * s j|
      ≤ ∑ j ∈ Finset.univ.erase i, |J i j * s j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.univ.erase i, |J i j| := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [abs_mul, abs_of_isSpin (hs j hj), mul_one]

/-- If $h_i > \sum_{j \neq i} |J_{ij}|$, the effective local field at spin $i$ is strictly positive
for every neighbor configuration $s_j \in \{-1, +1\}$, so flipping $s_i$ from $+1$ to $-1$
strictly lowers the single-spin contribution $s_i \cdot \mathrm{localField}_i(s)$. -/
theorem coercive_pos_strictly_favors_neg_one {n : ℕ} (h : Fin n → ℝ)
    (J : Fin n → Fin n → ℝ) (s : Fin n → ℝ) (i : Fin n)
    (hs : ∀ j ∈ Finset.univ.erase i, isSpin (s j))
    (hcoercive : h i > couplingNorm1 J i) :
    (-1 : ℝ) * localField h J s i < (1 : ℝ) * localField h J s i := by
  unfold localField
  have habs := abs_neighbor_sum_le_couplingNorm1 J s i hs
  have hlow : -couplingNorm1 J i ≤ ∑ j ∈ Finset.univ.erase i, J i j * s j :=
    neg_le_of_abs_le habs
  linarith

/-- If $-h_i > \sum_{j \neq i} |J_{ij}|$, the effective local field at spin $i$ is strictly negative
for every neighbor configuration $s_j \in \{-1, +1\}$, so flipping $s_i$ from $-1$ to $+1$
strictly lowers the single-spin contribution $s_i \cdot \mathrm{localField}_i(s)$. -/
theorem coercive_neg_strictly_favors_pos_one {n : ℕ} (h : Fin n → ℝ)
    (J : Fin n → Fin n → ℝ) (s : Fin n → ℝ) (i : Fin n)
    (hs : ∀ j ∈ Finset.univ.erase i, isSpin (s j))
    (hcoercive : -h i > couplingNorm1 J i) :
    (1 : ℝ) * localField h J s i < (-1 : ℝ) * localField h J s i := by
  unfold localField
  have habs := abs_neighbor_sum_le_couplingNorm1 J s i hs
  have hhigh : ∑ j ∈ Finset.univ.erase i, J i j * s j ≤ couplingNorm1 J i :=
    le_of_abs_le habs
  linarith

end QUBOPreprocessing
