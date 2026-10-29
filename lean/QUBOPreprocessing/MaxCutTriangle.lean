import Mathlib
import QUBOPreprocessing.GaugeCoercive

/-!
# Proposition 3: External-Degree-Aware Max-Cut Triangle Dominance and Multicut Counterexample

This module formalizes Proposition 3 of `QUBOPreprocessing.jl` (`docs/src/dominance.md` and
`src/maxcut.jl` / `test/maxcut.jl`):
1. The local 3-spin triangle Hamiltonian `triEnergy` with internal couplings $(J_{ab}, J_{ac}, J_{bc})$
   and effective external fields $(e_a, e_b, e_c)$ (representing reference-node fields $h_u$ plus
   couplings to spins outside $\{a, b, c\}$).
2. Exact energy-change identities for the single-spin flip $s_a \mapsto -s_a$ (`triEnergy_flip_a`)
   and the joint triangle co-flip $(s_a, s_c) \mapsto (-s_a, -s_c)$ (`triEnergy_flip_ac`).
3. The external-degree-aware triangle slack $\gamma_{abc}(\sigma)$ (`gammaTriangle`), its closed
   forms in the supportive ($\sigma J_{ac} J_{bc} \ge 0$), frustrated ($\sigma J_{ac} J_{bc} \le 0$),
   and zero-residual ($R_c = 0$) regimes, and **Proposition 3** (`maxcut_triangle_dominance_sound`
   and `maxcut_triangle_strict_improvement`): whenever $-\sigma J_{ab} + \gamma_{abc}(\sigma) - R_a > 0$,
   every violating spin configuration with $s_a = -\sigma s_b$ is strictly improved by either
   $s_a \mapsto -s_a$ or $(s_a, s_c) \mapsto (-s_a, -s_c)$.
4. The formal refutation (`uncorrected_multicut_triangle_counterexample`) of the uncorrected
   multicut triangle rule $-\sigma J_{ab} + \min(|J_{ac}|, |J_{bc}|) - R_a > 0$ on signed weighted
   Max-Cut / Ising models with nonzero external vertex slack $R_c > 0$.
-/

namespace QUBOPreprocessing

/-- Local Ising energy of a triangle $\{a, b, c\}$ with internal couplings $(J_{ab}, J_{ac}, J_{bc})$
and effective external fields $(e_a, e_b, e_c)$ acting on $(s_a, s_b, s_c)$. -/
def triEnergy (J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c : ℝ) : ℝ :=
  J_ab * s_a * s_b + J_ac * s_a * s_c + J_bc * s_b * s_c +
    e_a * s_a + e_b * s_b + e_c * s_c

/-- Energy reduction from the single-spin flip $s_a \mapsto -s_a$. -/
theorem triEnergy_flip_a (J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c : ℝ) :
    triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
      triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c =
      2 * (J_ab * s_a * s_b + J_ac * s_a * s_c + e_a * s_a) := by
  unfold triEnergy
  ring

/-- Energy reduction from the joint co-flip $(s_a, s_c) \mapsto (-s_a, -s_c)$. -/
theorem triEnergy_flip_ac (J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c : ℝ) :
    triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
      triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c) =
      2 * (J_ab * s_a * s_b + J_bc * s_b * s_c + e_a * s_a + e_c * s_c) := by
  unfold triEnergy
  ring

/-- External-degree-aware triangle slack $\gamma_{abc}(\sigma)$ for candidate parity
$s_a = \sigma s_b$, defined as the worst-case over $t = s_a s_c \in \{-1, +1\}$ of the best move
between flipping $s_a$ alone (gain $J_{ac} t$) and co-flipping $(s_a, s_c)$ (guaranteed gain
$-\sigma J_{bc} t - R_c$). -/
noncomputable def gammaTriangle (σ J_ac J_bc R_c : ℝ) : ℝ :=
  min (max J_ac (-σ * J_bc - R_c)) (max (-J_ac) (σ * J_bc - R_c))

/-- Helper identity for nonnegative $A, B, R_c$ in the supportive triangle regime. -/
theorem min_max_nonneg_supportive {A B R_c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hRc : 0 ≤ R_c) :
    min (max A (-B - R_c)) (max (-A) (B - R_c)) = max (-A) (min A (B - R_c)) := by
  have h1 : max A (-B - R_c) = A := max_eq_left (by linarith)
  rw [h1]
  rcases le_total A (B - R_c) with hle | hle
  · have h2 : max (-A) (B - R_c) = B - R_c := max_eq_right (by linarith)
    have h3 : min A (B - R_c) = A := min_eq_left hle
    have h4 : max (-A) A = A := max_eq_right (by linarith)
    rw [h2, h3, h4]
  · have h3 : min A (B - R_c) = B - R_c := min_eq_right hle
    rw [h3]
    rcases le_total (-A) (B - R_c) with hle2 | hle2
    · rw [max_eq_right hle2, min_eq_right hle]
    · rw [max_eq_left hle2, min_eq_right (by linarith)]

/-- Helper identity for nonnegative $A, B$ in the frustrated triangle regime. -/
theorem min_max_nonneg_frustrated {A B R_c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min (max A (B - R_c)) (max (-A) (-B - R_c)) = -min A (B + R_c) := by
  have hle_max : max (-A) (-B - R_c) ≤ max A (B - R_c) := by
    refine max_le ?_ ?_
    · exact le_trans (by linarith : -A ≤ A) (le_max_left _ _)
    · exact le_trans (by linarith : -B - R_c ≤ B - R_c) (le_max_right _ _)
  rw [min_eq_right hle_max]
  rcases le_total A (B + R_c) with hle | hle
  · rw [min_eq_left hle, max_eq_left (by linarith)]
  · rw [min_eq_right hle, max_eq_right (by linarith)]
    ring

/-- Closed-form expression for `gammaTriangle` in the supportive triangle regime
$\sigma J_{ac} J_{bc} \ge 0$ when $\sigma \in \{-1, +1\}$ and $R_c \ge 0$:
$\gamma_{abc}(\sigma) = \max(-|J_{ac}|, \min(|J_{ac}|, |J_{bc}| - R_c))$. -/
theorem gammaTriangle_supportive {σ J_ac J_bc R_c : ℝ}
    (hσ : isSpin σ) (hRc : 0 ≤ R_c) (hSup : 0 ≤ σ * J_ac * J_bc) :
    gammaTriangle σ J_ac J_bc R_c = max (-|J_ac|) (min |J_ac| (|J_bc| - R_c)) := by
  unfold gammaTriangle
  have hprod : 0 ≤ J_ac * (σ * J_bc) := by linarith
  have habs_bc : |σ * J_bc| = |J_bc| := by
    rw [abs_mul, abs_of_isSpin hσ, one_mul]
  rw [← habs_bc]
  rcases mul_nonneg_iff.mp hprod with ⟨hJac, hJbc⟩ | ⟨hJac, hJbc⟩
  · rw [abs_of_nonneg hJac, abs_of_nonneg hJbc]
    have hEq : max J_ac (-σ * J_bc - R_c) = max J_ac (-(σ * J_bc) - R_c) := by ring_nf
    rw [hEq]
    exact min_max_nonneg_supportive hJac hJbc hRc
  · rw [abs_of_nonpos hJac, abs_of_nonpos hJbc, min_comm]
    have hEq1 : max (-J_ac) (σ * J_bc - R_c) = max (-J_ac) (-( -(σ * J_bc) ) - R_c) := by ring_nf
    have hEq2 : max J_ac (-σ * J_bc - R_c) = max (-(-J_ac)) (-(σ * J_bc) - R_c) := by ring_nf
    rw [hEq1, hEq2]
    exact min_max_nonneg_supportive (by linarith : 0 ≤ -J_ac) (by linarith : 0 ≤ -(σ * J_bc)) hRc

/-- Closed-form expression for `gammaTriangle` in the frustrated triangle regime
$\sigma J_{ac} J_{bc} \le 0$ when $\sigma \in \{-1, +1\}$:
$\gamma_{abc}(\sigma) = -\min(|J_{ac}|, |J_{bc}| + R_c)$. -/
theorem gammaTriangle_frustrated {σ J_ac J_bc R_c : ℝ}
    (hσ : isSpin σ) (hFrust : σ * J_ac * J_bc ≤ 0) :
    gammaTriangle σ J_ac J_bc R_c = -min |J_ac| (|J_bc| + R_c) := by
  unfold gammaTriangle
  have hprod : J_ac * (σ * J_bc) ≤ 0 := by linarith
  have habs_bc : |σ * J_bc| = |J_bc| := by
    rw [abs_mul, abs_of_isSpin hσ, one_mul]
  rw [← habs_bc]
  rcases mul_nonpos_iff.mp hprod with ⟨hJac, hJbc⟩ | ⟨hJac, hJbc⟩
  · rw [abs_of_nonneg hJac, abs_of_nonpos hJbc]
    have hEq1 : max J_ac (-σ * J_bc - R_c) = max J_ac (-(σ * J_bc) - R_c) := by ring_nf
    have hEq2 : max (-J_ac) (σ * J_bc - R_c) = max (-J_ac) (-( -(σ * J_bc) ) - R_c) := by ring_nf
    rw [hEq1, hEq2]
    exact min_max_nonneg_frustrated hJac (by linarith : 0 ≤ -(σ * J_bc))
  · rw [abs_of_nonpos hJac, abs_of_nonneg hJbc, min_comm]
    have hEq1 : max J_ac (-σ * J_bc - R_c) = max (-(-J_ac)) (-(σ * J_bc) - R_c) := by ring_nf
    rw [hEq1]
    exact min_max_nonneg_frustrated (by linarith : 0 ≤ -J_ac) hJbc

/-- When $R_c = 0$ and the triangle is supportive ($\sigma J_{ac} J_{bc} \ge 0$), `gammaTriangle`
reduces to the pure triangle slack $\min(|J_{ac}|, |J_{bc}|)$. -/
theorem gammaTriangle_zero_residual {σ J_ac J_bc : ℝ}
    (hσ : isSpin σ) (hSup : 0 ≤ σ * J_ac * J_bc) :
    gammaTriangle σ J_ac J_bc 0 = min |J_ac| |J_bc| := by
  rw [gammaTriangle_supportive hσ le_rfl hSup, sub_zero]
  have hnonneg : 0 ≤ min |J_ac| |J_bc| := le_min (abs_nonneg _) (abs_nonneg _)
  have hle : -|J_ac| ≤ min |J_ac| |J_bc| := by
    have : -|J_ac| ≤ 0 := by linarith [abs_nonneg J_ac]
    exact le_trans this hnonneg
  exact max_eq_right hle

/-- **Proposition 3 (Soundness of External-Degree-Aware Max-Cut Triangle Dominance)**:
For any spin configuration $(s_a, s_b, s_c) \in \{-1, +1\}^3$ and parity $\sigma \in \{-1, +1\}$
in a violating state $s_a = -\sigma s_b$ with $|e_a| \le R_a$ and $|e_c| \le R_c$, the better of
the single-spin flip $s_a \mapsto -s_a$ and the joint co-flip $(s_a, s_c) \mapsto (-s_a, -s_c)$
lowers `triEnergy` by at least $2 (-\sigma J_{ab} + \gamma_{abc}(\sigma) - R_a)$. -/
theorem maxcut_triangle_dominance_sound
    (J_ab J_ac J_bc e_a e_b e_c R_a R_c σ s_a s_b s_c : ℝ)
    (hσ : isSpin σ) (hsa : isSpin s_a) (hsb : isSpin s_b) (hsc : isSpin s_c)
    (hviol : s_a = -σ * s_b)
    (hea : |e_a| ≤ R_a) (hec : |e_c| ≤ R_c) :
    min (triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c)
        (triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c)) ≤
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
        2 * (-σ * J_ab + gammaTriangle σ J_ac J_bc R_c - R_a) := by
  have hsasb : s_a * s_b = -σ := by
    rw [hviol]
    have hsb2 : s_b * s_b = 1 := isSpin_mul_self hsb
    calc
      (-σ * s_b) * s_b = -σ * (s_b * s_b) := by ring
      _ = -σ := by rw [hsb2, mul_one]
  have hsbsa : s_b = -σ * s_a := by
    rw [hviol]
    have hσ2 : σ * σ = 1 := isSpin_mul_self hσ
    calc
      s_b = (σ * σ) * s_b := by rw [hσ2, one_mul]
      _ = -σ * (-σ * s_b) := by ring
  have hea_bound : -R_a ≤ e_a * s_a := by
    have : |e_a * s_a| ≤ R_a := by
      rw [abs_mul, abs_of_isSpin hsa, mul_one]
      exact hea
    exact neg_le_of_abs_le this
  have hec_bound : -R_c ≤ e_c * s_c := by
    have : |e_c * s_c| ≤ R_c := by
      rw [abs_mul, abs_of_isSpin hsc, mul_one]
      exact hec
    exact neg_le_of_abs_le this
  have hsasc : isSpin (s_a * s_c) := isSpin_mul hsa hsc
  have hbc : J_bc * s_b * s_c = -σ * J_bc * (s_a * s_c) := by
    rw [hsbsa]
    ring
  have hflip1 :
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
        triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c =
        2 * (-σ * J_ab + J_ac * (s_a * s_c) + e_a * s_a) := by
    calc
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
          triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c
        = 2 * (J_ab * (s_a * s_b) + J_ac * (s_a * s_c) + e_a * s_a) := by
            rw [triEnergy_flip_a]; ring
      _ = 2 * (-σ * J_ab + J_ac * (s_a * s_c) + e_a * s_a) := by
            rw [hsasb]; ring
  have hflip2 :
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
        triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c) =
        2 * (-σ * J_ab - σ * J_bc * (s_a * s_c) + e_a * s_a + e_c * s_c) := by
    calc
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c -
          triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c)
        = 2 * (J_ab * (s_a * s_b) + J_bc * s_b * s_c + e_a * s_a + e_c * s_c) := by
            rw [triEnergy_flip_ac]; ring
      _ = 2 * (-σ * J_ab - σ * J_bc * (s_a * s_c) + e_a * s_a + e_c * s_c) := by
            rw [hsasb, hbc]; ring
  unfold gammaTriangle
  rcases hsasc with hprod | hprod
  · -- Case s_a * s_c = -1
    rw [hprod] at hflip1 hflip2
    have hgamma :
        min (max J_ac (-σ * J_bc - R_c)) (max (-J_ac) (σ * J_bc - R_c)) ≤
          max (-J_ac) (σ * J_bc - R_c) := min_le_right _ _
    rcases le_total (-J_ac) (σ * J_bc - R_c) with hbranch | hbranch
    · have hmax : max (-J_ac) (σ * J_bc - R_c) = σ * J_bc - R_c := max_eq_right hbranch
      refine le_trans (min_le_right _ _) ?_
      linarith
    · have hmax : max (-J_ac) (σ * J_bc - R_c) = -J_ac := max_eq_left hbranch
      refine le_trans (min_le_left _ _) ?_
      linarith
  · -- Case s_a * s_c = 1
    rw [hprod] at hflip1 hflip2
    have hgamma :
        min (max J_ac (-σ * J_bc - R_c)) (max (-J_ac) (σ * J_bc - R_c)) ≤
          max J_ac (-σ * J_bc - R_c) := min_le_left _ _
    rcases le_total J_ac (-σ * J_bc - R_c) with hbranch | hbranch
    · have hmax : max J_ac (-σ * J_bc - R_c) = -σ * J_bc - R_c := max_eq_right hbranch
      refine le_trans (min_le_right _ _) ?_
      linarith
    · have hmax : max J_ac (-σ * J_bc - R_c) = J_ac := max_eq_left hbranch
      refine le_trans (min_le_left _ _) ?_
      linarith

/-- **Proposition 3 (Strict Refutation of Violating Parity)**:
Whenever the external-degree-aware triangle margin $-\sigma J_{ab} + \gamma_{abc}(\sigma) - R_a > 0$,
every spin configuration with $s_a = -\sigma s_b$ is strictly suboptimal: either flipping $s_a$
alone or co-flipping $(s_a, s_c)$ yields a strictly lower energy. -/
theorem maxcut_triangle_strict_improvement
    (J_ab J_ac J_bc e_a e_b e_c R_a R_c σ s_a s_b s_c : ℝ)
    (hσ : isSpin σ) (hsa : isSpin s_a) (hsb : isSpin s_b) (hsc : isSpin s_c)
    (hviol : s_a = -σ * s_b)
    (hea : |e_a| ≤ R_a) (hec : |e_c| ≤ R_c)
    (hmargin : -σ * J_ab + gammaTriangle σ J_ac J_bc R_c - R_a > 0) :
    triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c <
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c ∨
    triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c) <
      triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c := by
  have hle := maxcut_triangle_dominance_sound
    J_ab J_ac J_bc e_a e_b e_c R_a R_c σ s_a s_b s_c hσ hsa hsb hsc hviol hea hec
  have hlt :
      min (triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b s_c)
          (triEnergy J_ab J_ac J_bc e_a e_b e_c (-s_a) s_b (-s_c)) <
        triEnergy J_ab J_ac J_bc e_a e_b e_c s_a s_b s_c := by
    linarith
  exact min_lt_iff.mp hlt

/-- **Refutation of Uncorrected Multicut Triangle Rule on Signed Weighted Max-Cut**:
Consider the triangle $\{1, 2, 3\}$ from `test/maxcut.jl` with couplings
$J_{12} = -2$, $J_{13} = 2$, $J_{23} = 2$, external fields $e_1 = 7/2$ ($R_1 = 7/2$),
$e_2 = -11/2$, and $e_3 = -6$ ($R_3 = 6 > 0$), and candidate parity $\sigma = +1$:
1. The naive multicut triangle margin ignoring $R_3$ is strictly positive:
   $-\sigma J_{12} + \min(|J_{13}|, |J_{23}|) - R_1 = 1/2 > 0$ (falsely certifying $s_1 = s_2$).
2. The external-degree-aware Max-Cut triangle margin is negative:
   $-\sigma J_{12} + \gamma_{123}(1) - R_1 = -7/2 < 0$ (correctly abstaining).
3. Across all $8$ spin configurations $(s_1, s_2, s_3) \in \{-1, +1\}^3$, the unique global
   minimizer is $(-1, 1, 1)$, which satisfies $s_1 = -s_2$ rather than $s_1 = +s_2$. -/
theorem uncorrected_multicut_triangle_counterexample :
    let J_12 : ℝ := -2
    let J_13 : ℝ := 2
    let J_23 : ℝ := 2
    let e_1 : ℝ := 7 / 2
    let e_2 : ℝ := -11 / 2
    let e_3 : ℝ := -6
    let R_1 : ℝ := 7 / 2
    let R_3 : ℝ := 6
    let σ : ℝ := 1
    (-σ * J_12 + min |J_13| |J_23| - R_1 = 1 / 2) ∧
    (-σ * J_12 + gammaTriangle σ J_13 J_23 R_3 - R_1 = -7 / 2) ∧
    (∀ s_1 s_2 s_3 : ℝ, isSpin s_1 → isSpin s_2 → isSpin s_3 →
      (s_1, s_2, s_3) ≠ (-1, 1, 1) →
      triEnergy J_12 J_13 J_23 e_1 e_2 e_3 (-1) 1 1 <
        triEnergy J_12 J_13 J_23 e_1 e_2 e_3 s_1 s_2 s_3) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · unfold gammaTriangle
    norm_num
  · intro s_1 s_2 s_3 hs1 hs2 hs3 hne
    unfold triEnergy
    rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact False.elim (hne rfl)
    · norm_num
    · norm_num
    · norm_num
    · norm_num

end QUBOPreprocessing
