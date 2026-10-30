import Mathlib
import QUBOPreprocessing.GaugeCoercive
import QUBOPreprocessing.CompositionRepair

/-!
# Theorem 5: General 3-Variable Walsh–Hadamard Quadratic Interpolation and Non-Zero-Field Degree-3 Elimination Cones

This module formalizes Theorem 5 of `QUBOPreprocessing.jl` (`docs/src/dominance.md` and
`src/certificates.jl`):
1. The complete 8-point Walsh–Hadamard decomposition on $\{-1, +1\}^3$ for an arbitrary real-valued
   function $\phi : \mathbb{R} \to \mathbb{R} \to \mathbb{R} \to \mathbb{R}$: constant shift
   `walshConst`, linear field shifts `walshH1`, `walshH2`, `walshH3`, pairwise quadratic couplings
   `walshJ12`, `walshJ13`, `walshJ23`, and cubic coefficient `walshCubic` ($\alpha_{123}$).
2. The exact pointwise residual identity (`walshQuadPoly_add_cubic_eq`)
   $$P_{\mathrm{quad}}(\phi)(s_1, s_2, s_3) + \alpha_{123}(\phi)\, s_1 s_2 s_3 = \phi(s_1, s_2, s_3)
     \quad \forall (s_1, s_2, s_3) \in \{-1, +1\}^3$$
   and the necessary and sufficient characterization (`walshQuadPoly_eq_iff_cubic_zero`) that
   $P_{\mathrm{quad}}(\phi)$ matches $\phi$ across all $8$ spin configurations if and only if
   $\alpha_{123}(\phi) = 0$.
3. General degree-3 Ising spin marginalization with a non-zero local field $h_0$:
   $$\mathrm{deg3StarMin}(h_0, J_1, J_2, J_3, s_1, s_2, s_3)
     = \min_{s_0 \in \{-1, +1\}} s_0 (h_0 + J_1 s_1 + J_2 s_2 + J_3 s_3)
     = -|h_0 + J_1 s_1 + J_2 s_2 + J_3 s_3|,$$
   its lower-bound and achievability properties (`deg3StarMin_le`, `deg3StarMin_achieved`), and
   exact quadratic representability when $\alpha_{123} = 0$
   (`deg3StarMin_eq_walshQuadPoly_of_cubic_zero`, `deg3StarMin_eq_walshQuadPoly_iff_cubic_zero`).
4. Full-dimensional vanishing cones ($\alpha_{123} = 0$) from the degree-3 trichotomy in
   `docs/src/dominance.md`:
   - Zero-field hyperplane $h_0 = 0$ (`deg3StarMin_cubic_zero_of_h0_zero`), where `walshQuadPoly`
     reduces identically to Eq. (4) `starTriPoly` (`walshQuadPoly_deg3StarMin_zero_eq_starTriPoly`);
   - Coercive-field dominant cone $|h_0| \ge |J_1| + |J_2| + |J_3|$
     (`deg3StarMin_cubic_zero_of_field_dominant`), where all three induced triangle couplings
     vanish (zero fill edges);
   - Heavy-edge relation-dominance cones $|J_k| \ge |h_0| + \sum_{\ell \neq k} |J_\ell|$
     (`deg3StarMin_cubic_zero_of_heavy_edge1`, `deg3StarMin_cubic_zero_of_heavy_edge2`,
     `deg3StarMin_cubic_zero_of_heavy_edge3`), where the non-dominant pair coupling vanishes
     (`walshJ23_deg3StarMin_zero_of_heavy_edge1`, introducing at most $2$ fill edges);
   together with the closed-form non-zero cubic obstructions on the additive cone
   $J_1 = J_2 + J_3$ ($\alpha_{123} = h_0 / 4$, `deg3StarMin_cubic_of_additive_cone`) and the
   equal-coupling plateau cone $J_1 = J_2 = J$, $J_3 \le |h_0| \le 2J - J_3$
   ($\alpha_{123} = \pm J_3 / 2$, `deg3StarMin_cubic_of_plateau_cone_pos`,
   `deg3StarMin_cubic_of_plateau_cone_neg`), certifying `:nonquadratic_elimination` when
   $\alpha_{123} \neq 0$ (`deg3StarMin_not_quad_representable_of_plateau_pos`).
-/

namespace QUBOPreprocessing

/-!
### Part 1: General 8-Point Walsh–Hadamard Decomposition on $\{-1, +1\}^3$
-/

/-- Constant Walsh–Hadamard coefficient $\Delta c(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} \phi(s_1, s_2, s_3)$. -/
noncomputable def walshConst (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 + φ 1 1 (-1) + φ 1 (-1) 1 + φ 1 (-1) (-1) +
   φ (-1) 1 1 + φ (-1) 1 (-1) + φ (-1) (-1) 1 + φ (-1) (-1) (-1)) / 8

/-- First linear Walsh–Hadamard coefficient $\Delta h_1(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_1 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshH1 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 + φ 1 1 (-1) + φ 1 (-1) 1 + φ 1 (-1) (-1) -
   φ (-1) 1 1 - φ (-1) 1 (-1) - φ (-1) (-1) 1 - φ (-1) (-1) (-1)) / 8

/-- Second linear Walsh–Hadamard coefficient $\Delta h_2(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_2 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshH2 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 + φ 1 1 (-1) - φ 1 (-1) 1 - φ 1 (-1) (-1) +
   φ (-1) 1 1 + φ (-1) 1 (-1) - φ (-1) (-1) 1 - φ (-1) (-1) (-1)) / 8

/-- Third linear Walsh–Hadamard coefficient $\Delta h_3(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_3 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshH3 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 - φ 1 1 (-1) + φ 1 (-1) 1 - φ 1 (-1) (-1) +
   φ (-1) 1 1 - φ (-1) 1 (-1) + φ (-1) (-1) 1 - φ (-1) (-1) (-1)) / 8

/-- Quadratic Walsh–Hadamard coupling $\Delta J_{12}(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_1 s_2 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshJ12 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 + φ 1 1 (-1) - φ 1 (-1) 1 - φ 1 (-1) (-1) -
   φ (-1) 1 1 - φ (-1) 1 (-1) + φ (-1) (-1) 1 + φ (-1) (-1) (-1)) / 8

/-- Quadratic Walsh–Hadamard coupling $\Delta J_{13}(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_1 s_3 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshJ13 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 - φ 1 1 (-1) + φ 1 (-1) 1 - φ 1 (-1) (-1) -
   φ (-1) 1 1 + φ (-1) 1 (-1) - φ (-1) (-1) 1 + φ (-1) (-1) (-1)) / 8

/-- Quadratic Walsh–Hadamard coupling $\Delta J_{23}(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_2 s_3 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshJ23 (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 - φ 1 1 (-1) - φ 1 (-1) 1 + φ 1 (-1) (-1) +
   φ (-1) 1 1 - φ (-1) 1 (-1) - φ (-1) (-1) 1 + φ (-1) (-1) (-1)) / 8

/-- Cubic Walsh–Hadamard coefficient $\alpha_{123}(\phi) = \frac{1}{8}\sum_{s \in \{-1, +1\}^3} s_1 s_2 s_3 \phi(s_1, s_2, s_3)$. -/
noncomputable def walshCubic (φ : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (φ 1 1 1 - φ 1 1 (-1) - φ 1 (-1) 1 + φ 1 (-1) (-1) -
   φ (-1) 1 1 + φ (-1) 1 (-1) + φ (-1) (-1) 1 - φ (-1) (-1) (-1)) / 8

/-- Quadratic Walsh–Hadamard projection of $\phi$ onto degree-$\le 2$ spin polynomials:
$P_{\mathrm{quad}}(\phi)(s_1, s_2, s_3) = \Delta c + \sum_{k=1}^3 \Delta h_k s_k + \sum_{k < \ell} \Delta J_{k\ell} s_k s_\ell$. -/
noncomputable def walshQuadPoly (φ : ℝ → ℝ → ℝ → ℝ) (s₁ s₂ s₃ : ℝ) : ℝ :=
  walshConst φ +
    walshH1 φ * s₁ + walshH2 φ * s₂ + walshH3 φ * s₃ +
    walshJ12 φ * s₁ * s₂ + walshJ13 φ * s₁ * s₃ + walshJ23 φ * s₂ * s₃

/-- **Theorem 5 (Part A: Exact 8-Point Walsh–Hadamard Decomposition)**:
For every spin configuration $(s_1, s_2, s_3) \in \{-1, +1\}^3$, the quadratic Walsh projection
plus the cubic Walsh term $\alpha_{123}(\phi)\, s_1 s_2 s_3$ recovers $\phi(s_1, s_2, s_3)$
identically. -/
theorem walshQuadPoly_add_cubic_eq (φ : ℝ → ℝ → ℝ → ℝ) (s₁ s₂ s₃ : ℝ)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) (hs₃ : isSpin s₃) :
    walshQuadPoly φ s₁ s₂ s₃ + walshCubic φ * s₁ * s₂ * s₃ = φ s₁ s₂ s₃ := by
  unfold walshQuadPoly walshConst walshH1 walshH2 walshH3 walshJ12 walshJ13 walshJ23 walshCubic
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> rcases hs₃ with rfl | rfl <;> ring

/-- If the cubic Walsh coefficient vanishes ($\alpha_{123}(\phi) = 0$), the quadratic Walsh
polynomial `walshQuadPoly φ` agrees with `φ` on all $8$ spin configurations in $\{-1, +1\}^3$. -/
theorem walshQuadPoly_eq_of_cubic_zero (φ : ℝ → ℝ → ℝ → ℝ) (s₁ s₂ s₃ : ℝ)
    (hcubic : walshCubic φ = 0)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) (hs₃ : isSpin s₃) :
    walshQuadPoly φ s₁ s₂ s₃ = φ s₁ s₂ s₃ := by
  have h := walshQuadPoly_add_cubic_eq φ s₁ s₂ s₃ hs₁ hs₂ hs₃
  rw [hcubic] at h
  linarith

/-- If `walshQuadPoly φ` agrees with `φ` on all spin configurations in $\{-1, +1\}^3$, then
$\alpha_{123}(\phi) = 0$. -/
theorem walshCubic_zero_of_walshQuadPoly_eq (φ : ℝ → ℝ → ℝ → ℝ)
    (h : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ → walshQuadPoly φ s₁ s₂ s₃ = φ s₁ s₂ s₃) :
    walshCubic φ = 0 := by
  have h1 : isSpin (1 : ℝ) := Or.inr rfl
  have hdecomp := walshQuadPoly_add_cubic_eq φ 1 1 1 h1 h1 h1
  have heq := h 1 1 1 h1 h1 h1
  linarith

/-- **Theorem 5 (Part B: Necessary and Sufficient Condition for Exact Quadratic Interpolation)**:
The quadratic Walsh projection `walshQuadPoly φ` agrees with `φ` on all $8$ spin states in
$\{-1, +1\}^3$ if and only if $\alpha_{123}(\phi) = 0$. -/
theorem walshQuadPoly_eq_iff_cubic_zero (φ : ℝ → ℝ → ℝ → ℝ) :
    (∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      walshQuadPoly φ s₁ s₂ s₃ = φ s₁ s₂ s₃) ↔ walshCubic φ = 0 := by
  constructor
  · exact walshCubic_zero_of_walshQuadPoly_eq φ
  · intro hcubic s₁ s₂ s₃ hs₁ hs₂ hs₃
    exact walshQuadPoly_eq_of_cubic_zero φ s₁ s₂ s₃ hcubic hs₁ hs₂ hs₃

/-!
### Part 2: General Degree-3 Ising Spin Marginalization with Non-Zero Local Field ($h_0$)
-/

/-- Optimal conditional energy of a degree-3 Ising spin $s_0 \in \{-1, +1\}$ with local field $h_0$
and neighbor couplings $(J_1, J_2, J_3)$:
$\min_{s_0 \in \{-1, +1\}} s_0 (h_0 + J_1 s_1 + J_2 s_2 + J_3 s_3) = -|h_0 + J_1 s_1 + J_2 s_2 + J_3 s_3|$. -/
noncomputable def deg3StarMin (h₀ J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) : ℝ :=
  -|h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃|

/-- When $h_0 = 0$, `deg3StarMin` reduces identically to the zero-field `starMin` of Theorem 2. -/
theorem deg3StarMin_zero_eq_starMin (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) :
    deg3StarMin 0 J₁ J₂ J₃ s₁ s₂ s₃ = starMin J₁ J₂ J₃ s₁ s₂ s₃ := by
  unfold deg3StarMin starMin
  rw [zero_add]

/-- For any central spin $s_0 \in \{-1, +1\}$, `deg3StarMin` is a lower bound on the degree-3
star energy $s_0 (h_0 + J_1 s_1 + J_2 s_2 + J_3 s_3)$. -/
theorem deg3StarMin_le (h₀ J₁ J₂ J₃ s₁ s₂ s₃ s₀ : ℝ) (hs₀ : isSpin s₀) :
    deg3StarMin h₀ J₁ J₂ J₃ s₁ s₂ s₃ ≤ s₀ * (h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃) := by
  unfold deg3StarMin
  rcases hs₀ with rfl | rfl
  · have h := le_abs_self (h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃)
    linarith
  · have h := neg_le_abs (h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃)
    linarith

/-- For every neighbor state $(s_1, s_2, s_3)$, there exists an optimal central spin
$s_0 \in \{-1, +1\}$ achieving `deg3StarMin`. -/
theorem deg3StarMin_achieved (h₀ J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) :
    ∃ s₀, isSpin s₀ ∧
      s₀ * (h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃) = deg3StarMin h₀ J₁ J₂ J₃ s₁ s₂ s₃ := by
  unfold deg3StarMin
  rcases le_total 0 (h₀ + J₁ * s₁ + J₂ * s₂ + J₃ * s₃) with h | h
  · refine ⟨-1, Or.inl rfl, ?_⟩
    rw [abs_of_nonneg h]
    ring
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [abs_of_nonpos h]
    ring

/-- When $\alpha_{123}(\mathrm{deg3StarMin}(h_0, J_1, J_2, J_3)) = 0$, the quadratic Walsh
polynomial represents `deg3StarMin` exactly across all $8$ neighbor spin configurations. -/
theorem deg3StarMin_eq_walshQuadPoly_of_cubic_zero (h₀ J₁ J₂ J₃ s₁ s₂ s₃ : ℝ)
    (hcubic : walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) (hs₃ : isSpin s₃) :
    walshQuadPoly (deg3StarMin h₀ J₁ J₂ J₃) s₁ s₂ s₃ = deg3StarMin h₀ J₁ J₂ J₃ s₁ s₂ s₃ :=
  walshQuadPoly_eq_of_cubic_zero (deg3StarMin h₀ J₁ J₂ J₃) s₁ s₂ s₃ hcubic hs₁ hs₂ hs₃

/-- Exact quadratic representability of `deg3StarMin` on $\{-1, +1\}^3$ holds if and only if
its cubic Walsh coefficient vanishes. -/
theorem deg3StarMin_eq_walshQuadPoly_iff_cubic_zero (h₀ J₁ J₂ J₃ : ℝ) :
    (∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      walshQuadPoly (deg3StarMin h₀ J₁ J₂ J₃) s₁ s₂ s₃ = deg3StarMin h₀ J₁ J₂ J₃ s₁ s₂ s₃) ↔
      walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 :=
  walshQuadPoly_eq_iff_cubic_zero (deg3StarMin h₀ J₁ J₂ J₃)

/-!
### Part 3: Vanishing Cones ($\alpha_{123} = 0$) and Non-Zero-Field Elimination Regimes
-/

/-- **Regime 1 (Zero-Field Hyperplane $h_0 = 0$)**:
When $h_0 = 0$, the cubic Walsh coefficient of `deg3StarMin` vanishes for all $(J_1, J_2, J_3) \in \mathbb{R}^3$. -/
theorem deg3StarMin_cubic_zero_of_h0_zero (J₁ J₂ J₃ : ℝ) :
    walshCubic (deg3StarMin 0 J₁ J₂ J₃) = 0 := by
  unfold walshCubic
  simp only [deg3StarMin_zero_eq_starMin]
  have h := starMin_cubic_walsh_zero J₁ J₂ J₃
  linarith

/-- When $h_0 = 0$, the general quadratic Walsh projection `walshQuadPoly (deg3StarMin 0 J₁ J₂ J₃)`
coincides with the zero-field triangle polynomial `starTriPoly J₁ J₂ J₃` of Eq. (4) on all
spin configurations in $\{-1, +1\}^3$. -/
theorem walshQuadPoly_deg3StarMin_zero_eq_starTriPoly (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) (hs₃ : isSpin s₃) :
    walshQuadPoly (deg3StarMin 0 J₁ J₂ J₃) s₁ s₂ s₃ = starTriPoly J₁ J₂ J₃ s₁ s₂ s₃ := by
  rw [deg3StarMin_eq_walshQuadPoly_of_cubic_zero 0 J₁ J₂ J₃ s₁ s₂ s₃
        (deg3StarMin_cubic_zero_of_h0_zero J₁ J₂ J₃) hs₁ hs₂ hs₃,
      deg3StarMin_zero_eq_starMin,
      starTriPoly_eq_starMin J₁ J₂ J₃ s₁ s₂ s₃ hs₁ hs₂ hs₃]

/-- **Regime 2 (Coercive-Field Dominant Cone $|h_0| \ge |J_1| + |J_2| + |J_3|$)**:
When the local field magnitude dominates the $\ell_1$ norm of the three incident couplings,
the cubic Walsh coefficient $\alpha_{123}$ vanishes identically. -/
theorem deg3StarMin_cubic_zero_of_field_dominant (h₀ J₁ J₂ J₃ : ℝ)
    (hdom : |J₁| + |J₂| + |J₃| ≤ |h₀|) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 := by
  have h1_lo : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h1_hi : J₁ ≤ |J₁| := le_abs_self J₁
  have h2_lo : -|J₂| ≤ J₂ := neg_abs_le J₂
  have h2_hi : J₂ ≤ |J₂| := le_abs_self J₂
  have h3_lo : -|J₃| ≤ J₃ := neg_abs_le J₃
  have h3_hi : J₃ ≤ |J₃| := le_abs_self J₃
  unfold walshCubic deg3StarMin
  rcases le_total 0 h₀ with hh₀ | hh₀
  · have habs : |h₀| = h₀ := abs_of_nonneg hh₀
    have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
    have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
    have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
    have hpmm : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) := by linarith
    have hmpp : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 := by linarith
    have hmpm : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) := by linarith
    have hmmp : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 := by linarith
    have hmmm : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) := by linarith
    rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonneg hpmp, abs_of_nonneg hpmm,
        abs_of_nonneg hmpp, abs_of_nonneg hmpm, abs_of_nonneg hmmp, abs_of_nonneg hmmm]
    ring
  · have habs : |h₀| = -h₀ := abs_of_nonpos hh₀
    have hppp : h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hppm : h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hpmp : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    rw [abs_of_nonpos hppp, abs_of_nonpos hppm, abs_of_nonpos hpmp, abs_of_nonpos hpmm,
        abs_of_nonpos hmpp, abs_of_nonpos hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
    ring

/-- In the coercive-field dominant cone $|h_0| \ge |J_1| + |J_2| + |J_3|$, all three induced
quadratic couplings vanish ($\Delta J_{12} = \Delta J_{13} = \Delta J_{23} = 0$), so eliminating
$s_0$ introduces zero fill edges. -/
theorem deg3StarMin_quad_couplings_zero_of_field_dominant (h₀ J₁ J₂ J₃ : ℝ)
    (hdom : |J₁| + |J₂| + |J₃| ≤ |h₀|) :
    walshJ12 (deg3StarMin h₀ J₁ J₂ J₃) = 0 ∧
      walshJ13 (deg3StarMin h₀ J₁ J₂ J₃) = 0 ∧
      walshJ23 (deg3StarMin h₀ J₁ J₂ J₃) = 0 := by
  have h1_lo : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h1_hi : J₁ ≤ |J₁| := le_abs_self J₁
  have h2_lo : -|J₂| ≤ J₂ := neg_abs_le J₂
  have h2_hi : J₂ ≤ |J₂| := le_abs_self J₂
  have h3_lo : -|J₃| ≤ J₃ := neg_abs_le J₃
  have h3_hi : J₃ ≤ |J₃| := le_abs_self J₃
  unfold walshJ12 walshJ13 walshJ23 deg3StarMin
  rcases le_total 0 h₀ with hh₀ | hh₀
  · have habs : |h₀| = h₀ := abs_of_nonneg hh₀
    have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
    have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
    have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
    have hpmm : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) := by linarith
    have hmpp : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 := by linarith
    have hmpm : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) := by linarith
    have hmmp : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 := by linarith
    have hmmm : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) := by linarith
    rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonneg hpmp, abs_of_nonneg hpmm,
        abs_of_nonneg hmpp, abs_of_nonneg hmpm, abs_of_nonneg hmmp, abs_of_nonneg hmmm]
    refine ⟨by ring, by ring, by ring⟩
  · have habs : |h₀| = -h₀ := abs_of_nonpos hh₀
    have hppp : h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hppm : h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hpmp : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    rw [abs_of_nonpos hppp, abs_of_nonpos hppm, abs_of_nonpos hpmp, abs_of_nonpos hpmm,
        abs_of_nonpos hmpp, abs_of_nonpos hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
    refine ⟨by ring, by ring, by ring⟩

/-- **Regime 3A (Heavy-Edge Relation-Dominance Cone for $J_1$: $|J_1| \ge |h_0| + |J_2| + |J_3|$)**:
When coupling $J_1$ dominates $|h_0| + |J_2| + |J_3|$ (so $s_0$ is locked to $\pm s_1$ across all
configurations of $(s_2, s_3)$), the cubic Walsh coefficient $\alpha_{123}$ vanishes identically
and the induced coupling $\Delta J_{23}$ between the two non-dominant neighbors is zero. -/
theorem deg3StarMin_cubic_zero_of_heavy_edge1 (h₀ J₁ J₂ J₃ : ℝ)
    (hdom : |h₀| + |J₂| + |J₃| ≤ |J₁|) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 ∧
      walshJ23 (deg3StarMin h₀ J₁ J₂ J₃) = 0 := by
  have hh0_lo : -|h₀| ≤ h₀ := neg_abs_le h₀
  have hh0_hi : h₀ ≤ |h₀| := le_abs_self h₀
  have h2_lo : -|J₂| ≤ J₂ := neg_abs_le J₂
  have h2_hi : J₂ ≤ |J₂| := le_abs_self J₂
  have h3_lo : -|J₃| ≤ J₃ := neg_abs_le J₃
  have h3_hi : J₃ ≤ |J₃| := le_abs_self J₃
  unfold walshCubic walshJ23 deg3StarMin
  rcases le_total 0 J₁ with hJ₁ | hJ₁
  · have habs : |J₁| = J₁ := abs_of_nonneg hJ₁
    have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
    have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
    have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
    have hpmm : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) := by linarith
    have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonneg hpmp, abs_of_nonneg hpmm,
        abs_of_nonpos hmpp, abs_of_nonpos hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
    exact ⟨by ring, by ring⟩
  · have habs : |J₁| = -J₁ := abs_of_nonpos hJ₁
    have hppp : h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hppm : h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hpmp : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    have hmpp : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 := by linarith
    have hmpm : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) := by linarith
    have hmmp : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 := by linarith
    have hmmm : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) := by linarith
    rw [abs_of_nonpos hppp, abs_of_nonpos hppm, abs_of_nonpos hpmp, abs_of_nonpos hpmm,
        abs_of_nonneg hmpp, abs_of_nonneg hmpm, abs_of_nonneg hmmp, abs_of_nonneg hmmm]
    exact ⟨by ring, by ring⟩

/-- **Regime 3B (Heavy-Edge Relation-Dominance Cone for $J_2$: $|J_2| \ge |h_0| + |J_1| + |J_3|$)**:
When coupling $J_2$ dominates $|h_0| + |J_1| + |J_3|$, the cubic Walsh coefficient $\alpha_{123}$
vanishes identically and the non-dominant pair coupling $\Delta J_{13}$ is zero. -/
theorem deg3StarMin_cubic_zero_of_heavy_edge2 (h₀ J₁ J₂ J₃ : ℝ)
    (hdom : |h₀| + |J₁| + |J₃| ≤ |J₂|) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 ∧
      walshJ13 (deg3StarMin h₀ J₁ J₂ J₃) = 0 := by
  have hh0_lo : -|h₀| ≤ h₀ := neg_abs_le h₀
  have hh0_hi : h₀ ≤ |h₀| := le_abs_self h₀
  have h1_lo : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h1_hi : J₁ ≤ |J₁| := le_abs_self J₁
  have h3_lo : -|J₃| ≤ J₃ := neg_abs_le J₃
  have h3_hi : J₃ ≤ |J₃| := le_abs_self J₃
  unfold walshCubic walshJ13 deg3StarMin
  rcases le_total 0 J₂ with hJ₂ | hJ₂
  · have habs : |J₂| = J₂ := abs_of_nonneg hJ₂
    have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
    have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
    have hpmp : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    have hmpp : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 := by linarith
    have hmpm : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) := by linarith
    have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonpos hpmp, abs_of_nonpos hpmm,
        abs_of_nonneg hmpp, abs_of_nonneg hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
    exact ⟨by ring, by ring⟩
  · have habs : |J₂| = -J₂ := abs_of_nonpos hJ₂
    have hppp : h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hppm : h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
    have hpmm : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) := by linarith
    have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hmmp : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 := by linarith
    have hmmm : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) := by linarith
    rw [abs_of_nonpos hppp, abs_of_nonpos hppm, abs_of_nonneg hpmp, abs_of_nonneg hpmm,
        abs_of_nonpos hmpp, abs_of_nonpos hmpm, abs_of_nonneg hmmp, abs_of_nonneg hmmm]
    exact ⟨by ring, by ring⟩

/-- **Regime 3C (Heavy-Edge Relation-Dominance Cone for $J_3$: $|J_3| \ge |h_0| + |J_1| + |J_2|$)**:
When coupling $J_3$ dominates $|h_0| + |J_1| + |J_2|$, the cubic Walsh coefficient $\alpha_{123}$
vanishes identically and the non-dominant pair coupling $\Delta J_{12}$ is zero. -/
theorem deg3StarMin_cubic_zero_of_heavy_edge3 (h₀ J₁ J₂ J₃ : ℝ)
    (hdom : |h₀| + |J₁| + |J₂| ≤ |J₃|) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 ∧
      walshJ12 (deg3StarMin h₀ J₁ J₂ J₃) = 0 := by
  have hh0_lo : -|h₀| ≤ h₀ := neg_abs_le h₀
  have hh0_hi : h₀ ≤ |h₀| := le_abs_self h₀
  have h1_lo : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h1_hi : J₁ ≤ |J₁| := le_abs_self J₁
  have h2_lo : -|J₂| ≤ J₂ := neg_abs_le J₂
  have h2_hi : J₂ ≤ |J₂| := le_abs_self J₂
  unfold walshCubic walshJ12 deg3StarMin
  rcases le_total 0 J₃ with hJ₃ | hJ₃
  · have habs : |J₃| = J₃ := abs_of_nonneg hJ₃
    have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
    have hppm : h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
    have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    have hmpp : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 := by linarith
    have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
    have hmmp : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 := by linarith
    have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
    rw [abs_of_nonneg hppp, abs_of_nonpos hppm, abs_of_nonneg hpmp, abs_of_nonpos hpmm,
        abs_of_nonneg hmpp, abs_of_nonpos hmpm, abs_of_nonneg hmmp, abs_of_nonpos hmmm]
    exact ⟨by ring, by ring⟩
  · have habs : |J₃| = -J₃ := abs_of_nonpos hJ₃
    have hppp : h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
    have hpmp : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hpmm : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) := by linarith
    have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 ≤ 0 := by linarith
    have hmpm : 0 ≤ h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) := by linarith
    have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
    have hmmm : 0 ≤ h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) := by linarith
    rw [abs_of_nonpos hppp, abs_of_nonneg hppm, abs_of_nonpos hpmp, abs_of_nonneg hpmm,
        abs_of_nonpos hmpp, abs_of_nonneg hmpm, abs_of_nonpos hmmp, abs_of_nonneg hmmm]
    exact ⟨by ring, by ring⟩

/-!
### Part 4: Closed-Form Cubic Obstructions Outside the Trichotomy (`:nonquadratic_elimination`)
-/

/-- **Additive-Coupling Boundary Cone ($J_1 = J_2 + J_3$ with $|h_0| \le 2 \min(J_2, J_3)$)**:
On the boundary $J_1 = J_2 + J_3$ with $-2 J_2 \le h_0 \le 2 J_2$ and
$-2 J_3 \le h_0 \le 2 J_3$, the two antipodal states $(1, -1, -1)$ and $(-1, 1, 1)$ both have
effective field $h_0$ and cancel identically, yielding the linear cubic coefficient
$\alpha_{123} = h_0 / 4$ (which vanishes if and only if $h_0 = 0$). -/
theorem deg3StarMin_cubic_of_additive_cone (h₀ J₁ J₂ J₃ : ℝ)
    (hJ₁ : J₁ = J₂ + J₃)
    (hh₂_lo : -2 * J₂ ≤ h₀) (hh₂_hi : h₀ ≤ 2 * J₂)
    (hh₃_lo : -2 * J₃ ≤ h₀) (hh₃_hi : h₀ ≤ 2 * J₃) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = h₀ / 4 := by
  unfold walshCubic deg3StarMin
  have hppp : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * 1 := by linarith
  have hppm : 0 ≤ h₀ + J₁ * 1 + J₂ * 1 + J₃ * (-1) := by linarith
  have hpmp : 0 ≤ h₀ + J₁ * 1 + J₂ * (-1) + J₃ * 1 := by linarith
  have hpmm : h₀ + J₁ * 1 + J₂ * (-1) + J₃ * (-1) = h₀ := by linarith
  have hmpp : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * 1 = h₀ := by linarith
  have hmpm : h₀ + J₁ * (-1) + J₂ * 1 + J₃ * (-1) ≤ 0 := by linarith
  have hmmp : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * 1 ≤ 0 := by linarith
  have hmmm : h₀ + J₁ * (-1) + J₂ * (-1) + J₃ * (-1) ≤ 0 := by linarith
  rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonneg hpmp, hpmm, hmpp,
      abs_of_nonpos hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
  ring

/-- On the additive-coupling boundary cone $J_1 = J_2 + J_3$ with $|h_0| \le 2 \min(J_2, J_3)$,
the cubic Walsh coefficient vanishes if and only if $h_0 = 0$. -/
theorem deg3StarMin_cubic_zero_iff_of_additive_cone (h₀ J₁ J₂ J₃ : ℝ)
    (hJ₁ : J₁ = J₂ + J₃)
    (hh₂_lo : -2 * J₂ ≤ h₀) (hh₂_hi : h₀ ≤ 2 * J₂)
    (hh₃_lo : -2 * J₃ ≤ h₀) (hh₃_hi : h₀ ≤ 2 * J₃) :
    walshCubic (deg3StarMin h₀ J₁ J₂ J₃) = 0 ↔ h₀ = 0 := by
  rw [deg3StarMin_cubic_of_additive_cone h₀ J₁ J₂ J₃ hJ₁ hh₂_lo hh₂_hi hh₃_lo hh₃_hi]
  constructor <;> intro h <;> linarith

/-- **Equal-Coupling Plateau Cone ($J_1 = J_2 = J$, $0 \le J_3 \le h_0 \le 2J - J_3$)**:
Across the positive plateau $J_3 \le h_0 \le 2J - J_3$, the cubic Walsh coefficient is
independent of $h_0$ and equals $J_3 / 2$. -/
theorem deg3StarMin_cubic_of_plateau_cone_pos (h₀ J J₃ : ℝ)
    (hJ₃ : 0 ≤ J₃) (hJ : J₃ ≤ J)
    (hh_lo : J₃ ≤ h₀) (hh_hi : h₀ ≤ 2 * J - J₃) :
    walshCubic (deg3StarMin h₀ J J J₃) = J₃ / 2 := by
  unfold walshCubic deg3StarMin
  have hppp : 0 ≤ h₀ + J * 1 + J * 1 + J₃ * 1 := by linarith
  have hppm : 0 ≤ h₀ + J * 1 + J * 1 + J₃ * (-1) := by linarith
  have hpmp : 0 ≤ h₀ + J * 1 + J * (-1) + J₃ * 1 := by linarith
  have hpmm : 0 ≤ h₀ + J * 1 + J * (-1) + J₃ * (-1) := by linarith
  have hmpp : 0 ≤ h₀ + J * (-1) + J * 1 + J₃ * 1 := by linarith
  have hmpm : 0 ≤ h₀ + J * (-1) + J * 1 + J₃ * (-1) := by linarith
  have hmmp : h₀ + J * (-1) + J * (-1) + J₃ * 1 ≤ 0 := by linarith
  have hmmm : h₀ + J * (-1) + J * (-1) + J₃ * (-1) ≤ 0 := by linarith
  rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonneg hpmp, abs_of_nonneg hpmm,
      abs_of_nonneg hmpp, abs_of_nonneg hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
  ring

/-- **Negative Equal-Coupling Plateau Cone ($J_1 = J_2 = J$, $-(2J - J_3) \le h_0 \le -J_3$)**:
Across the negative plateau $-(2J - J_3) \le h_0 \le -J_3$, the cubic Walsh coefficient is
independent of $h_0$ and equals $-J_3 / 2$. -/
theorem deg3StarMin_cubic_of_plateau_cone_neg (h₀ J J₃ : ℝ)
    (hJ₃ : 0 ≤ J₃) (hJ : J₃ ≤ J)
    (hh_lo : -(2 * J - J₃) ≤ h₀) (hh_hi : h₀ ≤ -J₃) :
    walshCubic (deg3StarMin h₀ J J J₃) = -J₃ / 2 := by
  unfold walshCubic deg3StarMin
  have hppp : 0 ≤ h₀ + J * 1 + J * 1 + J₃ * 1 := by linarith
  have hppm : 0 ≤ h₀ + J * 1 + J * 1 + J₃ * (-1) := by linarith
  have hpmp : h₀ + J * 1 + J * (-1) + J₃ * 1 ≤ 0 := by linarith
  have hpmm : h₀ + J * 1 + J * (-1) + J₃ * (-1) ≤ 0 := by linarith
  have hmpp : h₀ + J * (-1) + J * 1 + J₃ * 1 ≤ 0 := by linarith
  have hmpm : h₀ + J * (-1) + J * 1 + J₃ * (-1) ≤ 0 := by linarith
  have hmmp : h₀ + J * (-1) + J * (-1) + J₃ * 1 ≤ 0 := by linarith
  have hmmm : h₀ + J * (-1) + J * (-1) + J₃ * (-1) ≤ 0 := by linarith
  rw [abs_of_nonneg hppp, abs_of_nonneg hppm, abs_of_nonpos hpmp, abs_of_nonpos hpmm,
      abs_of_nonpos hmpp, abs_of_nonpos hmpm, abs_of_nonpos hmmp, abs_of_nonpos hmmm]
  ring

/-- **Non-Quadratic Obstruction Theorem (`:nonquadratic_elimination`)**:
Whenever $0 < J_3 \le J$ and $J_3 \le h_0 \le 2J - J_3$, the cubic Walsh coefficient is
$\alpha_{123} = J_3 / 2 > 0$, so `walshQuadPoly` cannot match `deg3StarMin` across all $8$
spin configurations in $\{-1, +1\}^3$. -/
theorem deg3StarMin_not_quad_representable_of_plateau_pos (h₀ J J₃ : ℝ)
    (hJ₃ : 0 < J₃) (hJ : J₃ ≤ J)
    (hh_lo : J₃ ≤ h₀) (hh_hi : h₀ ≤ 2 * J - J₃) :
    ¬ (∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
        walshQuadPoly (deg3StarMin h₀ J J J₃) s₁ s₂ s₃ = deg3StarMin h₀ J J J₃ s₁ s₂ s₃) := by
  rw [deg3StarMin_eq_walshQuadPoly_iff_cubic_zero]
  rw [deg3StarMin_cubic_of_plateau_cone_pos h₀ J J₃ (le_of_lt hJ₃) hJ hh_lo hh_hi]
  linarith

end QUBOPreprocessing
