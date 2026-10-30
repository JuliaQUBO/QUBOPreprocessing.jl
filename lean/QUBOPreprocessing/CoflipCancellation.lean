import Mathlib
import QUBOPreprocessing.GaugeCoercive
import QUBOPreprocessing.CompositionRepair

/-!
# Theorem 6: Two-Spin Co-Flip Shared-Neighbor Cancellation and Twin Contraction

This module formalizes Theorem 6 of `QUBOPreprocessing.jl` (`prove_relation` `:coflip_pair`,
`prove_twin`, `contract_twins!`, and `_verify_relation_step` in
`src/certificates.jl:1081-1255, 4993-5018`):
1. **Two-Spin Co-Flip Average Identity on Violation States ($s_u = -\sigma s_v$)**:
   For any pair of Ising spins $s_u, s_v \in \{-1, +1\}$, relation sign $\sigma \in \{-1, +1\}$,
   and environment spin assignment $s_W : W \to \{-1, +1\}$ on a finite type `W`, on any state
   violating $s_u = \sigma s_v$ (so $s_u = -\sigma s_v$), both single-spin flips
   $(-s_u, s_v, s_W)$ and $(s_u, -s_v, s_W)$ satisfy the relation $s_u' = \sigma s_v'$, and the
   average of their energy changes $\Delta E_u$ and $\Delta E_v$ satisfies the exact cancellation
   identity
   $$\frac{\Delta E_u + \Delta E_v}{2}
     = 2\sigma J_{uv} + \sigma s_v \left( (h_u - \sigma h_v)
       + \sum_{w \in W} (J_u(w) - \sigma J_v(w)) s_w \right).$$
2. **Co-Flip Radius, Two-Sided Enclosure, and Strong/Weak Persistency**:
   Defining $\mathrm{coflipCenter}(\sigma, J_{uv}) = -\sigma J_{uv}$,
   $\mathrm{coflipRadius}(\sigma, h_u, h_v, J_u, J_v)
     = \frac{1}{2}\big(|h_u - \sigma h_v| + \sum_{w \in W} |J_u(w) - \sigma J_v(w)|\big)$,
   `coflipLower = coflipCenter - coflipRadius`, and `coflipUpper = coflipCenter + coflipRadius`,
   every violating state satisfies
   $$\min(\Delta E_u, \Delta E_v) \le \frac{\Delta E_u + \Delta E_v}{2} \le -2\,\mathrm{coflipLower}$$
   and $-2\,\mathrm{coflipUpper} \le \frac{\Delta E_u + \Delta E_v}{2} \le -2\,\mathrm{coflipLower}$.
   Consequently, $\mathrm{coflipLower} > 0$ certifies strong persistency ($s_u = \sigma s_v$ in all
   global minimizers), $\mathrm{coflipLower} \ge 0$ certifies weak persistency, and structural twin
   matching ($h_u = \sigma h_v$ and $\forall w,\, J_u(w) = \sigma J_v(w)$) yields
   $\mathrm{coflipRadius} = 0$.
3. **One-Sided $N(v)$ Decomposition and Monotone Increment Identities**:
   Formalizes the one-sided summation identity over $N(v)$ used by `prove_relation` and
   `_verify_relation_step`, non-negativity of the per-neighbor monotone pruning increment
   $\Delta_w(\sigma, J_{uw}, J_{vw}) = |J_{uw} - \sigma J_{vw}| + |J_{uw}| - |J_{vw}| \ge 0$, and
   strict shared-neighbor cancellation $|J_{uw} - \sigma J_{vw}| < |J_{uw}| + |J_{vw}|$ whenever
   $\sigma J_{uw} J_{vw} > 0$.
4. **Compositional `ReductionStep` and `StrongReductionStep` Bridges**:
   Instantiates `ReductionStep` (under $\mathrm{coflipLower} \ge 0$) and `StrongReductionStep`
   (under $\mathrm{coflipLower} > 0$) from `QUBOPreprocessing.CompositionRepair` for pair
   contraction $s_u = \sigma s_v$, together with exact coefficient-merging and global-minimum
   preservation corollaries.
-/

open scoped BigOperators

namespace QUBOPreprocessing

/-!
### Part 1: Two-Spin Co-Flip Average Identity on Violation States ($s_u = -\sigma s_v$)
-/

/-- Decomposition of an Ising Hamiltonian isolating a spin pair $(s_u, s_v)$ with fields
$(h_u, h_v)$, direct coupling $J_{uv}$, environment couplings $J_u, J_v : W \to \mathbb{R}$,
and remaining environment energy $E_{\mathrm{rest}}(s_W)$. -/
noncomputable def pairEnvEnergy {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ) : ℝ :=
  E_rest s_W + h_u * s_u + h_v * s_v + J_uv * s_u * s_v +
    ∑ w, (J_u w * s_u + J_v w * s_v) * s_W w

/-- Single-spin flip energy change $\Delta E_u = E(-s_u, s_v, s_W) - E(s_u, s_v, s_W)$. -/
noncomputable def deltaFlipU {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ) : ℝ :=
  pairEnvEnergy E_rest h_u h_v J_uv J_u J_v (-s_u) s_v s_W -
    pairEnvEnergy E_rest h_u h_v J_uv J_u J_v s_u s_v s_W

/-- Single-spin flip energy change $\Delta E_v = E(s_u, -s_v, s_W) - E(s_u, s_v, s_W)$. -/
noncomputable def deltaFlipV {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ) : ℝ :=
  pairEnvEnergy E_rest h_u h_v J_uv J_u J_v s_u (-s_v) s_W -
    pairEnvEnergy E_rest h_u h_v J_uv J_u J_v s_u s_v s_W

/-- Explicit local-field factoring of $\Delta E_u = -2 s_u (h_u + J_{uv} s_v + \sum_w J_u(w) s_w)$. -/
theorem deltaFlipU_eq {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ) :
    deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W =
      -2 * s_u * (h_u + J_uv * s_v + ∑ w, J_u w * s_W w) := by
  unfold deltaFlipU pairEnvEnergy
  have hsum :
      (∑ w, (J_u w * (-s_u) + J_v w * s_v) * s_W w) -
        (∑ w, (J_u w * s_u + J_v w * s_v) * s_W w) =
      -2 * s_u * ∑ w, J_u w * s_W w := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  linarith [hsum]

/-- Explicit local-field factoring of $\Delta E_v = -2 s_v (h_v + J_{uv} s_u + \sum_w J_v(w) s_w)$. -/
theorem deltaFlipV_eq {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ) :
    deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W =
      -2 * s_v * (h_v + J_uv * s_u + ∑ w, J_v w * s_W w) := by
  unfold deltaFlipV pairEnvEnergy
  have hsum :
      (∑ w, (J_u w * s_u + J_v w * (-s_v)) * s_W w) -
        (∑ w, (J_u w * s_u + J_v w * s_v) * s_W w) =
      -2 * s_v * ∑ w, J_v w * s_W w := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  linarith [hsum]

/-- For any two spins $s_u, s_v \in \{-1, +1\}$ and relation sign $\sigma \in \{-1, +1\}$,
either the relation $s_u = \sigma s_v$ holds or the violation relation $s_u = -\sigma s_v$ holds. -/
theorem spin_rel_or_viol {s_u s_v σ : ℝ}
    (hs_u : isSpin s_u) (hs_v : isSpin s_v) (hσ : isSpin σ) :
    s_u = σ * s_v ∨ s_u = -σ * s_v := by
  rcases hs_u with rfl | rfl <;> rcases hs_v with rfl | rfl <;> rcases hσ with rfl | rfl <;>
    norm_num

/-- On a violating state $s_u = -\sigma s_v$, flipping $s_u \mapsto -s_u$ restores the target
relation $-s_u = \sigma s_v$. -/
theorem repair_u_satisfies_relation {s_u s_v σ : ℝ} (hviol : s_u = -σ * s_v) :
    -s_u = σ * s_v := by
  linarith

/-- On a violating state $s_u = -\sigma s_v$, flipping $s_v \mapsto -s_v$ restores the target
relation $s_u = \sigma (-s_v)$. -/
theorem repair_v_satisfies_relation {s_u s_v σ : ℝ} (hviol : s_u = -σ * s_v) :
    s_u = σ * (-s_v) := by
  linarith

/-- **Theorem 6 (Part 1 — Two-Spin Co-Flip Average Identity on Violation States)**:
For any state with $s_v \in \{-1, +1\}$, $\sigma \in \{-1, +1\}$, and $s_u = -\sigma s_v$,
the average of the two single-spin repair energy changes $\Delta E_u$ and $\Delta E_v$ satisfies
the exact shared-neighbor cancellation identity
$$\frac{\Delta E_u + \Delta E_v}{2}
  = 2\sigma J_{uv} + \sigma s_v \left( (h_u - \sigma h_v)
    + \sum_{w \in W} (J_u(w) - \sigma J_v(w)) s_w \right).$$ -/
theorem coflip_average_eq {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v) :
    (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
      deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) / 2 =
      2 * σ * J_uv +
        σ * s_v * ((h_u - σ * h_v) + ∑ w, (J_u w - σ * J_v w) * s_W w) := by
  rw [deltaFlipU_eq, deltaFlipV_eq, hviol]
  have hsum :
      (∑ w, (J_u w - σ * J_v w) * s_W w) =
        (∑ w, J_u w * s_W w) - σ * ∑ w, J_v w * s_W w := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  rw [hsum]
  rcases hσ with rfl | rfl <;> rcases hs_v with rfl | rfl <;> ring

/-!
### Part 2: Co-Flip Radius, Two-Sided Enclosure, and Strong/Weak Persistency
-/

/-- Center of the `:coflip_pair` relation margin: $\mathrm{coflipCenter}(\sigma, J_{uv}) = -\sigma J_{uv}$. -/
noncomputable def coflipCenter (σ J_uv : ℝ) : ℝ :=
  -σ * J_uv

/-- Worst-case fluctuation radius of the `:coflip_pair` relation margin over $s_W \in \{-1, +1\}^W$:
$$\mathrm{coflipRadius}(\sigma, h_u, h_v, J_u, J_v)
  = \frac{|h_u - \sigma h_v| + \sum_{w \in W} |J_u(w) - \sigma J_v(w)|}{2}.$$ -/
noncomputable def coflipRadius {W : Type*} [Fintype W]
    (σ h_u h_v : ℝ) (J_u J_v : W → ℝ) : ℝ :=
  (|h_u - σ * h_v| + ∑ w, |J_u w - σ * J_v w|) / 2

/-- Lower bound of the `:coflip_pair` relation margin (`lo = center - rad` in `src/certificates.jl:1192`):
$\mathrm{coflipLower} = -\sigma J_{uv} - \mathrm{coflipRadius}(\sigma, h_u, h_v, J_u, J_v)$. -/
noncomputable def coflipLower {W : Type*} [Fintype W]
    (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ) : ℝ :=
  coflipCenter σ J_uv - coflipRadius σ h_u h_v J_u J_v

/-- Upper bound of the `:coflip_pair` relation margin (`hi = center + rad` in `src/certificates.jl:1193`):
$\mathrm{coflipUpper} = -\sigma J_{uv} + \mathrm{coflipRadius}(\sigma, h_u, h_v, J_u, J_v)$. -/
noncomputable def coflipUpper {W : Type*} [Fintype W]
    (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ) : ℝ :=
  coflipCenter σ J_uv + coflipRadius σ h_u h_v J_u J_v

/-- The co-flip fluctuation radius is always non-negative. -/
theorem coflipRadius_nonneg {W : Type*} [Fintype W]
    (σ h_u h_v : ℝ) (J_u J_v : W → ℝ) :
    0 ≤ coflipRadius σ h_u h_v J_u J_v := by
  unfold coflipRadius
  have h1 : 0 ≤ |h_u - σ * h_v| := abs_nonneg _
  have h2 : 0 ≤ ∑ w, |J_u w - σ * J_v w| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

/-- The co-flip lower margin never exceeds the co-flip upper margin. -/
theorem coflipLower_le_coflipUpper {W : Type*} [Fintype W]
    (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ) :
    coflipLower σ h_u h_v J_uv J_u J_v ≤ coflipUpper σ h_u h_v J_uv J_u J_v := by
  unfold coflipLower coflipUpper
  have hrad := coflipRadius_nonneg σ h_u h_v J_u J_v
  linarith

/-- Bound on the fluctuating residual term in the co-flip average across all environment spin
configurations $s_W \in \{-1, +1\}^W$. -/
theorem abs_coflip_fluctuation_le_two_mul_coflipRadius {W : Type*} [Fintype W]
    (σ h_u h_v : ℝ) (J_u J_v : W → ℝ) (s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hs_W : ∀ w, isSpin (s_W w)) :
    |σ * s_v * ((h_u - σ * h_v) + ∑ w, (J_u w - σ * J_v w) * s_W w)| ≤
      2 * coflipRadius σ h_u h_v J_u J_v := by
  unfold coflipRadius
  have hσv : isSpin (σ * s_v) := isSpin_mul hσ hs_v
  rw [abs_mul, abs_of_isSpin hσv, one_mul]
  have htri :
      |(h_u - σ * h_v) + ∑ w, (J_u w - σ * J_v w) * s_W w| ≤
        |h_u - σ * h_v| + |∑ w, (J_u w - σ * J_v w) * s_W w| :=
    abs_add_le _ _
  have hsum :
      |∑ w, (J_u w - σ * J_v w) * s_W w| ≤ ∑ w, |J_u w - σ * J_v w| := by
    calc
      |∑ w, (J_u w - σ * J_v w) * s_W w|
        ≤ ∑ w, |(J_u w - σ * J_v w) * s_W w| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ w, |J_u w - σ * J_v w| := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [abs_mul, abs_of_isSpin (hs_W w), mul_one]
  linarith

/-- **Theorem 6 (Part 2A — Two-Sided Co-Flip Average Enclosure)**:
For any violating spin state ($s_u = -\sigma s_v$) with $s_v, \sigma \in \{-1, +1\}$ and
$s_W \in \{-1, +1\}^W$, the average repair energy change is enclosed in
$[-2\,\mathrm{coflipUpper}, -2\,\mathrm{coflipLower}]$. -/
theorem coflip_average_enclosure {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hs_W : ∀ w, isSpin (s_W w)) :
    -2 * coflipUpper σ h_u h_v J_uv J_u J_v ≤
        (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
          deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) / 2 ∧
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) / 2 ≤
        -2 * coflipLower σ h_u h_v J_uv J_u J_v := by
  rw [coflip_average_eq E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W hσ hs_v hviol]
  unfold coflipUpper coflipLower coflipCenter
  have habs := abs_coflip_fluctuation_le_two_mul_coflipRadius σ h_u h_v J_u J_v s_v s_W hσ hs_v hs_W
  have hlo := neg_le_of_abs_le habs
  have hhi := le_of_abs_le habs
  constructor <;> linarith

/-- **Theorem 6 (Part 2B — Best Single-Spin Repair Bound)**:
On any state violating $s_u = \sigma s_v$, the better of the two single-spin repairs satisfies
$\min(\Delta E_u, \Delta E_v) \le \frac{\Delta E_u + \Delta E_v}{2} \le -2\,\mathrm{coflipLower}$. -/
theorem min_deltaFlip_le_neg_two_mul_coflipLower {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hs_W : ∀ w, isSpin (s_W w)) :
    min (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W)
        (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) ≤
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) / 2 ∧
    (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) / 2 ≤
      -2 * coflipLower σ h_u h_v J_uv J_u J_v := by
  refine ⟨?_, (coflip_average_enclosure E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W
    hσ hs_v hviol hs_W).2⟩
  rcases le_total
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W)
      (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- **Theorem 6 (Part 2C — Strong `:coflip_pair` Persistency)**:
Whenever `coflipLower σ h_u h_v J_uv J_u J_v > 0`, on any state violating $s_u = \sigma s_v$,
at least one of the two single-spin repairs $(-s_u, s_v, s_W)$ or $(s_u, -s_v, s_W)$ decreases the
energy by at least $2\,\mathrm{coflipLower} > 0$. -/
theorem coflip_pair_strong_persistency {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hs_W : ∀ w, isSpin (s_W w))
    (hstrong : 0 < coflipLower σ h_u h_v J_uv J_u J_v) :
    (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤
        -2 * coflipLower σ h_u h_v J_uv J_u J_v ∧
      deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W < 0) ∨
    (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤
        -2 * coflipLower σ h_u h_v J_uv J_u J_v ∧
      deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W < 0) := by
  have havg :=
    (coflip_average_enclosure E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W hσ hs_v hviol hs_W).2
  rcases le_total
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W)
      (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) with h | h
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

/-- **Theorem 6 (Part 2D — Weak `:coflip_pair` Persistency)**:
Whenever `coflipLower σ h_u h_v J_uv J_u J_v ≥ 0`, on any state violating $s_u = \sigma s_v$,
at least one of the two single-spin repairs $(-s_u, s_v, s_W)$ or $(s_u, -s_v, s_W)$ does not
increase the energy ($\Delta E_u \le 0 \lor \Delta E_v \le 0$). -/
theorem coflip_pair_weak_persistency {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hs_W : ∀ w, isSpin (s_W w))
    (hweak : 0 ≤ coflipLower σ h_u h_v J_uv J_u J_v) :
    deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤ 0 ∨
      deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤ 0 := by
  have havg :=
    (coflip_average_enclosure E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W hσ hs_v hviol hs_W).2
  rcases le_total
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W)
      (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) with h | h
  · left; linarith
  · right; linarith

/-- Under structural twin matching ($h_u = \sigma h_v$ and $\forall w,\, J_u(w) = \sigma J_v(w)$),
the co-flip fluctuation radius vanishes identically (`coflipRadius = 0`). -/
theorem coflipRadius_eq_zero_of_twin {W : Type*} [Fintype W]
    (σ h_u h_v : ℝ) (J_u J_v : W → ℝ)
    (hh : h_u = σ * h_v) (hJ : ∀ w, J_u w = σ * J_v w) :
    coflipRadius σ h_u h_v J_u J_v = 0 := by
  unfold coflipRadius
  have hsum : (∑ w, |J_u w - σ * J_v w|) = 0 := by
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [hJ w, sub_self, abs_zero]
  rw [hh, sub_self, abs_zero, hsum]
  ring

/-- Under structural twin matching ($h_u = \sigma h_v$ and $\forall w,\, J_u(w) = \sigma J_v(w)$),
both `coflipLower` and `coflipUpper` collapse to the center $-\sigma J_{uv}$. -/
theorem coflipLower_eq_center_of_twin {W : Type*} [Fintype W]
    (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (hh : h_u = σ * h_v) (hJ : ∀ w, J_u w = σ * J_v w) :
    coflipLower σ h_u h_v J_uv J_u J_v = -σ * J_uv ∧
      coflipUpper σ h_u h_v J_uv J_u J_v = -σ * J_uv := by
  unfold coflipLower coflipUpper coflipCenter
  rw [coflipRadius_eq_zero_of_twin σ h_u h_v J_u J_v hh hJ]
  constructor <;> ring

/-- **Non-Adjacent Twin Contraction (`prove_twin` / `contract_twins!`)**:
When $J_{uv} = 0$, $h_u = \sigma h_v$, and $\forall w,\, J_u(w) = \sigma J_v(w)$,
`coflipCenter = 0`, `coflipRadius = 0`, `coflipLower = 0`, and on any violating state
$\Delta E_u + \Delta E_v = 0$, so at least one single-spin repair is non-increasing. -/
theorem nonadjacent_twin_weak_contraction {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hJuv : J_uv = 0) (hh : h_u = σ * h_v) (hJ : ∀ w, J_u w = σ * J_v w) :
    coflipCenter σ J_uv = 0 ∧
      coflipRadius σ h_u h_v J_u J_v = 0 ∧
      coflipLower σ h_u h_v J_uv J_u J_v = 0 ∧
      deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W = 0 ∧
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤ 0 ∨
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W ≤ 0) := by
  have hcenter : coflipCenter σ J_uv = 0 := by
    unfold coflipCenter; rw [hJuv]; ring
  have hrad := coflipRadius_eq_zero_of_twin σ h_u h_v J_u J_v hh hJ
  have hlow : coflipLower σ h_u h_v J_uv J_u J_v = 0 := by
    unfold coflipLower; rw [hcenter, hrad]; ring
  have havg := coflip_average_eq E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W hσ hs_v hviol
  have hsum0 : (∑ w, (J_u w - σ * J_v w) * s_W w) = 0 := by
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [hJ w, sub_self, zero_mul]
  have hrhs :
      2 * σ * J_uv +
        σ * s_v * ((h_u - σ * h_v) + ∑ w, (J_u w - σ * J_v w) * s_W w) = 0 := by
    rw [hJuv, hh, hsum0]; ring
  have hsum_delta :
      deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W +
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W = 0 := by
    linarith [havg, hrhs]
  refine ⟨hcenter, hrad, hlow, hsum_delta, ?_⟩
  rcases le_total
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W)
      (deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W) with h | h
  · left; linarith
  · right; linarith

/-- **Coupled Twin Strong Contraction**:
When $-\sigma J_{uv} > 0$, $h_u = \sigma h_v$, and $\forall w,\, J_u(w) = \sigma J_v(w)$,
`coflipLower = -σ * J_uv > 0` and every violating state has a strictly improving single-spin
repair. -/
theorem coupled_twin_strong_contraction {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_u s_v : ℝ) (s_W : W → ℝ)
    (hσ : isSpin σ) (hs_v : isSpin s_v) (hviol : s_u = -σ * s_v)
    (hs_W : ∀ w, isSpin (s_W w))
    (hJuv : 0 < -σ * J_uv) (hh : h_u = σ * h_v) (hJ : ∀ w, J_u w = σ * J_v w) :
    0 < coflipLower σ h_u h_v J_uv J_u J_v ∧
      (deltaFlipU E_rest h_u h_v J_uv J_u J_v s_u s_v s_W < 0 ∨
        deltaFlipV E_rest h_u h_v J_uv J_u J_v s_u s_v s_W < 0) := by
  have hlow := (coflipLower_eq_center_of_twin σ h_u h_v J_uv J_u J_v hh hJ).1
  have hpos : 0 < coflipLower σ h_u h_v J_uv J_u J_v := by linarith
  refine ⟨hpos, ?_⟩
  rcases coflip_pair_strong_persistency E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W
      hσ hs_v hviol hs_W hpos with ⟨_, hlt⟩ | ⟨_, hlt⟩
  · exact Or.inl hlt
  · exact Or.inr hlt

/-!
### Part 3: One-Sided $N(v)$ Decomposition and Monotone Increment Identities
-/

/-- **Theorem 6 (Part 3A — One-Sided Difference Decomposition)**:
Exact decomposition of $\sum_{w \in W} |J_u(w) - \sigma J_v(w)|$ into $\sum_{w \in W} |J_u(w)|$
plus the one-sided adjustment $\sum_{w \in W} (|J_u(w) - \sigma J_v(w)| - |J_u(w)|)$ used in
`prove_relation` (`src/certificates.jl:1173-1197`) and `_verify_relation_step`
(`src/certificates.jl:4997-5013`). -/
theorem one_sided_diff_sum_eq {W : Type*} [Fintype W]
    (σ : ℝ) (J_u J_v : W → ℝ) :
    (∑ w, |J_u w - σ * J_v w|) =
      (∑ w, |J_u w|) + ∑ w, (|J_u w - σ * J_v w| - |J_u w|) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring

/-- Per-neighbor monotone pruning increment
$\Delta_w(\sigma, J_{uw}, J_{vw}) = |J_{uw} - \sigma J_{vw}| + |J_{uw}| - |J_{vw}|$
accumulated during early-exit pruning in `_can_possibly_contract`. -/
noncomputable def coflipDelta (σ J_uw J_vw : ℝ) : ℝ :=
  |J_uw - σ * J_vw| + |J_uw| - |J_vw|

/-- **Theorem 6 (Part 3B — Pointwise Non-Negativity of the Pruning Increment)**:
For every $\sigma \in \{-1, +1\}$ and arbitrary real couplings $J_{uw}, J_{vw} \in \mathbb{R}$,
$\Delta_w(\sigma, J_{uw}, J_{vw}) = |J_{uw} - \sigma J_{vw}| + |J_{uw}| - |J_{vw}| \ge 0$,
confirming that the partial sum accumulated over $w \in N(v)$ is monotonically non-decreasing. -/
theorem coflipDelta_nonneg (σ J_uw J_vw : ℝ) (hσ : isSpin σ) :
    0 ≤ coflipDelta σ J_uw J_vw := by
  unfold coflipDelta
  have habs_v : |J_vw| = |σ * J_vw| := by
    rw [abs_mul, abs_of_isSpin hσ, one_mul]
  have htri : |σ * J_vw| ≤ |J_uw - σ * J_vw| + |J_uw| := by
    have hsplit : σ * J_vw = J_uw - (J_uw - σ * J_vw) := by ring
    calc
      |σ * J_vw| = |J_uw - (J_uw - σ * J_vw)| := by rw [← hsplit]
      _ ≤ |J_uw| + |J_uw - σ * J_vw| := abs_sub _ _
      _ = |J_uw - σ * J_vw| + |J_uw| := add_comm _ _
  linarith

/-- Triangle-inequality upper bound $|J_{uw} - \sigma J_{vw}| \le |J_{uw}| + |J_{vw}|$ on each
shared neighbor $w$ when $\sigma \in \{-1, +1\}$. -/
theorem abs_coflip_diff_le_add_abs (σ J_uw J_vw : ℝ) (hσ : isSpin σ) :
    |J_uw - σ * J_vw| ≤ |J_uw| + |J_vw| := by
  have habs_v : |σ * J_vw| = |J_vw| := by
    rw [abs_mul, abs_of_isSpin hσ, one_mul]
  calc
    |J_uw - σ * J_vw| ≤ |J_uw| + |σ * J_vw| := abs_sub _ _
    _ = |J_uw| + |J_vw| := by rw [habs_v]

/-- **Theorem 6 (Part 3C — Strict Shared-Neighbor Cancellation)**:
Whenever $\sigma \in \{-1, +1\}$ and $\sigma J_{uw} J_{vw} > 0$ (i.e., $J_{uw}$ and $\sigma J_{vw}$
have the same nonzero sign), the co-flip residual satisfies the strict inequality
$|J_{uw} - \sigma J_{vw}| < |J_{uw}| + |J_{vw}|$. -/
theorem abs_coflip_diff_lt_add_abs_of_aligned (σ J_uw J_vw : ℝ)
    (hσ : isSpin σ) (halign : 0 < σ * J_uw * J_vw) :
    |J_uw - σ * J_vw| < |J_uw| + |J_vw| := by
  have habs_v : |J_vw| = |σ * J_vw| := by
    rw [abs_mul, abs_of_isSpin hσ, one_mul]
  rw [habs_v]
  have hprod : 0 < J_uw * (σ * J_vw) := by
    calc
      0 < σ * J_uw * J_vw := halign
      _ = J_uw * (σ * J_vw) := by ring
  rcases le_total 0 J_uw with hJu | hJu
  · have hJu_pos : 0 < J_uw := by
      rcases eq_or_lt_of_le hJu with rfl | hlt
      · simp at hprod
      · exact hlt
    have hJv_pos : 0 < σ * J_vw := pos_of_mul_pos_right hprod hJu
    rw [abs_of_pos hJu_pos, abs_of_pos hJv_pos]
    rcases le_total 0 (J_uw - σ * J_vw) with hdiff | hdiff
    · rw [abs_of_nonneg hdiff]; linarith
    · rw [abs_of_nonpos hdiff]; linarith
  · have hJu_neg : J_uw < 0 := by
      rcases eq_or_lt_of_le hJu with rfl | hlt
      · simp at hprod
      · exact hlt
    have hJv_neg : σ * J_vw < 0 := neg_of_mul_pos_right hprod hJu
    rw [abs_of_neg hJu_neg, abs_of_neg hJv_neg]
    rcases le_total 0 (J_uw - σ * J_vw) with hdiff | hdiff
    · rw [abs_of_nonneg hdiff]; linarith
    · rw [abs_of_nonpos hdiff]; linarith

/-- **Theorem 6 (Part 3D — Co-Flip Radius vs. Single-Star / GLK Sum Radius)**:
For any $\sigma \in \{-1, +1\}$, the co-flip fluctuation radius never exceeds the uncancelled
sum of individual $\ell_1$ field and coupling radii:
$$\mathrm{coflipRadius}(\sigma, h_u, h_v, J_u, J_v)
  \le \frac{|h_u| + |h_v| + \sum_{w \in W} |J_u(w)| + \sum_{w \in W} |J_v(w)|}{2}.$$ -/
theorem coflipRadius_le_glk_sum_radius {W : Type*} [Fintype W]
    (σ h_u h_v : ℝ) (J_u J_v : W → ℝ) (hσ : isSpin σ) :
    coflipRadius σ h_u h_v J_u J_v ≤
      (|h_u| + |h_v| + (∑ w, |J_u w|) + ∑ w, |J_v w|) / 2 := by
  unfold coflipRadius
  have hh : |h_u - σ * h_v| ≤ |h_u| + |h_v| := abs_coflip_diff_le_add_abs σ h_u h_v hσ
  have hsum :
      (∑ w, |J_u w - σ * J_v w|) ≤ (∑ w, |J_u w|) + ∑ w, |J_v w| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun w _ => abs_coflip_diff_le_add_abs σ (J_u w) (J_v w) hσ)
  linarith

/-!
### Part 4: Compositional `ReductionStep` and `StrongReductionStep` Bridges
-/

/-- Feasible spin set for the pair-contracted reduced space $Y = \mathbb{R} \times (W \to \mathbb{R})$
representing $(s_v, s_W) \in \{-1, +1\} \times \{-1, +1\}^W$. -/
def pairReducedSet (W : Type*) : Set (ℝ × (W → ℝ)) :=
  {y | isSpin y.1 ∧ ∀ w, isSpin (y.2 w)}

/-- Feasible spin set for the full space $X = (\mathbb{R} \times (W \to \mathbb{R})) \times \mathbb{R}$
representing $((s_v, s_W), s_u) \in (\{-1, +1\} \times \{-1, +1\}^W) \times \{-1, +1\}$. -/
def pairFullSet (W : Type*) : Set ((ℝ × (W → ℝ)) × ℝ) :=
  pairReducedSet W ×ˢ {s_u | isSpin s_u}

/-- Full objective function on $X = (\mathbb{R} \times (W \to \mathbb{R})) \times \mathbb{R}$ mapping
$((s_v, s_W), s_u) \mapsto E(s_u, s_v, s_W)$. -/
noncomputable def pairFullEnergy {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (x : (ℝ × (W → ℝ)) × ℝ) : ℝ :=
  pairEnvEnergy E_rest h_u h_v J_uv J_u J_v x.2 x.1.1 x.1.2

/-- Pair-contracted reduced objective on $Y = \mathbb{R} \times (W \to \mathbb{R})$ obtained by
substituting $s_u = \sigma s_v$: $(s_v, s_W) \mapsto E(\sigma s_v, s_v, s_W)$. -/
noncomputable def pairContractedEnergy {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (y : ℝ × (W → ℝ)) : ℝ :=
  pairEnvEnergy E_rest h_u h_v J_uv J_u J_v (σ * y.1) y.1 y.2

/-- Reconstruction map $(s_v, s_W) \mapsto ((s_v, s_W), \sigma s_v)$ for pair contraction
$s_u = \sigma s_v$. -/
def coflipReconstruct {W : Type*} (σ : ℝ) :
    (ℝ × (W → ℝ)) → (ℝ × (W → ℝ)) × ℝ :=
  reconstruct (fun y => σ * y.1)

/-- Explicit coefficient-merging identity for `pairContractedEnergy` when $s_v \in \{-1, +1\}$:
substituting $s_u = \sigma s_v$ shifts the constant offset by $\sigma J_{uv}$, merges the linear
field into $(\sigma h_u + h_v) s_v$, and merges each neighbor coupling into
$(\sigma J_u(w) + J_v(w)) s_v s_w$, matching `contract_variables!`. -/
theorem pairContractedEnergy_eq_merged {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (s_v : ℝ) (s_W : W → ℝ) (hs_v : isSpin s_v) :
    pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v (s_v, s_W) =
      E_rest s_W + σ * J_uv + (σ * h_u + h_v) * s_v +
        ∑ w, (σ * J_u w + J_v w) * s_v * s_W w := by
  unfold pairContractedEnergy pairEnvEnergy
  dsimp
  have hsv2 : s_v * s_v = 1 := isSpin_mul_self hs_v
  have hsum :
      (∑ w, (J_u w * (σ * s_v) + J_v w * s_v) * s_W w) =
        ∑ w, (σ * J_u w + J_v w) * s_v * s_W w := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    ring
  rw [hsum]
  calc
    E_rest s_W + h_u * (σ * s_v) + h_v * s_v + J_uv * (σ * s_v) * s_v +
        ∑ w, (σ * J_u w + J_v w) * s_v * s_W w
      = E_rest s_W + σ * J_uv * (s_v * s_v) + (σ * h_u + h_v) * s_v +
          ∑ w, (σ * J_u w + J_v w) * s_v * s_W w := by ring
    _ = E_rest s_W + σ * J_uv + (σ * h_u + h_v) * s_v +
          ∑ w, (σ * J_u w + J_v w) * s_v * s_W w := by rw [hsv2, mul_one]

/-- **Theorem 6 (Part 4A — Compositional `ReductionStep` Bridge for Weak Co-Flip Contraction)**:
Whenever $\sigma \in \{-1, +1\}$ and `0 ≤ coflipLower σ h_u h_v J_uv J_u J_v`, pair contraction
$s_u = \sigma s_v$ defines a valid `ReductionStep` from `pairFullEnergy` on `pairFullSet W` to
`pairContractedEnergy` on `pairReducedSet W` with reconstruction map `coflipReconstruct σ`. -/
theorem coflip_reductionStep {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (hσ : isSpin σ)
    (hweak : 0 ≤ coflipLower σ h_u h_v J_uv J_u J_v) :
    ReductionStep (pairFullSet W)
      (pairFullEnergy E_rest h_u h_v J_uv J_u J_v)
      (pairReducedSet W)
      (pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v)
      (coflipReconstruct σ) where
  maps_into y hy := ⟨hy, isSpin_mul hσ hy.1⟩
  energy_eq _ _ := rfl
  weak_dom := by
    rintro ⟨⟨s_v, s_W⟩, s_u⟩ ⟨⟨hs_v, hs_W⟩, hs_u⟩
    rcases spin_rel_or_viol hs_u hs_v hσ with hrel | hviol
    · refine ⟨(s_v, s_W), ⟨hs_v, hs_W⟩, ?_⟩
      unfold pairContractedEnergy pairFullEnergy
      dsimp
      rw [← hrel]
    · rcases coflip_pair_weak_persistency E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W
          hσ hs_v hviol hs_W hweak with hdu | hdv
      · refine ⟨(s_v, s_W), ⟨hs_v, hs_W⟩, ?_⟩
        unfold pairContractedEnergy pairFullEnergy
        dsimp
        have hrep : σ * s_v = -s_u := (repair_u_satisfies_relation hviol).symm
        rw [hrep]
        unfold deltaFlipU at hdu
        linarith
      · refine ⟨(-s_v, s_W), ⟨isSpin_neg hs_v, hs_W⟩, ?_⟩
        unfold pairContractedEnergy pairFullEnergy
        dsimp
        have hrep : σ * (-s_v) = s_u := (repair_v_satisfies_relation hviol).symm
        rw [hrep]
        unfold deltaFlipV at hdv
        linarith

/-- **Theorem 6 (Part 4B — Compositional `StrongReductionStep` Bridge for Strong Co-Flip Contraction)**:
Whenever $\sigma \in \{-1, +1\}$ and `0 < coflipLower σ h_u h_v J_uv J_u J_v`, pair contraction
$s_u = \sigma s_v$ defines a `StrongReductionStep`, so `coflipReconstruct σ` is surjective onto the
set of all global minimizers of `pairFullEnergy` on `pairFullSet W`. -/
theorem coflip_strongReductionStep {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (hσ : isSpin σ)
    (hstrong : 0 < coflipLower σ h_u h_v J_uv J_u J_v) :
    StrongReductionStep (pairFullSet W)
      (pairFullEnergy E_rest h_u h_v J_uv J_u J_v)
      (pairReducedSet W)
      (pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v)
      (coflipReconstruct σ) where
  toReductionStep :=
    coflip_reductionStep E_rest σ h_u h_v J_uv J_u J_v hσ (le_of_lt hstrong)
  surj_on_min := by
    rintro ⟨⟨s_v, s_W⟩, s_u⟩ ⟨⟨⟨hs_v, hs_W⟩, hs_u⟩, hmin⟩
    dsimp at hs_v hs_W hs_u
    rcases spin_rel_or_viol hs_u hs_v hσ with hrel | hviol
    · refine ⟨(s_v, s_W), ⟨⟨hs_v, hs_W⟩, ?_⟩, ?_⟩
      · intro y' hy'
        have hx' : coflipReconstruct σ y' ∈ pairFullSet W :=
          ⟨hy', isSpin_mul hσ hy'.1⟩
        have hle := hmin (coflipReconstruct σ y') hx'
        unfold pairFullEnergy coflipReconstruct reconstruct at hle
        unfold pairContractedEnergy
        dsimp at hle ⊢
        rw [hrel] at hle
        exact hle
      · unfold coflipReconstruct reconstruct
        dsimp
        rw [← hrel]
    · exfalso
      rcases coflip_pair_strong_persistency E_rest σ h_u h_v J_uv J_u J_v s_u s_v s_W
          hσ hs_v hviol hs_W hstrong with ⟨_, hdu⟩ | ⟨_, hdv⟩
      · have hx' : ((s_v, s_W), -s_u) ∈ pairFullSet W :=
          ⟨⟨hs_v, hs_W⟩, isSpin_neg hs_u⟩
        have hle := hmin ((s_v, s_W), -s_u) hx'
        unfold pairFullEnergy at hle
        unfold deltaFlipU at hdu
        dsimp at hle
        linarith
      · have hx' : ((-s_v, s_W), s_u) ∈ pairFullSet W :=
          ⟨⟨isSpin_neg hs_v, hs_W⟩, hs_u⟩
        have hle := hmin ((-s_v, s_W), s_u) hx'
        unfold pairFullEnergy at hle
        unfold deltaFlipV at hdv
        dsimp at hle
        linarith

/-- **Corollary (Global Minimum Preservation under Weak Co-Flip Contraction)**:
When `0 ≤ coflipLower σ h_u h_v J_uv J_u J_v`, any global minimizer of `pairContractedEnergy`
on `pairReducedSet W` reconstructs via `coflipReconstruct σ` to a global minimizer of
`pairFullEnergy` on `pairFullSet W` with identical energy. -/
theorem coflip_preserves_global_min {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (hσ : isSpin σ)
    (hweak : 0 ≤ coflipLower σ h_u h_v J_uv J_u J_v)
    {y : ℝ × (W → ℝ)}
    (hy : IsGlobalMin (pairReducedSet W)
      (pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v) y) :
    IsGlobalMin (pairFullSet W)
        (pairFullEnergy E_rest h_u h_v J_uv J_u J_v) (coflipReconstruct σ y) ∧
      pairFullEnergy E_rest h_u h_v J_uv J_u J_v (coflipReconstruct σ y) =
        pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v y :=
  (coflip_reductionStep E_rest σ h_u h_v J_uv J_u J_v hσ hweak).preserves_global_min hy

/-- **Corollary (Exact Bijection on Global Minimizers under Strong Co-Flip Contraction)**:
When `0 < coflipLower σ h_u h_v J_uv J_u J_v`, the set of global minimizers of `pairFullEnergy`
on `pairFullSet W` is the exact image under `coflipReconstruct σ` of the set of global minimizers
of `pairContractedEnergy` on `pairReducedSet W`. -/
theorem coflip_strong_image_global_min_eq {W : Type*} [Fintype W]
    (E_rest : (W → ℝ) → ℝ) (σ h_u h_v J_uv : ℝ) (J_u J_v : W → ℝ)
    (hσ : isSpin σ)
    (hstrong : 0 < coflipLower σ h_u h_v J_uv J_u J_v) :
    {x | IsGlobalMin (pairFullSet W) (pairFullEnergy E_rest h_u h_v J_uv J_u J_v) x} =
      coflipReconstruct σ ''
        {y | IsGlobalMin (pairReducedSet W)
          (pairContractedEnergy E_rest σ h_u h_v J_uv J_u J_v) y} :=
  (coflip_strongReductionStep E_rest σ h_u h_v J_uv J_u J_v hσ hstrong).image_global_min_eq

end QUBOPreprocessing
