import Mathlib
import QUBOPreprocessing.GaugeCoercive

/-!
# Theorem 4: Exact Coefficient Compression Audit, Refutations, and Subsumption

This module formalizes Theorem 4 of `QUBOPreprocessing.jl` (`docs/src/dominance.md`, Section
"Exact coefficient compression and sparsification audit (`#21`)"), auditing the parameter
compression rules of Mücke, Gerlach & Piatkowski (2023), *Optimum-Preserving QUBO Parameter
Compression* (`arXiv:2307.02195`, Theorem 2):
1. **Closed-endpoint tie counterexamples** (`endpoint_tie_counterexample` and
   `quadratic_endpoint_tie_counterexample`): at the closed threshold $\tau = 0$, both diagonal and
   off-diagonal compression introduce strictly suboptimal states into $\operatorname{opt}(F')$,
   violating the reconstruction soundness contract $\operatorname{opt}(F') \subseteq \operatorname{opt}(F)$.
2. **Open-interior negative quadratic compression refutation**
   (`negative_quadratic_lost_optimum_counterexample`): on
   $F(x_1, x_2) = 2 x_1 + 2 x_2 - 5 x_1 x_2$ with open-interior threshold $\tau = 1/10 > 0$,
   compressing $Q_{12} = -5 \mapsto Q'_{12} = -21/10$ preserves 1-bit flip optimality at $(1, 1)$
   relative to $(1, 0)$ and $(0, 1)$ by margin $\tau = 1/10 > 0$, yet raises $F'(1, 1) = 19/10$
   above the 2-bit flip $F'(0, 0) = 0$, making $\operatorname{opt}(F) = \{(1, 1)\}$ and
   $\operatorname{opt}(F') = \{(0, 0)\}$ completely disjoint.
3. **Subsumption by exact unary dominance** (`diagonal_compression_subsumed_by_dominance` and
   `positive_quadratic_sparsification_subsumed_by_dominance`): open-interior diagonal compression
   and positive-coupling sparsification ($Q'_{ij} = 0$ for $Q_{ij} > 0$) hold if and only if at
   least one endpoint already satisfies the strict Hammer–Hansen–Simeone unary dominance condition
   $L_a + c_a^- > 0$ (or $L_a + c_a^+ < 0$), which eliminates the variable and all incident
   couplings outright.
4. **Non-constant energy transport** (`in_place_compression_nonconstant_shift`): a 2-variable
   in-place coefficient perturbation $\delta_1 x_1 + \delta_2 x_2 + \delta_{12} x_1 x_2$ produces a
   state-independent constant energy shift on $\{0, 1\}^2$ if and only if
   $\delta_1 = \delta_2 = \delta_{12} = 0$.
-/

namespace QUBOPreprocessing

/-- Two-variable Boolean QUBO objective $F(x_1, x_2) = L_1 x_1 + L_2 x_2 + Q_{12} x_1 x_2$. -/
def qubo2 (L₁ L₂ Q₁₂ x₁ x₂ : ℝ) : ℝ :=
  L₁ * x₁ + L₂ * x₂ + Q₁₂ * x₁ * x₂

/-- **Theorem 4 (Part 1a: Closed-Endpoint Diagonal Tie Counterexample)**:
For $F(x_1) = x_1$ and its closed-endpoint ($\tau = 0$) compressed polynomial $F'(x_1) = 0$:
- $x_1 = 0$ is the unique global minimizer of $F$ on $\{0, 1\}$ ($F(0) = 0 < 1 = F(1)$),
- yet $x_1 = 1$ minimizes $F'$ on $\{0, 1\}$ ($F'(1) = F'(0) = 0$), violating
  $\operatorname{opt}(F') \subseteq \operatorname{opt}(F)$. -/
theorem endpoint_tie_counterexample :
    let F : ℝ → ℝ := fun x₁ => x₁
    let F' : ℝ → ℝ := fun _ => 0
    (F 0 < F 1) ∧
    (∀ x₁ : ℝ, isBool x₁ → F' 1 ≤ F' x₁) := by
  refine ⟨by norm_num, ?_⟩
  intro x₁ _
  norm_num

/-- **Theorem 4 (Part 1b: Closed-Endpoint Quadratic Tie Counterexample)**:
For $F(x_1, x_2) = -x_1 - x_2 + 3 x_1 x_2$ and its closed-endpoint ($\tau = 0$) compressed
polynomial $F'(x_1, x_2) = -x_1 - x_2 + x_1 x_2$:
- On $\{0, 1\}^2$, the global minimum value of $F$ is $-1$ (attained at $(1, 0)$ and $(0, 1)$),
  while $F(1, 1) = 1 > -1$ is strictly suboptimal.
- In $F'$, $(1, 1)$ attains the global minimum value $-1$ across all $(x_1, x_2) \in \{0, 1\}^2$,
  so $(1, 1) \in \operatorname{opt}(F') \setminus \operatorname{opt}(F)$. -/
theorem quadratic_endpoint_tie_counterexample :
    let F := qubo2 (-1) (-1) 3
    let F' := qubo2 (-1) (-1) 1
    (∀ x₁ x₂ : ℝ, isBool x₁ → isBool x₂ → F 1 0 ≤ F x₁ x₂) ∧
    (F 1 0 < F 1 1) ∧
    (∀ x₁ x₂ : ℝ, isBool x₁ → isBool x₂ → F' 1 1 ≤ F' x₁ x₂) := by
  refine ⟨?_, by unfold qubo2; norm_num, ?_⟩
  · intro x₁ x₂ hx₁ hx₂
    unfold qubo2
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl <;> norm_num
  · intro x₁ x₂ hx₁ hx₂
    unfold qubo2
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl <;> norm_num

/-- **Theorem 4 (Part 2: Open-Interior Negative Quadratic Compression Loses All Original Optima)**:
Let $F(x_1, x_2) = 2 x_1 + 2 x_2 - 5 x_1 x_2$ and let $\tau = 1/10 > 0$. Applying the Mücke et al.
(2023) Theorem 2 negative-coupling compression rule
$Q'_{12} = -L_1 - c_{1,-2}^+ - \tau = -2 - 0 - 1/10 = -21/10$ yields
$F'(x_1, x_2) = 2 x_1 + 2 x_2 - \frac{21}{10} x_1 x_2$, for which:
1. $\tau = 1/10 > 0$ and the precondition $L_a + c_{a,-b}^+ + Q_{12} = -3 \le -\tau$ holds.
2. $(1, 1)$ is the **unique** global minimizer of $F$ on $\{0, 1\}^2$ ($F(1, 1) = -1$).
3. In $F'$, $(1, 1)$ still strictly beats both 1-bit flip neighbors $(1, 0)$ and $(0, 1)$ by exact
   margin $\tau = 1/10 > 0$.
4. Yet $(0, 0)$ is the **unique** global minimizer of $F'$ on $\{0, 1\}^2$
   ($F'(0, 0) = 0 < 19/10 = F'(1, 1)$), so $\operatorname{opt}(F) \cap \operatorname{opt}(F') = \emptyset$. -/
theorem negative_quadratic_lost_optimum_counterexample :
    let L₁ : ℝ := 2
    let L₂ : ℝ := 2
    let Q₁₂ : ℝ := -5
    let τ : ℝ := 1 / 10
    let Q'₁₂ : ℝ := -L₁ - τ
    let F := qubo2 L₁ L₂ Q₁₂
    let F' := qubo2 L₁ L₂ Q'₁₂
    (0 < τ) ∧
    (L₁ + Q₁₂ ≤ -τ) ∧
    (Q'₁₂ = -21 / 10) ∧
    (∀ x₁ x₂ : ℝ, isBool x₁ → isBool x₂ → (x₁, x₂) ≠ (1, 1) → F 1 1 < F x₁ x₂) ∧
    (F' 1 0 - F' 1 1 = τ ∧ F' 0 1 - F' 1 1 = τ) ∧
    (∀ x₁ x₂ : ℝ, isBool x₁ → isBool x₂ → (x₁, x₂) ≠ (0, 0) → F' 0 0 < F' x₁ x₂) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro x₁ x₂ hx₁ hx₂ hne
    unfold qubo2
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact False.elim (hne rfl)
  · unfold qubo2
    constructor <;> norm_num
  · intro x₁ x₂ hx₁ hx₂ hne
    unfold qubo2
    rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl
    · exact False.elim (hne rfl)
    · norm_num
    · norm_num
    · norm_num

/-- **Theorem 4 (Part 3a: Open-Interior Diagonal Compression Subsumed by Strict Unary Dominance)**:
For any open-interior threshold $\tau > 0$, the diagonal compression preconditions
$L_i + c_i^- \ge \tau$ and $L_i + c_i^+ \le -\tau$ imply the strict Hammer–Hansen–Simeone unary
dominance conditions $L_i + c_i^- > 0$ (fixing $x_i^* = 0$) and $L_i + c_i^+ < 0$ (fixing
$x_i^* = 1$). -/
theorem diagonal_compression_subsumed_by_dominance (L_i c_i_neg c_i_pos τ : ℝ) (hτ : 0 < τ) :
    ((L_i + c_i_neg ≥ τ → L_i + c_i_neg > 0) ∧
     (L_i + c_i_pos ≤ -τ → L_i + c_i_pos < 0)) := by
  constructor <;> intro h <;> linarith

/-- For a positive quadratic coupling $Q_{ij} > 0$, the pair-excluded lower derivative bound
$c_{a,-b}^- = c_a^- - \min(0, Q_{ij})$ is identical to the full lower derivative bound $c_a^-$. -/
theorem pair_excluded_lower_eq_full_of_pos {c_a_neg Q_ij : ℝ} (hQ : 0 < Q_ij) :
    c_a_neg - min 0 Q_ij = c_a_neg := by
  rw [min_eq_left (le_of_lt hQ), sub_zero]

/-- **Theorem 4 (Part 3b: Positive Quadratic Sparsification Subsumed by Strict Unary Dominance)**:
For a positive coupling $Q_{ij} > 0$ and open-interior threshold $\tau > 0$, the Mücke et al.
(2023) compressed coupling
$Q'_{ij} = \min(\max(0, -L_i - c_{i,-j}^- + \tau), \max(0, -L_j - c_{j,-i}^- + \tau))$
is sparsified to $0$ if and only if $L_i + c_i^- \ge \tau > 0$ or $L_j + c_j^- \ge \tau > 0$
(so at least one endpoint is already fixed to $0$ by strict unary dominance). -/
theorem positive_quadratic_sparsification_subsumed_by_dominance
    (L_i L_j c_i_neg c_j_neg Q_ij τ : ℝ) (hQ : 0 < Q_ij) :
    let c_i_excl := c_i_neg - min 0 Q_ij
    let c_j_excl := c_j_neg - min 0 Q_ij
    let Q'_ij := min (max 0 (-L_i - c_i_excl + τ)) (max 0 (-L_j - c_j_excl + τ))
    Q'_ij = 0 ↔ (L_i + c_i_neg ≥ τ ∨ L_j + c_j_neg ≥ τ) := by
  intro c_i_excl c_j_excl Q'_ij
  have hi : c_i_excl = c_i_neg := pair_excluded_lower_eq_full_of_pos hQ
  have hj : c_j_excl = c_j_neg := pair_excluded_lower_eq_full_of_pos hQ
  change min (max 0 (-L_i - c_i_excl + τ)) (max 0 (-L_j - c_j_excl + τ)) = 0 ↔ _
  rw [hi, hj]
  have h1 : 0 ≤ max 0 (-L_i - c_i_neg + τ) := le_max_left _ _
  have h2 : 0 ≤ max 0 (-L_j - c_j_neg + τ) := le_max_left _ _
  constructor
  · intro hmin
    rcases min_cases (max 0 (-L_i - c_i_neg + τ)) (max 0 (-L_j - c_j_neg + τ)) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq] at hmin
      have hle : -L_i - c_i_neg + τ ≤ 0 := by
        calc
          -L_i - c_i_neg + τ ≤ max 0 (-L_i - c_i_neg + τ) := le_max_right _ _
          _ = 0 := hmin
      left; linarith
    · rw [heq] at hmin
      have hle : -L_j - c_j_neg + τ ≤ 0 := by
        calc
          -L_j - c_j_neg + τ ≤ max 0 (-L_j - c_j_neg + τ) := le_max_right _ _
          _ = 0 := hmin
      right; linarith
  · rintro (hli | hlj)
    · have hmax : max 0 (-L_i - c_i_neg + τ) = 0 := max_eq_left (by linarith)
      rw [hmax, min_eq_left h2]
    · have hmax : max 0 (-L_j - c_j_neg + τ) = 0 := max_eq_left (by linarith)
      rw [hmax, min_eq_right h1]

/-- **Theorem 4 (Part 4: Non-Constant Energy Shift of In-Place Coefficient Compression)**:
A 2-variable coefficient perturbation $\Delta F(x_1, x_2) = \delta_1 x_1 + \delta_2 x_2 + \delta_{12} x_1 x_2$
is constant across the four Boolean states $(x_1, x_2) \in \{0, 1\}^2$ if and only if
$\delta_1 = 0 \wedge \delta_2 = 0 \wedge \delta_{12} = 0$. -/
theorem in_place_compression_nonconstant_shift (δ₁ δ₂ δ₁₂ : ℝ) :
    (∃ C : ℝ, ∀ x₁ x₂ : ℝ, isBool x₁ → isBool x₂ → qubo2 δ₁ δ₂ δ₁₂ x₁ x₂ = C) ↔
      (δ₁ = 0 ∧ δ₂ = 0 ∧ δ₁₂ = 0) := by
  constructor
  · rintro ⟨C, hC⟩
    have h00 := hC 0 0 (Or.inl rfl) (Or.inl rfl)
    have h10 := hC 1 0 (Or.inr rfl) (Or.inl rfl)
    have h01 := hC 0 1 (Or.inl rfl) (Or.inr rfl)
    have h11 := hC 1 1 (Or.inr rfl) (Or.inr rfl)
    unfold qubo2 at h00 h10 h01 h11
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨0, ?_⟩
    intro x₁ x₂ _ _
    unfold qubo2
    ring

end QUBOPreprocessing
