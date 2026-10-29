import Mathlib
import QUBOPreprocessing.GaugeCoercive

/-!
# Theorem 2: Compositional Soundness of Reduction Sequences, Monotonic Repair, and Star–Triangle Elimination

This module formalizes Theorem 2 and Corollary 2.1 of `QUBOPreprocessing.jl` (`docs/src/dominance.md`):
1. The abstract structure `ReductionStep` (and `StrongReductionStep`) capturing a single
   preprocessing step $(S_X, F_X) \rightsquigarrow (S_Y, F_Y)$ with reconstruction map $R : Y \to X$.
2. Closure under composition (`ReductionStep.comp` and `StrongReductionStep.comp`), proving by
   induction that any finite chain of valid preprocessing steps preserves the global minimum value
   and reconstructs a valid global minimizer of the original instance.
3. Corollary 2.1 (`repair_monotone` and `repair_strict_improvement`): conditional elimination rules
   $z = g(y)$ define valid reduction steps on $S_Y \times S_Z$ and act as monotonic (and strictly
   improving when $z \neq g(y)$ is suboptimal) post-processing repair operators on arbitrary
   feasible heuristic solutions.
4. Exact Walsh–Hadamard star–triangle elimination for a zero-field degree-3 Ising spin
   (`starTriPoly_eq_starMin`), showing that minimizing out $s_0 \in \{-1, +1\}$ with three
   incident couplings $(J_1, J_2, J_3)$ produces an even function on $\{-1, +1\}^3$ whose cubic
   Walsh coefficient vanishes identically and which is represented with zero error on all $8$ spin
   configurations by the explicit triangle polynomial of Eq. (4) in `docs/src/dominance.md`.
-/

namespace QUBOPreprocessing

/-- `IsGlobalMin S F x` states that `x` belongs to the feasible set `S` and attains the minimum
of `F` over `S`. -/
def IsGlobalMin {X : Type*} (S : Set X) (F : X → ℝ) (x : X) : Prop :=
  x ∈ S ∧ ∀ x' ∈ S, F x ≤ F x'

/-- A weak preprocessing reduction step from `(S_X, F_X)` to `(S_Y, F_Y)` with reconstruction
map `R : Y → X`. -/
structure ReductionStep {X Y : Type*} (S_X : Set X) (F_X : X → ℝ)
    (S_Y : Set Y) (F_Y : Y → ℝ) (R : Y → X) : Prop where
  maps_into : ∀ y ∈ S_Y, R y ∈ S_X
  energy_eq : ∀ y ∈ S_Y, F_X (R y) = F_Y y
  weak_dom : ∀ x ∈ S_X, ∃ y ∈ S_Y, F_Y y ≤ F_X x

/-- The identity map is a valid reduction step. -/
theorem ReductionStep.id {X : Type*} (S_X : Set X) (F_X : X → ℝ) :
    ReductionStep S_X F_X S_X F_X _root_.id where
  maps_into _ hy := hy
  energy_eq _ _ := rfl
  weak_dom x hx := ⟨x, hx, le_rfl⟩

/-- **Theorem 2 (Compositional Closure)**: The composition of two valid reduction steps is a valid
reduction step with composite reconstruction map `R₁ ∘ R₂`. -/
theorem ReductionStep.comp {X Y Z : Type*}
    {S_X : Set X} {F_X : X → ℝ} {S_Y : Set Y} {F_Y : Y → ℝ} {S_Z : Set Z} {F_Z : Z → ℝ}
    {R₁ : Y → X} {R₂ : Z → Y}
    (h₁ : ReductionStep S_X F_X S_Y F_Y R₁)
    (h₂ : ReductionStep S_Y F_Y S_Z F_Z R₂) :
    ReductionStep S_X F_X S_Z F_Z (R₁ ∘ R₂) where
  maps_into z hz := h₁.maps_into (R₂ z) (h₂.maps_into z hz)
  energy_eq z hz := by
    simp only [Function.comp_apply]
    rw [h₁.energy_eq (R₂ z) (h₂.maps_into z hz), h₂.energy_eq z hz]
  weak_dom x hx := by
    rcases h₁.weak_dom x hx with ⟨y, hy, hfy⟩
    rcases h₂.weak_dom y hy with ⟨z, hz, hfz⟩
    exact ⟨z, hz, le_trans hfz hfy⟩

/-- **Theorem 2 (Global Minimum Preservation)**: Any global minimizer `y*` of the reduced instance
`(S_Y, F_Y)` reconstructs to a global minimizer `R y*` of `(S_X, F_X)` with identical objective
value. -/
theorem ReductionStep.preserves_global_min {X Y : Type*}
    {S_X : Set X} {F_X : X → ℝ} {S_Y : Set Y} {F_Y : Y → ℝ} {R : Y → X}
    (h : ReductionStep S_X F_X S_Y F_Y R) {y : Y} (hy : IsGlobalMin S_Y F_Y y) :
    IsGlobalMin S_X F_X (R y) ∧ F_X (R y) = F_Y y := by
  rcases hy with ⟨hyS, hyMin⟩
  refine ⟨⟨h.maps_into y hyS, ?_⟩, h.energy_eq y hyS⟩
  intro x hxS
  rcases h.weak_dom x hxS with ⟨y', hy'S, hle⟩
  rw [h.energy_eq y hyS]
  exact le_trans (hyMin y' hy'S) hle

/-- Under a valid reduction step, the optimal objective values of `(S_X, F_X)` and `(S_Y, F_Y)`
coincide whenever global minimizers exist. -/
theorem ReductionStep.global_min_value_eq {X Y : Type*}
    {S_X : Set X} {F_X : X → ℝ} {S_Y : Set Y} {F_Y : Y → ℝ} {R : Y → X}
    (h : ReductionStep S_X F_X S_Y F_Y R)
    {x : X} (hx : IsGlobalMin S_X F_X x) {y : Y} (hy : IsGlobalMin S_Y F_Y y) :
    F_X x = F_Y y := by
  have hRy := (h.preserves_global_min hy).1
  have hEq := (h.preserves_global_min hy).2
  have h1 : F_X x ≤ F_X (R y) := hx.2 (R y) hRy.1
  have h2 : F_X (R y) ≤ F_X x := hRy.2 x hx.1
  linarith

/-- A strong (persistently exact) reduction step additionally satisfies surjectivity of `R` onto
the set of all global minimizers of `(S_X, F_X)`. -/
structure StrongReductionStep {X Y : Type*} (S_X : Set X) (F_X : X → ℝ)
    (S_Y : Set Y) (F_Y : Y → ℝ) (R : Y → X) : Prop extends
    ReductionStep S_X F_X S_Y F_Y R where
  surj_on_min : ∀ x, IsGlobalMin S_X F_X x → ∃ y, IsGlobalMin S_Y F_Y y ∧ R y = x

/-- Strong reduction steps are closed under composition. -/
theorem StrongReductionStep.comp {X Y Z : Type*}
    {S_X : Set X} {F_X : X → ℝ} {S_Y : Set Y} {F_Y : Y → ℝ} {S_Z : Set Z} {F_Z : Z → ℝ}
    {R₁ : Y → X} {R₂ : Z → Y}
    (h₁ : StrongReductionStep S_X F_X S_Y F_Y R₁)
    (h₂ : StrongReductionStep S_Y F_Y S_Z F_Z R₂) :
    StrongReductionStep S_X F_X S_Z F_Z (R₁ ∘ R₂) where
  toReductionStep := h₁.toReductionStep.comp h₂.toReductionStep
  surj_on_min x hx := by
    rcases h₁.surj_on_min x hx with ⟨y, hy, rfl⟩
    rcases h₂.surj_on_min y hy with ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- Under a strong reduction step, the set of global minimizers of `(S_X, F_X)` is the exact image
under `R` of the set of global minimizers of `(S_Y, F_Y)`. -/
theorem StrongReductionStep.image_global_min_eq {X Y : Type*}
    {S_X : Set X} {F_X : X → ℝ} {S_Y : Set Y} {F_Y : Y → ℝ} {R : Y → X}
    (h : StrongReductionStep S_X F_X S_Y F_Y R) :
    {x | IsGlobalMin S_X F_X x} = R '' {y | IsGlobalMin S_Y F_Y y} := by
  ext x
  constructor
  · intro hx
    rcases h.surj_on_min x hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (h.toReductionStep.preserves_global_min hy).1

/-- Reduced objective obtained by substituting a conditional elimination rule `z = g(y)`. -/
def reducedObj {Y Z : Type*} (F : Y × Z → ℝ) (g : Y → Z) (y : Y) : ℝ :=
  F (y, g y)

/-- Reconstruction map `y ↦ (y, g(y))` associated with a conditional elimination rule `g`. -/
def reconstruct {Y Z : Type*} (g : Y → Z) (y : Y) : Y × Z :=
  (y, g y)

/-- Conditional elimination `z = g(y)` defines a valid `ReductionStep` from `(S_Y ×ˢ S_Z, F)` to
`(S_Y, reducedObj F g)`. -/
theorem conditional_elimination_is_reduction {Y Z : Type*}
    (S_Y : Set Y) (S_Z : Set Z) (F : Y × Z → ℝ) (g : Y → Z)
    (hg_maps : ∀ y ∈ S_Y, g y ∈ S_Z)
    (hg_opt : ∀ y ∈ S_Y, ∀ z ∈ S_Z, F (y, g y) ≤ F (y, z)) :
    ReductionStep (S_Y ×ˢ S_Z) F S_Y (reducedObj F g) (reconstruct g) where
  maps_into y hy := ⟨hy, hg_maps y hy⟩
  energy_eq _ _ := rfl
  weak_dom
  | (y, z), ⟨hy, hz⟩ => ⟨y, hy, hg_opt y hy z hz⟩

/-- **Corollary 2.1 (Monotonic Solution Repair)**: For any feasible state `(y, z) ∈ S_Y ×ˢ S_Z`,
replacing `z` by the conditional elimination assignment `g(y)` yields a feasible state
`reconstruct g y = (y, g(y))` whose energy never exceeds `F(y, z)`. -/
theorem repair_monotone {Y Z : Type*}
    (S_Y : Set Y) (S_Z : Set Z) (F : Y × Z → ℝ) (g : Y → Z)
    (hg_maps : ∀ y ∈ S_Y, g y ∈ S_Z)
    (hg_opt : ∀ y ∈ S_Y, ∀ z ∈ S_Z, F (y, g y) ≤ F (y, z))
    {y : Y} {z : Z} (hy : y ∈ S_Y) (hz : z ∈ S_Z) :
    reconstruct g y ∈ S_Y ×ˢ S_Z ∧ F (reconstruct g y) ≤ F (y, z) :=
  ⟨⟨hy, hg_maps y hy⟩, hg_opt y hy z hz⟩

/-- **Corollary 2.1 (Strict Improvement on Violating Assignments)**: Whenever `z` is conditionally
suboptimal for `y` (`F (y, g y) < F (y, z)`), repairing `(y, z)` to `reconstruct g y` strictly
reduces the objective value. -/
theorem repair_strict_improvement {Y Z : Type*}
    (F : Y × Z → ℝ) (g : Y → Z) {y : Y} {z : Z}
    (h_subopt : F (y, g y) < F (y, z)) :
    F (reconstruct g y) < F (y, z) :=
  h_subopt

/-!
### Zero-Field Degree-3 Ising Star–Triangle Exact Reduction
-/

/-- Minimum energy of a zero-field degree-3 spin $s_0 \in \{-1, +1\}$ coupled to neighbors
$(s_1, s_2, s_3)$ with couplings $(J_1, J_2, J_3)$:
$\min_{s_0 \in \{-1, +1\}} s_0 (J_1 s_1 + J_2 s_2 + J_3 s_3) = -|J_1 s_1 + J_2 s_2 + J_3 s_3|$. -/
noncomputable def starMin (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) : ℝ :=
  -|J₁ * s₁ + J₂ * s₂ + J₃ * s₃|

/-- For any spin $s_0 \in \{-1, +1\}$, `starMin` is a lower bound on the star interaction energy. -/
theorem starMin_le (J₁ J₂ J₃ s₁ s₂ s₃ s₀ : ℝ) (hs₀ : isSpin s₀) :
    starMin J₁ J₂ J₃ s₁ s₂ s₃ ≤ s₀ * (J₁ * s₁ + J₂ * s₂ + J₃ * s₃) := by
  unfold starMin
  rcases hs₀ with rfl | rfl
  · have h := le_abs_self (J₁ * s₁ + J₂ * s₂ + J₃ * s₃)
    linarith
  · have h := neg_le_abs (J₁ * s₁ + J₂ * s₂ + J₃ * s₃)
    linarith

/-- There always exists an optimal central spin $s_0 \in \{-1, +1\}$ achieving `starMin`. -/
theorem starMin_achieved (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) :
    ∃ s₀, isSpin s₀ ∧ s₀ * (J₁ * s₁ + J₂ * s₂ + J₃ * s₃) = starMin J₁ J₂ J₃ s₁ s₂ s₃ := by
  unfold starMin
  rcases le_total 0 (J₁ * s₁ + J₂ * s₂ + J₃ * s₃) with h | h
  · refine ⟨-1, Or.inl rfl, ?_⟩
    rw [abs_of_nonneg h]
    ring
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [abs_of_nonpos h]
    ring

/-- `starMin` is an even function under global spin negation $(s_1, s_2, s_3) \mapsto (-s_1, -s_2, -s_3)$. -/
theorem starMin_even (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) :
    starMin J₁ J₂ J₃ (-s₁) (-s₂) (-s₃) = starMin J₁ J₂ J₃ s₁ s₂ s₃ := by
  unfold starMin
  have h : J₁ * (-s₁) + J₂ * (-s₂) + J₃ * (-s₃) = -(J₁ * s₁ + J₂ * s₂ + J₃ * s₃) := by ring
  rw [h, abs_neg]

/-- Because `starMin` is even under $(s_1, s_2, s_3) \mapsto (-s_1, -s_2, -s_3)` whereas the cubic
monomial $s_1 s_2 s_3$ is odd, the 8-state cubic Walsh–Hadamard coefficient of `starMin` vanishes
identically for all real couplings $(J_1, J_2, J_3)$. -/
theorem starMin_cubic_walsh_zero (J₁ J₂ J₃ : ℝ) :
    starMin J₁ J₂ J₃ 1 1 1 * (1 * 1 * 1) +
    starMin J₁ J₂ J₃ 1 1 (-1) * (1 * 1 * (-1)) +
    starMin J₁ J₂ J₃ 1 (-1) 1 * (1 * (-1) * 1) +
    starMin J₁ J₂ J₃ 1 (-1) (-1) * (1 * (-1) * (-1)) +
    starMin J₁ J₂ J₃ (-1) 1 1 * ((-1) * 1 * 1) +
    starMin J₁ J₂ J₃ (-1) 1 (-1) * ((-1) * 1 * (-1)) +
    starMin J₁ J₂ J₃ (-1) (-1) 1 * ((-1) * (-1) * 1) +
    starMin J₁ J₂ J₃ (-1) (-1) (-1) * ((-1) * (-1) * (-1)) = 0 := by
  have h000 := starMin_even J₁ J₂ J₃ 1 1 1
  have h001 := starMin_even J₁ J₂ J₃ 1 1 (-1)
  have h010 := starMin_even J₁ J₂ J₃ 1 (-1) 1
  have h100 := starMin_even J₁ J₂ J₃ (-1) 1 1
  norm_num at h000 h001 h010 h100
  linarith

/-- Corner energy $\varepsilon_0 = -|J_1 + J_2 + J_3|$ from Eq. (4) of `docs/src/dominance.md`. -/
noncomputable def eps0 (J₁ J₂ J₃ : ℝ) : ℝ := -|J₁ + J₂ + J₃|

/-- Corner energy $\varepsilon_1 = -|-J_1 + J_2 + J_3|$ from Eq. (4) of `docs/src/dominance.md`. -/
noncomputable def eps1 (J₁ J₂ J₃ : ℝ) : ℝ := -|-J₁ + J₂ + J₃|

/-- Corner energy $\varepsilon_2 = -|J_1 - J_2 + J_3|$ from Eq. (4) of `docs/src/dominance.md`. -/
noncomputable def eps2 (J₁ J₂ J₃ : ℝ) : ℝ := -|J₁ - J₂ + J₃|

/-- Corner energy $\varepsilon_3 = -|J_1 + J_2 - J_3|$ from Eq. (4) of `docs/src/dominance.md`. -/
noncomputable def eps3 (J₁ J₂ J₃ : ℝ) : ℝ := -|J₁ + J₂ - J₃|

/-- Constant energy shift $\Delta c = (\varepsilon_0 + \varepsilon_1 + \varepsilon_2 + \varepsilon_3) / 4$. -/
noncomputable def starTriConst (J₁ J₂ J₃ : ℝ) : ℝ :=
  (eps0 J₁ J₂ J₃ + eps1 J₁ J₂ J₃ + eps2 J₁ J₂ J₃ + eps3 J₁ J₂ J₃) / 4

/-- Induced triangle coupling $\Delta J_{12} = (\varepsilon_0 - \varepsilon_1 - \varepsilon_2 + \varepsilon_3) / 4$. -/
noncomputable def starTriJ12 (J₁ J₂ J₃ : ℝ) : ℝ :=
  (eps0 J₁ J₂ J₃ - eps1 J₁ J₂ J₃ - eps2 J₁ J₂ J₃ + eps3 J₁ J₂ J₃) / 4

/-- Induced triangle coupling $\Delta J_{13} = (\varepsilon_0 - \varepsilon_1 + \varepsilon_2 - \varepsilon_3) / 4$. -/
noncomputable def starTriJ13 (J₁ J₂ J₃ : ℝ) : ℝ :=
  (eps0 J₁ J₂ J₃ - eps1 J₁ J₂ J₃ + eps2 J₁ J₂ J₃ - eps3 J₁ J₂ J₃) / 4

/-- Induced triangle coupling $\Delta J_{23} = (\varepsilon_0 + \varepsilon_1 - \varepsilon_2 - \varepsilon_3) / 4$. -/
noncomputable def starTriJ23 (J₁ J₂ J₃ : ℝ) : ℝ :=
  (eps0 J₁ J₂ J₃ + eps1 J₁ J₂ J₃ - eps2 J₁ J₂ J₃ - eps3 J₁ J₂ J₃) / 4

/-- The quadratic triangle polynomial
$\Delta c + \Delta J_{12} s_1 s_2 + \Delta J_{13} s_1 s_3 + \Delta J_{23} s_2 s_3$. -/
noncomputable def starTriPoly (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ) : ℝ :=
  starTriConst J₁ J₂ J₃ +
    starTriJ12 J₁ J₂ J₃ * s₁ * s₂ +
    starTriJ13 J₁ J₂ J₃ * s₁ * s₃ +
    starTriJ23 J₁ J₂ J₃ * s₂ * s₃

/-- **Zero-Field Degree-3 Ising Star–Triangle Exact Identity (Eq. 4)**:
For every spin assignment $(s_1, s_2, s_3) \in \{-1, +1\}^3$ and arbitrary couplings
$(J_1, J_2, J_3) \in \mathbb{R}^3$, the quadratic triangle polynomial `starTriPoly` equals
`starMin` with zero approximation error and no auxiliary variables. -/
theorem starTriPoly_eq_starMin (J₁ J₂ J₃ s₁ s₂ s₃ : ℝ)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) (hs₃ : isSpin s₃) :
    starTriPoly J₁ J₂ J₃ s₁ s₂ s₃ = starMin J₁ J₂ J₃ s₁ s₂ s₃ := by
  unfold starTriPoly starTriConst starTriJ12 starTriJ13 starTriJ23 eps0 eps1 eps2 eps3 starMin
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> rcases hs₃ with rfl | rfl
  · have h : J₁ * (-1) + J₂ * (-1) + J₃ * (-1) = -(J₁ + J₂ + J₃) := by ring
    rw [h, abs_neg]; ring
  · have h : J₁ * (-1) + J₂ * (-1) + J₃ * 1 = -(J₁ + J₂ - J₃) := by ring
    rw [h, abs_neg]; ring
  · have h : J₁ * (-1) + J₂ * 1 + J₃ * (-1) = -(J₁ - J₂ + J₃) := by ring
    rw [h, abs_neg]; ring
  · have h : J₁ * (-1) + J₂ * 1 + J₃ * 1 = -J₁ + J₂ + J₃ := by ring
    rw [h]; ring
  · have h : J₁ * 1 + J₂ * (-1) + J₃ * (-1) = -(-J₁ + J₂ + J₃) := by ring
    rw [h, abs_neg]; ring
  · have h : J₁ * 1 + J₂ * (-1) + J₃ * 1 = J₁ - J₂ + J₃ := by ring
    rw [h]; ring
  · have h : J₁ * 1 + J₂ * 1 + J₃ * (-1) = J₁ + J₂ - J₃ := by ring
    rw [h]; ring
  · have h : J₁ * 1 + J₂ * 1 + J₃ * 1 = J₁ + J₂ + J₃ := by ring
    rw [h]; ring

end QUBOPreprocessing
