import Mathlib
import QUBOPreprocessing.GaugeCoercive
import QUBOPreprocessing.CompositionRepair
import QUBOPreprocessing.WalshDegree3

/-!
# Theorem 8: Multi-Variable Connected Block Elimination and Separator Interpolation

This module formalizes Theorem 8 of `QUBOPreprocessing.jl` (`_interpolate_quadratic_deltas`,
`_block_elimination_witness`, `prove_block_elimination`, `eliminate_blocks!`, and
`_verify_elimination_step` in `src/certificates.jl:1258-1298, 1393-1580, 5050-5217`):
1. **Separator-Conditioned Multi-Variable Block Marginalization & Unique-Argmin Persistency**:
   For a decomposed objective $E(y, x_B) = E_{\mathrm{rest}}(y) + E_{\mathrm{block}}(y, x_B)$ on
   $\Omega_S \times^s \Omega_B$, any block argmin table $T : Y \to B$ and value profile
   $\phi : Y \to \mathbb{R}$ matched by a reduced separator polynomial $\Delta Q : Y \to \mathbb{R}$
   on $\Omega_S$ induces a certified `ReductionStep` (`block_elimination_reductionStep`), and when
   $T(y)$ is the unique block minimizer for every separator state (`unique_argmin = true`,
   `opt_count == 1`), induces a `StrongReductionStep` (`block_elimination_strongReductionStep`).
2. **Universal Exactness of 0-, 1-, and 2-Separator Quadratic Interpolation**:
   Formalizes `_interpolate_quadratic_deltas` (`src/certificates.jl:1258-1298`) for $d \in \{0, 1, 2\}$
   in both the Boolean ($\{0, 1\}^d$) and Ising spin ($\{-1, +1\}^d$) domains, proving that every
   real-valued function $\phi$ on $\{0, 1\}^d$ or $\{-1, +1\}^d$ for $d \le 2$ is represented with
   zero higher-order residual by a degree-$\le 2$ polynomial, and establishing the exact equivalence
   between the Möbius-to-spin conversion formulas and the 4-point Walsh–Hadamard averages.
3. **Batch $k$-Step Materialization Equivalence (`_BlockEliminationWitness`)**:
   Proves that a batch of $k$ elimination steps whose first $k-1$ steps carry zero polynomial deltas
   and whose $k$-th step carries $\Delta Q$ accumulates total objective shift $\Delta Q$, while
   coordinate-wise table lookup $(T_1(y), \dots, T_k(y))$ reconstructs the joint block minimizer
   $T(y)$.
4. **Concrete 0-, 1-, 2-, and ($\alpha_{123} = 0$) 3-Separator Block Elimination Theorems**:
   Instantiates unconditional `ReductionStep` and `StrongReductionStep` theorems for 0-, 1-, and
   2-separator Ising spin block elimination of arbitrary block size $k$, as well as conditional 3-separator
   block elimination when `walshCubic φ = 0` (`QUBOPreprocessing.WalshDegree3`).
-/

open scoped BigOperators

namespace QUBOPreprocessing

/-!
### Part 1: Separator-Conditioned Multi-Variable Block Marginalization & Unique-Argmin Persistency
-/

/-- Full decomposed objective $E(y, x_B) = E_{\mathrm{rest}}(y) + E_{\mathrm{block}}(y, x_B)$,
where $y$ is the separator/environment configuration and $x_B$ is the $k$-variable block
configuration. -/
def blockFullEnergy {Y B : Type*} (E_rest : Y → ℝ) (E_block : Y → B → ℝ) (x : Y × B) : ℝ :=
  E_rest x.1 + E_block x.1 x.2

/-- Reduced objective $E_{\mathrm{red}}(y) = E_{\mathrm{rest}}(y) + \Delta Q(y)$ obtained after
marginalizing the block $B$ and adding the interpolated separator polynomial $\Delta Q(y)$. -/
def blockReducedEnergy {Y : Type*} (E_rest ΔQ : Y → ℝ) (y : Y) : ℝ :=
  E_rest y + ΔQ y

/-- Characterization of `unique_argmin` (`opt_count == 1` in `_verify_elimination_step`,
`src/certificates.jl:5188-5200`): given an optimal block assignment $T(y) \in \Omega_B$ with
$E_{\mathrm{block}}(y, T(y)) = \phi(y) \le E_{\mathrm{block}}(y, x_B)$, strict suboptimality of all
$x_B \neq T(y)$ is equivalent to $T(y)$ being the unique minimizer attaining $\phi(y)$. -/
theorem block_elimination_unique_argmin_iff {Y B : Type*}
    (Ω_B : Set B) (E_block : Y → B → ℝ) (T : Y → B) (φ : Y → ℝ) (y : Y)
    (hT_val : E_block y (T y) = φ y)
    (hT_opt : ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B) :
    (∀ x_B ∈ Ω_B, x_B ≠ T y → φ y < E_block y x_B) ↔
      (∀ x_B ∈ Ω_B, E_block y x_B = φ y ↔ x_B = T y) := by
  constructor
  · intro hstrict x_B hx_B
    constructor
    · intro hEq
      by_contra hne
      have hlt := hstrict x_B hx_B hne
      linarith
    · rintro rfl
      exact hT_val
  · intro huniq x_B hx_B hne
    have hle := hT_opt x_B hx_B
    rcases eq_or_lt_of_le hle with hEq | hlt
    · exfalso
      exact hne ((huniq x_B hx_B).mp hEq.symm)
    · exact hlt

/-- **Theorem 8 (Part 1A — Weak Multi-Variable Block Elimination `ReductionStep`)**:
If for every $y \in \Omega_S$, $T(y) \in \Omega_B$ attains the minimum block energy
$\phi(y) = \min_{x_B \in \Omega_B} E_{\mathrm{block}}(y, x_B)$ and $\Delta Q(y) = \phi(y)$, then
`reconstruct T` defines a valid `ReductionStep` from `blockFullEnergy E_rest E_block` on
$\Omega_S \times^s \Omega_B$ to `blockReducedEnergy E_rest ΔQ` on $\Omega_S$. -/
theorem block_elimination_reductionStep {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_block : Y → B → ℝ)
    (T : Y → B) (φ ΔQ : Y → ℝ)
    (hT_maps : ∀ y ∈ Ω_S, T y ∈ Ω_B)
    (hT_val : ∀ y ∈ Ω_S, E_block y (T y) = φ y)
    (hT_opt : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B)
    (hΔQ : ∀ y ∈ Ω_S, ΔQ y = φ y) :
    ReductionStep (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest E_block)
      Ω_S (blockReducedEnergy E_rest ΔQ) (reconstruct T) where
  maps_into y hy := ⟨hy, hT_maps y hy⟩
  energy_eq y hy := by
    unfold blockFullEnergy blockReducedEnergy reconstruct
    dsimp
    rw [hT_val y hy, hΔQ y hy]
  weak_dom := by
    rintro ⟨y, x_B⟩ ⟨hy, hx_B⟩
    refine ⟨y, hy, ?_⟩
    unfold blockReducedEnergy blockFullEnergy
    dsimp
    have hle := hT_opt y hy x_B hx_B
    have hq := hΔQ y hy
    linarith

/-- **Corollary (Monotonic Post-Processing Block Repair)**:
Under the hypotheses of `block_elimination_reductionStep`, replacing any feasible block assignment
$x_B \in \Omega_B$ by the table lookup $T(y)$ produces a feasible full state `(y, T y)` whose
energy never exceeds `blockFullEnergy E_rest E_block (y, x_B)`. -/
theorem block_elimination_repair_monotone {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_block : Y → B → ℝ)
    (T : Y → B) (φ : Y → ℝ)
    (hT_maps : ∀ y ∈ Ω_S, T y ∈ Ω_B)
    (hT_val : ∀ y ∈ Ω_S, E_block y (T y) = φ y)
    (hT_opt : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B)
    {y : Y} {x_B : B} (hy : y ∈ Ω_S) (hx_B : x_B ∈ Ω_B) :
    reconstruct T y ∈ Ω_S ×ˢ Ω_B ∧
      blockFullEnergy E_rest E_block (reconstruct T y) ≤
        blockFullEnergy E_rest E_block (y, x_B) := by
  refine ⟨⟨hy, hT_maps y hy⟩, ?_⟩
  unfold blockFullEnergy reconstruct
  dsimp
  have hval := hT_val y hy
  have hopt := hT_opt y hy x_B hx_B
  linarith

/-- **Corollary (Global Minimum Preservation under Weak Block Elimination)**:
Any global minimizer $y^*$ of `blockReducedEnergy E_rest ΔQ` on $\Omega_S$ lifts via
`reconstruct T` to a global minimizer $(y^*, T(y^*))$ of `blockFullEnergy E_rest E_block` on
$\Omega_S \times^s \Omega_B$ with identical objective value. -/
theorem block_elimination_preserves_global_min {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_block : Y → B → ℝ)
    (T : Y → B) (φ ΔQ : Y → ℝ)
    (hT_maps : ∀ y ∈ Ω_S, T y ∈ Ω_B)
    (hT_val : ∀ y ∈ Ω_S, E_block y (T y) = φ y)
    (hT_opt : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B)
    (hΔQ : ∀ y ∈ Ω_S, ΔQ y = φ y)
    {y : Y} (hy : IsGlobalMin Ω_S (blockReducedEnergy E_rest ΔQ) y) :
    IsGlobalMin (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest E_block) (reconstruct T y) ∧
      blockFullEnergy E_rest E_block (reconstruct T y) = blockReducedEnergy E_rest ΔQ y :=
  (block_elimination_reductionStep Ω_S Ω_B E_rest E_block T φ ΔQ
    hT_maps hT_val hT_opt hΔQ).preserves_global_min hy

/-- **Theorem 8 (Part 1B — Strong Multi-Variable Block Elimination `StrongReductionStep`)**:
When `unique_argmin` holds (`∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, x_B ≠ T y → φ y < E_block y x_B`),
`reconstruct T` defines a `StrongReductionStep` whose reconstruction map is surjective onto the set
of all global minimizers of `blockFullEnergy E_rest E_block` on $\Omega_S \times^s \Omega_B$. -/
theorem block_elimination_strongReductionStep {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_block : Y → B → ℝ)
    (T : Y → B) (φ ΔQ : Y → ℝ)
    (hT_maps : ∀ y ∈ Ω_S, T y ∈ Ω_B)
    (hT_val : ∀ y ∈ Ω_S, E_block y (T y) = φ y)
    (hT_opt : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B)
    (hT_unique : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, x_B ≠ T y → φ y < E_block y x_B)
    (hΔQ : ∀ y ∈ Ω_S, ΔQ y = φ y) :
    StrongReductionStep (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest E_block)
      Ω_S (blockReducedEnergy E_rest ΔQ) (reconstruct T) where
  toReductionStep :=
    block_elimination_reductionStep Ω_S Ω_B E_rest E_block T φ ΔQ
      hT_maps hT_val hT_opt hΔQ
  surj_on_min := by
    rintro ⟨y, x_B⟩ ⟨⟨hy, hx_B⟩, hmin⟩
    by_cases hEq : x_B = T y
    · refine ⟨y, ⟨hy, ?_⟩, ?_⟩
      · intro y' hy'
        have hx' : (y', T y') ∈ Ω_S ×ˢ Ω_B := ⟨hy', hT_maps y' hy'⟩
        have hle := hmin (y', T y') hx'
        unfold blockFullEnergy at hle
        unfold blockReducedEnergy
        dsimp at hle
        rw [hEq, hT_val y hy, hT_val y' hy'] at hle
        rw [hΔQ y hy, hΔQ y' hy']
        exact hle
      · unfold reconstruct
        rw [hEq]
    · exfalso
      have hstrict := hT_unique y hy x_B hx_B hEq
      have hx' : (y, T y) ∈ Ω_S ×ˢ Ω_B := ⟨hy, hT_maps y hy⟩
      have hle := hmin (y, T y) hx'
      unfold blockFullEnergy at hle
      dsimp at hle
      have hval := hT_val y hy
      linarith

/-- **Corollary (Exact Bijection on Global Minimizers under Strong Block Elimination)**:
When `unique_argmin` holds, the set of global minimizers of `blockFullEnergy E_rest E_block` on
$\Omega_S \times^s \Omega_B$ is the exact image under `reconstruct T` of the set of global
minimizers of `blockReducedEnergy E_rest ΔQ` on $\Omega_S$. -/
theorem block_elimination_strong_image_global_min_eq {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_block : Y → B → ℝ)
    (T : Y → B) (φ ΔQ : Y → ℝ)
    (hT_maps : ∀ y ∈ Ω_S, T y ∈ Ω_B)
    (hT_val : ∀ y ∈ Ω_S, E_block y (T y) = φ y)
    (hT_opt : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, φ y ≤ E_block y x_B)
    (hT_unique : ∀ y ∈ Ω_S, ∀ x_B ∈ Ω_B, x_B ≠ T y → φ y < E_block y x_B)
    (hΔQ : ∀ y ∈ Ω_S, ΔQ y = φ y) :
    {x | IsGlobalMin (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest E_block) x} =
      reconstruct T '' {y | IsGlobalMin Ω_S (blockReducedEnergy E_rest ΔQ) y} :=
  (block_elimination_strongReductionStep Ω_S Ω_B E_rest E_block T φ ΔQ
    hT_maps hT_val hT_opt hT_unique hΔQ).image_global_min_eq

/-!
### Part 2: Universal Exactness of 0-, 1-, and 2-Separator Quadratic Interpolation
-/

/-- 0-separator interpolated constant polynomial (`d = 0` in `_interpolate_quadratic_deltas`). -/
def interp0Poly (φ₀ : ℝ) : ℝ := φ₀

/-- Exactness of 0-separator constant interpolation. -/
theorem interp0Poly_eq (φ₀ : ℝ) : interp0Poly φ₀ = φ₀ := rfl

/-- 1-separator Boolean constant shift $\alpha_0 = \phi(0)$ (`d = 1`, `is_bool = true`). -/
def bool1Alpha0 (φ : ℝ → ℝ) : ℝ := φ 0

/-- 1-separator Boolean linear delta $\alpha_1 = \phi(1) - \phi(0)$ (`d = 1`, `is_bool = true`). -/
def bool1Alpha1 (φ : ℝ → ℝ) : ℝ := φ 1 - φ 0

/-- 1-separator Boolean interpolated polynomial $\alpha_0 + \alpha_1 z_1$. -/
def bool1Poly (φ : ℝ → ℝ) (z₁ : ℝ) : ℝ :=
  bool1Alpha0 φ + bool1Alpha1 φ * z₁

/-- **Universal Exactness of 1-Separator Boolean Interpolation**:
For every $\phi : \mathbb{R} \to \mathbb{R}$ and $z_1 \in \{0, 1\}$, `bool1Poly φ z₁ = φ z₁`. -/
theorem bool1Poly_eq (φ : ℝ → ℝ) (z₁ : ℝ) (hz₁ : isBool z₁) :
    bool1Poly φ z₁ = φ z₁ := by
  unfold bool1Poly bool1Alpha0 bool1Alpha1
  rcases hz₁ with rfl | rfl <;> ring

/-- 1-separator Spin base value $\alpha_0 = \phi(-1)$ (`d = 1`, `is_bool = false`). -/
def spin1Alpha0 (φ : ℝ → ℝ) : ℝ := φ (-1)

/-- 1-separator Spin first difference $\alpha_1 = \phi(1) - \phi(-1)$ (`d = 1`, `is_bool = false`). -/
def spin1Alpha1 (φ : ℝ → ℝ) : ℝ := φ 1 - φ (-1)

/-- 1-separator Spin constant delta $\Delta c = \alpha_0 + \alpha_1 / 2$
(`src/certificates.jl:1285`). -/
noncomputable def spin1Const (φ : ℝ → ℝ) : ℝ :=
  spin1Alpha0 φ + spin1Alpha1 φ / 2

/-- 1-separator Spin linear field delta $\Delta h_1 = \alpha_1 / 2$
(`src/certificates.jl:1289`). -/
noncomputable def spin1Field (φ : ℝ → ℝ) : ℝ :=
  spin1Alpha1 φ / 2

/-- 1-separator Spin interpolated polynomial $\Delta c + \Delta h_1 s_1$. -/
noncomputable def spin1Poly (φ : ℝ → ℝ) (s₁ : ℝ) : ℝ :=
  spin1Const φ + spin1Field φ * s₁

/-- Equivalence of `spin1Const` and the 2-point Walsh average $(\phi(-1) + \phi(1)) / 2$. -/
theorem spin1Const_eq_walsh (φ : ℝ → ℝ) :
    spin1Const φ = (φ (-1) + φ 1) / 2 := by
  unfold spin1Const spin1Alpha0 spin1Alpha1
  ring

/-- Equivalence of `spin1Field` and the 2-point Walsh slope $(\phi(1) - \phi(-1)) / 2$. -/
theorem spin1Field_eq_walsh (φ : ℝ → ℝ) :
    spin1Field φ = (φ 1 - φ (-1)) / 2 := by
  unfold spin1Field spin1Alpha1
  ring

/-- **Universal Exactness of 1-Separator Spin Interpolation**:
For every $\phi : \mathbb{R} \to \mathbb{R}$ and $s_1 \in \{-1, +1\}$, `spin1Poly φ s₁ = φ s₁`. -/
theorem spin1Poly_eq (φ : ℝ → ℝ) (s₁ : ℝ) (hs₁ : isSpin s₁) :
    spin1Poly φ s₁ = φ s₁ := by
  unfold spin1Poly spin1Const spin1Field spin1Alpha0 spin1Alpha1
  rcases hs₁ with rfl | rfl <;> ring

/-- 2-separator Boolean base value $\alpha_0 = \phi(0, 0)$ (`src/certificates.jl:1264`). -/
def bool2Alpha0 (φ : ℝ → ℝ → ℝ) : ℝ := φ 0 0

/-- 2-separator Boolean first linear difference $\alpha_1 = \phi(1, 0) - \phi(0, 0)$
(`src/certificates.jl:1267`). -/
def bool2Alpha1 (φ : ℝ → ℝ → ℝ) : ℝ := φ 1 0 - φ 0 0

/-- 2-separator Boolean second linear difference $\alpha_2 = \phi(0, 1) - \phi(0, 0)$
(`src/certificates.jl:1267`). -/
def bool2Alpha2 (φ : ℝ → ℝ → ℝ) : ℝ := φ 0 1 - φ 0 0

/-- 2-separator Boolean Möbius cross difference
$\alpha_{12} = \phi(1, 1) - \phi(1, 0) - \phi(0, 1) + \phi(0, 0)$
(`src/certificates.jl:1271`). -/
def bool2Alpha12 (φ : ℝ → ℝ → ℝ) : ℝ :=
  φ 1 1 - φ 1 0 - φ 0 1 + φ 0 0

/-- 2-separator Boolean quadratic polynomial
$\alpha_0 + \alpha_1 z_1 + \alpha_2 z_2 + \alpha_{12} z_1 z_2$. -/
def bool2QuadPoly (φ : ℝ → ℝ → ℝ) (z₁ z₂ : ℝ) : ℝ :=
  bool2Alpha0 φ + bool2Alpha1 φ * z₁ + bool2Alpha2 φ * z₂ + bool2Alpha12 φ * z₁ * z₂

/-- **Theorem 8 (Part 2A — Universal Exactness of 2-Separator Boolean Möbius Interpolation)**:
For every $\phi : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ and every $(z_1, z_2) \in \{0, 1\}^2$,
`bool2QuadPoly φ z₁ z₂ = φ z₁ z₂` with zero higher-order residual. -/
theorem bool2QuadPoly_eq (φ : ℝ → ℝ → ℝ) (z₁ z₂ : ℝ)
    (hz₁ : isBool z₁) (hz₂ : isBool z₂) :
    bool2QuadPoly φ z₁ z₂ = φ z₁ z₂ := by
  unfold bool2QuadPoly bool2Alpha0 bool2Alpha1 bool2Alpha2 bool2Alpha12
  rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl <;> ring

/-- 2-separator Spin base value $\alpha_0 = \phi(-1, -1)$ (`src/certificates.jl:1264`). -/
def spin2Alpha0 (φ : ℝ → ℝ → ℝ) : ℝ := φ (-1) (-1)

/-- 2-separator Spin first difference $\alpha_1 = \phi(1, -1) - \phi(-1, -1)$
(`src/certificates.jl:1267`). -/
def spin2Alpha1 (φ : ℝ → ℝ → ℝ) : ℝ := φ 1 (-1) - φ (-1) (-1)

/-- 2-separator Spin second difference $\alpha_2 = \phi(-1, 1) - \phi(-1, -1)$
(`src/certificates.jl:1267`). -/
def spin2Alpha2 (φ : ℝ → ℝ → ℝ) : ℝ := φ (-1) 1 - φ (-1) (-1)

/-- 2-separator Spin cross difference
$\alpha_{12} = \phi(1, 1) - \phi(1, -1) - \phi(-1, 1) + \phi(-1, -1)$
(`src/certificates.jl:1271`). -/
def spin2Alpha12 (φ : ℝ → ℝ → ℝ) : ℝ :=
  φ 1 1 - φ 1 (-1) - φ (-1) 1 + φ (-1) (-1)

/-- 2-separator Spin constant delta
$\Delta c = \alpha_0 + (\alpha_1 + \alpha_2) / 2 + \alpha_{12} / 4$
(`src/certificates.jl:1285-1286`). -/
noncomputable def spin2Const (φ : ℝ → ℝ → ℝ) : ℝ :=
  spin2Alpha0 φ + (spin2Alpha1 φ + spin2Alpha2 φ) / 2 + spin2Alpha12 φ / 4

/-- 2-separator Spin linear field delta on $s_1$:
$\Delta h_1 = \alpha_1 / 2 + \alpha_{12} / 4$ (`src/certificates.jl:1289`). -/
noncomputable def spin2H1 (φ : ℝ → ℝ → ℝ) : ℝ :=
  spin2Alpha1 φ / 2 + spin2Alpha12 φ / 4

/-- 2-separator Spin linear field delta on $s_2$:
$\Delta h_2 = \alpha_2 / 2 + \alpha_{12} / 4$ (`src/certificates.jl:1289`). -/
noncomputable def spin2H2 (φ : ℝ → ℝ → ℝ) : ℝ :=
  spin2Alpha2 φ / 2 + spin2Alpha12 φ / 4

/-- 2-separator Spin bilinear coupling delta on $s_1 s_2$:
$\Delta J_{12} = \alpha_{12} / 4$ (`src/certificates.jl:1293`). -/
noncomputable def spin2J12 (φ : ℝ → ℝ → ℝ) : ℝ :=
  spin2Alpha12 φ / 4

/-- 2-separator Spin quadratic polynomial
$\Delta c + \Delta h_1 s_1 + \Delta h_2 s_2 + \Delta J_{12} s_1 s_2$. -/
noncomputable def spin2QuadPoly (φ : ℝ → ℝ → ℝ) (s₁ s₂ : ℝ) : ℝ :=
  spin2Const φ + spin2H1 φ * s₁ + spin2H2 φ * s₂ + spin2J12 φ * s₁ * s₂

/-- Exact identity between `spin2Const` and the 4-point Walsh–Hadamard mean
$\frac{1}{4}\sum_{s \in \{-1, +1\}^2} \phi(s_1, s_2)$. -/
theorem spin2Const_eq_walsh (φ : ℝ → ℝ → ℝ) :
    spin2Const φ = (φ (-1) (-1) + φ 1 (-1) + φ (-1) 1 + φ 1 1) / 4 := by
  unfold spin2Const spin2Alpha0 spin2Alpha1 spin2Alpha2 spin2Alpha12
  ring

/-- Exact identity between `spin2H1` and the 4-point Walsh–Hadamard coefficient
$\frac{1}{4}\sum_{s \in \{-1, +1\}^2} s_1 \phi(s_1, s_2)$. -/
theorem spin2H1_eq_walsh (φ : ℝ → ℝ → ℝ) :
    spin2H1 φ = (-φ (-1) (-1) + φ 1 (-1) - φ (-1) 1 + φ 1 1) / 4 := by
  unfold spin2H1 spin2Alpha1 spin2Alpha12
  ring

/-- Exact identity between `spin2H2` and the 4-point Walsh–Hadamard coefficient
$\frac{1}{4}\sum_{s \in \{-1, +1\}^2} s_2 \phi(s_1, s_2)$. -/
theorem spin2H2_eq_walsh (φ : ℝ → ℝ → ℝ) :
    spin2H2 φ = (-φ (-1) (-1) - φ 1 (-1) + φ (-1) 1 + φ 1 1) / 4 := by
  unfold spin2H2 spin2Alpha2 spin2Alpha12
  ring

/-- Exact identity between `spin2J12` and the 4-point Walsh–Hadamard coefficient
$\frac{1}{4}\sum_{s \in \{-1, +1\}^2} s_1 s_2 \phi(s_1, s_2)$. -/
theorem spin2J12_eq_walsh (φ : ℝ → ℝ → ℝ) :
    spin2J12 φ = (φ (-1) (-1) - φ 1 (-1) - φ (-1) 1 + φ 1 1) / 4 := by
  unfold spin2J12 spin2Alpha12
  ring

/-- **Theorem 8 (Part 2B — Universal Exactness of 2-Separator Spin Quadratic Interpolation)**:
For every $\phi : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ and every $(s_1, s_2) \in \{-1, +1\}^2$,
`spin2QuadPoly φ s₁ s₂ = φ s₁ s₂` with zero higher-order residual. -/
theorem spin2QuadPoly_eq (φ : ℝ → ℝ → ℝ) (s₁ s₂ : ℝ)
    (hs₁ : isSpin s₁) (hs₂ : isSpin s₂) :
    spin2QuadPoly φ s₁ s₂ = φ s₁ s₂ := by
  unfold spin2QuadPoly spin2Const spin2H1 spin2H2 spin2J12
  unfold spin2Alpha0 spin2Alpha1 spin2Alpha2 spin2Alpha12
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> ring

/-!
### Part 3: Batch $k$-Step Materialization Equivalence (`_BlockEliminationWitness`)
-/

/-- Batch delta schedule of a $(k+1)$-variable block elimination certificate
(`src/certificates.jl:1549-1578, 5089-5092`): steps $r < \mathrm{Fin.last}(k)$ apply zero delta,
and the terminal step $r = \mathrm{Fin.last}(k)$ applies the interpolated separator polynomial
$\Delta Q(y)$. -/
def batchStepDelta {k : ℕ} {Y : Type*} (ΔQ : Y → ℝ) (r : Fin (k + 1)) (y : Y) : ℝ :=
  if r = Fin.last k then ΔQ y else 0

/-- Every non-terminal step $r < \mathrm{Fin.last}(k)$ in a block elimination batch has zero
polynomial delta (`src/certificates.jl:5089-5092`). -/
theorem batchStepDelta_lt_last {k : ℕ} {Y : Type*} (ΔQ : Y → ℝ)
    {r : Fin (k + 1)} (hr : r < Fin.last k) (y : Y) :
    batchStepDelta ΔQ r y = 0 := by
  unfold batchStepDelta
  exact if_neg (ne_of_lt hr)

/-- The terminal step $r = \mathrm{Fin.last}(k)$ in a block elimination batch carries the full
interpolated separator polynomial $\Delta Q(y)$. -/
theorem batchStepDelta_last {k : ℕ} {Y : Type*} (ΔQ : Y → ℝ) (y : Y) :
    batchStepDelta ΔQ (Fin.last k) y = ΔQ y := by
  unfold batchStepDelta
  exact if_pos rfl

/-- **Theorem 8 (Part 3A — Batch Delta Cumulative Sum Identity)**:
Summing `batchStepDelta ΔQ r y` across all steps $r \in \mathrm{Fin}(k+1)$ of a block elimination
batch yields $\Delta Q(y)$ identically. -/
theorem sum_batchStepDelta_eq {k : ℕ} {Y : Type*} (ΔQ : Y → ℝ) (y : Y) :
    (∑ r : Fin (k + 1), batchStepDelta ΔQ r y) = ΔQ y := by
  unfold batchStepDelta
  simp

/-- Coordinate-wise block table lookup assembling per-variable tables
`tables : Fin k → Y → α` into the joint block assignment `y ↦ (r ↦ tables r y)`
(`src/certificates.jl:1535-1537, 5169-5173`). -/
def coordBlockTable {k : ℕ} {Y α : Type*} (tables : Fin k → Y → α) (y : Y) : Fin k → α :=
  fun r => tables r y

/-- Evaluating `coordBlockTable tables y` at block index `r` returns `tables r y`. -/
@[simp]
theorem coordBlockTable_apply {k : ℕ} {Y α : Type*}
    (tables : Fin k → Y → α) (y : Y) (r : Fin k) :
    coordBlockTable tables y r = tables r y := rfl

/-- **Theorem 8 (Part 3B — Coordinate-Wise Table Equivalence)**:
Projecting any joint block argmin map `T : Y → Fin k → α` into per-variable tables
`tables r y = T y r` (`wit.block_tables[r]`) and reassembling via `coordBlockTable` recovers `T`
and `reconstruct T` identically. -/
theorem coordBlockTable_eq_joint {k : ℕ} {Y α : Type*} (T : Y → Fin k → α) :
    coordBlockTable (fun r y => T y r) = T := rfl

/-- Reconstructing a full state via `coordBlockTable` coincides with `reconstruct T`. -/
theorem reconstruct_coordBlockTable_eq {k : ℕ} {Y α : Type*} (T : Y → Fin k → α) (y : Y) :
    reconstruct (coordBlockTable (fun r y' => T y' r)) y = reconstruct T y := rfl

/-!
### Part 4: Concrete 0-, 1-, 2-, and ($\alpha_{123}=0$) 3-Separator Block Elimination Theorems
-/

/-- **Theorem 8 (Part 4A — Unconditional 0-Separator Block Elimination)**:
For an isolated block $B$ ($d = 0$) decoupled from the remaining variables $y \in \Omega_S$,
if $x_B^* \in \Omega_B$ minimizes $E_B$ with minimum value $\phi_0 = E_B(x_B^*)$, then eliminating
$B$ with constant shift $\phi_0$ defines a valid `ReductionStep` (and a `StrongReductionStep` when
$x_B^*$ is the unique minimizer of $E_B$). -/
theorem sep0_block_reductionStep {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_B : B → ℝ) (x_star : B) (φ₀ : ℝ)
    (hx_mem : x_star ∈ Ω_B)
    (hx_val : E_B x_star = φ₀)
    (hx_opt : ∀ x_B ∈ Ω_B, φ₀ ≤ E_B x_B) :
    ReductionStep (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest (fun _ x_B => E_B x_B))
      Ω_S (blockReducedEnergy E_rest (fun _ => interp0Poly φ₀))
      (reconstruct (fun _ => x_star)) :=
  block_elimination_reductionStep Ω_S Ω_B E_rest (fun _ x_B => E_B x_B)
    (fun _ => x_star) (fun _ => φ₀) (fun _ => interp0Poly φ₀)
    (fun _ _ => hx_mem) (fun _ _ => hx_val) (fun _ _ => hx_opt) (fun _ _ => rfl)

/-- Strong 0-separator block elimination under unique block minimizer $x_B^*$. -/
theorem sep0_block_strongReductionStep {Y B : Type*}
    (Ω_S : Set Y) (Ω_B : Set B)
    (E_rest : Y → ℝ) (E_B : B → ℝ) (x_star : B) (φ₀ : ℝ)
    (hx_mem : x_star ∈ Ω_B)
    (hx_val : E_B x_star = φ₀)
    (hx_opt : ∀ x_B ∈ Ω_B, φ₀ ≤ E_B x_B)
    (hx_unique : ∀ x_B ∈ Ω_B, x_B ≠ x_star → φ₀ < E_B x_B) :
    StrongReductionStep (Ω_S ×ˢ Ω_B) (blockFullEnergy E_rest (fun _ x_B => E_B x_B))
      Ω_S (blockReducedEnergy E_rest (fun _ => interp0Poly φ₀))
      (reconstruct (fun _ => x_star)) :=
  block_elimination_strongReductionStep Ω_S Ω_B E_rest (fun _ x_B => E_B x_B)
    (fun _ => x_star) (fun _ => φ₀) (fun _ => interp0Poly φ₀)
    (fun _ _ => hx_mem) (fun _ _ => hx_val) (fun _ _ => hx_opt)
    (fun _ _ => hx_unique) (fun _ _ => rfl)

/-- Feasible set for 1-separator spin block elimination: $(s_1, w) \in \{-1, +1\} \times \Omega_W$. -/
def sep1SpinSet {W : Type*} (Ω_W : Set W) : Set (ℝ × W) :=
  {y | isSpin y.1 ∧ y.2 ∈ Ω_W}

/-- **Theorem 8 (Part 4B — Unconditional 1-Separator Spin Block Elimination)**:
For any connected block $B$ separated from the rest of the graph by a single spin
$s_1 \in \{-1, +1\}$, substituting the linear interpolation `spin1Poly φ s₁` defines a valid
`ReductionStep` for any block size and internal topology. -/
theorem sep1_spin_block_reductionStep {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : ℝ × W → ℝ) (E_block : ℝ → B → ℝ)
    (T : ℝ → B) (φ : ℝ → ℝ)
    (hT_maps : ∀ s₁, isSpin s₁ → T s₁ ∈ Ω_B)
    (hT_val : ∀ s₁, isSpin s₁ → E_block s₁ (T s₁) = φ s₁)
    (hT_opt : ∀ s₁, isSpin s₁ → ∀ x_B ∈ Ω_B, φ s₁ ≤ E_block s₁ x_B) :
    ReductionStep (sep1SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1 x_B))
      (sep1SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => spin1Poly φ y.1))
      (reconstruct (fun y => T y.1)) :=
  block_elimination_reductionStep (sep1SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1 x_B)
    (fun y => T y.1) (fun y => φ y.1) (fun y => spin1Poly φ y.1)
    (fun y hy => hT_maps y.1 hy.1)
    (fun y hy => hT_val y.1 hy.1)
    (fun y hy => hT_opt y.1 hy.1)
    (fun y hy => spin1Poly_eq φ y.1 hy.1)

/-- Strong 1-separator spin block elimination when `T s₁` is the unique minimizer for each
$s_1 \in \{-1, +1\}$. -/
theorem sep1_spin_block_strongReductionStep {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : ℝ × W → ℝ) (E_block : ℝ → B → ℝ)
    (T : ℝ → B) (φ : ℝ → ℝ)
    (hT_maps : ∀ s₁, isSpin s₁ → T s₁ ∈ Ω_B)
    (hT_val : ∀ s₁, isSpin s₁ → E_block s₁ (T s₁) = φ s₁)
    (hT_opt : ∀ s₁, isSpin s₁ → ∀ x_B ∈ Ω_B, φ s₁ ≤ E_block s₁ x_B)
    (hT_unique : ∀ s₁, isSpin s₁ → ∀ x_B ∈ Ω_B, x_B ≠ T s₁ → φ s₁ < E_block s₁ x_B) :
    StrongReductionStep (sep1SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1 x_B))
      (sep1SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => spin1Poly φ y.1))
      (reconstruct (fun y => T y.1)) :=
  block_elimination_strongReductionStep (sep1SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1 x_B)
    (fun y => T y.1) (fun y => φ y.1) (fun y => spin1Poly φ y.1)
    (fun y hy => hT_maps y.1 hy.1)
    (fun y hy => hT_val y.1 hy.1)
    (fun y hy => hT_opt y.1 hy.1)
    (fun y hy => hT_unique y.1 hy.1)
    (fun y hy => spin1Poly_eq φ y.1 hy.1)

/-- Feasible set for 2-separator spin block elimination:
$((s_1, s_2), w) \in \{-1, +1\}^2 \times \Omega_W$. -/
def sep2SpinSet {W : Type*} (Ω_W : Set W) : Set ((ℝ × ℝ) × W) :=
  {y | isSpin y.1.1 ∧ isSpin y.1.2 ∧ y.2 ∈ Ω_W}

/-- **Theorem 8 (Part 4C — Unconditional 2-Separator Spin Block Elimination)**:
For any connected block $B$ separated from the rest of the graph by two spins
$(s_1, s_2) \in \{-1, +1\}^2$, substituting the quadratic interpolation `spin2QuadPoly φ s₁ s₂`
defines a valid `ReductionStep` unconditionally for any block size $k$ and internal topology. -/
theorem sep2_spin_block_reductionStep {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → T s₁ s₂ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → E_block s₁ s₂ (T s₁ s₂) = φ s₁ s₂)
    (hT_opt : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → ∀ x_B ∈ Ω_B, φ s₁ s₂ ≤ E_block s₁ s₂ x_B) :
    ReductionStep (sep2SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B))
      (sep2SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => spin2QuadPoly φ y.1.1 y.1.2))
      (reconstruct (fun y => T y.1.1 y.1.2)) :=
  block_elimination_reductionStep (sep2SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B)
    (fun y => T y.1.1 y.1.2) (fun y => φ y.1.1 y.1.2)
    (fun y => spin2QuadPoly φ y.1.1 y.1.2)
    (fun y hy => hT_maps y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => hT_val y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => hT_opt y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => spin2QuadPoly_eq φ y.1.1 y.1.2 hy.1 hy.2.1)

/-- **Theorem 8 (Part 4D — Strong 2-Separator Spin Block Elimination)**:
When `T s₁ s₂` is the unique block minimizer for all $4$ separator states
$(s_1, s_2) \in \{-1, +1\}^2$, 2-separator spin block elimination defines a `StrongReductionStep`. -/
theorem sep2_spin_block_strongReductionStep {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → T s₁ s₂ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → E_block s₁ s₂ (T s₁ s₂) = φ s₁ s₂)
    (hT_opt : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → ∀ x_B ∈ Ω_B, φ s₁ s₂ ≤ E_block s₁ s₂ x_B)
    (hT_unique : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ →
      ∀ x_B ∈ Ω_B, x_B ≠ T s₁ s₂ → φ s₁ s₂ < E_block s₁ s₂ x_B) :
    StrongReductionStep (sep2SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B))
      (sep2SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => spin2QuadPoly φ y.1.1 y.1.2))
      (reconstruct (fun y => T y.1.1 y.1.2)) :=
  block_elimination_strongReductionStep (sep2SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B)
    (fun y => T y.1.1 y.1.2) (fun y => φ y.1.1 y.1.2)
    (fun y => spin2QuadPoly φ y.1.1 y.1.2)
    (fun y hy => hT_maps y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => hT_val y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => hT_opt y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => hT_unique y.1.1 y.1.2 hy.1 hy.2.1)
    (fun y hy => spin2QuadPoly_eq φ y.1.1 y.1.2 hy.1 hy.2.1)

/-- **Corollary (Global Minimum Preservation under 2-Separator Spin Block Elimination)**:
Any global minimizer of the 2-separator reduced objective on `sep2SpinSet Ω_W` reconstructs to a
global minimizer of the full objective on `sep2SpinSet Ω_W ×ˢ Ω_B` with identical energy. -/
theorem sep2_spin_block_preserves_global_min {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → T s₁ s₂ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → E_block s₁ s₂ (T s₁ s₂) = φ s₁ s₂)
    (hT_opt : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → ∀ x_B ∈ Ω_B, φ s₁ s₂ ≤ E_block s₁ s₂ x_B)
    {y : (ℝ × ℝ) × W}
    (hy : IsGlobalMin (sep2SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => spin2QuadPoly φ y.1.1 y.1.2)) y) :
    IsGlobalMin (sep2SpinSet Ω_W ×ˢ Ω_B)
        (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B))
        (reconstruct (fun y => T y.1.1 y.1.2) y) ∧
      blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B)
          (reconstruct (fun y => T y.1.1 y.1.2) y) =
        blockReducedEnergy E_rest (fun y => spin2QuadPoly φ y.1.1 y.1.2) y :=
  (sep2_spin_block_reductionStep Ω_W Ω_B E_rest E_block T φ
    hT_maps hT_val hT_opt).preserves_global_min hy

/-- **Corollary (Exact Bijection on Global Minimizers under Strong 2-Separator Block Elimination)**:
When `T s₁ s₂` is the unique block minimizer for all $4$ separator states
$(s_1, s_2) \in \{-1, +1\}^2$, the set of global minimizers of the full objective on
`sep2SpinSet Ω_W ×ˢ Ω_B` is the exact image under `reconstruct (fun y => T y.1.1 y.1.2)` of the
global minimizers of the 2-separator reduced objective. -/
theorem sep2_spin_block_strong_image_global_min_eq {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → T s₁ s₂ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → E_block s₁ s₂ (T s₁ s₂) = φ s₁ s₂)
    (hT_opt : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ → ∀ x_B ∈ Ω_B, φ s₁ s₂ ≤ E_block s₁ s₂ x_B)
    (hT_unique : ∀ s₁ s₂, isSpin s₁ → isSpin s₂ →
      ∀ x_B ∈ Ω_B, x_B ≠ T s₁ s₂ → φ s₁ s₂ < E_block s₁ s₂ x_B) :
    {x | IsGlobalMin (sep2SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2 x_B)) x} =
      reconstruct (fun y => T y.1.1 y.1.2) ''
        {y | IsGlobalMin (sep2SpinSet Ω_W)
          (blockReducedEnergy E_rest (fun y => spin2QuadPoly φ y.1.1 y.1.2)) y} :=
  (sep2_spin_block_strongReductionStep Ω_W Ω_B E_rest E_block T φ
    hT_maps hT_val hT_opt hT_unique).image_global_min_eq

/-- Feasible set for 3-separator spin block elimination:
$((s_1, s_2, s_3), w) \in \{-1, +1\}^3 \times \Omega_W$. -/
def sep3SpinSet {W : Type*} (Ω_W : Set W) : Set ((ℝ × ℝ × ℝ) × W) :=
  {y | isSpin y.1.1 ∧ isSpin y.1.2.1 ∧ isSpin y.1.2.2 ∧ y.2 ∈ Ω_W}

/-- **Theorem 8 (Part 4E — Conditional 3-Separator Spin Block Elimination via Walsh Degree-3)**:
For any block $B$ separated by three spins $(s_1, s_2, s_3) \in \{-1, +1\}^3$ whose marginalized
value profile $\phi(s_1, s_2, s_3)$ has vanishing cubic Walsh–Hadamard coefficient
(`walshCubic φ = 0` from `QUBOPreprocessing.WalshDegree3`), substituting `walshQuadPoly φ` defines
a certified `ReductionStep`. -/
theorem sep3_spin_block_reductionStep_of_cubic_zero {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ → T s₁ s₂ s₃ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      E_block s₁ s₂ s₃ (T s₁ s₂ s₃) = φ s₁ s₂ s₃)
    (hT_opt : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      ∀ x_B ∈ Ω_B, φ s₁ s₂ s₃ ≤ E_block s₁ s₂ s₃ x_B)
    (hcubic : walshCubic φ = 0) :
    ReductionStep (sep3SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2.1 y.1.2.2 x_B))
      (sep3SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => walshQuadPoly φ y.1.1 y.1.2.1 y.1.2.2))
      (reconstruct (fun y => T y.1.1 y.1.2.1 y.1.2.2)) :=
  block_elimination_reductionStep (sep3SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1.1 y.1.2.1 y.1.2.2 x_B)
    (fun y => T y.1.1 y.1.2.1 y.1.2.2) (fun y => φ y.1.1 y.1.2.1 y.1.2.2)
    (fun y => walshQuadPoly φ y.1.1 y.1.2.1 y.1.2.2)
    (fun y hy => hT_maps y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => hT_val y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => hT_opt y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => walshQuadPoly_eq_of_cubic_zero φ y.1.1 y.1.2.1 y.1.2.2
      hcubic hy.1 hy.2.1 hy.2.2.1)

/-- Strong 3-separator spin block elimination when `walshCubic φ = 0` and `T s₁ s₂ s₃` is the
unique block minimizer for all $8$ separator states $(s_1, s_2, s_3) \in \{-1, +1\}^3$. -/
theorem sep3_spin_block_strongReductionStep_of_cubic_zero {W B : Type*}
    (Ω_W : Set W) (Ω_B : Set B)
    (E_rest : (ℝ × ℝ × ℝ) × W → ℝ) (E_block : ℝ → ℝ → ℝ → B → ℝ)
    (T : ℝ → ℝ → ℝ → B) (φ : ℝ → ℝ → ℝ → ℝ)
    (hT_maps : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ → T s₁ s₂ s₃ ∈ Ω_B)
    (hT_val : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      E_block s₁ s₂ s₃ (T s₁ s₂ s₃) = φ s₁ s₂ s₃)
    (hT_opt : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      ∀ x_B ∈ Ω_B, φ s₁ s₂ s₃ ≤ E_block s₁ s₂ s₃ x_B)
    (hT_unique : ∀ s₁ s₂ s₃, isSpin s₁ → isSpin s₂ → isSpin s₃ →
      ∀ x_B ∈ Ω_B, x_B ≠ T s₁ s₂ s₃ → φ s₁ s₂ s₃ < E_block s₁ s₂ s₃ x_B)
    (hcubic : walshCubic φ = 0) :
    StrongReductionStep (sep3SpinSet Ω_W ×ˢ Ω_B)
      (blockFullEnergy E_rest (fun y x_B => E_block y.1.1 y.1.2.1 y.1.2.2 x_B))
      (sep3SpinSet Ω_W)
      (blockReducedEnergy E_rest (fun y => walshQuadPoly φ y.1.1 y.1.2.1 y.1.2.2))
      (reconstruct (fun y => T y.1.1 y.1.2.1 y.1.2.2)) :=
  block_elimination_strongReductionStep (sep3SpinSet Ω_W) Ω_B
    E_rest (fun y x_B => E_block y.1.1 y.1.2.1 y.1.2.2 x_B)
    (fun y => T y.1.1 y.1.2.1 y.1.2.2) (fun y => φ y.1.1 y.1.2.1 y.1.2.2)
    (fun y => walshQuadPoly φ y.1.1 y.1.2.1 y.1.2.2)
    (fun y hy => hT_maps y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => hT_val y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => hT_opt y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => hT_unique y.1.1 y.1.2.1 y.1.2.2 hy.1 hy.2.1 hy.2.2.1)
    (fun y hy => walshQuadPoly_eq_of_cubic_zero φ y.1.1 y.1.2.1 y.1.2.2
      hcubic hy.1 hy.2.1 hy.2.2.1)

end QUBOPreprocessing
