# Models, ownership and numerical evaluation

This page is the representation reference for the [user guide](guide.md). Use it
when choosing input forms, transferring a solver state, or keeping snapshots
across model changes. The package follows the
[accepted certified preprocessing design](https://github.com/JuliaQUBO/QUBO.jl/blob/c0ab77d34e2281cfd6bd06e6c9c2f5ce13994670/docs/src/design.md#certified-preprocessing).

## Identity export example

Identity mode is useful for checking the model-to-solver-to-reconstruction path
without any deductions. This example retains every variable, including an
isolate, and exercises maximization with a negative scale. The user guide starts
with a simpler binary minimization that actually removes a variable.

```@example identity
using QUBOPreprocessing
import QUBOTools as QT
model = QT.Model(Dict(:x=>1.5, :y=>-2.0, :isolate=>0.0),
                 Dict((:x,:y)=>0.25); scale=-2.0, offset=0.5,
                 sense=:max, domain=:bool)
ws, report = preprocess(model; rules=:identity)
result = materialize(ws)
solver_model = export_model(result)
state = [label === :y ? 1 : 0 for label in original_variables(result)]
restored = reconstruct(result, state)
@assert restored.state == state
@assert restored.energy.value == 3.0
@assert result.certificate.reduction_chain == ()
(original_variables(result), restored.state, restored.energy)
```

The standalone `examples/identity.jl` uses the same public path.

## Representation and ownership

Accepted inputs are concrete `QUBOTools.Model` objects with finite Float64
objective coefficients, scale and offset, integer model state type, and the
built-in sparse, dense or dictionary forms. The quadratic form must already be
in strict upper triangular normal form (zero diagonal). Unsupported wrappers,
coefficient types and nonfinite data are rejected without conversion. Binary
and spin domains, both senses, arbitrary ordered labels, empty models,
isolates, constants, and finite positive/negative/nonunit/zero scales are supported.

The mathematical source is the exact binary value of each stored Float64:

```math
E(x)=\alpha\left(\beta+\sum_i L_i x_i+\sum_{i<j}Q_{ij}x_i x_j\right).
```

Identity export preserves coefficients, signed stored zeros, label/index order,
scale, offset, sense, domain and every variable. No arithmetic, normalization,
zero dropping or scale folding occurs. Exact representation identity proves
that source and export represent the same problem, with an empty reduction
chain and original scope. **It does not prove that a supplied state is optimal.**

A workspace privately freezes scalar storage and copies labels. Labels must
have stable equality/hash semantics and an owned `deepcopy` that preserves
those semantics. Identity-based mutable labels whose copies compare unequal
are rejected with `ArgumentError`, including transactionally by `reset!`.
Mutable labels with copy-stable value equality/hash are supported; their mutable
payloads must be correctly copied by `deepcopy`. Do not mutate a label identity
while it is retained. Model metadata, warm starts and attached solutions are
outside the snapshot and are omitted from exported solver models. One workspace is used
serially; independent workspaces share no mutable state.

`materialize` captures an owned historical export. `export_model(result)` returns
a fresh mutable QUBOTools model on each call. `original_variables` and `index_map`
return fresh owned data. Editing returned models/maps/states does not change the
workspace or export. Reconstruction refers to the captured objective, so a caller
who edits a solver model must independently verify that model still matches the
export before treating solver results as evidence about the original problem.
Private underscored fields are implementation details, not mutation APIs.

`generation(ws)` identifies both workspace and accepted source generation.
`reset!(ws, model)` validates before committing a fresh snapshot; invalid input
leaves the previous generation valid. Success creates a new generation even
with unchanged dimension or identical source data. Historical exports and their
reconstructed states retain their original generation. Consumers must compare
identities explicitly before treating them as evidence for a current workspace.

## Certified domain and gauge maps

Binary QUBO (`xᵢ ∈ {0,1}`) and Ising spin (`sᵢ ∈ {-1,+1}`) models are bijectively
related by `xᵢ = (sᵢ + 1)/2` (`sᵢ = 2xᵢ - 1`). For an unscaled polynomial
``F(x)=c+\sum_i a_i x_i+\sum_{i<j}b_{ij}x_i x_j``, exact substitution gives
``J_{ij}=b_{ij}/4``, ``h_i=a_i/2+\sum_{j\ne i}b_{ij}/4`` and
``c_{\text{spin}}=c+\frac{1}{2}\sum_i a_i+\frac{1}{4}\sum_{i<j}b_{ij}``. A spin
gauge ``s_i=g_i t_i`` with ``g_i\in\{-1,+1\}`` transports fields as
``h'_i=g_i h_i`` and couplings as ``J'_{ij}=g_i g_j J_{ij}`` while leaving the
spin constant unchanged.

Distinguish four different operations:

- **Bijective conversion (`DomainGaugeMap`):** a one-to-one change of coordinates
  (`xᵢ = (sᵢ + 1)/2`, `sᵢ = gᵢ tᵢ`) that preserves every state and its exact
  energy. Optional gauge selection transforms fields as well as couplings; it
  **never** means assuming every model is zero-field or dropping nonzero fields.
- **Constant fixing and pair relations (`DominanceStep`, `RelationStep`):**
  proves a variable takes a constant value or locked signed relation
  ``s_u = \sigma_{\text{orig}} s_v`` in every scoped optimum (`:strong`
  persistency) or in at least one optimum of the current conditioned residual
  (`:weak` persistency, applied sequentially).
- **Exact elimination (`EliminationStep`):** minimizes a bounded-degree
  (`0 <= d <= 3`) variable out as an exact quadratic function of surviving
  neighbors and restores it via its ``2^d`` argmin lookup table during
  reverse-order reconstruction.
- **Symmetry or compatible-optimum selection:** chooses one representative among
  tied or symmetric optima (such as global spin-flip symmetry when all fields
  vanish); this does not hold in every optimum and must not be conflated with
  strong persistency.

```@example identity
smap = domain_map(ws; domain=:spin, gauge=Dict(:x => -1, :y => 1, :isolate => 1))
mapped_state = map_state(smap, state)
@assert lift_state(smap, mapped_state) == state
@assert [degree(ws, v) for v in (:x, :y, :isolate)] == [1, 1, 0]
(effective_field(ws, :x; map=smap), conditioned_constant(ws; map=smap))
```

Ordinary floating-point casting is not itself a certificate: `materialize(ws, map)`
requires every converted coefficient and constant to be exactly representable in
`Float64`, or it abstains with `ArgumentError`; pass
`coefficient_type=Rational{BigInt}` for verified exact transport.

## Reconstruction and numerical evaluation

`reconstruct(result, y)` accepts a complete one-based vector in residual index
order. Each entry must be a finite real exactly in `{0,1}` or `{-1,1}`
according to the residual's target domain (which equals the original domain for
unmapped exports, or `map.target_domain` when materialized through a
[`DomainGaugeMap`](@ref)). It rejects missing, malformed, partial and
out-of-domain states and returns an owned `Vector{Int}` in original-variable
order and original domain.

`restored.energy` is an ordinary QUBOTools Float64 evaluation with `method=:float64`
and a `finite` flag. Floating rounding, cancellation, overflow and summation
order apply; exact stored-value preservation does not imply exact numerical
energy evaluation. Nonfinite numerical results are reported without upgrading
them to proof. Tests use independent exact binary-value rational references on
guarded tiny fixtures. Reversible conditioning uses exact rational algebra;
individual strict-dominance bounds and independent proof verification are now
implemented. Automatic strict dominance retains a separate deduction trail.

## Costs and composition

Snapshotting, materialization and model retrieval copy stored objective/label
data explicitly. Sparse structural work/storage is O(n+m); dense storage copying
can cost O(n²). Reconstruction validates all n entries, constructs evaluation
storage and evaluates the original objective. Dictionary iteration and numerical
summation order can differ between copies. The [measured operating envelope](performance.md) records repeated sparse reuse,
complete one-shot costs and their limits; it provides no hard timing guarantee. Workspace work/deadline
contracts apply to explicit conditioning updates, as described in its manual.
Generation/report inspection is constant-size. `preprocess` constructs a workspace
and either returns a no-inference report or runs the selected dominance rule;
it does not materialize a model implicitly.

Use the [workspace manual](workspace.md) for exact conditioning and ownership,
[certificates](certificates.md) for scoped proofs and numeric transport,
[dominance](dominance.md) for bounded propagation and
[branch workloads](scopes.md) for rollback, arbitrary unfix and resumption.
The [optional consumer](consumers.md) covers direct/MOI/ToQUBO composition.
For decomposition, select a QUBODecomposition version that documents support
for opt-in root preprocessing, and follow its installation and support policy.

`checkpoint`, `assume!`, `changes`, `rollback!` and `unfix!` implement explicit
caller conditioning. `propagate!` performs bounded strict dominance when selected. Under fixings,
`materialize` accepts exact Float64 or Rational{BigInt} transport; propagation limits are explicit keyword arguments. The [optional consumer](consumers.md) loads only when QUBODrivers is imported.
