module

public import Mathlib.Algebra.Colimit.Module
public import StacksCore.Tactic.StacksAttribute

/-!
# The map induced on colimits by a homomorphism of systems of modules

Let `(M i, μ i j)` and `(N i, ν i j)` be systems of `R`-modules over the same preordered set `ι`,
and let `φ i : M i →ₗ[R] N i` be a homomorphism of systems, that is, `φ j ∘ₗ μ i j = ν i j ∘ₗ φ i`
for all `i ≤ j` (Definition 00D9). Lemma 00DA says that there is a unique `R`-linear map
`colim φ : colim M ⟶ colim N` with `colim φ ∘ₗ of i = of i ∘ₗ φ i` for every `i`.

Mathlib constructs the map as `Module.DirectLimit.map φ hφ`, proves the squares commute
(`Module.DirectLimit.map_apply_of`), and proves that a linear map out of a direct limit is
determined by its composites with the coprojections (`Module.DirectLimit.hom_ext`). This file
packages these into the existence-and-uniqueness statement of the source.

## Main results

* `Module.DirectLimit.existsUnique_comp_of_eq_of_comp`: a homomorphism of systems induces a unique
  linear map between the direct limits compatible with the coprojections, namely
  `Module.DirectLimit.map φ hφ`.

## Implementation notes

The statement is in the generality of `Module.DirectLimit`: `R` is a semiring acting on additive
commutative monoids, and the axioms `μ i i = id`, `μ i k = μ j k ∘ₗ μ i j` making `μ` and `ν`
systems are not assumed, neither existence nor uniqueness depending on them. The source's
setting (a ring acting on abelian groups, `DirectedSystem` transition maps) is a special case.

## References

* [StacksProject 00DA](https://stacks.math.columbia.edu/tag/00DA)

## Tags

direct limit, colimit, system of modules, homomorphism of systems
-/

@[expose] public section

namespace Module.DirectLimit

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] [DecidableEq ι]
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {μ : (i j : ι) → i ≤ j → M i →ₗ[R] M j}
  {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  {ν : (i j : ι) → i ≤ j → N i →ₗ[R] N j}

/-- **Stacks 00DA.** Let `(M i, μ i j)` and `(N i, ν i j)` be systems of `R`-modules over the same
preordered set `ι`. A homomorphism of systems `φ i : M i →ₗ[R] N i` (so
`φ j ∘ₗ μ i j = ν i j ∘ₗ φ i` for all `i ≤ j`) induces a unique `R`-linear map
`ψ : colim M →ₗ[R] colim N` such that the square `ψ ∘ₗ of i = of i ∘ₗ φ i` commutes for every
`i`; the map is `Module.DirectLimit.map φ hφ`. -/
@[stacks 00DA "Existence and uniqueness of the induced map `Module.DirectLimit.map φ hφ`, from \
  Mathlib's `Module.DirectLimit.map_apply_of` (the squares commute) and \
  `Module.DirectLimit.hom_ext` (uniqueness). Stated in the generality of `Module.DirectLimit`: \
  `R` a semiring acting on additive commutative monoids, and the system axioms of `μ` and `ν` \
  not assumed, neither part depending on them."]
theorem existsUnique_comp_of_eq_of_comp (φ : (i : ι) → M i →ₗ[R] N i)
    (hφ : ∀ i j h, φ j ∘ₗ μ i j h = ν i j h ∘ₗ φ i) :
    ∃! ψ : DirectLimit M μ →ₗ[R] DirectLimit N ν,
      ∀ i, ψ ∘ₗ of R ι M μ i = of R ι N ν i ∘ₗ φ i :=
  ⟨map φ hφ, fun _ ↦ LinearMap.ext fun x ↦ map_apply_of φ hφ x,
    fun _ hψ ↦ hom_ext fun i ↦ (hψ i).trans
      (LinearMap.ext fun x ↦ (map_apply_of φ hφ x).symm)⟩

/-- The linear map induced on direct limits by a homomorphism of systems is the only one compatible
with the coprojections: any `ψ` with `ψ ∘ₗ of i = of i ∘ₗ φ i` for all `i` is
`Module.DirectLimit.map φ hφ` (the uniqueness half of Lemma 00DA). -/
theorem eq_map_of_comp_of_eq {φ : (i : ι) → M i →ₗ[R] N i}
    (hφ : ∀ i j h, φ j ∘ₗ μ i j h = ν i j h ∘ₗ φ i) {ψ : DirectLimit M μ →ₗ[R] DirectLimit N ν}
    (hψ : ∀ i, ψ ∘ₗ of R ι M μ i = of R ι N ν i ∘ₗ φ i) : ψ = map φ hφ :=
  (existsUnique_comp_of_eq_of_comp φ hφ).unique hψ
    fun _ ↦ LinearMap.ext fun x ↦ map_apply_of φ hφ x

end Module.DirectLimit
