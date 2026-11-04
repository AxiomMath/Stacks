module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Homomorphisms of systems of modules over a preordered set

A system of `R`-modules over a preordered set `ι` is a family of `R`-modules `M i` together with
`R`-linear transition maps `μ i j : M i →ₗ[R] M j`, one for each `i ≤ j`, satisfying `μ i i = id`
and `μ i k = μ j k ∘ₗ μ i j` (Definition 00D4, `DirectedSystem` in Mathlib's spelling). Given two
such systems `(M, μ)` and `(N, ν)` over the same `ι`, a *homomorphism of systems* from `(M, μ)`
to `(N, ν)` is a family of `R`-linear maps `φ i : M i →ₗ[R] N i` making every transition square
commute:

`φ j ∘ₗ μ i j = ν i j ∘ₗ φ i` for all `i ≤ j`.

Writing the two systems as diagrams `M, N : ι ⥤ ModuleCat R` — the functors
`ModuleCat.directLimitDiagram` — a homomorphism of systems is exactly a natural transformation
`M ⟶ N`. The identity family is a homomorphism of systems and composites of homomorphisms of
systems are again ones, so systems over `ι` and their homomorphisms form a category.

## Main definitions

* `Module.IsSystemHom`: the property of a family of `R`-linear maps `φ i : M i →ₗ[R] N i` that it
  commutes with the transition maps of two given systems, that is, that `φ` is a homomorphism of
  systems.

## Main results

* `Module.isSystemHom_of_apply`, `Module.IsSystemHom.naturality_apply`: the two directions of the
  elementwise reading of the commuting squares, `φ j (μ i j h x) = ν i j h (φ i x)`.
* `Module.isSystemHom_id`, `Module.IsSystemHom.comp`: the identity family is a homomorphism of
  systems, and a composite of two is one.

## Implementation notes

The condition is a `Prop`-valued predicate on the family `φ` rather than a bundled structure:
bundling would duplicate `CategoryTheory.NatTrans` at the diagrams, whereas the predicate is the
shape in which Mathlib's theory of direct limits of modules consumes the condition, as the
anonymous hypothesis of `Module.DirectLimit.map`, and of `Module.DirectLimit.congr` at the family
of linear maps underlying a family of equivalences. Being exposed, and reducibly that
`∀`-statement, a proof `h : Module.IsSystemHom μ ν φ` is accepted where that hypothesis is
expected: the map induced on colimits (Lemma 00DA) is `Module.DirectLimit.map φ h`.

The transition maps are arbitrary families of `R`-linear maps indexed by `i ≤ j`; the axioms
`μ i i = id` and `μ i k = μ j k ∘ₗ μ i j` making each of `μ` and `ν` a system are not assumed,
the commuting squares not referring to them. And `R` is a semiring acting on additive commutative
monoids — the weakest setting in which the composites are defined, and the setting of
`Module.DirectLimit` — rather than the source's ring acting on abelian groups.

## References

* [StacksProject 00D9](https://stacks.math.columbia.edu/tag/00D9)

## Tags

direct limit, colimit, directed system, system of modules, homomorphism of systems,
natural transformation
-/

@[expose] public section

namespace Module

/-- **Stacks 00D9.** Let `(M i, μ i j)` and `(N i, ν i j)` be systems of `R`-modules over the same
preordered set `ι`. A family of `R`-linear maps `φ i : M i →ₗ[R] N i` is a *homomorphism of
systems* from `(M, μ)` to `(N, ν)` when every transition square commutes, that is, when
`φ j ∘ₗ μ i j = ν i j ∘ₗ φ i` for all `i ≤ j`; equivalently, when `φ` is a natural transformation
between the associated diagrams `ι ⥤ ModuleCat R`. The axioms making `μ` and `ν` systems are not
needed to state the condition and are not assumed. -/
@[stacks 00D9 "Stated as a `Prop`-valued predicate on the family `φ`, in the unbundled language \
  of `Module.DirectLimit`, so that `Module.DirectLimit.map φ h` is the induced map on colimits of \
  Lemma 00DA. The axioms of a system (`DirectedSystem`) are not assumed, the commuting squares \
  not referring to them, and `R` is only a semiring acting on additive commutative monoids."]
def IsSystemHom {R : Type*} [Semiring R] {ι : Type*} [Preorder ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (μ : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
    {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (ν : (i j : ι) → i ≤ j → N i →ₗ[R] N j)
    (φ : (i : ι) → M i →ₗ[R] N i) : Prop :=
  ∀ (i j : ι) (h : i ≤ j), φ j ∘ₗ μ i j h = ν i j h ∘ₗ φ i

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {M N P : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  {μ : (i j : ι) → i ≤ j → M i →ₗ[R] M j} {ν : (i j : ι) → i ≤ j → N i →ₗ[R] N j}
  {ξ : (i j : ι) → i ≤ j → P i →ₗ[R] P j}
  {φ : (i : ι) → M i →ₗ[R] N i} {ψ : (i : ι) → N i →ₗ[R] P i}

/-- A family of `R`-linear maps whose transition squares commute on elements is a homomorphism of
systems. -/
theorem isSystemHom_of_apply
    (h : ∀ (i j : ι) (hij : i ≤ j) (x : M i), φ j (μ i j hij x) = ν i j hij (φ i x)) :
    IsSystemHom μ ν φ :=
  fun i j hij => LinearMap.ext (h i j hij)

/-- The transition square of a homomorphism of systems, read on elements. -/
theorem IsSystemHom.naturality_apply (h : IsSystemHom μ ν φ) {i j : ι} (hij : i ≤ j) (x : M i) :
    φ j (μ i j hij x) = ν i j hij (φ i x) :=
  LinearMap.congr_fun (h i j hij) x

/-- The identity family is a homomorphism of systems from a system to itself. -/
theorem isSystemHom_id : IsSystemHom μ μ fun _ => LinearMap.id := fun _ _ _ => rfl

/-- A composite of homomorphisms of systems is a homomorphism of systems. -/
theorem IsSystemHom.comp (hψ : IsSystemHom ν ξ ψ) (hφ : IsSystemHom μ ν φ) :
    IsSystemHom μ ξ fun i => ψ i ∘ₗ φ i := fun i j hij => by
  rw [LinearMap.comp_assoc, hφ i j hij, ← LinearMap.comp_assoc, hψ i j hij, LinearMap.comp_assoc]

end Module

end
