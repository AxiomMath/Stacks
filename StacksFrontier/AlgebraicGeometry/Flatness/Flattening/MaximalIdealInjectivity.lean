module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Injectivity modulo the maximal ideal

Fix a local homomorphism `A → B` of local rings which is essentially of finite type, a flat
`A`-module `M`, a finite `B`-module `N`, and an `A`-linear map `u : N → M` which is injective
modulo the maximal ideal of `A`.

Over a Noetherian base this forces `u` to be universally injective, `N` to be finitely
presented over `B`, and `N` to be flat over `A`.

## Main definitions

* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation` bundles the standing data and
  hypotheses.

## Main results

* `AlgebraicGeometry.universallyInjective_of_isNoetherianRing` gives universal injectivity.
* `Module.finitePresentation_of_finite` gives finite presentation over a Noetherian ring.
* `AlgebraicGeometry.flat_of_isNoetherianRing` gives flatness over the base ring.

## Implementation notes

The essential finite type hypothesis is Mathlib's `Algebra.EssFiniteType`. The quotients by
the maximal ideal are represented by quotients by `IsLocalRing.maximalIdeal A • ⊤`, and the
induced map is the canonical `Submodule.mapQ` of `u`. Universal injectivity is expressed by
the universe-polymorphic predicate `UniversallyInjectivePoly`.

For finite presentation, essential finite type over the Noetherian ring `A` implies that `B`
is Noetherian; the conclusion is then Mathlib's general theorem for finite modules over
Noetherian rings, which is adopted directly rather than specialized to this situation.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT1](https://stacks.math.columbia.edu/tag/0AT1)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

/-- The standing data and hypotheses of Stacks Project, Tag 0AT0: a local homomorphism
`A → B` of local rings which is essentially of finite type, a flat `A`-module `M`, a finite
`B`-module `N`, and an `A`-linear map `N → M` which is injective modulo the maximal ideal
of `A`. -/
@[stacks 0AT0]
structure InjectiveModuloMaximalIdealSituation where
  /-- The local base ring. -/
  A : Type u₁
  /-- The local algebra over `A`. -/
  B : Type u₂
  /-- The flat `A`-module. -/
  M : Type u₃
  /-- The finite `B`-module. -/
  N : Type u₄
  /-- The commutative ring structure on `A`. -/
  [commRingA : CommRing A]
  /-- The local ring structure on `A`. -/
  [localRingA : IsLocalRing A]
  /-- The commutative ring structure on `B`. -/
  [commRingB : CommRing B]
  /-- The local ring structure on `B`. -/
  [localRingB : IsLocalRing B]
  /-- The ring homomorphism `A → B`. -/
  [algebraAB : Algebra A B]
  /-- The ring homomorphism `A → B` is local. -/
  [localHom : IsLocalHom (algebraMap A B)]
  /-- The algebra `B` is essentially of finite type over `A`. -/
  [essentiallyFiniteType : Algebra.EssFiniteType A B]
  /-- The additive group underlying `M`. -/
  [addCommGroupM : AddCommGroup M]
  /-- The `A`-module structure on `M`. -/
  [moduleAM : Module A M]
  /-- The module `M` is flat over `A`. -/
  [flatM : Module.Flat A M]
  /-- The additive group underlying `N`. -/
  [addCommGroupN : AddCommGroup N]
  /-- The `B`-module structure on `N`. -/
  [moduleBN : Module B N]
  /-- The `A`-module structure on `N` obtained by restriction of scalars. -/
  [moduleAN : Module A N]
  /-- The `A`-action on `N` is the restriction of its `B`-action. -/
  [isScalarTower : IsScalarTower A B N]
  /-- The module `N` is finite over `B`. -/
  [finiteN : Module.Finite B N]
  /-- The given `A`-linear map. -/
  u : N →ₗ[A] M
  /-- The map induced by `u` modulo the maximal ideal of `A` is injective. -/
  injective_mod_maximalIdeal : Function.Injective
    (Submodule.mapQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) u
      (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u))

attribute [instance]
  InjectiveModuloMaximalIdealSituation.commRingA
  InjectiveModuloMaximalIdealSituation.localRingA
  InjectiveModuloMaximalIdealSituation.commRingB
  InjectiveModuloMaximalIdealSituation.localRingB
  InjectiveModuloMaximalIdealSituation.algebraAB
  InjectiveModuloMaximalIdealSituation.localHom
  InjectiveModuloMaximalIdealSituation.essentiallyFiniteType
  InjectiveModuloMaximalIdealSituation.addCommGroupM
  InjectiveModuloMaximalIdealSituation.moduleAM
  InjectiveModuloMaximalIdealSituation.flatM
  InjectiveModuloMaximalIdealSituation.addCommGroupN
  InjectiveModuloMaximalIdealSituation.moduleBN
  InjectiveModuloMaximalIdealSituation.moduleAN
  InjectiveModuloMaximalIdealSituation.isScalarTower
  InjectiveModuloMaximalIdealSituation.finiteN

add_to_stacks 0AT1 "finite presentation" Module.finitePresentation_of_finite
add_to_ega "0 1.0.5" "more general" Module.finitePresentation_of_finite
add_to_ega "0 1.3.5" "more general" Module.finitePresentation_of_finite

/-- An injective map whose cokernel is flat is universally injective. -/
private lemma universallyInjective_of_injective_and_flat_quotient
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (hflat : Module.Flat R (M ⧸ LinearMap.range f)) : UniversallyInjectivePoly f := by
  intro Q _ _ x y hxy
  have := hflat
  apply (TensorProduct.comm R N Q).injective
  apply LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
    (Submodule.mkQ_surjective _) f hf (LinearMap.exact_map_mkQ_range f) Q
  rw [LinearMap.lTensor_comm, LinearMap.lTensor_comm, hxy]

/-- Over a Noetherian base, the given map is injective with flat cokernel. -/
private theorem injective_and_flat_quotient_range
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [IsNoetherianRing S.A] :
    Function.Injective S.u ∧ Module.Flat S.A (S.M ⧸ LinearMap.range S.u) := by
  have : IsNoetherianRing S.B := Algebra.EssFiniteType.isNoetherianRing S.A S.B
  exact
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (R := S.A) (S := S.B) (N := S.N) (M := S.M) S.u S.injective_mod_maximalIdeal

/-- **Stacks Project, Tag 0AT1.** In Situation 0AT0 over a Noetherian base, the given map is
universally injective over the base ring. -/
@[stacks 0AT1 "universal injectivity"]
theorem universallyInjective_of_isNoetherianRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsNoetherianRing S.A] : UniversallyInjectivePoly S.u := by
  have h := injective_and_flat_quotient_range S
  exact universallyInjective_of_injective_and_flat_quotient S.u h.1 h.2

/-- **Stacks Project, Tag 0AT1.** In Situation 0AT0 over a Noetherian base, the source module
is flat over the base ring. -/
@[stacks 0AT1 "flatness"]
theorem flat_of_isNoetherianRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsNoetherianRing S.A] : Module.Flat S.A S.N := by
  have h := injective_and_flat_quotient_range S
  have := h.2
  exact flat_of_flat_of_flat_quotient S.u (LinearMap.range S.u).mkQ h.1
    (LinearMap.exact_map_mkQ_range S.u) (Submodule.mkQ_surjective _)

end AlgebraicGeometry
