module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# Pullback of modules along a flat morphism of ringed spaces

Let `f : X ⟶ Y` be a flat morphism of ringed spaces, that is, one whose every germ map
`𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` is a flat ring homomorphism. Then pullback of sheaves of modules along
`f` is exact, and consequently its right adjoint, pushforward, carries injective `𝒪_X`-modules
to injective `𝒪_Y`-modules.

The route is the stalkwise one of
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/ClosedSubsetPullbackLeftExact.lean`,
with flatness of the germ map in place of invertibility: the stalk of `f^*M` at `x` is the base
change of the stalk of `M` at `f(x)` along the germ map, the stalk functor on sheaves of modules
is exact, and base change along a *flat* ring map preserves finite limits. Monomorphisms of
sheaves of modules are detected on stalks, so `f^*` preserves monomorphisms; being additive and
a left adjoint it is then exact, and the adjunction transports exactness of `f^*` to preservation
of injectives by `f_*`.

The one genuinely new input is flatness of the `RingCat`-valued germ map
`Stacks.RingedSpace.stalkRingMap f x`, which is flatness of the `CommRingCat`-valued stalk map
`f.hom.stalkMap x` transported along the ring isomorphisms `Stacks.RingedSpace.ringStalkCommIso`
on source and target. That transport is isolated in the purely algebraic
`RingHom.Flat.of_ringEquiv_square`.

## Main results

* `RingHom.Flat.of_ringEquiv_square`: flatness of a ring homomorphism transfers across a
  commutative square whose vertical maps are ring isomorphisms.
* `RingedSpaceModuleAdjunction.exactFunctor_modulePullback_of_isFlat`: **pullback of sheaves of
  modules along a flat morphism of ringed spaces is exact** — [Stacks, Tag 02N4].
* `RingedSpaceModuleAdjunction.modulePushforward_preservesInjectiveObjects`: **pushforward along
  a flat morphism of ringed spaces carries injective `𝒪_X`-modules to injective
  `𝒪_Y`-modules** — [Stacks, Tag 02N5], in full.

The stalkwise inputs the two results are assembled from are proved in
`StacksFrontier/Topology/Sheaves/RingedSpace/FlatModulePullback.lean`, not here:
`Stacks.RingedSpace.preservesFiniteLimits_stalkBaseChange_of_isFlatAt` (base change along a flat
germ map preserves finite limits),
`RingedSpaceModuleAdjunction.preservesMonomorphisms_modulePullback_of_isFlat` and
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat`.

Inhabitants of the flatness hypothesis that are not isomorphisms of ringed spaces are in
`StacksFrontier/AlgebraicGeometry/RingedSpace/FlatOfIsoStalkMap.lean`.

## References

* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
* [Stacks Project, Tag 02N5](https://stacks.math.columbia.edu/tag/02N5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace RingHom.Flat

/-- **Flatness transfers across a square of ring isomorphisms.** If `eA ∘ φ = ψ ∘ eB` with
`eB : B ≃+* B'` and `eA : A ≃+* A'` ring isomorphisms and `ψ : B' →+* A'` flat, then
`φ : B →+* A` is flat: `φ` factors as `eA⁻¹ ∘ ψ ∘ eB`, and precomposing or postcomposing with a
bijective ring map does not change flatness. -/
theorem of_ringEquiv_square {B B' A A' : Type*} [CommRing B] [CommRing B'] [CommRing A]
    [CommRing A'] {φ : B →+* A} {ψ : B' →+* A'} (eB : B ≃+* B') (eA : A ≃+* A')
    (hsq : eA.toRingHom.comp φ = ψ.comp eB.toRingHom) (hψ : ψ.Flat) : φ.Flat := by
  have hφ : φ = eA.symm.toRingHom.comp (ψ.comp eB.toRingHom) := by
    rw [← hsq]
    ext b
    simp
  rw [hφ, RingHom.Flat.comp_iff_of_bijective_left eA.symm.bijective,
    RingHom.Flat.comp_iff_of_bijective_right eB.bijective]
  exact hψ

end RingHom.Flat

namespace RingedSpaceModuleAdjunction

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)


/-- **Module pullback along a flat morphism of ringed spaces is exact.** -/
@[stacks 02N4, ega "0 6.7.8" "f* exact", sga "4 Vbis 2.4.0.1" "ringed spaces"]
theorem exactFunctor_modulePullback_of_isFlat (hf : AlgebraicGeometry.IsFlat f) :
    exactFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
      (_root_.SheafOfModules.{u} (structureSheafRing X)) (modulePullback f) :=
  exactFunctor_modulePullback_of_preservesFiniteLimits _
    (preservesFiniteLimits_modulePullback_of_isFlat f hf)

/-- **Pushforward along a flat morphism of ringed spaces preserves injective modules.** The left
adjoint `f^*` of `f_*` is exact, and a functor with an exact left adjoint preserves injective
objects. -/
@[stacks 02N5]
theorem modulePushforward_preservesInjectiveObjects (hf : AlgebraicGeometry.IsFlat f) :
    (modulePushforward f).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact (modulePushforward f) (modulePullback f)
    (modulePullbackPushforwardAdjunction f)
    ⟨preservesFiniteLimits_modulePullback_of_isFlat f hf,
      preservesFiniteColimits_modulePullback f⟩

end RingedSpaceModuleAdjunction

end
