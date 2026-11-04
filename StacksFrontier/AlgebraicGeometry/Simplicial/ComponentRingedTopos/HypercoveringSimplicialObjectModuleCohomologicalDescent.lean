module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleDescent

/-!
# Cohomological descent along a hypercovering by a simplicial object of the site: modules

Let `C` be a site with fibre products, let `O_C` be a sheaf of commutative rings on it, let `X`
be an object of `C` and set `O_X = O_C|_{C/X}`. Let `U` be a simplicial object of `C` augmented
to `X`. Reading each term of `U` as a one-summand family of objects over `X` turns `U ⟶ X` into
a simplicial semi-representable object `associatedSimplicialObject U a` of `SR(C, X)`, whose
total site `(C/U)_total` carries the pulled-back structure sheaf `O = a⁻¹O_X` and the morphism
of ringed topoi `a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` of Stacks 0D9X.

Stacks 0DAC asserts that for `E` in the unbounded derived category `D(O_X)` the map

`E ⟶ Ra_*La^*E`

is an isomorphism.

This file records the site and the structure sheaf of the ringed topos that `a` maps to.
Stacks 0DAC itself is
`isIso_derivedPullbackPushforwardUnit_app_of_isHypercoveringAugmentation`, in the namespace
`CategoryTheory.SimplicialSemiRepresentable`, in
`...ComponentRingedTopos.HypercoveringSimplicialObjectModuleCohomologicalDescentUnconditional`.

## Main definitions

There are no new definitions: the ringed augmentation is the one of Stacks 0D9X attached by
`CategoryTheory.SimplicialSemiRepresentable.hypercoveringObjectRingedAugmentation` to the
associated simplicial semi-representable object, and the map `E ⟶ Ra_*La^*E` is
`AlgebraicGeometry.RingedToposHom.derivedPullbackPushforwardUnit` at its total ringed morphism.

## Implementation notes

The coefficients really are the sheaves of `O_X`-modules on the slice site: the two `rfl`
identifications below compute the site and the structure sheaf of the ringed topos that `a` maps
to, as in the file carrying this library's Stacks 0DA0.

The ringed augmentation is written out rather than abbreviated, for the reason recorded in
`...ComponentRingedTopos.HypercoveringSimplicialObjectModuleDescent`:
an abbreviation interposes a further layer of unfolding between these statements and the
sheafification instances their types need. Those instances are the three stated for an arbitrary
simplicial-site situation in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent`;
being attached there as local instances they are not visible here, and are re-attached below.

## References

* [Stacks Project, Tag 0DAC](https://stacks.math.columbia.edu/tag/0DAC)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0DAB](https://stacks.math.columbia.edu/tag/0DAB)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0GM9](https://stacks.math.columbia.edu/tag/0GM9)
* [Stacks Project, Section 85.21 (Tag 09X8)](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- The site of the ringed topos that the augmentation of a simplicial object of `C` over `X`
maps to is the slice site `C/X`. -/
theorem simplicialObjectRingedAugmentation_augmentationRingedTopos_J :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).augmentationRingedTopos.J = P.toGrothendieck.over X :=
  rfl

/-- The structure sheaf of the ringed topos that the augmentation of a simplicial object of `C`
over `X` maps to is `O_X = O_C|_{C/X}`. -/
theorem simplicialObjectRingedAugmentation_augmentationRingedTopos_O :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).augmentationRingedTopos.O = OC.over X :=
  rfl

end CategoryTheory.SimplicialSemiRepresentable

end
