module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedPullbackUnitLawsOfRingedSpace
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion

/-!
# The two unit laws for the composition isomorphism of derived pullback, for schemes

`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_id_comp_anyModel` and
`...derivedPullbackCompIsoCanonical_comp_id_anyModel` prove the two unit laws for the
composition isomorphism of derived pullback of [Stacks, Tag 0D5S] at an arbitrary model of the
derived categories. This file reads them for a morphism of schemes at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, where `Stacks.Duality.derivedPullback`
and `Stacks.Duality.derivedPullbackCompIso` live.

These two statements are exactly the hypothesis `hpull` that conditions (b) and (c) of
[Stacks, Tag 0ATY] were carrying in
`StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionUnits`; with them the
two conditions are unconditional.

## Main results

All in the namespace `Stacks.Duality`.

* `derivedPullbackIdIso_eq` — the scheme-level identification `L(𝟙_Y)^* ≅ 𝟭` is the
  ringed-space one at the locally small model. The two are the same term.
* `derivedPullbackCompIso_id_comp` and `derivedPullbackCompIso_comp_id` — **the two unit laws**
  `L(𝟙 Y ≫ g)^* = Lg^* ⋙ L(𝟙 Y)^* ≅ Lg^*` and `L(f ≫ 𝟙 Y)^* = L(𝟙 Y)^* ⋙ Lf^* ≅ Lf^*`.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open Stacks.DerivedPullback.Composition (derivedPullbackIdIsoOfRingedSpace
  derivedPullbackCompIsoCanonical_id_comp_anyModel
  derivedPullbackCompIsoCanonical_comp_id_anyModel)

universe u

namespace Stacks.Duality

/-- The identification of `L(𝟙_Y)^*` with the identity functor of `D(𝒪_Y)` is the ringed-space
one read at the locally small model: the two are the same term. -/
theorem derivedPullbackIdIso_eq (Y : Scheme.{u}) :
    derivedPullbackIdIso Y =
      derivedPullbackIdIsoOfRingedSpace Y.toLocallyRingedSpace.toRingedSpace :=
  rfl

/-- **The left unit law for the composition isomorphism of derived pullback on a scheme**, at the
locally small model: `L(𝟙 Y ≫ g)^* = Lg^* ⋙ L(𝟙 Y)^* ≅ Lg^*` is the identification of
`L(𝟙 Y)^*` with the identity, whiskered by `Lg^*`.

This is `derivedPullbackCompIsoCanonical_id_comp_anyModel` at the underlying morphism of ringed
spaces; it is the hypothesis `hpull` that
`Stacks.Duality.twistedInverseImageCompIso_id_comp_eq_rightUnitor_symm` was carrying. -/
theorem derivedPullbackCompIso_id_comp (Y : Scheme.{u}) {Z : Scheme.{u}} (g : Y ⟶ Z) :
    derivedPullbackCompIso (𝟙 Y) g =
      isoWhiskerLeft (derivedPullback g) (derivedPullbackIdIso Y) ≪≫
        rightUnitor (derivedPullback g) :=
  derivedPullbackCompIsoCanonical_id_comp_anyModel (Scheme.Hom.toLRSHom g).toShHom

/-- **The right unit law for the composition isomorphism of derived pullback on a scheme**, at
the locally small model. This is the hypothesis `hpull` that
`Stacks.Duality.twistedInverseImageCompIso_comp_id_eq_leftUnitor_symm` was carrying. -/
theorem derivedPullbackCompIso_comp_id {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullbackCompIso f (𝟙 Y) =
      isoWhiskerRight (derivedPullbackIdIso Y) (derivedPullback f) ≪≫
        leftUnitor (derivedPullback f) :=
  derivedPullbackCompIsoCanonical_comp_id_anyModel (Scheme.Hom.toLRSHom f).toShHom

end Stacks.Duality

end
