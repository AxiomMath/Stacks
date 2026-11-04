module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# A point of a ringed space, as a morphism from the one-point ringed space

`Stacks.AssociatedSheaf.coefficientPoint R` is the one-point ringed space with structure sheaf
the skyscraper with value `R`.  A ring map `R ⟶ Γ(X, 𝒪_X)` induces a morphism *into* it,
`Stacks.AssociatedSheaf.toCoefficientPoint`.  This file constructs the morphism *out of* it at a
point: for a ringed space `X` and `x ∈ X`,

`({x}, 𝒪_{X,x}) ⟶ (X, 𝒪_X)`,

sending the point to `x` and acting on sections by taking germs at `x`.

This is the morphism the Stacks project introduces in the proof of Tag 0GM8 — "let `Y = {x}` be
the ringed space with `𝒪_Y = 𝒪_{X,x}`, so that `Y ⟶ X` is flat" — and it is the ringed-space
counterpart of a point of a scheme.

## Main definitions

* `Stacks.AssociatedSheaf.pointStalkIso`: the structure sheaf of the one-point ringed space has
  stalk `R` at the point.
* `Stacks.AssociatedSheaf.fromCoefficientPoint`: the morphism
  `({x}, 𝒪_{X,x}) ⟶ (X, 𝒪_X)` at a point `x` of `X`.

## Main results

* `Stacks.AssociatedSheaf.fromCoefficientPoint_base_pt`: it sends the point to `x`.
* `Stacks.AssociatedSheaf.fromCoefficientPoint_c_app`: its structure-sheaf comparison is the
  germ map at `x`, read through the identification of the two skyscrapers.
* `Stacks.AssociatedSheaf.isIso_stalkMap_fromCoefficientPoint`: it is flat, that is it induces an
  isomorphism on stalks of structure sheaves.

## Implementation notes

*Why the structure-sheaf comparison is free.*  The comparison `𝒪_X ⟶ f_*𝒪_Y` is the unit of the
stalk–skyscraper adjunction at `x`, `toSkyscraperPresheaf x (𝟙  𝒪_{X,x})`, composed with
`skyscraperPresheaf_eq_pushforward`, which says that the skyscraper on `X` at `x` *is* the
pushforward along the constant map of the skyscraper on the one-point space.  So no naturality
is checked here, and the comparison is pinned by `fromCoefficientPoint_c_app`.

*Two decidability instances.*  `skyscraperPresheaf` takes `∀ U, Decidable (p₀ ∈ U)` as an
instance argument and the membership is not decidable constructively, so `Classical.propDecidable`
is a local instance here for the opens of `X`.  For the opens of the one-point space
`Stacks.AssociatedSheaf.pointMemDecidable` is registered *after* it, so that it wins and the
skyscraper appearing here is the one baked into `coefficientPoint` rather than a second copy
with a different instance.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open StalkSkyscraperPresheafAdjunctionAuxs

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] Classical.propDecidable
attribute [local instance] Stacks.AssociatedSheaf.pointMemDecidable
attribute [local implicit_reducible] coefficientPoint

/-- The structure sheaf of the one-point ringed space has stalk `R` at the point: the stalk of a
skyscraper at a point of the closure of its support. -/
def pointStalkIso (R : CommRingCat.{u}) :
    (coefficientPoint R).presheaf.stalk PUnit.unit ≅ R :=
  skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit.{u + 1}) PUnit.unit R
    specializes_rfl

/-- **A point of a ringed space, as a morphism from the one-point ringed space.**  The morphism

`({x}, 𝒪_{X,x}) ⟶ (X, 𝒪_X)`

whose underlying map sends the point to `x` and whose structure-sheaf comparison is the germ map
at `x`.

The comparison is the unit of the stalk–skyscraper adjunction at `x`, read through
`skyscraperPresheaf_eq_pushforward`: the skyscraper on `X` at `x` with value `𝒪_{X,x}` is the
pushforward along the constant map of the structure sheaf of `coefficientPoint 𝒪_{X,x}`. -/
def fromCoefficientPoint (X : RingedSpace.{u, u}) (x : X.carrier) :
    coefficientPoint (X.presheaf.stalk x) ⟶ X :=
  { hom :=
    { base := TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1}) x)
      c := toSkyscraperPresheaf x (𝟙 (X.presheaf.stalk x)) ≫
        eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x)) } }

/-- The morphism out of the one-point ringed space sends the point to `x`. -/
theorem fromCoefficientPoint_base_pt (X : RingedSpace.{u, u}) (x : X.carrier) :
    (ConcreteCategory.hom (fromCoefficientPoint X x).hom.base) PUnit.unit = x := rfl

/-- The structure-sheaf comparison of `fromCoefficientPoint` is the unit of the stalk–skyscraper
adjunction at `x`, that is the germ map, read through the identification of the skyscraper on `X`
with the pushforward of the skyscraper on the point.  This pins the morphism down. -/
theorem fromCoefficientPoint_c_app (X : RingedSpace.{u, u}) (x : X.carrier)
    (U : (Opens X.carrier)ᵒᵖ) :
    (fromCoefficientPoint X x).hom.c.app U =
      (toSkyscraperPresheaf x (𝟙 (X.presheaf.stalk x))).app U ≫
        (eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x))).app U := rfl

/-- **The morphism out of the one-point ringed space is flat.**  It induces an isomorphism on
stalks of structure sheaves at the point: the induced map is the inverse of the identification
`Stacks.AssociatedSheaf.pointStalkIso` of the stalk of `coefficientPoint 𝒪_{X,x}` with
`𝒪_{X,x}`. -/
instance isIso_stalkMap_fromCoefficientPoint (X : RingedSpace.{u, u}) (x : X.carrier) :
    IsIso ((fromCoefficientPoint X x).hom.stalkMap PUnit.unit) := by
  have key : (fromCoefficientPoint X x).hom.stalkMap PUnit.unit ≫
      (pointStalkIso (X.presheaf.stalk x)).hom = 𝟙 _ := by
    refine X.presheaf.stalk_hom_ext fun U hxU ↦ ?_
    refine (PresheafedSpace.stalkMap_germ_assoc (fromCoefficientPoint X x).hom U PUnit.unit hxU
      (pointStalkIso (X.presheaf.stalk x)).hom).trans ?_
    have hx : x ∈ U := hxU
    have hV : PUnit.unit ∈ (Opens.map (TopCat.ofHom
        (ContinuousMap.const (TopCat.of PUnit.{u + 1}) x))).obj U := hx
    -- The germ at `x` is the unit of the stalk–skyscraper adjunction, so the composite with the
    -- counit `pointStalkIso` is the identity.
    have hgerm := germ_fromStalk x (toSkyscraperPresheaf x (𝟙 (X.presheaf.stalk x))) U hx
    rw [fromStalk_to_skyscraper] at hgerm
    -- Spell the comparison out as in `fromCoefficientPoint_c_app`, with the opens and the
    -- skyscrapers named so that the `eqToHom` of `skyscraperPresheaf_eq_pushforward` lines up
    -- syntactically.
    change ((toSkyscraperPresheaf x (𝟙 (X.presheaf.stalk x))).app (op U) ≫
          (eqToHom (skyscraperPresheaf_eq_pushforward x (X.presheaf.stalk x))).app (op U)) ≫
        (skyscraperPresheaf (X := TopCat.of PUnit.{u + 1}) PUnit.unit (X.presheaf.stalk x)).germ
            ((Opens.map (TopCat.ofHom
              (ContinuousMap.const (TopCat.of PUnit.{u + 1}) x))).obj U) PUnit.unit hV ≫
          (skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit.{u + 1}) PUnit.unit
            (X.presheaf.stalk x) specializes_rfl).hom =
        X.presheaf.germ U x hx ≫ 𝟙 (X.presheaf.stalk x)
    rw [Category.assoc, germ_skyscraperPresheafStalkOfSpecializes_hom]
    exact hgerm.symm
  rw [(pointStalkIso (X.presheaf.stalk x)).comp_hom_eq_id.mp key]
  exact Iso.isIso_inv _

end Stacks.AssociatedSheaf

end
