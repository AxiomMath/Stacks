module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.CategoryTheory.Adjunction.LeftTensorHomDiagonalTransport

/-!
# Stacks 08J8 on an algebraic space, through the model

The adjunction `- ⊗^L M ⊣ R𝓗om(M, -)` on `D(𝒪_X)` of an algebraic space `X` is that of the
equi-universe model `AlgebraicGeometry.Space.smallEtaleModelRingedSite`, transported along the
derived equivalence `E` and its comparison `smallEtaleModelDerivedTensorIso` with `⊗^L`. This file
records that description as equations usable at other spellings of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction_eq`: the adjunction is the
  composite of the model adjunction with the derived equivalence.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensorRightIso_hom_app`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `smallEtaleDerivedTensorSheafHomAdjunction` is the adjunction of the model, composed with the
derived equivalence on both sides and re-seated along `smallEtaleDerivedTensorRightIso`. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_eq (X : AlgebraicSpaces B S hS)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedTensorSheafHomAdjunction B S hS X M =
      ((((smallEtaleModelDerivedEquivalence B S hS X).toAdjunction.comp
      (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)
        ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M))).comp
          (smallEtaleModelDerivedEquivalence B S hS X).symm.toAdjunction).ofNatIsoLeft
    (smallEtaleDerivedTensorRightIso B S hS X M).symm) := by
  unfold smallEtaleDerivedTensorSheafHomAdjunction
  congr 1

/-- The components of `smallEtaleDerivedTensorRightIso`: the unit of the derived equivalence
followed by its inverse applied to the comparison of Stacks 07A4 with the model. -/
theorem smallEtaleDerivedTensorRightIso_hom_app (X : AlgebraicSpaces B S hS)
    (M A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensorRightIso B S hS X M).hom.app A =
      (smallEtaleModelDerivedEquivalence B S hS X).unit.app
          (((smallEtaleDerivedTensor B S hS X).obj A).obj M) ≫
        (smallEtaleModelDerivedEquivalence B S hS X).inverse.map
          ((smallEtaleModelDerivedTensorIso B S hS X).hom.app (A, M)) := by
  simp [smallEtaleDerivedTensorRightIso]
  rfl

end AlgebraicGeometry.Space

end
