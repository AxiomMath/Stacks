module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Decent algebraic stacks

A point of a category fibred in groupoids `𝒳` over the big fppf site of `S` is an equivalence
class of field-valued points. Each field-valued point `p` with base `Spec k` determines, by the
2-Yoneda lemma, a 1-morphism `Spec k → 𝒳`. The category `𝒳` is *decent* when every one of its
points has a field-valued representative for which this 1-morphism is quasi-compact.

## Main definitions

* `AlgebraicGeometry.Stack.fieldValuedPointMorphism`: the 1-morphism from the category
  represented by the base of a field-valued point to the category fibred in groupoids, given
  by the 2-Yoneda lemma.
* `AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint`: quasi-compactness of that
  1-morphism.
* `AlgebraicGeometry.Stack.IsDecent`: decency.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_iff_hasRelativeProperty`:
  `AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint` is the relative property
  `AlgebraicGeometry.Stack.HasRelativeProperty` for quasi-compactness of morphisms of algebraic
  spaces, given that this property is local at the target for the fppf precoverage.

## References

* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The 1-morphism `Spec k → 𝒳` to a category fibred in groupoids over the big fppf site of `S`
from the category represented by the base `Spec k` of a field-valued point of it, given by the
2-Yoneda lemma. -/
@[sga "3 XI 1.7"]
noncomputable def fieldValuedPointMorphism (p : FieldValuedPoint B S hS 𝒳.val) :
    schemeFibredCategory B S hS p.base ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids p.base
      (Functor.Fiber.mk (a := p.obj) p.over))

/-- A field-valued point of a category fibred in groupoids over the big fppf site of `S` *is
quasi-compact* when the 1-morphism it determines is representable by algebraic spaces and
every algebraic space representing a base change of it along a scheme-valued point of the
target has quasi-compact structural morphism, read as a morphism of algebraic spaces over `S`. -/
abbrev IsQuasiCompactFieldValuedPoint (p : FieldValuedPoint B S hS 𝒳.val) : Prop :=
  ∃ _hf : IsRepresentableByAlgebraicSpaces B S hS
      (fieldValuedPointMorphism B S hS 𝒳 p).hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (schemeFibredCategory B S hS p.base).val.p 𝒳.val.p y
            (CatFiberedInGroupoids.homFunctor (fieldValuedPointMorphism B S hS 𝒳 p)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsQuasiCompact B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- `AlgebraicGeometry.Stack.IsQuasiCompactFieldValuedPoint` is the relative property
`AlgebraicGeometry.Stack.HasRelativeProperty` for quasi-compactness of morphisms of algebraic
spaces, for the 1-morphism a field-valued point determines, given that quasi-compactness of
morphisms of algebraic spaces is local at the target for the fppf precoverage. -/
theorem isQuasiCompactFieldValuedPoint_iff_hasRelativeProperty
    [MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => Space.IsQuasiCompact B S hS f.hom)
      (Space.Topology.precoverage.{u, u + 1} .fppf B S hS)]
    (p : FieldValuedPoint B S hS 𝒳.val) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒳 p ↔
      ∃ hf : IsRepresentableByAlgebraicSpaces B S hS
          (fieldValuedPointMorphism B S hS 𝒳 p).hom,
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (fun _ _ g => Space.IsQuasiCompact B S hS g.hom)
          (fieldValuedPointMorphism B S hS 𝒳 p) hf :=
  Iff.rfl

/-- A category fibred in groupoids over the big fppf site of `S` — in particular an algebraic
stack — is *decent* when every one of its points admits a quasi-compact field-valued
representative. -/
@[stacks 0GW1]
abbrev IsDecent : Prop :=
  ∀ x : points B S hS 𝒳.val 𝒳.isFiberedInGroupoids,
    ∃ p : FieldValuedPoint B S hS 𝒳.val,
      pointClass B S hS 𝒳.val 𝒳.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳 p

end AlgebraicGeometry.Stack

end
