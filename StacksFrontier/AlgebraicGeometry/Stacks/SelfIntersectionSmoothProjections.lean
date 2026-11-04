module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionPresentation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Smoothness of the two projections of the self-intersection groupoid

Let `F : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, representable by algebraic spaces and smooth, with `𝒰` represented by an algebraic
space `U` and the self-intersection `ℛ = 𝒰 ×_{F, 𝒳, F} 𝒰` represented by an algebraic space `R`.
These choices give a groupoid in algebraic spaces with object space `U` and arrow space `R`,
carried by the presentation datum
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation`. This module shows that
the source and target morphisms `R ⟶ U` of that groupoid are smooth.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isSmooth_selfIntersectionPresentation_source`: the
  source morphism is smooth.
* `AlgebraicGeometry.Stack.SelfIntersection.isSmooth_selfIntersectionPresentation_target`: the
  target morphism is smooth.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {F : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 F.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The source morphism `R ⟶ U` of the groupoid in algebraic spaces
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation` is smooth when the
presenting 1-morphism `F` is representable by algebraic spaces and smooth. -/
@[stacks 04T5 "part (1): source projection"]
theorem isSmooth_selfIntersectionPresentation_source
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsSmooth B S hS (selfIntersectionPresentation eU eR h𝒳).groupoid.source.hom :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF).mp hsmooth
    𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F))
    R.obj U.obj R.property U.property eR eU

/-- The target morphism `R ⟶ U` of the groupoid in algebraic spaces
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation` is smooth when the
presenting 1-morphism `F` is representable by algebraic spaces and smooth. -/
@[stacks 04T5 "part (1): target projection"]
theorem isSmooth_selfIntersectionPresentation_target
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hsmooth : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsSmooth B S hS (selfIntersectionPresentation eU eR h𝒳).groupoid.target.hom :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) F hF).mp hsmooth
    𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    R.obj U.obj R.property U.property eR eU

end AlgebraicGeometry.Stack.SelfIntersection

end
