module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.Deformation.Artin.Obstruction.Theory

/-!
# Lifts across a deformation situation as morphisms lying over the thickening

Let `p` be a category fibred in groupoids over the big fppf site of `S`, `(x, A)` an object over
an `S`-algebra and `A' → A` a deformation situation. A lift of `x` to `A'`
(`Deformation.Artin.AffineObject.HasLift`) is an object `x'` over `Spec A'` together with an
isomorphism, in the fibre over `Spec A`, from its chosen pullback to `x`. This file shows that the
same thing is an object `x'` over `Spec A'` together with a morphism `x ⟶ x'` lying over
`Spec A ⟶ Spec A'`: every such morphism is cartesian, so its source is canonically the chosen
pullback.

## Main results

* `AlgebraicGeometry.PairDeformation.hasLift_iff_exists_isHomLift`: a lift exists if and only if
  there is a morphism from `x` to an object over `Spec A'` lying over `Spec A ⟶ Spec A'`.

## References

* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open Deformation.Artin

universe u v w

namespace AlgebraicGeometry.PairDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- A lift of `x` across a deformation situation `A' → A` exists if and only if `x` maps to an
object over `Spec A'` by a morphism lying over `Spec A ⟶ Spec A'`. -/
public theorem hasLift_iff_exists_isHomLift (hp : p.IsFiberedInGroupoids)
    (P : AffineObject B S hS p) (t : DeformationSituation B S hS P.alg) :
    P.HasLift hp t ↔
      ∃ (x' : p.Fiber t.top.over) (φ : P.obj.1 ⟶ x'.1), p.IsHomLift t.hom.specMap φ := by
  let : p.IsFibered := hp.isFibered
  constructor
  · rintro ⟨x', ⟨e⟩⟩
    refine ⟨x', Fiber.fiberInclusion.map e.inv ≫ p.chosenPullbacks.map t.hom.specMap x', ?_⟩
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _ P.alg.over _ e.inv.2 _ _
      t.hom.specMap _ (p.chosenPullbacks.isStronglyCartesian _ _).toIsHomLift
  · rintro ⟨x', φ, hφ⟩
    have : p.IsStronglyCartesian t.hom.specMap φ := hp.isStronglyCartesian_homLift _ φ
    have : p.IsStronglyCartesian t.hom.specMap (p.chosenPullbacks.map t.hom.specMap x') :=
      p.chosenPullbacks.isStronglyCartesian _ _
    exact ⟨x', ⟨fiberIsoOfCartesian t.hom.specMap (p.chosenPullbacks.map t.hom.specMap x')
      (z' := P.obj) φ
      (IsStronglyCartesian.isCartesian_of_isStronglyCartesian p t.hom.specMap
        (p.chosenPullbacks.map t.hom.specMap x'))
      (IsStronglyCartesian.isCartesian_of_isStronglyCartesian p t.hom.specMap φ)⟩⟩

end AlgebraicGeometry.PairDeformation

end
