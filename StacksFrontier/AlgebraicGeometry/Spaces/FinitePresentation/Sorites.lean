module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion

/-!
# Composition and cancellation for relative limit preservation

Relative limit preservation of a transformation of presheaves on the big fppf site over a
scheme is stable under composition, and can be cancelled on the right: if a transformation
and its composite with a preceding one are relatively limit preserving, so is the preceding
transformation.

## Main results

* `AlgebraicGeometry.relativelyLimitPreserving_comp` is stability under composition.
* `AlgebraicGeometry.relativelyLimitPreserving_of_comp_of_right` cancels a relatively
  limit-preserving transformation from a composite.

## Implementation notes

Both proofs go through the affine-limit criterion
`AlgebraicGeometry.relativelyLimitPreserving_iff_affineLimit_isPullback`, which turns the
statements into pasting and cancellation of cartesian squares. The index object universe
`max w w'` is closed under passage to a slice, which is what makes the criterion applicable
on both sides of each equivalence.

## References

* [Stacks Project, Tag 049L](https://stacks.math.columbia.edu/tag/049L)
* [Stacks Project, Tag 0GDY](https://stacks.math.columbia.edu/tag/0GDY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry

/-- The composition of two relatively limit-preserving transformations is
relatively limit preserving. -/
@[stacks 049L]
public theorem relativelyLimitPreserving_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : RelativelyLimitPreserving.{u, v, max w w', w'} B S hS a)
    (hb : RelativelyLimitPreserving.{u, v, max w w', w'} B S hS b) :
    RelativelyLimitPreserving.{u, v, max w w', w'} B S hS (a ≫ b) := by
  rw [relativelyLimitPreserving_iff_affineLimit_isPullback.{u, v, w, w'}]
  intro I hI hI' D c hc hD hcAffine
  let U := CategoryTheory.uliftFunctor.{max w w', v}
  let a' := Functor.whiskerRight a U
  let b' := Functor.whiskerRight b U
  have hA := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, v, w, w'}
    B S hS a).1 ha I D c hc hD hcAffine
  have hB := (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, v, w, w'}
    B S hS b).1 hb I D c hc hD hcAffine
  have hmid :
      colimMap (D.op.whiskerLeft a') ≫ colimMap (D.op.whiskerLeft b') =
        colimMap (D.op.whiskerLeft (a' ≫ b')) := by
    apply colimit.hom_ext
    intro i
    simp only [ι_colimMap_assoc, ι_colimMap, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.assoc]
  have hAB := hA.paste_vert hB
  rw [hmid] at hAB
  simpa only [Functor.whiskerRight_comp, NatTrans.comp_app, Functor.map_comp] using hAB

/-- If `b` and `a ≫ b` preserve limits relatively, then so does `a`. -/
@[stacks 0GDY]
public theorem relativelyLimitPreserving_of_comp_of_right
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H)
    (hba : RelativelyLimitPreserving.{u, v, w, w'} B S hS (a ≫ b))
    (hb : RelativelyLimitPreserving.{u, v, w, w'} B S hS b) :
    RelativelyLimitPreserving.{u, v, w, w'} B S hS a := by
  simp only [relativelyLimitPreserving_iff_affineLimit_isPullback.{u, v, w, w'}
    B S hS] at hba hb ⊢
  intro I instI instC D c hc hDaff hcaff
  have houter := hba I D c hc hDaff hcaff
  rw [Functor.whiskerRight_comp, Functor.whiskerLeft_comp] at houter
  refine IsPullback.of_bot ?_ ?_ (hb I D c hc hDaff hcaff)
  · simpa only [Limits.colimMap_eq, Limits.colim.map_comp,
      NatTrans.comp_app, Functor.map_comp] using houter
  · apply Limits.colimit.hom_ext; intro i
    rw [Limits.colimit.ι_desc_assoc, Limits.ι_colimMap_assoc]
    simpa only [Functor.mapCocone_ι_app, Functor.comp_map,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
      Functor.const_obj_obj, Limits.Cone.op_pt, Limits.colimit.ι_desc]
      using congrArg (fun f => uliftFunctor.{max w w', v}.map f)
        (NatTrans.naturality a (c.op.ι.app i))

end AlgebraicGeometry
