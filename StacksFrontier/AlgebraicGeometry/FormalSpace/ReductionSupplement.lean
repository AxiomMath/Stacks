module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction`

Representable thickenings of presheaves on the big fppf site are bijective on sections over
objects whose underlying scheme is reduced, and hence on points; consequences for reductions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable thickenings on reduced test objects

A representable thickening of presheaves is bijective on the sections over any object of the
site whose underlying scheme is reduced, and hence bijective on points. **Nothing here uses the
universal property of a reduction**: the base change of a thickening to a reduced scheme is a
surjective closed immersion into a reduced scheme, hence an isomorphism, and that is already the
whole of the lifting step. The `IsReduction` statements further down are corollaries.

This is the `AlgebraicGeometry.Space.IsRepresentableThickeningULift` form of the
universal-homeomorphism statement whose absence is recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms`; the topological half is
`AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionPointTopology`.
-/

variable {B S hS}

/-- **A section over a reduced object of the site lifts uniquely along a representable
thickening.** The base change of the thickening to that object is a surjective closed immersion
into a reduced scheme, hence an isomorphism, and the lift is built from its inverse. -/
theorem existsUnique_comp_eq_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS a)
    (T : BigFppfOver B S hS) (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (v : G.obj (Opposite.op T)) :
    ∃! l : (uliftYoneda.{u + 1}).obj T ⟶ F, l ≫ a = uliftYonedaEquiv.{u + 1}.symm v := by
  obtain ⟨b, snd, fst, sq⟩ := h.1 (uliftYonedaEquiv.{u + 1}.symm v)
  obtain ⟨hclosed, hsurj⟩ := h.2 _ fst snd sq
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) := hclosed
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map snd) := ⟨hsurj⟩
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
    isIso_of_isClosedImmersion_of_surjective _
  have _ : IsIso snd := isIso_of_reflects_iso snd (BigFppfOver.toScheme B S hS)
  refine ⟨inv ((uliftYoneda.{u + 1}).map snd) ≫ fst, ?_, ?_⟩
  · simp only [Category.assoc, sq.w, IsIso.inv_hom_id_assoc]
  · intro l hl
    have hw : l ≫ a = 𝟙 _ ≫ uliftYonedaEquiv.{u + 1}.symm v := by
      rwa [Category.id_comp]
    have hm : sq.lift l (𝟙 _) hw = inv ((uliftYoneda.{u + 1}).map snd) :=
      (cancel_mono ((uliftYoneda.{u + 1}).map snd)).mp
        (by rw [sq.lift_snd, IsIso.inv_hom_id])
    rw [← sq.lift_fst l (𝟙 _) hw, hm]

/-- **A representable thickening is bijective on the sections over a reduced object of the
site.** -/
theorem bijective_app_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS a)
    (T : BigFppfOver B S hS) (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T)) :
    Function.Bijective (a.app (Opposite.op T)) := by
  refine ⟨fun a₁ a₂ he ↦ ?_, fun v ↦ ?_⟩
  · apply uliftYonedaEquiv.{u + 1}.symm.injective
    exact (existsUnique_comp_eq_of_isRepresentableThickeningULift h T hT
      (a.app (Opposite.op T) a₁)).unique (uliftYonedaEquiv_symm_comp a₁ a)
      (by rw [uliftYonedaEquiv_symm_comp, he])
  · obtain ⟨l, hl, -⟩ := existsUnique_comp_eq_of_isRepresentableThickeningULift h T hT v
    refine ⟨uliftYonedaEquiv.{u + 1} l, ?_⟩
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg uliftYonedaEquiv.{u + 1} hl

/-- **A representable thickening is bijective on points.** Every field-valued point is a section
over the spectrum of a field, which is reduced, so it lifts uniquely. -/
theorem bijective_pointsMapULift_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G}
    (h : Space.IsRepresentableThickeningULift.{u + 1} B S hS a) :
    Function.Bijective (Space.pointsMapULift.{u + 1} B S hS F a) := by
  have hbij (q : Space.FieldValuedPointULift.{u + 1} B S hS G) :=
    bijective_app_of_isRepresentableThickeningULift h _
      (IsReduction.isReduced_toScheme_obj_siteObject G q)
  refine ⟨fun first second equality ↦ ?_, fun p ↦ ?_⟩
  · induction first using Quot.ind with | _ first =>
    induction second using Quot.ind with | _ second =>
    obtain ⟨common, ⟨toFirst, hfirst⟩, ⟨toSecond, hsecond⟩⟩ :=
      (Space.FieldValuedPointULift.class_eq_class_iff B S hS G _ _).mp equality
    obtain ⟨value, hvalue⟩ := (hbij common).2 common.value
    refine Quot.sound ⟨⟨common.carrier, common.contained, common.toBase, value⟩,
      ⟨toFirst, ?_⟩, ⟨toSecond, ?_⟩⟩ <;>
      exact (hbij common).1 (by rwa [NatTrans.naturality_apply, hvalue])
  · induction p using Quot.ind with | _ p =>
    obtain ⟨value, hvalue⟩ := (hbij p).2 p.value
    refine ⟨(⟨p.carrier, p.contained, p.toBase, value⟩ :
      Space.FieldValuedPointULift.{u + 1} B S hS F).class B S hS F, ?_⟩
    rw [Space.pointsMapULift_class]
    exact congrArg (fun v ↦ (⟨p.carrier, p.contained, p.toBase, v⟩ :
      Space.FieldValuedPointULift.{u + 1} B S hS G).class B S hS G) hvalue

end AlgebraicGeometry.FormalSpace

end
