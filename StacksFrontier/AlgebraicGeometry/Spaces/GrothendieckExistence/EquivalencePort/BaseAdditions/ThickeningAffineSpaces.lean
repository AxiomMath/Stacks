module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
import all StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces

/-!
# The pushout of a thickening along an affine morphism, from one atlas

`AlgebraicGeometry.Space.pushout_inr_isThickening` asks for compatible pairs of étale scheme
charts for *every* span of a thickening and an affine morphism.  The proof only uses the charts of
the given span; this module states that form, for a single `ThickeningAffineAtlas`, with the
proof of the base theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasPullback_presheaf_thickeningAffineSpacesC1573
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The morphism `Y ⟶ Y'` from the affine target into the pushout is a thickening, for a span
admitting a compatible pair of étale scheme charts. -/
theorem pushout_inr_isThickening_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) [HasPushout i f] :
    IsThickeningHom B S hS (pushout.inr i f) := by
  obtain ⟨E, a, b, hpush, qm, hqm, hqmS, hqmE, -, hb₀⟩ :=
    isPushout_quotient_of_thickeningAffineAtlas B S hS A
  have := A.isAffineHom_g
  have := A.isAffineHom_gR
  -- the right leg of each scheme pushout is a thickening
  have hbT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.b) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_k A.isPushout_chart
  have hbRT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.bR) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_kR A.isPushout_relation
  -- the two first projections are étale
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map A.s) := by
    have h : (relation B S hS A.s A.t).source = (Over.post B.inclusion).map A.s :=
      prod.lift_snd _ _
    have hrel := A.etaleRelation.etale_source
    rw [h] at hrel
    exact hrel
  have hEsY : Etale ((BigFppfOver.toScheme B S hS).map A.sY) :=
    A.etale_q.property A.q (yoneda.map A.tY) A.sY A.kernelPair_Y.flip
  -- the relation square over the first projections is cartesian
  have hcartScheme : IsPullback ((BigFppfOver.toScheme B S hS).map A.bR)
      ((BigFppfOver.toScheme B S hS).map A.sY) ((BigFppfOver.toScheme B S hS).map A.s)
      ((BigFppfOver.toScheme B S hS).map A.b) :=
    isPullback_of_isThickening_of_etale _ _ _ _ hbRT hbT
      (by simpa only [← Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map A.bR_s)
  have hcart : IsPullback A.bR A.sY A.s A.b :=
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hcartScheme
  -- hence the chart of `Y` is the base change of the chart of the pushout
  have hbase : IsPullback (yoneda.map A.b) A.q qm b.hom :=
    isPullback_chart_of_isPullback_source B S hS Y.property.isSheaf E.property.isSheaf
      A.q qm b.hom A.surjective_q A.etale_q hqmS hqmE A.kernelPair_Y hqm
      A.bR_s A.bR_t hcart hb₀
  -- `b` is a closed immersion, by the étale-local criterion on the chart `qm`
  have hstabCI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hstabS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hbCI : IsClosedImmersion B S hS (yoneda.map A.b) :=
    MorphismProperty.relative_map hbT.1
  have hbS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map A.b) :=
    MorphismProperty.relative_map (show (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) A.b from ⟨hbT.2⟩)
  have hsnd : IsClosedImmersion B S hS (pullback.snd b.hom qm) := by
    have heq : hbase.flip.isoPullback.inv ≫ yoneda.map A.b = pullback.snd b.hom qm := by simp
    have h := MorphismProperty.RespectsIso.precomp
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) hbase.flip.isoPullback.inv _ hbCI
    rwa [heq] at h
  have hclosed : IsClosedImmersion B S hS b.hom := by
    refine ((isClosedImmersion_tfae B S hS Y.property E.property b.hom).out 4 1).mp ?_
    exact ⟨A.P, qm, hqmS, hqmE, hsnd⟩
  -- `b` is surjective on points
  have hbPts : Function.Surjective
      (pointsMap B S hS (yoneda.obj A.V) (yoneda.map A.b)) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj A.P)
      (isAlgebraicSpace_yoneda B S hS A.P) A.V (yoneda.map A.b)).mp hbS
  have hqmPts : Function.Surjective (pointsMap B S hS (yoneda.obj A.P) qm) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS E.1 E.property A.P qm).mp hqmS
  have hbSurj : Function.Surjective (pointsMap B S hS Y.1 b.hom) := by
    intro e
    obtain ⟨z, hz⟩ := hqmPts e
    obtain ⟨v, hv⟩ := hbPts z
    refine ⟨pointsMap B S hS (yoneda.obj A.V) A.q v, ?_⟩
    have h : pointsMap B S hS (yoneda.obj A.V) (A.q ≫ b.hom) v = e := by
      rw [hb₀, pointsMap_comp]
      simp only [Function.comp_apply]
      rw [hv, hz]
    rw [pointsMap_comp] at h
    simpa only [Function.comp_apply] using h
  have hbThick : IsThickeningHom B S hS b :=
    (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS b).mpr ⟨hclosed, hbSurj⟩
  have hiso := isThickeningHom_comp_iso B S hS hbThick hpush.isoPushout
  rwa [hpush.inr_isoPushout_hom] at hiso


end AlgebraicGeometry.Space.C1573

end
