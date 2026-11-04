module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleStageFormalSpectrumMap
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange

/-!
# Smoothness of a morphism to a formal spectrum from its quotient stages

Let `S` be a scheme contained in a big fppf site `B`, let `A` be a weakly admissible topological
ring presented over `S` by a quotient system `D`, and let `g : X ⟶ Spf A` be a morphism of fppf
sheaves which is representable by algebraic spaces. Suppose that over a cofinal family of quotient
stages `Spec (A ⧸ J) ⟶ Spf A` the base change of `g` is represented by an object `Y` of the site
whose morphism to the stage is smooth. Then `g` is smooth in the bootstrap sense of Stacks 03XZ.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSmoothULift_of_stage_pullbacks`: the
  statement above.

## Implementation notes

The argument is the one of
`AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_formalSpectrumMap_of_etale_stageMap` with
étaleness of the stage maps replaced by smoothness. A point of `Spf A` out of an affine object of
the site factors through a stage by Stacks 0AIA, hence through one of the given stages, over which
the base change of `g` is represented and smooth. For an arbitrary point `T ⟶ Spf A` and an étale
chart `U ⟶ T ×_{Spf A} X`, the composite `U ⟶ T` is then smooth over each member `Tᵢ` of an affine
open cover of `T`, being an étale morphism followed by a smooth one there, and smoothness is local
on the target; a chart of `T` itself is étale over `T`, so the chart morphism is smooth by
étale-local cancellation.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Smooth

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The hypothesis of the criterion: over a cofinal family of quotient stages the base change
of `g` is represented by an object of the site, smooth over the stage. -/
abbrev HasSmoothStagePullbacks (D : QuotientSystem B S hS A) {X : FppfSheaf B S hS}
    (g : X ⟶ formalSpectrum D) : Prop :=
  ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
    ∃ (J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (_ : J'.1 ≤ J.1)
      (Y : BigFppfOver B S hS) (q : Y ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J'))
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Y ⟶ X),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) g
        (formalSpectrumInclusion D (OrderDual.toDual J')) ∧
      AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map q)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **The base change over a point factoring through a stage is smooth.** -/
private theorem exists_isPullback_smooth_of_factorsThroughStage
    (D : QuotientSystem B S hS A) {X : FppfSheaf B S hS} (g : X ⟶ formalSpectrum D)
    (hg : HasSmoothStagePullbacks B S hS D g)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS) (t : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D)
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
      formalSpectrumInclusion D (OrderDual.toDual I) = a) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X),
      IsPullback q ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) g a ∧
      AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map p) := by
  subst ha
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let _ : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  obtain ⟨J', hJ', Y, qY, pY, hpb, hsm⟩ := hg I
  have hw := colimit.w (formalSpectrumDiagram D) (homOfLE hJ' : OrderDual.toDual I ⟶ _)
  let t' := t ≫ (BigAffineFppf.inclusion B S hS).map (D.transition hJ')
  refine ⟨pullback qY t', pullback.snd _ _, F.map (pullback.fst qY t') ≫ pY, ?_, ?_⟩
  · have H := ((IsPullback.of_hasPullback qY t').map F).paste_horiz hpb
    have e := (congrArg (fun z => F.map t ≫ z) hw).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ _) (F.map_comp _ _).symm))
    exact e ▸ H
  · exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth.{u})
      ((IsPullback.of_hasPullback qY t').map (BigFppfOver.toScheme B S hS)) hsm

/-- **The base change over a point out of a quasi-compact object is smooth.** -/
private theorem exists_isPullback_smooth_of_compactSpace
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {X : FppfSheaf B S hS} (g : X ⟶ formalSpectrum D)
    (hg : HasSmoothStagePullbacks B S hS D g)
    (U : BigFppfOver B S hS) (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ X),
      IsPullback q ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) g ξ ∧
      AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map p) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ε := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨I, t, ht⟩ :=
    exists_factorsThroughStage_of_compactSpace hA.1 D U hU (ε.inv.app U ≫ ξ)
  obtain ⟨V, p, c, hpb, hp⟩ :=
    exists_isPullback_smooth_of_factorsThroughStage B S hS D g hg I U t _ ht
  exact ⟨V, p, ε.hom.app V ≫ c,
    hpb.of_iso' (ε.app V) (Iso.refl _) (ε.app U) (Iso.refl _) (by simp)
      (ε.hom.naturality p).symm (by simp)
      (by rw [← Iso.app_inv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]), hp⟩

/-- **Smoothness of the base change of a point along a smooth represented pullback.** -/
theorem smooth_map_pullback_snd_of_isPullback
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {T U' Ti V : BigFppfOver B S hS}
    {ξ : uliftYoneda.{u + 1}.obj T ⟶ P} {a : Q ⟶ P}
    (φ : uliftYoneda.{u + 1}.obj U' ⟶ pullback ξ a)
    (hφ : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.inverseImage (@Etale) (BigFppfOver.toScheme B S hS)) φ)
    (h₀ : U' ⟶ T) (hh₀ : uliftYoneda.{u + 1}.map h₀ = φ ≫ pullback.fst ξ a) (ai : Ti ⟶ T)
    (p : V ⟶ Ti) (c' : uliftYoneda.{u + 1}.obj V ⟶ Q)
    (hpbP : IsPullback c' (uliftYoneda.{u + 1}.map p) a (uliftYoneda.{u + 1}.map ai ≫ ξ))
    (hp : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map p)) :
    AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map (pullback.snd h₀ ai)) := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let Sch := BigFppfOver.toScheme B S hS
  obtain ⟨gm, hgm₁, hgm₂⟩ : ∃ gm : Y.obj V ⟶ pullback ξ a,
      gm ≫ pullback.fst ξ a = Y.map p ≫ Y.map ai ∧ gm ≫ pullback.snd ξ a = c' :=
    ⟨pullback.lift (Y.map p ≫ Y.map ai) c' ((Category.assoc _ _ _).trans hpbP.w.symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ht : IsPullback (Y.map p) gm (Y.map ai) (pullback.fst ξ a) :=
    IsPullback.of_bot (hgm₂ ▸ hpbP.flip) hgm₁.symm (IsPullback.of_hasPullback ξ a)
  have hcond : (Y.map (pullback.fst h₀ ai) ≫ φ ≫ pullback.snd ξ a) ≫ a =
      Y.map (pullback.snd h₀ ai) ≫ Y.map ai ≫ ξ := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc φ, ← hh₀,
      ← Category.assoc, ← Category.assoc, ← Y.map_comp, ← Y.map_comp, pullback.condition]
  obtain ⟨q, hq⟩ : ∃ q : pullback h₀ ai ⟶ V, Y.map q = hpbP.lift _ _ hcond :=
    ⟨Y.preimage _, Y.map_preimage _⟩
  have hqp : Y.map q ≫ Y.map p = Y.map (pullback.snd h₀ ai) :=
    hq ▸ hpbP.lift_snd _ _ hcond
  have hs : IsPullback (Y.map q ≫ Y.map p) (Y.map (pullback.fst h₀ ai)) (Y.map ai)
      (φ ≫ pullback.fst ξ a) := by
    rw [hqp, ← hh₀]
    exact ((IsPullback.of_hasPullback h₀ ai).map Y).flip
  have hcomm : Y.map q ≫ gm = Y.map (pullback.fst h₀ ai) ≫ φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hgm₁, ← Category.assoc, hqp, Category.assoc, ← hh₀,
        ← Y.map_comp, ← Y.map_comp, pullback.condition]
    · rw [Category.assoc, hgm₂, hq, Category.assoc, hpbP.lift_fst]
  have hqe : Etale (Sch.map q) :=
    hφ.property gm (Y.map (pullback.fst h₀ ai)) q (IsPullback.of_right hs hcomm ht).flip
  have hqp' : q ≫ p = pullback.snd h₀ ai := Y.map_injective (by rw [Y.map_comp, hqp])
  rw [← hqp', Sch.map_comp]
  infer_instance

/-- **Smoothness over a member of an affine open cover of the source of a point.** -/
theorem smooth_pullback_snd_affineCover_of_hasSmoothStagePullbacks
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {X : FppfSheaf B S hS} (g : X ⟶ formalSpectrum D)
    (hg : HasSmoothStagePullbacks B S hS D g) (T : BigFppfOver B S hS)
    (ξ : uliftYoneda.{u + 1}.obj T ⟶ (formalSpectrum D).obj) {U' : BigFppfOver B S hS}
    (φ : uliftYoneda.{u + 1}.obj U' ⟶ pullback ξ g.hom)
    (hφ : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.inverseImage (@Etale) (BigFppfOver.toScheme B S hS)) φ)
    (h₀ : U' ⟶ T) (hh₀ : uliftYoneda.{u + 1}.map h₀ = φ ≫ pullback.fst ξ g.hom)
    (i : ((BigFppfOver.toScheme B S hS).obj T).affineCover.I₀) :
    AlgebraicGeometry.Smooth (pullback.snd ((BigFppfOver.toScheme B S hS).map h₀)
      (((BigFppfOver.toScheme B S hS).obj T).affineCover.f i)) := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let Sch := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have hpres : PreservesLimitsOfShape WalkingCospan Sch := by
    dsimp [Sch, BigFppfOver.toScheme]
    infer_instance
  have hTi : B.Contains ((Sch.obj T).affineCover.X i) :=
    Scheme.size_lt_of_isOpenImmersion ((Sch.obj T).affineCover.f i) T.left.property
  let e : B.obj hTi ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hTi) ⟶ B.inclusion.obj T.left from
        (Sch.obj T).affineCover.f i)
  let Ti : BigFppfOver B S hS := Over.mk (e ≫ T.hom)
  let ai : Ti ⟶ T := Over.homMk e (by simp [Ti])
  have hai : Sch.map ai = (Sch.obj T).affineCover.f i := B.inclusion.map_preimage _
  have hcpt : CompactSpace (Sch.obj Ti) :=
    inferInstanceAs (CompactSpace ((Sch.obj T).affineCover.X i))
  obtain ⟨V, p, c, hpb, hp⟩ :=
    exists_isPullback_smooth_of_compactSpace B S hS hA D g hg Ti hcpt ⟨Y.map ai ≫ ξ⟩
  let c' : Y.obj V ⟶ X.obj := c.hom
  have hpbP : IsPullback c' (Y.map p) g.hom (Y.map ai ≫ ξ) :=
    hpb.map (sheafToPresheaf J (Type (u + 1)))
  have hsnd := smooth_map_pullback_snd_of_isPullback B S hS φ hφ h₀ hh₀ ai p c' hpbP hp
  have hsq' := (IsPullback.of_hasPullback h₀ ai).map Sch
  show AlgebraicGeometry.Smooth (pullback.snd (Sch.map h₀) ((Sch.obj T).affineCover.f i))
  rw [← hai]
  rw [← hsq'.isoPullback_hom_snd] at hsnd
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.Smooth.{u})
    hsq'.isoPullback.hom _).mp hsnd

/-- **Smoothness of a morphism to a formal spectrum from its quotient stages.** Let
`g : X ⟶ Spf A` be representable by algebraic spaces, with smooth represented base changes over
a cofinal family of quotient stages. Then `g` is smooth in the bootstrap sense of Stacks 03XZ:
its base change along every scheme-valued point of `Spf A` is a smooth morphism of algebraic
spaces. -/
theorem hasPropertyULift_isSmoothULift_of_stage_pullbacks
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {X : FppfSheaf B S hS} (g : X ⟶ formalSpectrum D)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hg : HasSmoothStagePullbacks B S hS D g) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom) g.hom hrep := by
  intro T ξ
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let Sch := BigFppfOver.toScheme B S hS
  let a := g.hom
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  show Space.IsSmoothULift.{u + 1} B S hS (pullback.fst ξ a)
  intro U' V' φ b h hφ hb hsq
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : U' ⟶ T, Y.map h₀ = φ ≫ pullback.fst ξ a :=
    ⟨Y.preimage _, Y.map_preimage _⟩
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : V' ⟶ T, Y.map b₀ = b := ⟨Y.preimage b, Y.map_preimage b⟩
  have hsm₀ : AlgebraicGeometry.Smooth (Sch.map h₀) := by
    have : IsZariskiLocalAtTarget (@AlgebraicGeometry.Smooth.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @AlgebraicGeometry.Smooth.{u})
        (Q := RingHom.Smooth)
    exact IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.Smooth.{u})
      (Sch.obj T).affineCover fun i ↦
        smooth_pullback_snd_affineCover_of_hasSmoothStagePullbacks B S hS hA D g hg T ξ φ hφ h₀
          hh₀ i
  have hcomp : h ≫ b₀ = h₀ := Y.map_injective (by rw [Y.map_comp, hsq, hh₀])
  exact AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget.of_commSq_etale (𝟙 _)
    (Sch.map b₀) (Sch.map h₀) (Sch.map h) inferInstance
    ((Space.relative_etale_uliftYoneda_map_iff B S hS b₀).1 hb) hsm₀
    (by rw [Category.id_comp, ← Sch.map_comp, hcomp])

end Smooth

end AlgebraicGeometry.FormalSpace
