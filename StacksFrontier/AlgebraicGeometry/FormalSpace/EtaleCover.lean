module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Étale coverings by formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `{Xᵢ ⟶ X}` be a family of maps
of fppf sheaves on the big fppf site of `S` with each `Xᵢ` a formal algebraic space over `S`,
each map representable by algebraic spaces and étale, and `∐ Xᵢ ⟶ X` a surjection of sheaves.
**Stacks 0AJ1** says that `X` is then a formal algebraic space over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`: **Stacks 0AJ1**.

## Implementation notes

The set-theoretic condition of Stacks 0AIS is a hypothesis rather than a conclusion: the
source imposes it on `X` as part of the definition of a formal algebraic space, and it does
not follow from the corresponding conditions on the members of the covering family.

The atlas of `X` is assembled from the atlases of the `Xᵢ`: an affine formal algebraic space
`Y` over some `Xᵢ` maps to `X` by composition, and the composite is again representable by
algebraic spaces (Stacks 0APY) and étale. Étaleness of the composite is the only real work.
It is obtained by base changing to a scheme-valued point `ξ` of `X`, choosing a surjective
étale chart `q` of the resulting algebraic space, and descending étaleness along that chart:
over the chart the base change of `Y ⟶ Xᵢ` is étale by hypothesis, and étaleness of a morphism
of schemes descends along a surjective étale morphism (Stacks 02KM). Surjectivity of the
assembled atlas is epimorphy of the induced map from the coproduct, which follows from
epimorphy of the two stages.

Étaleness of the charts is recorded by the universe-independent notions of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal
algebraic spaces take values in `Type (u + 1)`.

## References

* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étale morphisms of schemes are stable under base change along a morphism of the big fppf
site of `S`, since that site's structure functor to schemes preserves fibre products. -/
public instance inverseImage_etale_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun hs hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale.{u}) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- Surjective morphisms of schemes are stable under base change along a morphism of the big
fppf site of `S`. -/
public instance inverseImage_surjective_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨fun hs hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Surjective.{u}) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- Étaleness of morphisms of fppf sheaves with values in a larger universe is stable under
composition. -/
public theorem isEtaleULift_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G} {b : G ⟶ H}
    (ha : Space.IsEtaleULift.{u + 1} B S hS a)
    (hb : Space.IsEtaleULift.{u + 1} B S hS b) :
    Space.IsEtaleULift.{u + 1} B S hS (a ≫ b) :=
  fun U φ hφ ↦ hb U (φ ≫ a) (ha U φ hφ)

/-- An isomorphism of fppf sheaves with values in a larger universe is étale. -/
public theorem isEtaleULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G) [IsIso f] :
    Space.IsEtaleULift.{u + 1} B S hS f :=
  fun _ φ hφ ↦ MorphismProperty.RespectsIso.postcomp _ f φ hφ

/-- Precomposing an étale morphism of fppf sheaves with an isomorphism keeps it étale. -/
public theorem isEtaleULift_precomp_iso
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ≅ G) (f : G ⟶ H)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.IsEtaleULift.{u + 1} B S hS (e.hom ≫ f) := by
  let P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
  intro U φ hφ
  simpa only [Category.assoc] using
    hf U (φ ≫ e.hom) ((P.cancel_right_of_respectsIso φ e.hom).mpr hφ)

/-- A base change along a composite factors through the base change along the second factor:
the square comparing the two fibre products with the first factor is cartesian. -/
private theorem isPullback_intermediate_baseChange
    {C : Type*} [Category C] [HasPullbacks C] {U X Y T V : C}
    (ξ : U ⟶ X) (f : T ⟶ X) (g : Y ⟶ T) (q : V ⟶ pullback ξ f)
    (π : pullback ξ (g ≫ f) ⟶ pullback ξ f)
    (hπ₁ : π ≫ pullback.fst ξ f = pullback.fst ξ (g ≫ f))
    (hπ₂ : π ≫ pullback.snd ξ f = pullback.snd ξ (g ≫ f) ≫ g) :
    IsPullback (pullback.fst q π) (pullback.snd q π ≫ pullback.snd ξ (g ≫ f))
      (q ≫ pullback.snd ξ f) g := by
  have hπ : IsPullback π (pullback.snd ξ (g ≫ f)) (pullback.snd ξ f) g :=
    (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback ξ f) hπ₂).mp
      (by simpa only [hπ₁] using IsPullback.of_hasPullback ξ (g ≫ f))
  exact ((IsPullback.of_hasPullback q π).flip.paste_horiz hπ.flip).flip

/-- Étaleness of a scheme-valued point of an fppf sheaf descends along a surjective étale
morphism of the site: this is Stacks 02KM applied after base change. -/
private theorem relative_etale_of_comp_surjective_etale
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {U V : BigFppfOver B S hS} (χ : U ⟶ V)
    [Surjective ((BigFppfOver.toScheme B S hS).map χ)]
    [Etale ((BigFppfOver.toScheme B S hS).map χ)]
    (φ : (uliftYoneda.{u + 1}).obj V ⟶ X)
    (hrep : (uliftYoneda.{u + 1}).relativelyRepresentable φ)
    (hφ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
        ((uliftYoneda.{u + 1}).map χ ≫ φ)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) φ := by
  classical
  let C := BigFppfOver B S hS
  let q := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q
  let _ : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  apply MorphismProperty.relative_of_snd (P := P) hrep
  intro A g
  let d := hrep.fst' g
  let s := hrep.snd g
  have hpb : IsPullback (pullback.fst d χ) (pullback.snd d χ) d χ :=
    IsPullback.of_hasPullback (f := d) (g := χ)
  have hcompPB : IsPullback ((uliftYoneda.{u + 1}).map (pullback.snd d χ))
      ((uliftYoneda.{u + 1}).map (pullback.fst d χ) ≫ (uliftYoneda.{u + 1}).map s)
      ((uliftYoneda.{u + 1}).map χ ≫ φ) g :=
    (hpb.map (uliftYoneda.{u + 1})).flip.paste_vert
      (by rw [hrep.map_fst' g]; exact hrep.isPullback g)
  let _ : Surjective (q.map (pullback.fst d χ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb.map q).flip
      (show Surjective (q.map χ) from inferInstance)
  let _ : Etale (q.map (pullback.fst d χ)) :=
    Etale.etale_isStableUnderBaseChange.of_isPullback (hpb.map q).flip
      (show Etale (q.map χ) from inferInstance)
  let _ : Etale (q.map (pullback.fst d χ) ≫ q.map s) := q.map_comp _ _ ▸
    hφ.property g ((uliftYoneda.{u + 1}).map (pullback.snd d χ)) (pullback.fst d χ ≫ s) hcompPB
  exact Stacks.Etale.etale_of_comp_surjective_etale (q.map (pullback.fst d χ)) (q.map s)

/-- Étaleness of a scheme-valued point of an fppf sheaf descends along a surjective étale
morphism of the site: this is Stacks 02KM applied after base change. -/
public alias relative_etale_of_comp_surjective_etale' := relative_etale_of_comp_surjective_etale

/-- Étaleness of a morphism of fppf sheaves may be checked after base change to a surjective
étale chart of its target. -/
private theorem isEtaleULift_of_targetChart
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hG : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G)
    (f : F ⟶ G) (V : BigFppfOver B S hS) (q : (uliftYoneda.{u + 1}).obj V ⟶ G)
    (hqS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) q)
    (hqE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) q)
    (hpb : Space.IsEtaleULift.{u + 1} B S hS (pullback.fst q f)) :
    Space.IsEtaleULift.{u + 1} B S hS f := by
  let Tsch := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tsch
  let PP := P.relative (uliftYoneda.{u + 1})
  let Q := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) Tsch
  let QQ := Q.relative (uliftYoneda.{u + 1})
  let _ : PP.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange P
  let _ : QQ.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  let _ : PP.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition P
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  intro U φ hφ
  have hpb' : IsPullback (pullback.fst q f) (pullback.snd q f) q f :=
    IsPullback.of_hasPullback q f
  have hfst : PP (pullback.snd q f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb' hqE
  have hfstSurj : QQ (pullback.snd q f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb' hqS
  have hχrep : (uliftYoneda.{u + 1}).relativelyRepresentable (pullback.snd q f) := hfst.1
  let χ := hχrep.snd φ
  let η := hχrep.fst φ
  have hW : IsPullback η ((uliftYoneda.{u + 1}).map χ) (pullback.snd q f) φ :=
    hχrep.isPullback φ
  have _ : Surjective (Tsch.map χ) := hfstSurj.2 φ η χ hW
  have _ : Etale (Tsch.map χ) := hfst.2 φ η χ hW
  have hηg : PP (η ≫ pullback.fst q f) :=
    hpb _ η (MorphismProperty.IsStableUnderBaseChange.of_isPullback hW.flip hφ)
  have hdesc : PP ((uliftYoneda.{u + 1}).map χ ≫ (φ ≫ f)) := by
    rw [← Category.assoc, ← hW.w, Category.assoc, ← pullback.condition, ← Category.assoc]
    exact MorphismProperty.comp_mem PP _ q hηg hqE
  exact relative_etale_of_comp_surjective_etale B S hS χ (φ ≫ f)
    ((Functor.relativelyRepresentable.diag_iff).1 hG.diagonal_representable (φ ≫ f)) hdesc

/-- Étaleness of the base change along a composite follows from étaleness of the base changes
along its two factors, the target of the second being an algebraic space. -/
private theorem isEtaleULift_pullback_fst_comp_aux
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {gg : F ⟶ G} {ff : G ⟶ H}
    (hrepF : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ff)
    (hetF : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ H),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ ff))
    (het : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ gg))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ H) :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (gg ≫ ff)) := by
  have hT : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ ff) := hrepF U ξ
  obtain ⟨V, q, hqS, hqE⟩ := hT.exists_atlas
  let π : pullback ξ (gg ≫ ff) ⟶ pullback ξ ff :=
    pullback.lift (pullback.fst ξ (gg ≫ ff)) (pullback.snd ξ (gg ≫ ff) ≫ gg) (by
      simpa only [Category.assoc] using
        (pullback.condition : pullback.fst ξ (gg ≫ ff) ≫ ξ =
          pullback.snd ξ (gg ≫ ff) ≫ (gg ≫ ff)))
  have hπ₁ : π ≫ pullback.fst ξ ff = pullback.fst ξ (gg ≫ ff) := pullback.lift_fst _ _ _
  have hAlpha := isPullback_intermediate_baseChange ξ ff gg q π hπ₁ (pullback.lift_snd _ _ _)
  have hpb : Space.IsEtaleULift.{u + 1} B S hS (pullback.fst q π) := by
    have hpre := isEtaleULift_precomp_iso B S hS hAlpha.isoPullback
      (pullback.fst (q ≫ pullback.snd ξ ff) gg) (het V (q ≫ pullback.snd ξ ff))
    rwa [hAlpha.isoPullback_hom_fst] at hpre
  have hcomp := isEtaleULift_comp B S hS
    (isEtaleULift_of_targetChart B S hS hT π V q hqS hqE hpb) (hetF U ξ)
  rwa [hπ₁] at hcomp

/-- **Stacks 0AJ1.** A jointly surjective family of representable étale maps from formal
algebraic spaces makes its target a formal algebraic space, provided the target satisfies the
set-theoretic condition of Stacks 0AIS. -/
@[stacks 0AJ1]
theorem isFormalAlgebraicSpace_of_etaleCover {I : Type (u + 1)}
    (X : FppfSheaf B S hS) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsFormalAlgebraicSpace B S hS (Xi i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    (hXset : SatisfiesSetTheoreticCondition B S hS X) :
    IsFormalAlgebraicSpace B S hS X := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨hXset, ?_⟩
  choose J Y g hY hg hcov using fun i ↦ (hXi i).2
  refine ⟨Σ i, J i, fun p ↦ Y p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1, fun p ↦ hY p.1 p.2,
    fun p ↦ ?_, ?_⟩
  · obtain ⟨hrep, het⟩ := hg p.1 p.2
    obtain ⟨hrepF, hetF⟩ := hf p.1
    refine ⟨Space.isRepresentableByAlgebraicSpacesULift_comp B S hS
      (g p.1 p.2).hom (f p.1).hom hrep hrepF, ?_⟩
    exact isEtaleULift_pullback_fst_comp_aux B S hS hrepF hetF het
  · let q (i : I) : (∐ (fun j ↦ Y i j)) ⟶ Xi i := Sigma.desc (g i)
    let e : (∐ (fun p : (Σ i, J i) ↦ Y p.1 p.2)) ⟶ (∐ Xi) :=
      Sigma.desc (fun p ↦ g p.1 p.2 ≫ Sigma.ι Xi p.1)
    have _ (i : I) : Epi (q i) := (Sheaf.isLocallySurjective_iff_epi (q i)).mp (hcov i)
    have he : Epi e := ⟨fun k l hkl ↦ Sigma.hom_ext _ _ fun i ↦ (cancel_epi (q i)).1 <|
      Sigma.hom_ext _ _ fun j ↦ by
        simpa [e, q] using congrArg (Sigma.ι (fun p : Σ i, J i ↦ Y p.1 p.2) ⟨i, j⟩ ≫ ·) hkl⟩
    have hcomp : e ≫ Sigma.desc f = Sigma.desc (fun p : Σ i, J i ↦ g p.1 p.2 ≫ f p.1) :=
      Sigma.hom_ext _ _ fun p ↦ by simp [e]
    have _ : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).mp hsurj
    rw [← hcomp]
    exact (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance

/-- Étaleness of a morphism of fppf sheaves is stable under base change: the base change of an
étale morphism representable by algebraic spaces along any morphism is again étale. -/
theorem isEtaleULift_pullback_fst_of_isPullback
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {p : H ⟶ F} {a' : H ⟶ G'} {a : F ⟶ G} {g : G' ⟶ G} (hsq : IsPullback p a' a g)
    (het : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ a))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G') :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ a') := by
  have hcomp : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ p) (ξ ≫ g) a :=
    (IsPullback.of_hasPullback ξ a').paste_vert hsq.flip
  have hpre := isEtaleULift_precomp_iso B S hS hcomp.isoPullback
    (pullback.fst (ξ ≫ g) a) (het U (ξ ≫ g))
  rwa [hcomp.isoPullback_hom_fst] at hpre

/-- Étaleness of a morphism of fppf sheaves representable by algebraic spaces is stable under
composition: this is the step which, in the proof of Stacks 0AJ1, assembles the atlas of the
target out of the atlases of the members of the covering family. -/
theorem isEtaleULift_pullback_fst_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {gg : F ⟶ G} {ff : G ⟶ H}
    (hrepF : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS ff)
    (hetF : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ H),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ ff))
    (het : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ gg))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ H) :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (gg ≫ ff)) :=
  isEtaleULift_pullback_fst_comp_aux B S hS hrepF hetF het U ξ

end AlgebraicGeometry.FormalSpace

end
