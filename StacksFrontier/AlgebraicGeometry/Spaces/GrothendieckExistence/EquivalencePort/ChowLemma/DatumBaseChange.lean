module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Datum
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback

namespace CategoryTheory.Limits.IsPullback.C1573
end CategoryTheory.Limits.IsPullback.C1573
namespace CategoryTheory.Limits.C1573
end CategoryTheory.Limits.C1573
namespace AlgebraicGeometry.Space.C1573.ChowDatum
end AlgebraicGeometry.Space.C1573.ChowDatum

/-!
# Base change of a Chow datum along an affine morphism

Let `Y ⟶ Y₀` be an affine morphism and `X = X₀ ×_{Y₀} Y`. A Chow datum for `X₀ ⟶ Y₀` base
changes to one for `X ⟶ Y`, provided that the inverse images in `X` of dense opens of `X₀` are
dense. This is the step of the proof of Stacks 088U which passes from a stage `X_i ⟶ Y_i` of a
Noetherian approximation to `X ⟶ Y` itself.

## Main results

* `CategoryTheory.Limits.IsPullback.C1573.of_baseChange`: base change commutes with fibre products.
* `AlgebraicGeometry.Space.C1573.ChowDatum.baseChange`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace CategoryTheory.Limits

open _root_.CategoryTheory.Limits.C1573 _root_.AlgebraicGeometry.C1573
/-- **Base change commutes with fibre products.** Let `p : X ⟶ X₀` and let `P₀ = B₀ ×_{X₀} C₀`.
If `B`, `C` and `P` are the base changes of `B₀`, `C₀` and `P₀` along `p`, then `P = B ×_X C`. -/
theorem IsPullback.C1573.of_baseChange {C' : Type*} [Category C'] {X X₀ B₀ C₀ P₀ B C P : C'}
    {p : X ⟶ X₀} {β₀ : B₀ ⟶ X₀} {γ₀ : C₀ ⟶ X₀} {a₀ : P₀ ⟶ B₀} {c₀ : P₀ ⟶ C₀}
    (h₀ : IsPullback a₀ c₀ β₀ γ₀)
    {β : B ⟶ X} {pB : B ⟶ B₀} (hB : IsPullback β pB p β₀)
    {γ : C ⟶ X} {pC : C ⟶ C₀} (hC : IsPullback γ pC p γ₀)
    {π : P ⟶ X} {pP : P ⟶ P₀} (hP : IsPullback π pP p (a₀ ≫ β₀))
    {a : P ⟶ B} {c : P ⟶ C} (ha : a ≫ pB = pP ≫ a₀) (ha' : a ≫ β = π)
    (hc : c ≫ pC = pP ≫ c₀) (hc' : c ≫ γ = π) :
    IsPullback a c β γ := by
  have left : IsPullback a pP pB a₀ := by
    refine IsPullback.of_right ?_ ha hB
    rw [ha']
    exact hP
  have outer := left.paste_vert h₀
  refine IsPullback.of_bot ?_ (by rw [ha', hc']) hC
  rw [hc, hB.w]
  exact outer

/-- **A product with a fixed object, over a terminal object, is a base change of the first
factor.** -/
theorem C1573.isPullback_pullbackMap_terminal_left {C' : Type*} [Category C'] [HasPullbacks C']
    {T A A' Q : C'} (hT : IsTerminal T) (g : A ⟶ A') :
    IsPullback (pullback.fst (hT.from A) (hT.from Q))
      (pullback.map (hT.from A) (hT.from Q) (hT.from A') (hT.from Q) g (𝟙 Q) (𝟙 T)
        (hT.hom_ext _ _) (hT.hom_ext _ _)) g (pullback.fst (hT.from A') (hT.from Q)) := by
  refine (IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (hT.from A') (hT.from Q)).flip).flip
  rw [pullback.lift_snd, Category.comp_id,
    show g ≫ hT.from A' = hT.from A from hT.hom_ext _ _]
  exact (IsPullback.of_hasPullback (hT.from A) (hT.from Q)).flip

/-- **A fibre product over a base, changed along the first factor, is a base change.** -/
theorem C1573.isPullback_pullbackMap_left {C' : Type*} [Category C'] [HasPullbacks C']
    {V V₀ Z T : C'} (g : V ⟶ V₀) (pV₀ : V₀ ⟶ T) (pZ : Z ⟶ T) (pV : V ⟶ T)
    (hg : pV = g ≫ pV₀) :
    IsPullback (pullback.fst pV pZ)
      (pullback.map pV pZ pV₀ pZ g (𝟙 Z) (𝟙 T) (by simp [hg]) (by simp)) g
      (pullback.fst pV₀ pZ) := by
  subst hg
  refine (IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback pV₀ pZ).flip).flip
  rw [pullback.lift_snd, Category.comp_id]
  exact (IsPullback.of_hasPullback (g ≫ pV₀) pZ).flip

/-- A square over the base change `pullback.map` of a fibre product, given by a lift into it. -/
private theorem isPullback_lift_pullbackMap {C' : Type*} [Category C'] [HasPullbacks C']
    {V V₀ Z T E E₀ : C'} (g : V ⟶ V₀) (pV₀ : V₀ ⟶ T) (pZ : Z ⟶ T) (pV : V ⟶ T)
    (hg : pV = g ≫ pV₀) (e : E ⟶ E₀) (c₀ : E₀ ⟶ pullback pV₀ pZ) (a : E ⟶ V)
    (h : a ≫ pV = (e ≫ c₀ ≫ pullback.snd _ _) ≫ pZ)
    (hsq : IsPullback a e g (c₀ ≫ pullback.fst _ _)) :
    IsPullback (pullback.lift a (e ≫ c₀ ≫ pullback.snd _ _) h) e
      (pullback.map pV pZ pV₀ pZ g (𝟙 Z) (𝟙 T) (by simp [hg]) (by simp)) c₀ := by
  subst hg
  refine IsPullback.of_right ?_ ?_ (C1573.isPullback_pullbackMap_left g pV₀ pZ _ rfl)
  · rw [pullback.lift_fst]
    exact hsq
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.map_fst, pullback.lift_fst_assoc] using hsq.w
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573 _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Base change of a Chow datum along an affine morphism.** Let `X ⟶ X₀` be the base change of
an affine morphism `Y ⟶ Y₀` along `f₀ : X₀ ⟶ Y₀`, with `X` separated over an affine base and
locally Noetherian, and suppose that inverse images of dense opens of `X₀` are dense in `X`. A
Chow datum for `f₀` then base changes to a Chow datum for `f : X ⟶ Y`. -/
theorem C1573.ChowDatum.baseChange [IsAffine S] {X₀ X : AlgebraicSpaces B S hS}
    {Y₀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀.1 ⟶ Y₀} (d₀ : ChowDatum X₀ f₀)
    (f : X.1 ⟶ Y) (p : X.1 ⟶ X₀.1) (q : Y ⟶ Y₀) (hpq : IsPullback p f f₀ q)
    (hp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p)
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X.1))
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdense : letI := pointTopology B S hS X₀.1; letI := pointTopology B S hS X.1
      ∀ O : Set (points B S hS X₀.1), IsOpen O → Dense O →
        Dense (pointsMap B S hS X.1 p ⁻¹' O)) :
    Nonempty (ChowDatum X f) := by
  letI := pointTopology B S hS X₀.1
  letI := pointTopology B S hS X.1
  have hrep : yoneda.relativelyRepresentable p := hp.rep
  have hbcE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcO : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  haveI := d₀.affV
  haveI := d₀.noethD
  haveI := d₀.compactT₀
  haveI := d₀.noethT₀
  -- the dense open
  set D := hrep.pullback d₀.u with hDdef
  set u : yoneda.obj D ⟶ X.1 := hrep.fst d₀.u with hudef
  set vD : D ⟶ d₀.D := hrep.snd d₀.u with hvD
  have hD : IsPullback u (yoneda.map vD) p d₀.u := hrep.isPullback d₀.u
  have hu : IsOpenImmersion B S hS u := hbcO.of_isPullback hD.flip d₀.hu
  have hvDa : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map vD) :=
    hp.property_snd d₀.u
  have hudense : DenseRange (pointsMap B S hS (yoneda.obj D) u) := by
    letI := pointTopology B S hS (yoneda.obj d₀.D)
    have hopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj d₀.D) d₀.u)) :=
      (isOpenMap_pointsMap_of_presheafEtale B S hS d₀.u
        (presheaf_etale_of_isOpenImmersion B S hS d₀.hu)).isOpen_range
    have heq : Set.range (pointsMap B S hS (yoneda.obj D) u) =
        pointsMap B S hS X.1 p ⁻¹' Set.range (pointsMap B S hS (yoneda.obj d₀.D) d₀.u) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨pointsMap B S hS _ (yoneda.map vD) y, ?_⟩
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hD.w]
      · rintro ⟨y, hy⟩
        obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hD x y hy.symm
        exact ⟨w, hw⟩
    change Dense _
    rw [heq]
    exact hdense _ hopen d₀.hdense
  -- the atlas
  set V := hrep.pullback d₀.φ with hVdef
  set φ : yoneda.obj V ⟶ X.1 := hrep.fst d₀.φ with hφdef
  set vV : V ⟶ d₀.V := hrep.snd d₀.φ with hvV
  have hV : IsPullback φ (yoneda.map vV) p d₀.φ := hrep.isPullback d₀.φ
  have hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ :=
    hbcS.of_isPullback hV.flip d₀.hs
  have he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ :=
    hbcE.of_isPullback hV.flip d₀.he
  have hvVa : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map vV) :=
    hp.property_snd d₀.φ
  haveI affV : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map vV)
  have affR : IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)) := by
    have hw : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ≫
        B.inclusion.map V.hom = (BigFppfOver.toScheme B S hS).map
          (atlasRelationSource B S hS hs) ≫ B.inclusion.map V.hom := by
      change B.inclusion.map (atlasRelationTarget B S hS hs).left ≫ _ =
        B.inclusion.map (atlasRelationSource B S hS hs).left ≫ _
      rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w, Over.w]
    haveI : IsAffine (B.inclusion.obj V.left) := affV
    haveI : IsAffine (B.inclusion.obj (B.obj hS)) := inferInstanceAs (IsAffine S)
    have := isClosedImmersion_toScheme_lift_of_isSeparated X _ hXsep φ φ _ _
      (isPullback_yoneda_map_atlasRelation B S hS hs) hw
    exact isAffine_of_isAffineHom (pullback.lift _ _ hw)
  have noethV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_etaleChart B S hS X.1 X.2 hXN V φ he
  -- the scheme `T` over `X`
  set T := hrep.pullback d₀.τ with hTdef
  set τ : yoneda.obj T ⟶ X.1 := hrep.fst d₀.τ with hτdef
  set vT : T ⟶ d₀.T₀ := hrep.snd d₀.τ with hvT
  have hT : IsPullback τ (yoneda.map vT) p d₀.τ := hrep.isPullback d₀.τ
  have hvTa : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map vT) :=
    hp.property_snd d₀.τ
  -- the chart `TV`
  set TV := hrep.pullback (yoneda.map d₀.tV ≫ d₀.φ) with hTVdef
  set τV : yoneda.obj TV ⟶ X.1 := hrep.fst (yoneda.map d₀.tV ≫ d₀.φ) with hτV
  set vTV : TV ⟶ d₀.TV := hrep.snd (yoneda.map d₀.tV ≫ d₀.φ) with hvTV
  have hTV0 : IsPullback τV (yoneda.map vTV) p (yoneda.map d₀.tV ≫ d₀.φ) :=
    hrep.isPullback _
  have hTV0' : IsPullback τV (yoneda.map vTV) p (yoneda.map d₀.pT ≫ d₀.τ) := by
    rw [d₀.hsq.w]; exact hTV0
  set pT : TV ⟶ T := yoneda.preimage (hT.lift τV (yoneda.map (vTV ≫ d₀.pT)) (by
    rw [hTV0'.w, yoneda.map_comp, Category.assoc])) with hpTdef
  set tV : TV ⟶ V := yoneda.preimage (hV.lift τV (yoneda.map (vTV ≫ d₀.tV)) (by
    rw [hTV0.w, yoneda.map_comp, Category.assoc])) with htVdef
  have hpT1 : yoneda.map pT ≫ τ = τV := by rw [hpTdef, Functor.map_preimage, hT.lift_fst]
  have hpT2 : yoneda.map pT ≫ yoneda.map vT = yoneda.map vTV ≫ yoneda.map d₀.pT := by
    rw [hpTdef, Functor.map_preimage, hT.lift_snd, yoneda.map_comp]
  have htV1 : yoneda.map tV ≫ φ = τV := by rw [htVdef, Functor.map_preimage, hV.lift_fst]
  have htV2 : yoneda.map tV ≫ yoneda.map vV = yoneda.map vTV ≫ yoneda.map d₀.tV := by
    rw [htVdef, Functor.map_preimage, hV.lift_snd, yoneda.map_comp]
  have hsq : IsPullback (yoneda.map pT) (yoneda.map tV) τ φ :=
    IsPullback.C1573.of_baseChange d₀.hsq hT hV hTV0' hpT2 hpT1 htV2 htV1
  -- `TV = TV₀ ×_{V₀} V`
  have hTVV : IsPullback (yoneda.map tV) (yoneda.map vTV) (yoneda.map vV) (yoneda.map d₀.tV) := by
    refine IsPullback.of_right ?_ htV2 hV
    rw [htV1]
    exact hTV0
  have hTVVs : IsPullback tV vTV vV d₀.tV := IsPullback.of_map_of_faithful yoneda hTVV
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hTVVsch := hTVVs.map (BigFppfOver.toScheme B S hS)
  -- local Noetherianity of the charts
  have hZ₂lft : LocallyOfFiniteType (B.inclusion.map d₀.Z₂.hom) := by
    haveI := d₀.hiC
    have := isProper_projectiveSpaceOver d₀.m S
    rw [← d₀.hi]
    infer_instance
  have htV₀lft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d₀.tV) := by
    haveI := d₀.hcC
    rw [← d₀.hc1]
    infer_instance
  have htVlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map tV) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hTVVsch.flip htV₀lft
  have noethTV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj TV) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map tV)
  have hpTs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map pT) := hbcS.of_isPullback hsq.flip hs
  have hpTe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (yoneda.map pT) := hbcE.of_isPullback hsq.flip he
  have noethT : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T) :=
    isLocallyNoetherian_of_etaleChart B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      ⟨TV, yoneda.map pT, hpTs, hpTe, noethTV⟩ T (yoneda.map (𝟙 T))
      (presheaf_yoneda_map_id_etale B S hS T)
  haveI : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj d₀.T₀) := {}
  have compactT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    (quasiCompact_iff_compactSpace ((BigFppfOver.toScheme B S hS).map vT)).1 inferInstance
  haveI : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj d₀.D) :=
    d₀.noethD
  have noethD : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj D) :=
    { toIsLocallyNoetherian := isLocallyNoetherian_of_etaleChart B S hS X.1 X.2 hXN D u
        (presheaf_etale_of_isOpenImmersion B S hS hu),
      toCompactSpace :=
        (quasiCompact_iff_compactSpace ((BigFppfOver.toScheme B S hS).map vD)).1 inferInstance }
  -- the section over the dense open
  set σ : D ⟶ T := yoneda.preimage (hT.lift u (yoneda.map (vD ≫ d₀.σ)) (by
    rw [hD.w, yoneda.map_comp, Category.assoc, d₀.hσ.w, Category.id_comp])) with hσdef
  have hσ1 : yoneda.map σ ≫ τ = u := by rw [hσdef, Functor.map_preimage, hT.lift_fst]
  have hσ2 : yoneda.map σ ≫ yoneda.map vT = yoneda.map vD ≫ yoneda.map d₀.σ := by
    rw [hσdef, Functor.map_preimage, hT.lift_snd, yoneda.map_comp]
  have hσ : IsPullback (yoneda.map σ) (𝟙 _) τ u := by
    refine IsPullback.C1573.of_baseChange d₀.hσ hT hD ?_ hσ2 hσ1 (by simp) (Category.id_comp _)
    rw [d₀.hσ.w, Category.id_comp]
    exact hD
  -- the closed immersion of the chart into `V ×_S Z₂`
  have hpT' : pT ≫ vT = vTV ≫ d₀.pT := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hpT2]
  have hVw : B.inclusion.map V.hom =
      (BigFppfOver.toScheme B S hS).map vV ≫ B.inclusion.map d₀.V.hom := by
    change _ = B.inclusion.map vV.left ≫ _
    rw [← B.inclusion.map_comp, Over.w vV]
  have hcw : (BigFppfOver.toScheme B S hS).map tV ≫ B.inclusion.map V.hom =
      ((BigFppfOver.toScheme B S hS).map vTV ≫ d₀.cS ≫ pullback.snd _ _) ≫
        B.inclusion.map d₀.Z₂.hom := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% d₀.hc1, hVw]
    exact (reassoc_of% hTVVsch.w) _
  set cS : (BigFppfOver.toScheme B S hS).obj TV ⟶
      pullback (B.inclusion.map V.hom) (B.inclusion.map d₀.Z₂.hom) :=
    pullback.lift _ _ hcw with hcSdef
  set mVZ := pullback.map (B.inclusion.map V.hom) (B.inclusion.map d₀.Z₂.hom)
    (B.inclusion.map d₀.V.hom) (B.inclusion.map d₀.Z₂.hom) ((BigFppfOver.toScheme B S hS).map vV)
    (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hVw]) (by simp) with hmVZ
  have hcsq : IsPullback cS ((BigFppfOver.toScheme B S hS).map vTV) mVZ d₀.cS := by
    refine isPullback_lift_pullbackMap _ _ _ _ hVw _ _ _ _ ?_
    rw [d₀.hc1]
    exact hTVVsch
  haveI := d₀.hcC
  have hcC : _root_.AlgebraicGeometry.IsClosedImmersion cS :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
      hcsq.flip inferInstance
  have hc1 : cS ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV := pullback.lift_fst _ _ _
  have hc2 : cS ≫ pullback.snd _ _ = (BigFppfOver.toScheme B S hS).map (pT ≫ (vT ≫ d₀.o)) := by
    rw [pullback.lift_snd, d₀.hc2, ← Category.assoc pT, hpT']
    simp only [Functor.map_comp, Category.assoc]
  -- the ample module
  haveI := d₀.hMi
  have hM := Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom
    ((BigFppfOver.toScheme B S hS).map vT) d₀.M d₀.hM
  -- the immersion into projective space over `Y`
  set tS := isTerminal_yoneda_obj_base B S hS
  set jT : yoneda.obj T ⟶ projectiveSpacePresheaf B S hS Y d₀.k :=
    pullback.lift (τ ≫ f) (yoneda.map vT ≫ d₀.jT ≫ pullback.snd _ _) (tS.hom_ext _ _) with hjTdef
  set mP := pullback.map (tS.from Y) (tS.from (yoneda.obj (projectiveSpaceSiteObject B S hS d₀.k)))
    (tS.from Y₀) (tS.from (yoneda.obj (projectiveSpaceSiteObject B S hS d₀.k))) q (𝟙 _) (𝟙 _)
    (tS.hom_ext _ _) (tS.hom_ext _ _) with hmP
  have hjTsq : IsPullback jT (yoneda.map vT) mP d₀.jT := by
    refine isPullback_lift_pullbackMap q _ _ _ (tS.hom_ext _ _) _ _ _ _ ?_
    rw [d₀.hjTf]
    exact hT.paste_horiz hpq.flip
  have hjT : IsImmersion B S hS jT := isImmersion_of_isPullback' hjTsq.flip d₀.hjT
  exact ⟨⟨D, V, T, TV, d₀.Z₂, u, hu, hudense, φ, hs, he, affV, affR, noethV, noethT, noethTV,
    noethD, compactT, τ, σ, hσ, pT, tV, hsq, vT ≫ d₀.o, d₀.m, d₀.i, d₀.hiC, d₀.hi, cS, hcC, hc1,
    hc2, _, inferInstance, hM, d₀.k, jT, hjT, pullback.lift_fst _ _ _⟩⟩

end AlgebraicGeometry.Space

end
