module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSitePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.SmallAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.CategoryTheory.Adjunction.LimitPostCoreflective

/-!
# Enlarging the big fppf site commutes with limits of affine systems

Let `B ⊆ B'` be big fppf sites (`AlgebraicGeometry.IsContained`) and let `D` be a cofiltered
inverse system of algebraic spaces over `S` in `B` with affine transition morphisms, satisfying the
chapter's standing convention of Section 70.2 (tag 07SD) in `B`
(`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limit of the base changes of the
stages along an affine scheme-valued point lies in `B`), and suppose one stage is quasi-compact.
Nothing is asked of the size of the index category in `B`. If in `B'` the index category is smaller
than the cofinality of `cutoff B'`, then the inverse image along the inclusion of sites (Stacks
04W1, `AlgebraicGeometry.changeBigSite`) carries every limit of `D` to a limit of the transported
system.

## Main definitions

* `AlgebraicGeometry.Space.changeBigSiteSystem`: the transported inverse system.
* `AlgebraicGeometry.Space.isLimitChangeBigSiteMapCone`: the change of big site preserves the limit
  of the system.

## Main results

* `AlgebraicGeometry.Space.AffineChartSystem.map_comp_stageMap`,
  `AlgebraicGeometry.Space.AffineChartSystem.map_comp_baseMap`: the projections of a chart system
  are natural.
* `AlgebraicGeometry.Space.exists_changeBigSite_iso_limit`: the limit of the transported system
  descends to the smaller site.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace AffineChartSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {I : Type u} [Category.{u} I]
  {i₀ : I} {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  (C : AffineChartSystem B S hS i₀ D U₀ f₀)

/-- Transporting a chart transition morphism across the chart isomorphism, followed by any
morphism out of the base change. -/
private theorem yoneda_map_siteDiagram_map_comp_iso_hom_app_comp {k l : Over i₀} (g : k ⟶ l)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).obj l ⟶ Z) :
    yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app l ≫ p =
      C.iso.hom.app k ≫ (stageBaseChangeDiagram B S hS i₀ D U₀ f₀).map g ≫ p := by
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ p) (C.iso.hom.naturality g)

/-- The projections of the charts to their stages are natural in the stage. -/
theorem map_comp_stageMap {k l : Over i₀} (g : k ⟶ l) :
    yoneda.map (C.siteDiagram.map g) ≫ C.stageMap l = C.stageMap k ≫ D.map g.left := by
  refine (C.yoneda_map_siteDiagram_map_comp_iso_hom_app_comp g _).trans ?_
  rw [stageBaseChangeDiagram_map_comp_fst, ← Category.assoc]
  rfl

/-- The projections of the charts to the chosen affine point are compatible with the transition
morphisms of the charts. -/
theorem map_comp_baseMap {k l : Over i₀} (g : k ⟶ l) :
    yoneda.map (C.siteDiagram.map g) ≫ C.baseMap l = C.baseMap k := by
  refine (C.yoneda_map_siteDiagram_map_comp_iso_hom_app_comp g _).trans ?_
  rw [stageBaseChangeDiagram_map_comp_snd]
  rfl

end AffineChartSystem

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ AlgebraicSpaces B S hS)

/-- The image of an inverse system of algebraic spaces under the change of big site, as an inverse
system of presheaves on the larger site. -/
noncomputable abbrev changeBigSiteSystem :
    I ⥤ (BigFppfOver B' S (largerContains h hS))ᵒᵖ ⥤ Type u :=
  D ⋙ changeBigSite B B' h S hS ⋙ ObjectProperty.ι _

/-- The limit of the transported system descends to the smaller site: it is isomorphic to the image
under the change of big site of an algebraic space over `S` in `B`. -/
theorem exists_changeBigSite_iso_limit (hSize' : #I < B'.cutoff.ord.cof)
    (hHomSize' : ∀ i j : I, #(i ⟶ j) < B'.cutoff.ord.cof)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f).hom)
    (hconv : SiteContainsBaseChangeLimits B S hS (D ⋙ ObjectProperty.ι _)) (i₀ : I)
    (hqc : IsQuasiCompactSpace B S hS (D.obj i₀).obj) :
    ∃ X : AlgebraicSpaces B S hS, Nonempty ((changeBigSite B B' h S hS).obj X ≅
      ⟨limit (changeBigSiteSystem B B' h S hS D),
        isAlgebraicSpace_limit B' S (largerContains h hS) _ hSize' hHomSize'
          (fun i ↦ ((changeBigSite B B' h S hS).obj (D.obj i)).property)
          (fun f ↦ isAffineHom_changeBigSite_map B B' h S hS _ (D.map f) (hAffine f))⟩) := by
  set hS' : B'.Contains S := largerContains h hS
  set D' := changeBigSiteSystem B B' h S hS D
  have hlimD' : HasLimit D' := inferInstance
  have hD' : ∀ i, IsAlgebraicSpace B' S hS' (D'.obj i) :=
    fun i ↦ ((changeBigSite B B' h S hS).obj (D.obj i)).property
  have hAffine' : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B' S hS' (D'.map f) :=
    fun f ↦ isAffineHom_changeBigSite_map B B' h S hS _ (D.map f) (hAffine f)
  have hL' : IsAlgebraicSpace B' S hS' (limit D') :=
    isAlgebraicSpace_limit B' S hS' D' hSize' hHomSize' hD' hAffine'
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
      (D.obj i₀).property).mp hqc
  have hq₀E' : IsEtaleChart B S hS (D.obj i₀).obj (CostructuredArrow.mk q₀) :=
    (isEtale_iff_presheaf_of_yoneda B S hS q₀).mp hq₀E
  let ch := changeBigSiteChart B B' h S hS (D.obj i₀) (CostructuredArrow.mk q₀)
  let U₀' : BigAffineFppf B' S hS' := ⟨(inclusionOver h S hS).obj U₀, hU₀⟩
  let f₀' : yoneda.obj ((BigAffineFppf.inclusion B' S hS').obj U₀') ⟶ D'.obj i₀ := ch.hom
  have hf₀'E : IsEtaleChart B' S hS' (D'.obj i₀) ch :=
    isEtaleChart_changeBigSiteChart B B' h S hS (D.obj i₀) hq₀E'
  let C' := affineChartSystem B' S hS' i₀ D' U₀' f₀' hAffine'
  let L := C'.limitBridge hSize' hHomSize'
  let C := affineChartSystem B S hS i₀ (D ⋙ ObjectProperty.ι _) ⟨U₀, hU₀⟩ q₀ (fun f => hAffine f)
  have hC : BigFppfOver.LimitInSite C.siteDiagram :=
    C.limitInSite_of_siteContainsBaseChangeLimits hconv
  obtain ⟨r, hr⟩ : ∃ r : ∀ k : Over i₀, C.siteDiagram.obj k ⟶ U₀,
      ∀ k, yoneda.map (r k) = C.baseMap k :=
    ⟨fun k => Yoneda.fullyFaithful.preimage (C.baseMap k),
      fun k => Yoneda.fullyFaithful.map_preimage _⟩
  have h1 : ∀ k : Over i₀, IsPullback
      (changeBigSiteChart B B' h S hS (D.obj k.left) (CostructuredArrow.mk (C.stageMap k))).hom
      (yoneda.map ((inclusionOver h S hS).map (r k))) (D'.map k.hom) f₀' := fun k =>
    isPullback_changeBigSiteChart B B' h S hS (D.map k.hom) _ _ q₀
      (by rw [hr]; exact C.isPullback k)
  obtain ⟨e, he₁, he₂⟩ : ∃ e : ∀ k : Over i₀,
      C'.siteDiagram.obj k ≅ (inclusionOver h S hS).obj (C.siteDiagram.obj k),
      (∀ k, yoneda.map (e k).hom ≫
        (changeBigSiteChart B B' h S hS (D.obj k.left) (CostructuredArrow.mk (C.stageMap k))).hom =
          C'.stageMap k) ∧
      (∀ k, yoneda.map (e k).hom ≫ yoneda.map ((inclusionOver h S hS).map (r k)) =
        C'.baseMap k) :=
    ⟨fun k => Yoneda.fullyFaithful.preimageIso ((C'.isPullback k).isoIsPullback _ _ (h1 k)),
      fun k => (congrArg (· ≫ _) (Yoneda.fullyFaithful.map_preimage
        ((C'.isPullback k).isoIsPullback _ _ (h1 k)).hom)).trans
          (IsPullback.isoIsPullback_hom_fst _ _ _ _),
      fun k => (congrArg (· ≫ _) (Yoneda.fullyFaithful.map_preimage
        ((C'.isPullback k).isoIsPullback _ _ (h1 k)).hom)).trans
          (IsPullback.isoIsPullback_hom_snd _ _ _ _)⟩
  have hcm : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : BigFppfOver B S hS}
      (a : yoneda.obj T ⟶ X.obj),
      (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk a)).hom ≫
          ((changeBigSite B B' h S hS).map f).hom =
        (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk (a ≫ f.hom))).hom := by
    intro X Y f T a
    rw [changeBigSiteChart_hom, changeBigSiteChart_hom]
    refine (Category.assoc _ _ _).trans (congrArg (changeBigSiteYonedaHom B B' h S hS T ≫ ·) ?_)
    exact (congrArg (fun k => k.hom)
      ((changeBigSite B B' h S hS).map_comp
        (ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj T ⟶ X) f)).symm
  have hnat : ∀ {k l : Over i₀} (g : k ⟶ l), C'.siteDiagram.map g ≫ (e l).hom =
      (e k).hom ≫ (inclusionOver h S hS).map (C.siteDiagram.map g) := by
    intro k l g
    apply Yoneda.fullyFaithful.map_injective
    refine (yoneda.map_comp _ _).trans (Eq.trans ?_ (yoneda.map_comp _ _).symm)
    apply (h1 l).hom_ext
    · calc (yoneda.map (C'.siteDiagram.map g) ≫ yoneda.map (e l).hom) ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left)
              (CostructuredArrow.mk (C.stageMap l))).hom
          = yoneda.map (C'.siteDiagram.map g) ≫ (yoneda.map (e l).hom ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left)
              (CostructuredArrow.mk (C.stageMap l))).hom) := Category.assoc _ _ _
        _ = yoneda.map (C'.siteDiagram.map g) ≫ C'.stageMap l := congrArg _ (he₁ l)
        _ = C'.stageMap k ≫ D'.map g.left := AffineChartSystem.map_comp_stageMap C' g
        _ = (yoneda.map (e k).hom ≫
            (changeBigSiteChart B B' h S hS (D.obj k.left)
              (CostructuredArrow.mk (C.stageMap k))).hom) ≫
            ((changeBigSite B B' h S hS).map (D.map g.left)).hom :=
          congrArg (· ≫ _) (he₁ k).symm
        _ = yoneda.map (e k).hom ≫
            ((changeBigSiteChart B B' h S hS (D.obj k.left)
              (CostructuredArrow.mk (C.stageMap k))).hom ≫
            ((changeBigSite B B' h S hS).map (D.map g.left)).hom) := Category.assoc _ _ _
        _ = yoneda.map (e k).hom ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left)
              (CostructuredArrow.mk (C.stageMap k ≫ (D.map g.left).hom))).hom :=
          congrArg _ (hcm (D.map g.left) (C.stageMap k))
        _ = yoneda.map (e k).hom ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left) (CostructuredArrow.mk
              (yoneda.map (C.siteDiagram.map g) ≫ C.stageMap l))).hom :=
          congrArg (fun a => yoneda.map (e k).hom ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left) (CostructuredArrow.mk a)).hom)
            (AffineChartSystem.map_comp_stageMap C g).symm
        _ = yoneda.map (e k).hom ≫
            (yoneda.map ((inclusionOver h S hS).map (C.siteDiagram.map g)) ≫
            (changeBigSiteChart B B' h S hS (D.obj l.left)
              (CostructuredArrow.mk (C.stageMap l))).hom) :=
          congrArg _ (changeBigSiteChart_w B B' h S hS (D.obj l.left)
            (CostructuredArrow.homMk
              (f := CostructuredArrow.mk (yoneda.map (C.siteDiagram.map g) ≫ C.stageMap l))
              (f' := CostructuredArrow.mk (C.stageMap l)) (C.siteDiagram.map g) rfl)).symm
        _ = _ := (Category.assoc _ _ _).symm
    · have hrg : C.siteDiagram.map g ≫ r l = r k := Yoneda.fullyFaithful.map_injective
        ((yoneda.map_comp _ _).trans ((congrArg (yoneda.map (C.siteDiagram.map g) ≫ ·) (hr l)).trans
          ((AffineChartSystem.map_comp_baseMap C g).trans (hr k).symm)))
      refine (Category.assoc _ _ _).trans ((congrArg _ (he₂ l)).trans
        ((AffineChartSystem.map_comp_baseMap C' g).trans ((he₂ k).symm.trans ?_)))
      simp only [← hrg]
      exact (congrArg _ ((congrArg yoneda.map ((inclusionOver h S hS).map_comp _ _)).trans
        (yoneda.map_comp _ _))).trans (Category.assoc _ _ _).symm
  let α : C'.schemeDiagram ≅ underlyingDiagram C.siteDiagram :=
    NatIso.ofComponents (fun k => (BigFppfOver.toScheme B' S hS').mapIso (e k)) (fun {k l} g =>
      ((BigFppfOver.toScheme B' S hS').map_comp _ _).symm.trans
        ((congrArg (BigFppfOver.toScheme B' S hS').map (hnat g)).trans
          ((BigFppfOver.toScheme B' S hS').map_comp _ _)))
  have hlim : IsLimit ((Cone.postcompose α.hom).obj
      ((BigFppfOver.toScheme B' S hS').mapCone L.cone)) :=
    (IsLimit.postcomposeHomEquiv α _).symm L.schemeIsLimit
  have hLsize : ((BigFppfOver.toScheme B' S hS').obj L.cone.pt).size < B.cutoff :=
    hC ((Cone.postcompose α.hom).obj ((BigFppfOver.toScheme B' S hS').mapCone L.cone)) hlim
  let U : BigFppfOver B S hS := Over.mk (Y := B.obj hLsize) (X := B.obj hS) ⟨L.cone.pt.hom.hom⟩
  have hfE : IsEtaleChart B' S hS' (limit D') (CostructuredArrow.mk L.toLimit) :=
    presheaf_of_isPullback B' S hS' L.isPullback.flip hf₀'E
  have hfS : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B' S hS'))
      L.toLimit :=
    presheaf_of_isPullback B' S hS' L.isPullback.flip
      (presheaf_surjective_changeBigSiteChart B B' h S hS (D.obj i₀) hq₀S hq₀E')
  exact mem_essentialImage_changeBigSite_of_etale_surjective B B' h S hS ⟨limit D', hL'⟩ U
    L.toLimit hfS hfE

/-- Enlarging the big fppf site preserves the limit of an affine system satisfying the convention
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the image of a limit cone of `D` under the
change of big site is a limit cone. -/
noncomputable def isLimitChangeBigSiteMapCone (hSize' : #I < B'.cutoff.ord.cof)
    (hHomSize' : ∀ i j : I, #(i ⟶ j) < B'.cutoff.ord.cof)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f).hom)
    (hconv : SiteContainsBaseChangeLimits B S hS (D ⋙ ObjectProperty.ι _)) (i₀ : I)
    (hqc : IsQuasiCompactSpace B S hS (D.obj i₀).obj)
    (c : Cone D) (hc : IsLimit ((ObjectProperty.ι _).mapCone c)) :
    IsLimit ((ObjectProperty.ι _).mapCone ((changeBigSite B B' h S hS).mapCone c)) := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : i.IsCocontinuous J K := inclusionOver_isCocontinuous (τ := .fppf) B B' h S hS
  let : i.Full := inclusionOver_full h S hS
  let : i.Faithful := inclusionOver_faithful h S hS
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B) := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B') := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
    essentiallySmall_bigFppfOver B S hS
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B' S hS')) :=
    essentiallySmall_bigFppfOver B' S hS'
  let : ∀ F : (Over (base (τ := .fppf) B S hS))ᵒᵖ ⥤ Type u,
      i.op.HasPointwiseRightKanExtension F := by
    intro F Y
    let : HasLimitsOfShape (StructuredArrow Y i.op) (Type u) :=
      hasLimitsOfShape_of_essentiallySmall.{u} _ _
    change HasLimit (StructuredArrow.proj Y i.op ⋙ F)
    infer_instance
  have hpullff := Functor.full_and_faithful_sheafPullback i (Type u) J K
  let G := i.sheafPullback (Type u) J K
  let : G.Full := hpullff.1
  let : G.Faithful := hpullff.2
  let adj := i.sheafAdjunctionContinuous (Type u) J K
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf J (Type u) :=
    ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.property.isSheaf
  let Ds := D ⋙ toSheaf
  have hex := exists_changeBigSite_iso_limit B B' h S hS D hSize' hHomSize' hAffine hconv i₀ hqc
  let X := hex.choose
  let e := hex.choose_spec.some
  let e₁ := (ObjectProperty.ι (fun F => IsAlgebraicSpace B' S hS' F)).mapIso e
  let e₂ := (limit.isLimit (changeBigSiteSystem B B' h S hS D)).conePointUniqueUpToIso
    (isLimitOfPreserves (sheafToPresheaf K (Type u)) (limit.isLimit (Ds ⋙ G)))
  have hmem : G.essImage (limit (Ds ⋙ G)) :=
    ⟨toSheaf.obj X, ⟨(fullyFaithfulSheafToPresheaf K (Type u)).preimageIso (e₁ ≪≫ e₂)⟩⟩
  have : IsIso (limit.post Ds G) := adj.isIso_limit_post_of_mem_essImage Ds hmem
  have : PreservesLimit Ds G := preservesLimit_of_isIso_post G Ds
  exact isLimitOfPreserves (sheafToPresheaf K (Type u))
    (isLimitOfPreserves G (isLimitOfReflects (sheafToPresheaf J (Type u)) hc :
      IsLimit (toSheaf.mapCone c)))

end AlgebraicGeometry.Space

end
