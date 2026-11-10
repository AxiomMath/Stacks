module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeSeminormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationLocalization
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.GluedFactorization

/-!
# Initiality of the relative seminormalization factorization

The chart lifts into a competing subintegral factorization glue to a comparison morphism from the
glued relative seminormalization, which is unique. Hence the glued factorization is an initial
subintegral factorization (Stacks Project, Tag 0H3N, part (2)), and a chosen initial
factorization `AlgebraicGeometry.seminormalizationFactorization` is extracted from this.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

public noncomputable def relativeSeminormalization_competitorChartMapToF
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.AffineZariskiSite) :
    (relativeSeminormalizationGlueData f).functor.obj U ⟶ F.middle := by
  letI : IsIntegralHom F.toBase :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective
      F.toBase).mp F.universalHomeomorphism |>.1
  let W := F.toBase ⁻¹ᵁ U.1
  let hW : IsAffineOpen W := U.2.preimage F.toBase
  exact Scheme.Spec.map (CommRingCat.ofHom
      (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫
    hW.isoSpec.inv ≫ W.ι

/-- The base map of a subintegral factorization is integral. -/
private theorem isIntegralHom_toBase {Y X : Scheme.{u}} {f : Y ⟶ X}
    (F : SubintegralFactorization f) : IsIntegralHom F.toBase :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective
    F.toBase).mp F.universalHomeomorphism).1

/-- On an affine open `U`, `Spec` of `g.app U` is the restriction of `g` to `g ⁻¹ᵁ U`, up to the
affine charts. -/
private theorem spec_map_app_comp_isoSpec_inv {Y X : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Scheme.Spec.map (g.app U).op ≫ hU.isoSpec.inv =
      (hU.preimage g).isoSpec.inv ≫ (g ∣_ U) := by
  apply (cancel_mono hU.isoSpec.hom).1
  rw [Category.assoc, hU.isoSpec.inv_hom_id]
  have hn := Scheme.Opens.toSpecΓ_naturality g U
  change (g ⁻¹ᵁ U).toSpecΓ ≫ Scheme.Spec.map (g.app U).op = (g ∣_ U) ≫ U.toSpecΓ at hn
  calc
    Scheme.Spec.map (g.app U).op =
        (hU.preimage g).isoSpec.inv ≫ (g ⁻¹ᵁ U).toSpecΓ ≫ Scheme.Spec.map (g.app U).op := by
      rw [← (hU.preimage g).isoSpec_hom, Iso.inv_hom_id_assoc]
    _ = (hU.preimage g).isoSpec.inv ≫ (g ∣_ U) ≫ hU.isoSpec.hom := by
      rw [hn, ← hU.isoSpec_hom]

public theorem relativeSeminormalization_competitorChartMapToF_fromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.AffineZariskiSite) :
    affineSemiNormalizationFromSource f U.1 U.2 ≫
        relativeSeminormalization_competitorChartMapToF f F U =
      (f ⁻¹ᵁ U.1).ι ≫ F.toMiddle := by
  let Q := f ⁻¹ᵁ U.1
  let W := F.toBase ⁻¹ᵁ U.1
  have := isIntegralHom_toBase F
  let hW : IsAffineOpen W := U.2.preimage F.toBase
  let A := Γ(X, U.1)
  let B := Γ(Y, Q)
  let : Algebra A B := (f.app U.1).hom.toAlgebra
  let hdom := affineChart_app_isDominant f U.1 U.2
  have hpre : Q ≤ F.toMiddle ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, F.fac]
  let φ := (relativeSeminormalization_competitorChartMap f F U.1 U.2).hom
  let ℓ := relativeSeminormalization_competitorChartLift f F U.1 U.2
  have hring : CommRingCat.ofHom (((relativeSeminormalization Γ(X, U.1)
        Γ(Y, Q) hdom).val.toRingHom).comp ℓ) =
      CommRingCat.ofHom φ := by
    apply CommRingCat.hom_ext
    ext c
    exact relativeSeminormalization_competitorChartLift_val f F U.1 U.2 c
  change Q.toSpecΓ ≫ Scheme.Spec.map (CommRingCat.ofHom
      ((relativeSeminormalization Γ(X, U.1) Γ(Y, Q)
        hdom).val.toRingHom)).op ≫
      Scheme.Spec.map (CommRingCat.ofHom ℓ).op ≫ hW.isoSpec.inv ≫ W.ι = _
  have hnat := Scheme.Opens.toSpecΓ_SpecMap_appLE
    (f := F.toMiddle) (U := W) (V := Q) hpre
  change Q.toSpecΓ ≫ Scheme.Spec.map (CommRingCat.ofHom φ).op =
    F.toMiddle.resLE W Q hpre ≫ W.toSpecΓ at hnat
  have hspec : Scheme.Spec.map (CommRingCat.ofHom φ).op =
      Scheme.Spec.map (CommRingCat.ofHom
          ((relativeSeminormalization Γ(X, U.1) Γ(Y, Q)
            hdom).val.toRingHom)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom ℓ).op := by
    have hringCat : CommRingCat.ofHom ℓ ≫ CommRingCat.ofHom
        ((relativeSeminormalization Γ(X, U.1) Γ(Y, Q)
          hdom).val.toRingHom) = CommRingCat.ofHom φ := by
      rw [← CommRingCat.ofHom_comp]
      exact hring
    have hspecRaw := congrArg (fun q => Scheme.Spec.map q)
      (congrArg (fun q => q.op) hringCat)
    simpa [Q] using hspecRaw.symm
  have hmap : Scheme.Spec.map (CommRingCat.ofHom φ).op ≫ hW.isoSpec.inv ≫ W.ι =
      Scheme.Spec.map (CommRingCat.ofHom
          ((relativeSeminormalization Γ(X, U.1) Γ(Y, Q)
            hdom).val.toRingHom)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom ℓ).op ≫ hW.isoSpec.inv ≫ W.ι := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ hW.isoSpec.inv ≫ W.ι) hspec
  have hnat' : Q.toSpecΓ ≫ Scheme.Spec.map (CommRingCat.ofHom φ).op ≫
      hW.isoSpec.inv ≫ W.ι =
      F.toMiddle.resLE W Q hpre ≫ W.toSpecΓ ≫ hW.isoSpec.inv ≫ W.ι := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ hW.isoSpec.inv ≫ W.ι) hnat
  rw [← hmap, hnat']
  have hWid : W.toSpecΓ ≫ hW.isoSpec.inv = 𝟙 W.toScheme := by
    rw [← hW.isoSpec_hom]
    exact Iso.hom_inv_id hW.isoSpec
  calc
    F.toMiddle.resLE W Q hpre ≫ W.toSpecΓ ≫ hW.isoSpec.inv ≫ W.ι =
        F.toMiddle.resLE W Q hpre ≫
          ((W.toSpecΓ ≫ hW.isoSpec.inv) ≫ W.ι) :=
      congrArg (fun k => F.toMiddle.resLE W Q hpre ≫ k) (Category.assoc _ _ _).symm
    _ = (F.toMiddle.resLE W Q hpre ≫ (W.toSpecΓ ≫ hW.isoSpec.inv)) ≫ W.ι :=
      (Category.assoc _ _ _).symm
    _ = (F.toMiddle.resLE W Q hpre ≫ 𝟙 W.toScheme) ≫ W.ι := by
      rw [hWid]
    _ = Q.ι ≫ F.toMiddle := by
      simp

/-- `Spec` of a composite of ring maps, as a composite in the opposite direction. Stated with
variables so that it applies without the `rw` motive check having to inspect the chart indices. -/
public lemma specMap_op_comp {R S T : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) :
    Scheme.Spec.map (a ≫ b).op = Scheme.Spec.map b.op ≫ Scheme.Spec.map a.op := by
  rw [CategoryTheory.op_comp, Scheme.Spec.map_comp]

public theorem relativeSeminormalization_competitorChartMapToF_compatible
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f)
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    (relativeSeminormalizationGlueData f).functor.map i ≫
        relativeSeminormalization_competitorChartMapToF f F V =
      relativeSeminormalization_competitorChartMapToF f F U := by
  have := isIntegralHom_toBase F
  let WU := F.toBase ⁻¹ᵁ U.1
  let WV := F.toBase ⁻¹ᵁ V.1
  let hWU : IsAffineOpen WU := U.2.preimage F.toBase
  let hWV : IsAffineOpen WV := V.2.preimage F.toBase
  let cUV := F.middle.presheaf.map (homOfLE
    (F.toBase.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op
  have hring := relativeSeminormalization_competitorChartLift_natural f F i
  have hcat :
      CommRingCat.ofHom (relativeSeminormalization_competitorChartLift f F V.1 V.2) ≫
          (relativeSeminormalizationDiagram f).map i.op =
        cUV ≫
          CommRingCat.ofHom (relativeSeminormalization_competitorChartLift f F U.1 U.2) := by
    apply CommRingCat.hom_ext
    exact hring
  have hcat' := congrArg (fun q => q.op) hcat
  have hscheme :
      Scheme.Spec.map ((relativeSeminormalizationDiagram f).map i.op).op ≫
          Scheme.Spec.map (CommRingCat.ofHom
            (relativeSeminormalization_competitorChartLift f F V.1 V.2)).op =
          Scheme.Spec.map (CommRingCat.ofHom
            (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫
          Scheme.Spec.map cUV.op :=
    (specMap_op_comp _ _).symm.trans
      ((congrArg (fun q => Scheme.Spec.map q) hcat').trans (specMap_op_comp _ _))
  have htarget :
      Scheme.Spec.map cUV.op ≫ hWV.isoSpec.inv ≫ WV.ι =
        hWU.isoSpec.inv ≫ WU.ι := by
    apply (cancel_epi hWU.isoSpec.hom).1
    have hUV : U.1 ≤ V.1 :=
      Scheme.AffineZariskiSite.toOpens_mono (X := X) i.1.1
    have hn := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map WU WV
      (F.toBase.preimage_mono hUV)
    change WU.toSpecΓ ≫ Scheme.Spec.map cUV.op =
      F.middle.homOfLE (F.toBase.preimage_mono hUV) ≫ WV.toSpecΓ at hn
    change WU.toSpecΓ ≫ Scheme.Spec.map cUV.op ≫
      hWV.isoSpec.inv ≫ WV.ι = WU.toSpecΓ ≫ hWU.isoSpec.inv ≫ WU.ι
    have hstep := congrArg (fun q => q ≫ hWV.isoSpec.inv ≫ WV.ι) hn
    calc
      _ = F.middle.homOfLE (F.toBase.preimage_mono hUV) ≫
          WV.toSpecΓ ≫ hWV.isoSpec.inv ≫ WV.ι := hstep
      _ = WU.ι := by
        rw [← hWV.isoSpec_hom]
        simp only [Iso.hom_inv_id_assoc]
        exact Scheme.homOfLE_ι F.middle (F.toBase.preimage_mono hUV)
      _ = WU.toSpecΓ ≫ hWU.isoSpec.inv ≫ WU.ι := by
        rw [← hWU.isoSpec_hom]
        simp only [Iso.hom_inv_id_assoc]
  dsimp [relativeSeminormalizationGlueData,
    Scheme.AffineZariskiSite.relativeGluingData,
    relativeSeminormalization_competitorChartMapToF]
  change Scheme.Spec.map ((relativeSeminormalizationDiagram f).map i.op).op ≫
      Scheme.Spec.map (CommRingCat.ofHom
        (relativeSeminormalization_competitorChartLift f F V.1 V.2)).op ≫
      hWV.isoSpec.inv ≫ WV.ι =
    Scheme.Spec.map (CommRingCat.ofHom
      (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫
      hWU.isoSpec.inv ≫ WU.ι
  have hscheme' := congrArg (fun q => q ≫ hWV.isoSpec.inv ≫ WV.ι) hscheme
  exact ((Category.assoc _ _ _).symm.trans hscheme').trans
    ((Category.assoc _ _ _).trans (congrArg (fun q => Scheme.Spec.map (CommRingCat.ofHom
      (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫ q) htarget))

public noncomputable def relativeSeminormalization_comparison
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) :
    relativeSeminormalizationMiddle f ⟶ F.middle := by
  let d := relativeSeminormalizationGlueData f
  letI : Quiver.IsThin X.AffineZariskiSite := inferInstance
  letI : Small.{u} X.AffineZariskiSite := inferInstance
  letI : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  letI : Limits.HasColimit d.functor := inferInstance
  refine Limits.colimit.desc d.functor ⟨F.middle, {
    app := relativeSeminormalization_competitorChartMapToF f F
    naturality := ?_ }⟩
  intro i j hij
  exact relativeSeminormalization_competitorChartMapToF_compatible f F hij

public theorem relativeSeminormalization_comparison_ι
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (i : X.AffineZariskiSite)
    [hcol : Limits.HasColimit (relativeSeminormalizationGlueData f).functor] :
    Limits.colimit.ι (relativeSeminormalizationGlueData f).functor i ≫
      relativeSeminormalization_comparison f F =
        relativeSeminormalization_competitorChartMapToF f F i := by
  let d := relativeSeminormalizationGlueData f
  simp [relativeSeminormalization_comparison]

public theorem relativeSeminormalization_competitorChartMapToF_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.AffineZariskiSite) :
    relativeSeminormalization_competitorChartMapToF f F U ≫ F.toBase =
      (relativeSeminormalizationGlueData f).natTrans.app U ≫ U.1.ι := by
  have := isIntegralHom_toBase F
  let W := F.toBase ⁻¹ᵁ U.1
  let hW : IsAffineOpen W := U.2.preimage F.toBase
  let A := Γ(X, U.1)
  let : Algebra (Γ(X, U.1)) (Γ(Y, f ⁻¹ᵁ U.1)) := (f.app U.1).hom.toAlgebra
  let hdom := affineChart_app_isDominant f U.1 U.2
  let E := relativeSeminormalization Γ(X, U.1) Γ(Y, f ⁻¹ᵁ U.1)
    hdom
  have hq := spec_map_app_comp_isoSpec_inv F.toBase U.2
  have hlocal :=
    (relativeSeminormalization_competitorChartComparison f F U.1 U.2).hom_toBase
  change Scheme.Spec.map (CommRingCat.ofHom
      (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫
      Scheme.Spec.map (F.toBase.app U.1).op =
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A E)).op at hlocal
  change Scheme.Spec.map (CommRingCat.ofHom
      (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op ≫
      hW.isoSpec.inv ≫ W.ι ≫ F.toBase =
    (relativeSeminormalizationGlueData f).natTrans.app U ≫ U.1.ι
  have hrestrict : W.ι ≫ F.toBase = (F.toBase ∣_ U.1) ≫ U.1.ι :=
    (morphismRestrict_ι F.toBase U.1).symm
  rw [← Category.assoc, hrestrict]
  let ℓ := Scheme.Spec.map (CommRingCat.ofHom
    (relativeSeminormalization_competitorChartLift f F U.1 U.2)).op
  have hq' : (ℓ ≫ hW.isoSpec.inv) ≫ (F.toBase ∣_ U.1) =
      (ℓ ≫ Scheme.Spec.map (F.toBase.app U.1).op) ≫ U.2.isoSpec.inv := by
    simpa only [Category.assoc] using congrArg (fun g => ℓ ≫ g) hq.symm
  have hq'' := congrArg (fun g => g ≫ U.1.ι) hq'
  change ((ℓ ≫ hW.isoSpec.inv) ≫ (F.toBase ∣_ U.1)) ≫ U.1.ι =
    (relativeSeminormalizationGlueData f).natTrans.app U ≫ U.1.ι
  rw [hq'']
  have hlocalℓ : ℓ ≫ Scheme.Spec.map (F.toBase.app U.1).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A E)).op := by
    simpa [ℓ] using hlocal
  change ((ℓ ≫ Scheme.Spec.map (F.toBase.app U.1).op) ≫ U.2.isoSpec.inv) ≫ U.1.ι =
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A E)).op ≫
      U.2.isoSpec.inv) ≫ U.1.ι
  exact congrArg (fun g => (g ≫ U.2.isoSpec.inv) ≫ U.1.ι) hlocalℓ

public theorem relativeSeminormalization_comparison_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f)
    [hcol : Limits.HasColimit (relativeSeminormalizationGlueData f).functor] :
    relativeSeminormalization_comparison f F ≫ F.toBase =
      relativeSeminormalizationToBase f := by
  let d := relativeSeminormalizationGlueData f
  apply Scheme.Cover.hom_ext d.cover
  intro (U : X.AffineZariskiSite)
  change Limits.colimit.ι d.functor U ≫
      relativeSeminormalization_comparison f F ≫ F.toBase =
    Limits.colimit.ι d.functor U ≫ d.toBase
  calc
    _ = relativeSeminormalization_competitorChartMapToF f F U ≫ F.toBase :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ F.toBase) (relativeSeminormalization_comparison_ι f F U))
    _ = d.natTrans.app U ≫ U.1.ι :=
      relativeSeminormalization_competitorChartMapToF_toBase f F U
    _ = Limits.colimit.ι d.functor U ≫ d.toBase :=
      (Scheme.Cover.RelativeGluingData.ι_toBase (d := d) U).symm

public theorem relativeSeminormalization_comparison_fromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f)
    [hcol : Limits.HasColimit (relativeSeminormalizationGlueData f).functor] :
    relativeSeminormalizationFromSource f ≫
        relativeSeminormalization_comparison f F = F.toMiddle := by
  let d := relativeSeminormalizationGlueData f
  apply Scheme.Cover.hom_ext
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f)
  intro U
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  let := (f.app V.1).hom.toAlgebra
  change Limits.pullback.fst f U.1.ι ≫ _ = Limits.pullback.fst f U.1.ι ≫ F.toMiddle
  rw [← pullbackRestrictIsoRestrict_hom_ι (f := f) V.1]
  change (pullbackRestrictIsoRestrict f V.1).hom ≫
      ((f ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource f ≫
        relativeSeminormalization_comparison f F) =
    (pullbackRestrictIsoRestrict f V.1).hom ≫
      ((f ⁻¹ᵁ V.1).ι ≫ F.toMiddle)
  apply (cancel_epi (pullbackRestrictIsoRestrict f V.1).hom).2
  have hsource := relativeSeminormalizationFromSource_chart (f := f) V
  have hsource' : (f ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource f =
      affineSemiNormalizationFromSource f V.1 V.2 ≫ d.cover.f V := by
    simpa [relativeSeminormalizationOpenCover, relativeSeminormalizationMiddle, d]
      using hsource
  have hmap : d.cover.f V ≫ relativeSeminormalization_comparison f F =
      relativeSeminormalization_competitorChartMapToF f F V := by
    rw [d.cover_f V]
    exact relativeSeminormalization_comparison_ι f F V
  calc
    (f ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource f ≫
        relativeSeminormalization_comparison f F =
      (affineSemiNormalizationFromSource f V.1 V.2 ≫ d.cover.f V) ≫
        relativeSeminormalization_comparison f F :=
      congrArg (fun k => k ≫ relativeSeminormalization_comparison f F) hsource'
    _ = affineSemiNormalizationFromSource f V.1 V.2 ≫
        relativeSeminormalization_competitorChartMapToF f F V :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => affineSemiNormalizationFromSource f V.1 V.2 ≫ q) hmap)
    _ = (f ⁻¹ᵁ V.1).ι ≫ F.toMiddle :=
      relativeSeminormalization_competitorChartMapToF_fromSource f F V

public theorem relativeSeminormalization_comparison_unique
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f)
    [hcol : Limits.HasColimit (relativeSeminormalizationGlueData f).functor]
    (m : SubintegralFactorization.Hom (relativeSeminormalizationFactorization f) F) :
    m.hom = relativeSeminormalization_comparison f F := by
  let d := relativeSeminormalizationGlueData f
  apply Limits.colimit.hom_ext
  intro U
  let V : X.AffineZariskiSite := U
  let Q := f ⁻¹ᵁ V.1
  let W := F.toBase ⁻¹ᵁ V.1
  have := isIntegralHom_toBase F
  let hW : IsAffineOpen W := V.2.preimage F.toBase
  let A := Γ(X, V.1)
  let B := Γ(Y, Q)
  let C := Γ(F.middle, W)
  let : Algebra A B := (f.app V.1).hom.toAlgebra
  let hdom := affineChart_app_isDominant f V.1 V.2
  let : Algebra A C := (F.toBase.app V.1).hom.toAlgebra
  let φ := (relativeSeminormalization_competitorChartMap f F V.1 V.2).hom
  let : Algebra C B := φ.toAlgebra
  have hcomp : algebraMap A B = (algebraMap C B).comp (algebraMap A C) := by
    have h := relativeSeminormalization_competitorChartMap_base f F V.1 V.2
    simpa only [RingHom.algebraMap_toAlgebra, Scheme.Hom.app_eq_appLE,
      CommRingCat.hom_comp, φ] using (congrArg CommRingCat.Hom.hom h).symm
  let : IsScalarTower A C B := .of_algebraMap_eq' hcomp
  let G_U := affineSubintegralFactorization A B hdom
  let F_U := relativeSeminormalization_competitorChartFactorization f F V.1 V.2
  let gM := Limits.colimit.ι d.functor V ≫ m.hom
  have hbaseGlobal : gM ≫ F.toBase = d.natTrans.app V ≫ V.1.ι := by
    calc
      gM ≫ F.toBase = Limits.colimit.ι d.functor V ≫
          (relativeSeminormalizationFactorization f).toBase :=
        (Category.assoc _ _ _).trans
          (congrArg (fun q => Limits.colimit.ι d.functor V ≫ q) m.hom_toBase)
      _ = Limits.colimit.ι d.functor V ≫ d.toBase := rfl
      _ = d.natTrans.app V ≫ V.1.ι := d.ι_toBase V
  have hbaseTop := congrArg (fun k => k.base) hbaseGlobal
  have hrange : Set.range gM.base ⊆ Set.range W.ι.base := by
    rintro y ⟨z, rfl⟩
    refine ⟨⟨gM.base z, ?_⟩, rfl⟩
    change F.toBase.base (gM.base z) ∈ V.1
    have hz : F.toBase.base (gM.base z) =
        V.1.ι.base ((d.natTrans.app V).base z) :=
      congrArg (fun k => k z) hbaseTop
    rw [hz]
    exact ((d.natTrans.app V).base z).property
  let gLift : d.functor.obj V ⟶ W.toScheme := IsOpenImmersion.lift W.ι gM hrange
  let localMap : G_U.middle ⟶ F_U.middle := gLift ≫ hW.isoSpec.hom
  let sourceMap := affineSemiNormalizationFromSource f V.1 V.2
  have hsourceChart : Q.ι ≫ relativeSeminormalizationFromSource f =
      sourceMap ≫ Limits.colimit.ι d.functor V := by
    have h := relativeSeminormalizationFromSource_chart (f := f) V
    change Q.ι ≫ relativeSeminormalizationFromSource f =
      sourceMap ≫ (relativeSeminormalizationOpenCover f).f V at h
    exact h.trans (congrArg (fun q => sourceMap ≫ q) (d.cover_f V))
  have hmto : relativeSeminormalizationFromSource f ≫ m.hom = F.toMiddle := by
    simpa [relativeSeminormalizationFactorization] using m.toMiddle_hom
  have hsourceGlobal : sourceMap ≫ gM = Q.ι ≫ F.toMiddle := by
    calc
      sourceMap ≫ gM = (sourceMap ≫ Limits.colimit.ι d.functor V) ≫ m.hom :=
        (Category.assoc _ _ _).symm
      _ = (Q.ι ≫ relativeSeminormalizationFromSource f) ≫ m.hom :=
        congrArg (fun k => k ≫ m.hom) hsourceChart.symm
      _ = Q.ι ≫ F.toMiddle :=
        (Category.assoc _ _ _).trans (congrArg (fun q => Q.ι ≫ q) hmto)
  let canonicalLocal := relativeSeminormalization_competitorChartComparison f F V.1 V.2
  have hsourcePost : sourceMap ≫ localMap ≫ hW.isoSpec.inv ≫ W.ι =
      sourceMap ≫ canonicalLocal.hom ≫ hW.isoSpec.inv ≫ W.ι := by
    calc
      sourceMap ≫ localMap ≫ hW.isoSpec.inv ≫ W.ι = sourceMap ≫ gM :=
        congrArg (fun q => sourceMap ≫ q)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun q => IsOpenImmersion.lift W.ι gM hrange ≫ q)
                (Iso.hom_inv_id_assoc hW.isoSpec W.ι)).trans
              (IsOpenImmersion.lift_fac W.ι gM hrange)))
      _ = Q.ι ≫ F.toMiddle := hsourceGlobal
      _ = sourceMap ≫ relativeSeminormalization_competitorChartMapToF f F V := by
        rw [relativeSeminormalization_competitorChartMapToF_fromSource]
      _ = sourceMap ≫ canonicalLocal.hom ≫ hW.isoSpec.inv ≫ W.ι := by
        rfl
  have hsourcePost' : sourceMap ≫ localMap = sourceMap ≫ canonicalLocal.hom :=
    (cancel_mono (hW.isoSpec.inv ≫ W.ι)).1 hsourcePost
  have hsourcePre : Q.toSpecΓ ≫ G_U.toMiddle ≫ localMap =
      Q.toSpecΓ ≫ G_U.toMiddle ≫ canonicalLocal.hom := by
    rw [← Category.assoc, ← Category.assoc]
    exact hsourcePost'
  have hsourceApp := congrArg (fun k : Q.toScheme ⟶ F_U.middle => k.appTop) hsourcePre
  have hsourceApp' : (G_U.toMiddle ≫ localMap).appTop =
      (G_U.toMiddle ≫ canonicalLocal.hom).appTop := by
    have : IsIso (Q.toSpecΓ.appTop) := by
      rw [Scheme.Opens.toSpecΓ_appTop]
      infer_instance
    rw [Scheme.Hom.comp_appTop] at hsourceApp
    exact (cancel_mono Q.toSpecΓ.appTop).1 hsourceApp
  have hsourceLocal : G_U.toMiddle ≫ localMap = F_U.toMiddle := by
    let : IsAffine F_U.middle := by
      change IsAffine (Spec (CommRingCat.of C))
      infer_instance
    apply ext_of_isAffine
    exact hsourceApp'.trans (congrArg (fun k => k.appTop)
      canonicalLocal.toMiddle_hom)
  let κ : Spec (CommRingCat.of (Γ(X, V.1))) ⟶ X := V.2.isoSpec.inv ≫ V.1.ι
  have hbaseLocal : localMap ≫ F_U.toBase = G_U.toBase := by
    apply (cancel_mono κ).1
    have hspecBase : hW.isoSpec.hom ≫ F_U.toBase ≫ V.2.isoSpec.inv =
        (F.toBase ∣_ V.1) := by
      have hq := spec_map_app_comp_isoSpec_inv F.toBase V.2
      calc
        _ = hW.isoSpec.hom ≫ Scheme.Spec.map (F.toBase.app V.1).op ≫ V.2.isoSpec.inv := rfl
        _ = F.toBase ∣_ V.1 := by rw [hq, Iso.hom_inv_id_assoc]
    have h1a : localMap ≫ F_U.toBase ≫ κ =
        gLift ≫ hW.isoSpec.hom ≫ F_U.toBase ≫ V.2.isoSpec.inv ≫ V.1.ι :=
      Category.assoc _ _ _
    have hassoc : hW.isoSpec.hom ≫ F_U.toBase ≫ V.2.isoSpec.inv ≫ V.1.ι =
        (hW.isoSpec.hom ≫ F_U.toBase ≫ V.2.isoSpec.inv) ≫ V.1.ι :=
      congrArg (fun k => hW.isoSpec.hom ≫ k) (Category.assoc _ _ _).symm
    have h1b : gLift ≫ hW.isoSpec.hom ≫ F_U.toBase ≫ V.2.isoSpec.inv ≫ V.1.ι =
        gLift ≫ (F.toBase ∣_ V.1) ≫ V.1.ι :=
      congrArg (fun k => gLift ≫ k)
        (hassoc.trans (congrArg (fun k => k ≫ V.1.ι) hspecBase))
    have h2 : gLift ≫ (F.toBase ∣_ V.1) ≫ V.1.ι = gLift ≫ W.ι ≫ F.toBase :=
      congrArg (fun k => gLift ≫ k) (morphismRestrict_ι F.toBase V.1)
    have h3 : gLift ≫ W.ι ≫ F.toBase = gM ≫ F.toBase :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ F.toBase) (IsOpenImmersion.lift_fac W.ι gM hrange))
    refine (Category.assoc _ _ _).trans ?_
    exact ((((h1a.trans h1b).trans h2).trans h3).trans hbaseGlobal)
  let mU : SubintegralFactorization.Hom G_U F_U :=
    ⟨localMap, hsourceLocal, hbaseLocal⟩
  have hprops := relativeSeminormalization_competitorChart_subintegral f F V.1 V.2
  have huniq := affineSubintegralFactorization_hom_unique
    A B C hdom (relativeSeminormalization_competitorChartAlgebra f F V.1 V.2)
    hprops.1 hprops.2 mU
  have hlocalEq := congrArg SubintegralFactorization.Hom.hom huniq
  calc
    Limits.colimit.ι d.functor V ≫ m.hom =
        relativeSeminormalization_competitorChartMapToF f F V := by
      have k1 : Limits.colimit.ι d.functor V ≫ m.hom = gLift ≫ W.ι := by
        dsimp [gM]
        exact (IsOpenImmersion.lift_fac W.ι gM hrange).symm
      have k2 : gLift ≫ W.ι = localMap ≫ hW.isoSpec.inv ≫ W.ι :=
        (congrArg (fun k => gLift ≫ k)
          (Iso.hom_inv_id_assoc hW.isoSpec W.ι)).symm.trans (Category.assoc _ _ _).symm
      have k3 : localMap ≫ hW.isoSpec.inv ≫ W.ι =
          (relativeSeminormalization_competitorChartComparison f F V.1 V.2).hom ≫
            hW.isoSpec.inv ≫ W.ι :=
        congrArg (fun k => k ≫ hW.isoSpec.inv ≫ W.ι) hlocalEq
      exact (k1.trans k2).trans k3
    _ = Limits.colimit.ι d.functor V ≫ relativeSeminormalization_comparison f F :=
      (relativeSeminormalization_comparison_ι f F V).symm

/-- The diagram of affine relative-seminormalization charts is locally directed, so its
colimit is the glued relative seminormalization. -/
public theorem relativeSeminormalizationGlueData_isLocallyDirected
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    ((relativeSeminormalizationGlueData f).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The glued relative seminormalization is an initial subintegral factorization. -/
public noncomputable def relativeSeminormalizationFactorizationIsInitial
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Limits.IsInitial (relativeSeminormalizationFactorization f) := by
  let d := relativeSeminormalizationGlueData f
  let : Quiver.IsThin X.AffineZariskiSite := inferInstance
  let : Small.{u} X.AffineZariskiSite := inferInstance
  let : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin d
  let : Limits.HasColimit d.functor := inferInstance
  apply CategoryTheory.Limits.IsInitial.ofUniqueHom
    (fun F => (show SubintegralFactorization.Hom
      (relativeSeminormalizationFactorization f) F from
      { hom := relativeSeminormalization_comparison f F
        toMiddle_hom := by
          change relativeSeminormalizationFromSource f ≫
            relativeSeminormalization_comparison f F = F.toMiddle
          exact relativeSeminormalization_comparison_fromSource f F
        hom_toBase := by
          change relativeSeminormalization_comparison f F ≫ F.toBase =
            relativeSeminormalizationToBase f
          exact relativeSeminormalization_comparison_toBase f F }))
  intro F m
  apply SubintegralFactorization.Hom.ext
  exact relativeSeminormalization_comparison_unique f F m

/-- The category of factorizations through universal homeomorphisms inducing
isomorphisms on residue fields has an initial object. -/
@[stacks 0H3N "part (2), the seminormalization factorization"]
public theorem exists_initial_subintegralFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    ∃ F : SubintegralFactorization f, Nonempty (Limits.IsInitial F) :=
  ⟨relativeSeminormalizationFactorization f,
    ⟨relativeSeminormalizationFactorizationIsInitial f⟩⟩

/-- A chosen relative seminormalization factorization. -/
public noncomputable def seminormalizationFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : SubintegralFactorization f :=
  Classical.choose (exists_initial_subintegralFactorization f)

/-- The chosen relative seminormalization factorization is initial. -/
public noncomputable def seminormalizationFactorizationIsInitial
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Limits.IsInitial (seminormalizationFactorization f) :=
  Classical.choice (Classical.choose_spec (exists_initial_subintegralFactorization f))

end AlgebraicGeometry

end
