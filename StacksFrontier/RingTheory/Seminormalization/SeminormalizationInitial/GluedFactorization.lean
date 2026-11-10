module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Factorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeSeminormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalizationLocalization
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial.AffineChartGluing

/-!
# The glued relative seminormalization factorization

The local first legs of the affine chart factorizations agree on overlaps and glue to a morphism
from the source to the glued relative seminormalization; together with the gluing map to the
target this gives the subintegral factorization
`AlgebraicGeometry.relativeSeminormalizationFactorization`. This file also restricts a competing
subintegral factorization to the affine charts of the target and lifts each chart algebra of the
competitor through the relative seminormalization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Compose a compatibility of two charts over an inclusion of opens of `X` with the canonical
identifications of the base changes. The binders are opens of `X` for the same reason as in
`pullbackRestrictIsoRestrict_trans_eq_homOfLE`. -/
public lemma pullbackRestrictIsoRestrict_hom_comp_eq
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (hUV : U ≤ V)
    (t : Limits.pullback f U.ι ⟶ Limits.pullback f V.ι)
    (ht : t ≫ Limits.pullback.fst f V.ι = Limits.pullback.fst f U.ι)
    {G : Scheme.{u}} (cU : (f ⁻¹ᵁ U).toScheme ⟶ G) (cV : (f ⁻¹ᵁ V).toScheme ⟶ G)
    (hc : Y.homOfLE (f.preimage_mono hUV) ≫ cV = cU) :
    t ≫ (pullbackRestrictIsoRestrict f V).hom ≫ cV =
      (pullbackRestrictIsoRestrict f U).hom ≫ cU := by
  have H := (Iso.inv_comp_eq _).mp
    (pullbackRestrictIsoRestrict_trans_eq_homOfLE f hUV t ht)
  rw [← Category.assoc, H, Category.assoc, hc]

/-- The first legs of the local factorizations agree on chart overlaps. -/
public theorem relativeSeminormalizationFromSource_compatible
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom ≫
        affineSemiNormalizationFromSource f V.1 V.2 ≫
        (relativeSeminormalizationOpenCover f).f V =
      (pullbackRestrictIsoRestrict f U.1).hom ≫
        affineSemiNormalizationFromSource f U.1 U.2 ≫
        (relativeSeminormalizationOpenCover f).f U := by
  refine pullbackRestrictIsoRestrict_hom_comp_eq f
    (Scheme.AffineZariskiSite.toOpens_mono i.1.1)
    (Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f) i)
    (Scheme.Cover.trans_map ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f) i)
    _ _ ?_
  have hΓ : Y.homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i.1.1)) ≫
      (f ⁻¹ᵁ V.1).toSpecΓ =
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map
        (Y.presheaf.map (homOfLE (f.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op) := by
    simp
  rcases i.1.1 with ⟨r, hr⟩
  have hUV : U = V.basicOpen r := Subtype.ext hr.symm
  subst U
  let A := Γ(X, V.1)
  let B := Γ(Y, f ⁻¹ᵁ V.1)
  let Aₛ := Γ(X, (V.basicOpen r).1)
  let Bₛ := Γ(Y, f ⁻¹ᵁ (V.basicOpen r).1)
  let : Algebra A B := (f.app V.1).hom.toAlgebra
  let : Algebra A Aₛ := (X.presheaf.map (homOfLE
    (Scheme.AffineZariskiSite.toOpens_mono (V.basicOpen_le r))).op).hom.toAlgebra
  let : IsLocalization.Away r Aₛ := by
    dsimp [Aₛ]
    exact V.2.isLocalization_basicOpen r
  let inst : Algebra B Bₛ := (Y.presheaf.map (homOfLE (f.preimage_mono
    (Scheme.AffineZariskiSite.toOpens_mono (V.basicOpen_le r)))).op).hom.toAlgebra
  let : Algebra Aₛ Bₛ := (f.app (V.basicOpen r).1).hom.toAlgebra
  let : Algebra A Bₛ := (f.appLE V.1 (f ⁻¹ᵁ (V.basicOpen r).1)
    (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono (V.basicOpen_le r)))).hom.toAlgebra
  have hB : let := inst; IsLocalization.Away ((algebraMap A B) r) Bₛ := by
    let : Algebra B Γ(Y, Y.basicOpen ((f.app V.1) r)) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le ((f.app V.1) r))).op).hom.toAlgebra
    dsimp +instances [Bₛ, inst, Scheme.AffineZariskiSite.basicOpen]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs
      (f.isCompact_preimage V.2.isCompact)
      (f.isQuasiSeparated_preimage V.2.isQuasiSeparated) ((f.app V.1) r)
  let := inst
  let : IsLocalization ((Submonoid.powers r).map (algebraMap A B)) Bₛ := by
    simpa [Submonoid.map_powers] using hB
  let : IsScalarTower A B Bₛ := .of_algebraMap_eq' rfl
  let : IsScalarTower A Aₛ Bₛ := by
    apply IsScalarTower.of_algebraMap_eq'
    have hnat := f.naturality
      (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
        (V.basicOpen_le r))).op
    change (f.appLE V.1 (f ⁻¹ᵁ (V.basicOpen r).1)
        (f.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono
          (V.basicOpen_le r)))).hom =
      (f.app (V.basicOpen r).1).hom.comp (X.presheaf.map
        (homOfLE (Scheme.AffineZariskiSite.toOpens_mono
          (V.basicOpen_le r))).op).hom
    exact congrArg CommRingCat.Hom.hom hnat.symm
  have hi : i = homOfLE (V.basicOpen_le r) := Subsingleton.elim _ _
  have hBmap : (Y.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op).hom =
      (algebraMap B Bₛ : B →+* Bₛ) := by
    rw [hi]
    rfl
  have hBspec : Spec.map (Y.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op) =
      Spec.map (CommRingCat.ofHom (algebraMap B Bₛ)) := by
    congr 1
  have hsource := relativeSeminormalization_localization_specMap_source
    A B Aₛ Bₛ (Submonoid.powers r)
    (affineChart_app_isDominant f V.1 V.2)
    (affineChart_app_isDominant f (V.basicOpen r).1 (V.basicOpen r).2)
  have htransition : relativeSeminormalization_localization_specMap
      A B Aₛ Bₛ (Submonoid.powers r)
      (affineChart_app_isDominant f V.1 V.2)
      (affineChart_app_isDominant f (V.basicOpen r).1 (V.basicOpen r).2) =
    Scheme.Spec.map ((CommRingCat.ofHom
      ((relativeSeminormalizationDiagram f).map i.op).hom).op) := by
    dsimp [relativeSeminormalization_localization_specMap,
      relativeSeminormalization_localization_algHom,
      relativeSeminormalizationDiagram]
    congr 1
  have hcoverTransition : relativeSeminormalization_localization_specMap
      A B Aₛ Bₛ (Submonoid.powers r)
      (affineChart_app_isDominant f V.1 V.2)
      (affineChart_app_isDominant f (V.basicOpen r).1 (V.basicOpen r).2) ≫
      (relativeSeminormalizationOpenCover f).f V =
      (relativeSeminormalizationOpenCover f).f (V.basicOpen r) := by
    let : Quiver.IsThin X.AffineZariskiSite := inferInstance
    let : Small.{u} X.AffineZariskiSite := inferInstance
    let : ((relativeSeminormalizationGlueData f).functor ⋙ Scheme.forget).IsLocallyDirected :=
      Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
    let : Limits.HasColimit (relativeSeminormalizationGlueData f).functor := inferInstance
    dsimp [relativeSeminormalizationOpenCover]
    rw [htransition]
    change (relativeSeminormalizationGlueData f).functor.map i ≫
      Limits.colimit.ι (relativeSeminormalizationGlueData f).functor V = _
    exact Limits.colimit.w (relativeSeminormalizationGlueData f).functor i
  calc
    _ = Y.homOfLE (f.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono i.1.1)) ≫
        affineSemiNormalizationFromSource f V.1 V.2 ≫
          (relativeSeminormalizationOpenCover f).f V := by rfl
    _ = ((f ⁻¹ᵁ (V.basicOpen r).1).toSpecΓ ≫ Spec.map
          (Y.presheaf.map (homOfLE (f.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op)) ≫
          Spec.map (CommRingCat.ofHom
            (relativeSeminormalization Γ(X, V.1)
              Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)).val.toRingHom) ≫
          (relativeSeminormalizationOpenCover f).f V := by
      have e := congrArg (fun q => q ≫ Spec.map (CommRingCat.ofHom
          (relativeSeminormalization Γ(X, V.1)
            Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)).val.toRingHom) ≫
          (relativeSeminormalizationOpenCover f).f V) hΓ
      simp only [Category.assoc] at e ⊢
      exact e
    _ = ((f ⁻¹ᵁ (V.basicOpen r).1).toSpecΓ ≫ Spec.map
          (CommRingCat.ofHom
            (relativeSeminormalization Aₛ Bₛ
              (affineChart_app_isDominant f (V.basicOpen r).1
                (V.basicOpen r).2)).val.toRingHom)) ≫
          relativeSeminormalization_localization_specMap
            A B Aₛ Bₛ (Submonoid.powers r)
            (affineChart_app_isDominant f V.1 V.2)
            (affineChart_app_isDominant f (V.basicOpen r).1
              (V.basicOpen r).2) ≫
          (relativeSeminormalizationOpenCover f).f V := by
      rw [hBspec]
      have hspec {R S : Type u} [CommRing R] [CommRing S]
          (g : R →+* S) :
          Spec.map (CommRingCat.ofHom g) =
            Scheme.Spec.map (CommRingCat.ofHom g).op := rfl
      have hsource' :
          Spec.map (CommRingCat.ofHom
            ((relativeSeminormalization Aₛ Bₛ
              (affineChart_app_isDominant f (V.basicOpen r).1
                (V.basicOpen r).2)).val.toRingHom)) ≫
            relativeSeminormalization_localization_specMap
              A B Aₛ Bₛ (Submonoid.powers r)
              (affineChart_app_isDominant f V.1 V.2)
              (affineChart_app_isDominant f (V.basicOpen r).1 (V.basicOpen r).2) =
          Spec.map (CommRingCat.ofHom (algebraMap B Bₛ)) ≫
            Spec.map (CommRingCat.ofHom
              ((relativeSeminormalization A B
                (affineChart_app_isDominant f V.1 V.2)).val.toRingHom)) := by
        simpa only [A, B, Aₛ, Bₛ, ← hspec] using hsource
      exact congrArg
        (fun q => ((f ⁻¹ᵁ (V.basicOpen r).1).toSpecΓ ≫ q) ≫
          (relativeSeminormalizationOpenCover f).f V) hsource'.symm
    _ = ((f ⁻¹ᵁ (V.basicOpen r).1).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (relativeSeminormalization Aₛ Bₛ
              (affineChart_app_isDominant f (V.basicOpen r).1
                (V.basicOpen r).2)).val.toRingHom)) ≫
          (relativeSeminormalizationOpenCover f).f (V.basicOpen r) := by
      simpa only [Category.assoc] using congrArg
        (fun q => ((f ⁻¹ᵁ (V.basicOpen r).1).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (relativeSeminormalization Aₛ Bₛ
              (affineChart_app_isDominant f (V.basicOpen r).1
                (V.basicOpen r).2)).val.toRingHom)) ≫ q) hcoverTransition
    _ = affineSemiNormalizationFromSource f (V.basicOpen r).1
          (V.basicOpen r).2 ≫
          (relativeSeminormalizationOpenCover f).f (V.basicOpen r) := by
      rfl

public noncomputable def relativeSeminormalizationFromSource
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : Y ⟶ relativeSeminormalizationMiddle f :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f)
    (fun U => (pullbackRestrictIsoRestrict f U.1).hom ≫
      affineSemiNormalizationFromSource f U.1 U.2 ≫
      (relativeSeminormalizationOpenCover f).f U)
    (by intro U V i; exact relativeSeminormalizationFromSource_compatible f i)

@[reassoc (attr := simp)]
public theorem relativeSeminormalizationFromSource_chart
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.AffineZariskiSite) :
    (f ⁻¹ᵁ U.1).ι ≫ relativeSeminormalizationFromSource f =
      affineSemiNormalizationFromSource f U.1 U.2 ≫
        (relativeSeminormalizationOpenCover f).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  rw [pullbackRestrictIsoRestrict_hom_ι]
  unfold relativeSeminormalizationFromSource
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f)
    (fun U => (pullbackRestrictIsoRestrict f U.1).hom ≫
      affineSemiNormalizationFromSource f U.1 U.2 ≫
      (relativeSeminormalizationOpenCover f).f U)
    (by intro U V i; exact relativeSeminormalizationFromSource_compatible f i) U

@[reassoc (attr := simp)]
public theorem relativeSeminormalizationOpenCover_toBase
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (U : X.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    let E := relativeSeminormalization Γ(X, U.1)
      Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2)
    (relativeSeminormalizationOpenCover f).f U ≫
        relativeSeminormalizationToBase f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) E)) ≫ U.2.fromSpec := by
  dsimp [relativeSeminormalizationOpenCover, relativeSeminormalizationToBase,
    relativeSeminormalizationMiddle]
  rw [(relativeSeminormalizationGlueData f).cover_f U]
  refine Eq.trans (Scheme.Cover.RelativeGluingData.ι_toBase
      (𝒰 := Scheme.AffineZariskiSite.directedCover X)
      (d := relativeSeminormalizationGlueData f) U) ?_
  dsimp [relativeSeminormalizationGlueData,
    Scheme.AffineZariskiSite.relativeGluingData]
  rfl

public theorem relativeSeminormalizationFactorization_fac
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    relativeSeminormalizationFromSource f ≫ relativeSeminormalizationToBase f = f := by
  apply Scheme.Cover.hom_ext
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ f)
  intro U
  let V : X.AffineZariskiSite := ⟨U.1, U.2⟩
  let := (f.app V.1).hom.toAlgebra
  change Limits.pullback.fst f U.1.ι ≫ _ = Limits.pullback.fst f U.1.ι ≫ f
  rw [← pullbackRestrictIsoRestrict_hom_ι (f := f) V.1]
  change (pullbackRestrictIsoRestrict f V.1).hom ≫
      ((f ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource f ≫
        relativeSeminormalizationToBase f) =
    (pullbackRestrictIsoRestrict f V.1).hom ≫ ((f ⁻¹ᵁ V.1).ι ≫ f)
  apply (cancel_epi (pullbackRestrictIsoRestrict f V.1).hom).2
  have hchart := relativeSeminormalizationFromSource_chart (f := f)
    (⟨U.1, U.2⟩ : X.AffineZariskiSite)
  have hchart' : (f ⁻¹ᵁ V.1).ι ≫ relativeSeminormalizationFromSource f =
      affineSemiNormalizationFromSource f V.1 V.2 ≫
        (relativeSeminormalizationOpenCover f).f V := by
    simpa only [V] using hchart
  have hbase := relativeSeminormalizationOpenCover_toBase (f := f)
    (⟨U.1, U.2⟩ : X.AffineZariskiSite)
  have hbase' : (relativeSeminormalizationOpenCover f).f V ≫
      relativeSeminormalizationToBase f =
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
      (relativeSeminormalization Γ(X, V.1)
        Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)))) ≫ V.2.fromSpec := by
    simpa only [V] using hbase
  calc
    _ = (affineSemiNormalizationFromSource f V.1 V.2 ≫
        (relativeSeminormalizationOpenCover f).f V) ≫
        relativeSeminormalizationToBase f :=
      congrArg (fun q => q ≫ relativeSeminormalizationToBase f) hchart'
    _ = affineSemiNormalizationFromSource f V.1 V.2 ≫
        affineSemiNormalizationToBase f V.1 V.2 ≫ V.1.ι := by
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg (fun q => affineSemiNormalizationFromSource f V.1 V.2 ≫ q) hbase'
    _ = (f ∣_ V.1) ≫ V.1.ι :=
      congrArg (fun g => g ≫ V.1.ι) (affineSemiNormalization_fac f V.1 V.2)
    _ = (f ⁻¹ᵁ V.1).ι ≫ f := by simp

public theorem residueFieldMap_isIso_opens_inclusion {X : Scheme.{u}}
    (U : X.Opens) (x : U.toScheme) : IsIso (U.ι.residueFieldMap x) :=
  inferInstance

public theorem relativeSeminormalizationToBase_universalHomeomorphism
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] :
    UniversalHomeomorphism (relativeSeminormalizationToBase f) := by
  have : IsZariskiLocalAtTarget
      ((topologically @IsHomeomorph).universally : MorphismProperty Scheme) :=
    universally_isZariskiLocalAtTarget (topologically @IsHomeomorph) (by
      intro A B g ι U hU hlocal
      simp_rw [topologically, morphismRestrict_base] at hlocal
      exact (hU.isHomeomorph_iff_restrictPreimage g.continuous).mpr hlocal)
  apply (universalHomeomorphism_iff _).mpr
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (topologically @IsHomeomorph).universally)
    (Scheme.AffineZariskiSite.directedCover X)]
  intro i
  let d := relativeSeminormalizationGlueData f
  have hpb := d.isPullback_natTrans_ι_toBase i
  have hchart : UniversalHomeomorphism (d.natTrans.app i) := by
    change UniversalHomeomorphism
      (affineSemiNormalizationToBase f i.1 i.2)
    exact (affineSemiNormalizationToBase_subintegral f i.1 i.2).1
  have hinv : UniversalHomeomorphism (hpb.flip.isoPullback.inv) :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have hcomp := universalHomeomorphism_comp hpb.flip.isoPullback.inv
    (d.natTrans.app i) hinv hchart
  have heq : hpb.flip.isoPullback.inv ≫ d.natTrans.app i =
      (Scheme.AffineZariskiSite.directedCover X).pullbackHom
        (relativeSeminormalizationToBase f) i := by
    rw [hpb.flip.isoPullback_inv_snd]
    rfl
  have hlocal := heq ▸ hcomp
  exact (universalHomeomorphism_iff _).mp hlocal

public theorem relativeSeminormalizationToBase_residueFieldMap_isIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (x : relativeSeminormalizationMiddle f) :
    IsIso ((relativeSeminormalizationToBase f).residueFieldMap x) := by
  let d := relativeSeminormalizationGlueData f
  let : Quiver.IsThin X.AffineZariskiSite := inferInstance
  let : Small.{u} X.AffineZariskiSite := inferInstance
  let : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  let : Limits.HasColimit d.functor := inferInstance
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective d.functor x
  have hchart : IsIso ((d.natTrans.app i).residueFieldMap y) := by
    change IsIso ((affineSemiNormalizationToBase f i.1 i.2).residueFieldMap y)
    exact (affineSemiNormalizationToBase_subintegral f i.1 i.2).2 y
  have hopen : IsIso
      (((Scheme.AffineZariskiSite.directedCover X).f i).residueFieldMap
        (d.natTrans.app i y)) := by
    simpa [Scheme.AffineZariskiSite.directedCover] using
      residueFieldMap_isIso_opens_inclusion i.1 (d.natTrans.app i y)
  have heq : Limits.colimit.ι d.functor i ≫ d.toBase =
      d.natTrans.app i ≫ i.1.ι :=
    Scheme.Cover.RelativeGluingData.ι_toBase (d := d) i
  have hchartComp : IsIso ((d.natTrans.app i ≫ i.1.ι).residueFieldMap y) := by
    rw [Scheme.residueFieldMap_comp (d.natTrans.app i) i.1.ι y]
    change IsIso (((Scheme.AffineZariskiSite.directedCover X).f i).residueFieldMap
      (d.natTrans.app i y) ≫ (d.natTrans.app i).residueFieldMap y)
    exact IsIso.comp_isIso' hopen hchart
  have hglobal : IsIso
      ((Limits.colimit.ι d.functor i ≫ d.toBase).residueFieldMap y) := by
    rw [heq]
    exact hchartComp
  have hcover : IsIso ((Limits.colimit.ι d.functor i).residueFieldMap y) := inferInstance
  have hglobal' : IsIso
      (d.toBase.residueFieldMap ((Limits.colimit.ι d.functor i) y) ≫
        (Limits.colimit.ι d.functor i).residueFieldMap y) := by
    rw [← Scheme.residueFieldMap_comp]
    exact hglobal
  let : IsIso ((Limits.colimit.ι d.functor i).residueFieldMap y) := hcover
  change IsIso (d.toBase.residueFieldMap x)
  rw [← hy]
  exact (isIso_comp_right_iff _ _).mp hglobal'

public noncomputable def relativeSeminormalizationFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] : SubintegralFactorization f where
  middle := relativeSeminormalizationMiddle f
  toMiddle := relativeSeminormalizationFromSource f
  toBase := relativeSeminormalizationToBase f
  fac := relativeSeminormalizationFactorization_fac f
  universalHomeomorphism := relativeSeminormalizationToBase_universalHomeomorphism f
  residueFieldIsomorphisms := relativeSeminormalizationToBase_residueFieldMap_isIso f

/-- Restrict a competing factorization to the inverse image of an affine base chart. -/
public noncomputable def relativeSeminormalization_competitorChartMap
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (_hU : IsAffineOpen U) :
    Γ(F.middle, F.toBase ⁻¹ᵁ U) ⟶ Γ(Y, f ⁻¹ᵁ U) := by
  let W := F.toBase ⁻¹ᵁ U
  have hpre : f ⁻¹ᵁ U ≤ F.toMiddle ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, F.fac]
  exact F.toMiddle.appLE W (f ⁻¹ᵁ U) hpre

public theorem relativeSeminormalization_competitorChartMap_base
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    F.toBase.appLE U (F.toBase ⁻¹ᵁ U) (by rfl) ≫
        relativeSeminormalization_competitorChartMap f F U hU =
      f.appLE U (f ⁻¹ᵁ U) (by simp) := by
  let W := F.toBase ⁻¹ᵁ U
  have hW : W ≤ F.toBase ⁻¹ᵁ U := le_rfl
  have hpre : f ⁻¹ᵁ U ≤ F.toMiddle ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, F.fac]
  have h := Scheme.Hom.appLE_comp_appLE F.toMiddle F.toBase U W (f ⁻¹ᵁ U)
    hW hpre
  simpa [W, relativeSeminormalization_competitorChartMap,
    Scheme.Hom.app_eq_appLE, F.fac] using h

public theorem relativeSeminormalization_competitorChart_subintegral
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    UniversalHomeomorphism
        (Scheme.Spec.map (F.toBase.app U).op) ∧
      ∀ x, IsIso ((Scheme.Spec.map (F.toBase.app U).op).residueFieldMap x) := by
  let W := F.toBase ⁻¹ᵁ U
  let hprops :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective
      F.toBase).mp F.universalHomeomorphism
  let : IsIntegralHom F.toBase := hprops.1
  let hW : IsAffineOpen W := hU.preimage F.toBase
  have hBaseU : UniversalHomeomorphism (F.toBase ∣_ U) := by
    let : UniversallyInjective F.toBase := hprops.2.1
    let : Surjective F.toBase := hprops.2.2
    have : IsIntegralHom (F.toBase ∣_ U) :=
      MorphismProperty.of_isPullback
        (isPullback_morphismRestrict F.toBase U).flip inferInstance
    have : UniversallyInjective (F.toBase ∣_ U) :=
      MorphismProperty.of_isPullback
        (isPullback_morphismRestrict F.toBase U).flip inferInstance
    have hsurj : Surjective (F.toBase ∣_ U) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨y, hy⟩ := hprops.2.2.surj x.1
      have hyU : F.toBase y ∈ U := by
        rw [hy]
        exact x.2
      let yU : W.toScheme := ⟨y, hyU⟩
      refine ⟨yU, Subtype.ext ?_⟩
      rw [morphismRestrict_base_coe]
      exact hy
    exact (universalHomeomorphism_iff_integral_universallyInjective_surjective
      (F.toBase ∣_ U)).mpr ⟨inferInstance, inferInstance, hsurj⟩
  have hresBaseU (x : W.toScheme) :
      IsIso ((F.toBase ∣_ U).residueFieldMap x) := by
    have hx : ((F.toBase ∣_ U) ≫ U.ι) x = (W.ι ≫ F.toBase) x :=
      congrArg (fun g : W.toScheme ⟶ X => g x) (morphismRestrict_ι F.toBase U)
    have heq := Scheme.Hom.residueFieldMap_congr
      (morphismRestrict_ι F.toBase U) x
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at heq
    have hWopen : IsIso (W.ι.residueFieldMap x) :=
      residueFieldMap_isIso_opens_inclusion W x
    have hF : IsIso (F.toBase.residueFieldMap (W.ι x)) := F.residueFieldIsomorphisms _
    have hc : IsIso (U.ι.residueFieldMap ((F.toBase ∣_ U) x) ≫
        (F.toBase ∣_ U).residueFieldMap x) := by
      rw [heq]
      exact IsIso.comp_isIso' (X.residueFieldCongr hx).isIso_hom
        (IsIso.comp_isIso' hF hWopen)
    exact IsIso.of_isIso_comp_left
      (U.ι.residueFieldMap ((F.toBase ∣_ U) x)) _
  have hIso {P Q : Scheme.{u}} (g : P ⟶ Q) [IsIso g] : UniversalHomeomorphism g :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have hq :
      Scheme.Spec.map (F.toBase.app U).op ≫ hU.isoSpec.inv =
        hW.isoSpec.inv ≫ (F.toBase ∣_ U) := by
    apply (cancel_mono hU.isoSpec.hom).1
    rw [Category.assoc, hU.isoSpec.inv_hom_id]
    have hn := Scheme.Opens.toSpecΓ_naturality F.toBase U
    change W.toSpecΓ ≫ Scheme.Spec.map (F.toBase.app U).op =
      (F.toBase ∣_ U) ≫ U.toSpecΓ at hn
    calc
      Scheme.Spec.map (F.toBase.app U).op =
          hW.isoSpec.inv ≫ W.toSpecΓ ≫
            Scheme.Spec.map (F.toBase.app U).op := by simp
      _ = hW.isoSpec.inv ≫ (F.toBase ∣_ U) ≫ U.toSpecΓ := by rw [hn]
      _ = hW.isoSpec.inv ≫ (F.toBase ∣_ U) ≫ hU.isoSpec.hom := by
        rw [← hU.isoSpec_hom]
  have hCompUH : UniversalHomeomorphism
      (Scheme.Spec.map (F.toBase.app U).op ≫ hU.isoSpec.inv) := by
    rw [hq]
    exact universalHomeomorphism_comp _ _ (hIso _) hBaseU
  have hq' : Scheme.Spec.map (F.toBase.app U).op =
      (Scheme.Spec.map (F.toBase.app U).op ≫ hU.isoSpec.inv) ≫ hU.isoSpec.hom := by
    simp
  refine ⟨?_, ?_⟩
  · rw [hq']
    exact universalHomeomorphism_comp _ _ hCompUH (hIso _)
  · intro x
    have hc : IsIso
        ((Scheme.Spec.map (F.toBase.app U).op ≫ hU.isoSpec.inv).residueFieldMap x) := by
      rw [hq, Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' (hresBaseU (hW.isoSpec.inv x))
        (residueFieldMap_isIso_of_isIso hW.isoSpec.inv x)
    rw [Scheme.residueFieldMap_comp] at hc
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (residueFieldMap_isIso_of_isIso hU.isoSpec.inv ((Scheme.Spec.map (F.toBase.app U).op) x)) hc

public noncomputable def relativeSeminormalization_competitorChartAlgebra
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (letI : Algebra (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U)) := (f.app U).hom.toAlgebra
     letI : Algebra (Γ(X, U)) (Γ(F.middle, F.toBase ⁻¹ᵁ U)) :=
       (F.toBase.app U).hom.toAlgebra
     letI : Algebra (Γ(F.middle, F.toBase ⁻¹ᵁ U)) (Γ(Y, f ⁻¹ᵁ U)) :=
       (relativeSeminormalization_competitorChartMap f F U hU).hom.toAlgebra
     Γ(F.middle, F.toBase ⁻¹ᵁ U) →ₐ[Γ(X, U)] Γ(Y, f ⁻¹ᵁ U)) := by
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  let C := Γ(F.middle, F.toBase ⁻¹ᵁ U)
  let φ := (relativeSeminormalization_competitorChartMap f F U hU).hom
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A C := (F.toBase.app U).hom.toAlgebra
  letI : Algebra C B := φ.toAlgebra
  have hcomp : algebraMap A B = (algebraMap C B).comp (algebraMap A C) := by
    have h := relativeSeminormalization_competitorChartMap_base f F U hU
    simpa only [RingHom.algebraMap_toAlgebra, Scheme.Hom.app_eq_appLE,
      CommRingCat.hom_comp, φ] using
      (congrArg CommRingCat.Hom.hom h).symm
  letI : IsScalarTower A C B := .of_algebraMap_eq' hcomp
  refine { toRingHom := φ, commutes' := ?_ }
  intro a
  exact congrArg (fun q : A →+* B => q a) hcomp.symm

public noncomputable def relativeSeminormalization_competitorChartFactorization
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    SubintegralFactorization
      (Scheme.Spec.map (CommRingCat.ofHom ((f.app U).hom)).op) := by
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  let C := Γ(F.middle, F.toBase ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A C := (F.toBase.app U).hom.toAlgebra
  let φ := (relativeSeminormalization_competitorChartMap f F U hU).hom
  letI : Algebra C B := φ.toAlgebra
  have hcomp : algebraMap A B = (algebraMap C B).comp (algebraMap A C) := by
    have h := relativeSeminormalization_competitorChartMap_base f F U hU
    simpa only [RingHom.algebraMap_toAlgebra, Scheme.Hom.app_eq_appLE,
      CommRingCat.hom_comp, φ] using
      (congrArg CommRingCat.Hom.hom h).symm
  letI : IsScalarTower A C B := .of_algebraMap_eq' hcomp
  have hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
    have heq : CommRingCat.ofHom (algebraMap A B) = f.app U := by
      apply CommRingCat.hom_ext
      rfl
    rw [heq]
    change IsDominant (AlgebraicGeometry.Spec.map (f.app U))
    exact affineChart_app_isDominant f U hU
  let hprops := relativeSeminormalization_competitorChart_subintegral f F U hU
  exact affineSubintegralFactorization_target A B C
    hdom
    (relativeSeminormalization_competitorChartAlgebra f F U hU)
    hprops.1 hprops.2

public noncomputable def relativeSeminormalization_competitorChartComparison
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (letI : Algebra (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U)) := (f.app U).hom.toAlgebra
    SubintegralFactorization.Hom
      (affineSubintegralFactorization (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U))
        (by
          have hmap : Scheme.Spec.map
              (CommRingCat.ofHom (algebraMap (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U)))).op =
              AlgebraicGeometry.Spec.map (f.app U) := rfl
          exact hmap ▸ affineChart_app_isDominant f U hU))
      (relativeSeminormalization_competitorChartFactorization f F U hU)) := by
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  let C := Γ(F.middle, F.toBase ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A C := (F.toBase.app U).hom.toAlgebra
  let φ := (relativeSeminormalization_competitorChartMap f F U hU).hom
  letI : Algebra C B := φ.toAlgebra
  have hcomp : algebraMap A B = (algebraMap C B).comp (algebraMap A C) := by
    have h := relativeSeminormalization_competitorChartMap_base f F U hU
    simpa only [RingHom.algebraMap_toAlgebra, Scheme.Hom.app_eq_appLE,
      CommRingCat.hom_comp, φ] using
      (congrArg CommRingCat.Hom.hom h).symm
  letI : IsScalarTower A C B := .of_algebraMap_eq' hcomp
  have hdom : IsDominant
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) := by
    have heq : CommRingCat.ofHom (algebraMap A B) = f.app U := by
      apply CommRingCat.hom_ext
      rfl
    rw [heq]
    change IsDominant (AlgebraicGeometry.Spec.map (f.app U))
    exact affineChart_app_isDominant f U hU
  let hprops := relativeSeminormalization_competitorChart_subintegral f F U hU
  exact affineSubintegralFactorization_hom A B C
    hdom
    (relativeSeminormalization_competitorChartAlgebra f F U hU)
    hprops.1 hprops.2

public noncomputable def relativeSeminormalization_competitorChartLift
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (letI : Algebra (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U)) := (f.app U).hom.toAlgebra
     Γ(F.middle, F.toBase ⁻¹ᵁ U) →+*
       relativeSeminormalization (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U))
         (affineChart_app_isDominant f U hU)) := by
  let A := Γ(X, U)
  let B := Γ(Y, f ⁻¹ᵁ U)
  let C := Γ(F.middle, F.toBase ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A C := (F.toBase.app U).hom.toAlgebra
  let φ := (relativeSeminormalization_competitorChartMap f F U hU).hom
  letI : Algebra C B := φ.toAlgebra
  have hcomp : algebraMap A B = (algebraMap C B).comp (algebraMap A C) := by
    have h := relativeSeminormalization_competitorChartMap_base f F U hU
    simpa only [RingHom.algebraMap_toAlgebra, Scheme.Hom.app_eq_appLE,
      CommRingCat.hom_comp, φ] using
      (congrArg CommRingCat.Hom.hom h).symm
  letI : IsScalarTower A C B := .of_algebraMap_eq' hcomp
  let hprops := relativeSeminormalization_competitorChart_subintegral f F U hU
  exact (affineSubintegralFactorization_lift A B C
    (affineChart_app_isDominant f U hU)
    (relativeSeminormalization_competitorChartAlgebra f F U hU)
    hprops.1 hprops.2).toRingHom

public theorem relativeSeminormalization_competitorChartLift_val
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f) (U : X.Opens)
    (hU : IsAffineOpen U) (c : Γ(F.middle, F.toBase ⁻¹ᵁ U)) :
    (letI : Algebra (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U)) := (f.app U).hom.toAlgebra
     ((relativeSeminormalization_competitorChartLift f F U hU c :
        relativeSeminormalization (Γ(X, U)) (Γ(Y, f ⁻¹ᵁ U))
          (affineChart_app_isDominant f U hU)) : Γ(Y, f ⁻¹ᵁ U)) =
      relativeSeminormalization_competitorChartAlgebra f F U hU c) := by
  rfl

public theorem relativeSeminormalization_competitorChartLift_natural
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [IsDominant f] (F : SubintegralFactorization f)
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    (letI : Algebra (Γ(X, U.1)) (Γ(Y, f ⁻¹ᵁ U.1)) := (f.app U.1).hom.toAlgebra
     letI : Algebra (Γ(X, V.1)) (Γ(Y, f ⁻¹ᵁ V.1)) := (f.app V.1).hom.toAlgebra
    let _E_U := relativeSeminormalization Γ(X, U.1)
      Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2)
    let _E_V := relativeSeminormalization Γ(X, V.1)
      Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)
    ((relativeSeminormalizationDiagram f).map i.op).hom.comp
        (relativeSeminormalization_competitorChartLift f F V.1 V.2) =
      (relativeSeminormalization_competitorChartLift f F U.1 U.2).comp
        (F.middle.presheaf.map (homOfLE (F.toBase.preimage_mono
          (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op).hom) := by
  let : Algebra Γ(X, U.1) (Γ(Y, f ⁻¹ᵁ U.1)) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(X, V.1) (Γ(Y, f ⁻¹ᵁ V.1)) := (f.app V.1).hom.toAlgebra
  let E_U := relativeSeminormalization Γ(X, U.1)
    Γ(Y, f ⁻¹ᵁ U.1) (affineChart_app_isDominant f U.1 U.2)
  let E_V := relativeSeminormalization Γ(X, V.1)
    Γ(Y, f ⁻¹ᵁ V.1) (affineChart_app_isDominant f V.1 V.2)
  let : Algebra Γ(X, V.1) (Γ(F.middle, F.toBase ⁻¹ᵁ V.1)) :=
    (F.toBase.app V.1).hom.toAlgebra
  let : Algebra Γ(X, U.1) (Γ(F.middle, F.toBase ⁻¹ᵁ U.1)) :=
    (F.toBase.app U.1).hom.toAlgebra
  let : Algebra (Γ(F.middle, F.toBase ⁻¹ᵁ V.1)) (Γ(Y, f ⁻¹ᵁ V.1)) :=
    (relativeSeminormalization_competitorChartMap f F V.1 V.2).hom.toAlgebra
  let : Algebra (Γ(F.middle, F.toBase ⁻¹ᵁ U.1)) (Γ(Y, f ⁻¹ᵁ U.1)) :=
    (relativeSeminormalization_competitorChartMap f F U.1 U.2).hom.toAlgebra
  dsimp
  ext c
  apply Subtype.ext
  have hpreU : f ⁻¹ᵁ U.1 ≤ F.toMiddle ⁻¹ᵁ (F.toBase ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, F.fac]
  have hpre : f ⁻¹ᵁ U.1 ≤ F.toMiddle ⁻¹ᵁ (F.toBase ⁻¹ᵁ V.1) :=
    hpreU.trans (F.toMiddle.preimage_mono
      (F.toBase.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.1.1)))
  have hpreV : f ⁻¹ᵁ V.1 ≤ F.toMiddle ⁻¹ᵁ (F.toBase ⁻¹ᵁ V.1) := by
    rw [← Scheme.Hom.comp_preimage, F.fac]
  have hnat :
      F.toMiddle.appLE (F.toBase ⁻¹ᵁ V.1) (f ⁻¹ᵁ U.1)
          hpre =
        F.toMiddle.appLE (F.toBase ⁻¹ᵁ V.1) (f ⁻¹ᵁ V.1)
          hpreV ≫
          Y.presheaf.map (homOfLE (f.preimage_mono
            (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op := by
    symm
    exact Scheme.Hom.appLE_map _ _ _
  have hnat' :
      F.middle.presheaf.map (homOfLE (F.toBase.preimage_mono
        (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op ≫
        F.toMiddle.appLE (F.toBase ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
          hpreU =
      F.toMiddle.appLE (F.toBase ⁻¹ᵁ V.1) (f ⁻¹ᵁ U.1)
        hpre :=
    Scheme.Hom.map_appLE _ _ _
  have h := congrArg CommRingCat.Hom.hom (hnat.symm.trans hnat'.symm)
  dsimp only [relativeSeminormalizationDiagram, E_U, E_V] at h ⊢
  change ((Y.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op).hom
      (relativeSeminormalization_competitorChartAlgebra f F V.1 V.2 c)) =
    relativeSeminormalization_competitorChartAlgebra f F U.1 U.2
      ((F.middle.presheaf.map (homOfLE (F.toBase.preimage_mono
        (Scheme.AffineZariskiSite.toOpens_mono i.1.1))).op).hom c)
  exact congrArg (fun q : Γ(F.middle, F.toBase ⁻¹ᵁ V.1) →+*
      Γ(Y, f ⁻¹ᵁ U.1) => q c) h

end AlgebraicGeometry

end
