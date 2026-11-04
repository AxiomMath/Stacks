module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Morphisms.UnitPushforwardFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsolatedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HigherDirectImageVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# Condition (1) of Stacks 0E8A for a morphism of schemes

Let `f : Z ⟶ W` be a quasi-compact and quasi-separated morphism of schemes of the site, read as a
morphism of algebraic spaces. If `𝒪_W ⟶ f_*𝒪_Z` is an isomorphism of `𝒪_W`-modules on the Zariski
site, then so is the structure map `𝒪_W ⟶ f_*𝒪_Z` of Stacks 03G8 on the small étale site. On an
étale chart `V ⟶ W` the structure map is pullback of functions along `Z ×_W V ⟶ V` (Stacks 03G8,
part (2)), and this is bijective by flat base change. Likewise, over an affine `W`, the vanishing
of `R¹f_*𝒪_Z` on the Zariski site gives its vanishing on the small étale site (Stacks 071Z, 03DW,
01XK).

The local instance `HasDerivedCategory.standard` in the second half is only there to consume the
`ℤ`-indexed statements of Stacks 01XK on base; no statement here involves a derived category.

## Main results

* `AlgebraicGeometry.C1590Private.isIso_structureSharp_schemeSpaceMap`: the structure map.
* `AlgebraicGeometry.C1590Private.isZero_firstDirectImage_schemeSpaceMap`: the vanishing of
  `R¹f_*𝒪`, from the affine case over the affine opens of the target.
* `AlgebraicGeometry.C1590Private.isEtaleCovering_yoneda_map`: jointly surjective étale
  morphisms of schemes give an étale covering of the represented algebraic space.
* `AlgebraicGeometry.C1590Private.isZero_firstDirectImage_schemeSpaceMap_of_isAffine`: the
  vanishing of `R¹f_*𝒪`, over an affine target.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme-valued functor on the big site preserves pullbacks. -/
private instance preservesLimitsOfShape_walkingCospan_toScheme' {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS

/-- **The structure map of a morphism of schemes, on the small étale site.** If `f : Z ⟶ W` is a
quasi-compact, quasi-separated morphism of schemes of the site with `𝒪_W ⟶ f_*𝒪_Z` an
isomorphism, then the structure map of Stacks 03G8 of `f`, read as a morphism of algebraic
spaces, is an isomorphism. -/
theorem isIso_structureSharp_schemeSpaceMap {Z W : BigFppfOver B S hS} (f : Z ⟶ W)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f)]
    (hO : IsIso (Scheme.Modules.unitToPushforwardUnit ((BigFppfOver.toScheme B S hS).map f))) :
    IsIso (Space.structureSharp B S hS (schemeSpaceMap f)) := by
  have hf : yoneda.relativelyRepresentable (schemeSpaceMap f).hom :=
    Space.relativelyRepresentable_yoneda_map B S hS f
  let := Space.isContinuous_smallBaseChange B S hS (schemeSpaceMap f) hf
  suffices h : IsIso (Space.cartesianProjectionSharp B S hS (schemeSpaceMap f) hf) by
    have : IsIso (Space.structureSharp B S hS (schemeSpaceMap f) ≫
        Space.chartProjectionSharpDirectImage B S hS (schemeSpaceMap f) hf) := by
      rwa [Space.structureSharp_comp_chartProjectionSharpDirectImage B S hS (schemeSpaceMap f) hf]
    exact IsIso.of_isIso_comp_right (Space.structureSharp B S hS (schemeSpaceMap f))
      (Space.chartProjectionSharpDirectImage B S hS (schemeSpaceMap f) hf)
  refine (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).1 ?_
  have hV : ∀ V, IsIso (((sheafToPresheaf _ _).map
      (Space.cartesianProjectionSharp B S hS (schemeSpaceMap f) hf)).app V) := by
    intro V
    show IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.unop.1.hom)).op))
    suffices h : IsIso (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hf.snd V.unop.1.hom)).op) from Functor.map_isIso _ _
    rw [Scheme.Γ_map_op]
    obtain ⟨v, hv⟩ : ∃ v : V.unop.1.left ⟶ W, yoneda.map v = V.unop.1.hom :=
      ⟨Yoneda.fullyFaithful.preimage V.unop.1.hom, Yoneda.fullyFaithful.map_preimage _⟩
    have hsq : IsPullback (hf.fst' V.unop.1.hom) (hf.snd V.unop.1.hom) f v := by
      rw [← hv]
      exact hf.isPullback_of_map v
    have hve : Etale ((BigFppfOver.toScheme B S hS).map v) :=
      (Space.presheaf_yoneda_map_etale_iff B S hS v).1 (hv ▸ V.unop.2)
    have : Flat ((BigFppfOver.toScheme B S hS).map v) := inferInstance
    exact Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit _
      (Scheme.Hom.isIso_unitToPushforwardObjUnit_of_isPullback _
        (hsq.map (BigFppfOver.toScheme B S hS)) hO) ⊤
  exact NatIso.isIso_of_isIso_app _

section Higher

attribute [local instance 2000] HasDerivedCategory.standard

variable {B} (hZ : B.Contains integerBase)

/-- **The vanishing of `R¹f_*𝒪` for a morphism of schemes over an affine scheme, on the small
étale site.** If `f : Z ⟶ W` is a quasi-compact, quasi-separated morphism of schemes of the site
with `W` affine and `R¹f_*𝒪_Z = 0` on the Zariski site, then `R¹f_*𝒪_Z = 0` on the small étale
site, `f` being read as a morphism of algebraic spaces.

The identity chart of `W` is a surjective affine chart, over which the base change of `f` is a
scheme `T` isomorphic to `Z` over `W`. By Stacks 071Z, 0720 and the Leray collapse
(`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_chart`), it suffices
that the Zariski cohomology `H¹(T, 𝒪_T)` vanishes (Stacks 03DW). Over the affine `W` this is
`Γ(W, R¹(T ⟶ W)_*𝒪_T)` (Stacks 01XK), which vanishes by flat base change along the
isomorphism `T ≅ Z`. -/
theorem isZero_firstDirectImage_schemeSpaceMap_of_isAffine {Z W : BigFppfOver B integerBase hZ}
    (f : Z ⟶ W) [IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj W)]
    [QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map f)]
    [QuasiSeparated ((BigFppfOver.toScheme B integerBase hZ).map f)]
    (hR : IsZero (((Scheme.Modules.pushforward
        ((BigFppfOver.toScheme B integerBase hZ).map f)).rightDerived 1).obj
      (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))) :
    IsZero (firstDirectImage B hZ (schemeSpaceMap f)) := by
  have hρ : yoneda.relativelyRepresentable (schemeSpaceMap f).hom :=
    Space.relativelyRepresentable_yoneda_map B integerBase hZ f
  let A := Space.idEtaleChart B integerBase hZ W
  have hA : IsAffine (Space.chartScheme A) := by
    rw [Space.chartScheme_idEtaleChart]
    infer_instance
  have hsurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B integerBase hZ)).presheaf A.1.hom :=
    presheaf_id_of_iso B integerBase hZ _ (fun _ _ g hg => by
      have : IsIso g := hg
      show Surjective ((BigFppfOver.toScheme B integerBase hZ).map g)
      infer_instance) W
  have hqc := Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ f inferInstance
  have hqs := (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ f).2 inferInstance
  let T := (Space.smallBaseChange B integerBase hZ (schemeSpaceMap f) hρ).obj A
  -- the base-changed chart is `Z` over `W`
  have hsq := hρ.isPullback_of_map (𝟙 W)
  rw [CategoryTheory.Functor.map_id] at hsq
  have hsq' := hsq.map (BigFppfOver.toScheme B integerBase hZ)
  rw [CategoryTheory.Functor.map_id] at hsq'
  let g := (BigFppfOver.toScheme B integerBase hZ).map (hρ.snd (𝟙 (yoneda.obj W)))
  have : QuasiCompact g := MorphismProperty.of_isPullback hsq' inferInstance
  have : QuasiSeparated g := MorphismProperty.of_isPullback hsq' inferInstance
  have hRg : IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (SheafOfModules.unit (Space.chartScheme T).ringCatSheaf)) :=
    open Stacks.AlgebraicGeometry in
    FlatBaseChangeDerived.isZero_rightDerived_pushforward_unit_of_isPullback hsq' 1 hR
  have hH : IsZero (Hgroup (Space.chartScheme T).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (Space.chartScheme T).ringCatSheaf)) :=
    open Stacks.AlgebraicGeometry in
    (Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
      _ _ 1).mp
      (@TopDegreeBaseChange.isZero_cohomology_of_isZero_rightDerivedPlus_pushforward
        _ _ g _ _ _ (1 : ℕ) _ (AffineQcohPushforward.isQuasicoherent_unit _)
        ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).1 hRg))
  let M := Space.structureSheafModule B integerBase hZ (schemeSpace Z)
  have hM : M.IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
  have e : Space.restrictToChart B integerBase hZ (schemeSpace Z).2 M T ≅
      SheafOfModules.unit (Space.chartScheme T).ringCatSheaf :=
    Space.restrictToChartIsoRestrictToChartScheme B integerBase hZ (schemeSpace Z).2 M T ≪≫
      Space.restrictToChartSchemeUnitIso B integerBase hZ _ (schemeSpace Z).2 T
  have := Space.hasInjectiveResolutions_modules B integerBase hZ (schemeSpace Z).1
    (schemeSpace Z).2
  exact Space.isZero_rightDerived_modulePushforward_of_isZero_chart B integerBase hZ
    (schemeSpaceMap f) hρ hqc hqs A hA hsurj M hM 1 one_pos
    (Space.isZero_rightDerived_evaluation_chartSpace_of_isZero_hgroup_restrictToChart T M hM 1
      one_pos (hH.of_iso ((Hfunctor (Space.chartScheme T).ringCatSheaf ⊤ 1).mapIso e)))

end Higher

section Covering

/-- **A jointly surjective family of étale morphisms of schemes of the site is an étale covering of
the represented algebraic space.** -/
theorem isEtaleCovering_yoneda_map {W : BigFppfOver B S hS} {ι : Type*}
    {Wj : ι → BigFppfOver B S hS} (g : ∀ j, Wj j ⟶ W)
    (hg : ∀ j, Etale ((BigFppfOver.toScheme B S hS).map (g j)))
    (hsurj : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ j, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g j))) :
    Space.IsEtaleCovering B S hS (fun j => yoneda.obj (Wj j)) (fun j => yoneda.map (g j)) where
  target_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS W
  source_isAlgebraicSpace j := isAlgebraicSpace_yoneda B S hS (Wj j)
  etale j := Space.isEtale_of_presheaf_etale B S hS
    ((Space.presheaf_yoneda_map_etale_iff B S hS (g j)).2 (hg j))
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨j, y, hy⟩ := hsurj (Space.pointsToScheme B S hS W x)
    obtain ⟨w, rfl⟩ := Space.surjective_pointsToScheme B S hS (Wj j) y
    refine Set.mem_iUnion.2 ⟨j, w, Space.injective_pointsToScheme B S hS W ?_⟩
    rw [Space.pointsToScheme_pointsMap_yoneda, hy]

end Covering

section HigherGeneral

attribute [local instance 2000] HasDerivedCategory.standard

variable {B} (hZ : B.Contains integerBase)

/-- **The vanishing of `R¹f_*𝒪` for a morphism of schemes, on the small étale site.** If
`f : Z ⟶ W` is a quasi-compact, quasi-separated morphism of schemes of the site with
`R¹f_*𝒪_Z = 0` on the Zariski site, then `R¹f_*𝒪_Z = 0` on the small étale site. The affine
opens of `W` form an étale covering of the represented algebraic space; over each the claim is
`AlgebraicGeometry.C1590Private.isZero_firstDirectImage_schemeSpaceMap_of_isAffine`, the hypothesis
passing to the restriction by flat base change; and the vanishing is étale local on the target
(`AlgebraicGeometry.C1590Private.isZero_firstDirectImage_of_isPullback_etale`). -/
theorem isZero_firstDirectImage_schemeSpaceMap {Z W : BigFppfOver B integerBase hZ}
    (f : Z ⟶ W) [QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map f)]
    [QuasiSeparated ((BigFppfOver.toScheme B integerBase hZ).map f)]
    (hR : IsZero (((Scheme.Modules.pushforward
        ((BigFppfOver.toScheme B integerBase hZ).map f)).rightDerived 1).obj
      (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj Z).ringCatSheaf))) :
    IsZero (firstDirectImage B hZ (schemeSpaceMap f)) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  let Wj : (T.obj W).affineOpens → BigFppfOver B integerBase hZ := fun j =>
    BigFppfOver.siteObjectOver B integerBase hZ W (B.contains_of_mono j.1.ι W.left.2) j.1.ι
  let gj : ∀ j, Wj j ⟶ W := fun j =>
    BigFppfOver.siteMapOver B integerBase hZ W (B.contains_of_mono j.1.ι W.left.2) j.1.ι
  have hcov := isEtaleCovering_yoneda_map B integerBase hZ gj
    (fun j => by
      show Etale j.1.ι
      infer_instance)
    (fun w => by
      obtain ⟨_, ⟨j, hja, rfl⟩, hwj, -⟩ :=
        (T.obj W).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
      exact ⟨⟨j, hja⟩, ⟨⟨w, hwj⟩, rfl⟩⟩)
  refine isZero_firstDirectImage_of_isPullback_etale (schemeSpaceMap f)
    (W := fun j => schemeSpace (Wj j)) (fun j => schemeSpaceMap (gj j))
    (A' := fun j => schemeSpace (pullback f (gj j)))
    (fun j => schemeSpaceMap (pullback.fst f (gj j)))
    (fun j => schemeSpaceMap (pullback.snd f (gj j))) hcov (fun j => ?_) (fun j => ?_)
  · refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ ?_)
      ((IsPullback.of_hasPullback f (gj j)).map yoneda)
    show yoneda.map (pullback.fst f (gj j)) ≫ yoneda.map f =
      yoneda.map (pullback.snd f (gj j)) ≫ yoneda.map (gj j)
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  · have hsq := (IsPullback.of_hasPullback f (gj j)).map T
    have : IsAffine (T.obj (Wj j)) := j.2
    have : Flat (T.map (gj j)) := by
      show Flat j.1.ι
      infer_instance
    have : QuasiCompact (T.map (pullback.snd f (gj j))) :=
      MorphismProperty.of_isPullback hsq inferInstance
    have : QuasiSeparated (T.map (pullback.snd f (gj j))) :=
      MorphismProperty.of_isPullback hsq inferInstance
    exact isZero_firstDirectImage_schemeSpaceMap_of_isAffine hZ (pullback.snd f (gj j))
      (open Stacks.AlgebraicGeometry in
        FlatBaseChangeDerived.isZero_rightDerived_pushforward_unit_of_isPullback hsq 1 hR)

end HigherGeneral

end AlgebraicGeometry.C1590Private

end
