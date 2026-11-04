module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.C1764Prereq.AffineDualitySection
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardDegreeOne
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre

/-!
# A summand `𝒪[-1]` of `Rf_*𝒪_X` over an affine étale neighbourhood

Let `f : X → S` be a prestable family of curves and `s ∈ S` a point whose fibre `X_s` has
positive genus `g`. Étale locally on `S`, `Rf_*𝒪_X ≅ 𝒪_S ⊕ 𝒪_S^{⊕ m}[-1]` (Stacks 0E1J, in the
form `AlgebraicGeometry.Space.exists_coversTop_derivedModulePushforward_iso_biprod`), and the
rank `m` of the summand in degree one is the rank of `R¹f_*𝒪_X` at `s`, the genus `g ≠ 0`.
Shrinking the étale chart to an affine open, we get an affine scheme `T`, an étale `c : T ⟶ S`
and `t ∈ T` over `s` such that `Lc^*Rf_*𝒪_X` has a summand `𝒪_T[-1]`. Since the formation of
`Rf_*𝒪_X` commutes with base change (Stacks 0CTM), `Rf'_*𝒪_{X_T}` has the summand `𝒪_T[-1]` for
the base change `f' : X_T → T`, which after shifting is a split epimorphism
`Rf'_*(𝒪_{X_T}[1]) ⟶ 𝒪_T`.

This is the first step of the genus one case of the proof of [Stacks, Tag 0E6Y].

## Main results

* `AlgebraicGeometry.C1764Prereq.exists_etale_isSplitEpi_of_genus_ne_zero`: the affine étale
  neighbourhood `T` with the split epimorphism `Rf'_*(𝒪_{X_T}[1]) ⟶ 𝒪_T`.
* `AlgebraicGeometry.C1764Prereq.exists_affine_etale_iso_biprod`: Stacks 0E1J on an affine étale
  neighbourhood of a point.
* `AlgebraicGeometry.C1764Prereq.ne_zero_of_iso_biprod_single_free`: the summand in degree one
  has the rank of `H¹`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace C1764Prereq

section Generic


variable {S : Scheme.{u}} {hS : B.Contains S}

/-- **The summand in degree one of `Lg^*E ≅ 𝒪 ⊕ 𝒪^{⊕ m}[-1]` is nonzero when `H¹(E)` has nonzero
rank at the image point.** If `E` has no cohomology above degree one, `H¹(E)` is finite locally
free with rank `r ≠ 0` at the image of `z`, then `m ≠ 0`: in the top degree
`H¹(Lg^*E) ≅ g^*H¹(E)`, of rank `r` at `z`, while `H¹(𝒪 ⊕ 𝒪^{⊕ 0}[-1]) = 0`. -/
theorem ne_zero_of_iso_biprod_single_free {Y Z : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)))
    (hE : E.IsLE 1)
    (hR : SheafOfModules.IsFiniteLocallyFreeOnSite
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) 1).obj E))
    (hRq : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) 1).obj
          E).IsQuasicoherentOnSite)
    {r : ℕ} (hr : r ≠ 0) (g : Z ⟶ Y) (z : Space.points B S hS Z.1)
    (hz : Space.pointsMap B S hS Z.1 g.hom z ∈
      Space.rankLocus ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) 1).obj E) r)
    {m : ℕ}
    (e : (Space.smallEtaleDerivedModulePullback B S hS g).obj E ≅
      (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Z)) ⊞
        (DerivedCategory.singleFunctor _ 1).obj
          (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
            (ULift.{u} (Fin m)))) :
    m ≠ 0 := by
  rintro rfl
  obtain ⟨e₁⟩ := Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE g E 1 hE
  have hz' : z ∈ Space.rankLocus ((Space.modulePullback B S hS g).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) 1).obj E)) r := by
    rwa [← Space.preimage_rankLocus_modulePullback g hR hRq r]
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Z)) 1
  have hfree : IsZero (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
      (ULift.{u} (Fin 0))) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)
  have hzero : IsZero (H.obj ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Z)) ⊞
        (DerivedCategory.singleFunctor _ 1).obj
          (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
            (ULift.{u} (Fin 0))))) := by
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Z)) 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Z))
    let P := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Z)) 1).obj
        (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
          (ULift.{u} (Fin 0)))
    have := preservesBinaryBiproduct_of_preservesBiproduct H A P
    exact IsZero.of_iso ((biprod_isZero_iff _ _).2
      ⟨DerivedCategory.isZero_of_isLE A 0 1 (by omega),
        H.map_isZero ((DerivedCategory.singleFunctor _ 1).map_isZero hfree)⟩) (H.mapBiprod A P)
  have h0 := Space.mem_rankLocus_of_isFiniteLocallyFreeOfRank
    (Space.isFiniteLocallyFreeOfRank_free_ulift_fin (Z := Z) 0) z
  rw [← Space.rankLocus_congr ((hzero.of_iso (e₁.symm ≪≫ H.mapIso e)).iso hfree) 0] at h0
  exact hr (Space.eq_of_mem_rankLocus_of_mem_rankLocus hz' h0)

/-- **An affine Zariski open of an étale chart through a point.** For an étale chart `U` of an
algebraic space and a point `w` of `U`, there are an affine open `O` of the scheme of `U` and a
point of the chart cut out by `O` mapping to `w`. -/
theorem exists_isAffineOpen_openChart_point {F : AlgebraicSpaces B S hS}
    (U : Space.SmallEtale B S hS F.1)
    (w : Space.points B S hS (yoneda.obj ((Space.SmallEtale.toOver B S hS F.1).obj U))) :
    ∃ (O : ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS F.1).obj U)).Opens)
      (w' : Space.points B S hS (yoneda.obj ((Space.SmallEtale.toOver B S hS F.1).obj
        (Space.openChart B S hS F.1 U O)))),
      IsAffineOpen O ∧
        Space.pointsMap B S hS _
          (Space.chartMap B S hS F (Space.openChartInclusion B S hS F.1 U O)).hom w' = w := by
  obtain ⟨O, hO, hwO, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj
      ((Space.SmallEtale.toOver B S hS F.1).obj U)).Opens))
    (Set.mem_univ (Space.pointsToScheme B S hS _ w))
  obtain ⟨w', hw'⟩ := Space.surjective_pointsToScheme B S hS
    ((Space.SmallEtale.toOver B S hS F.1).obj (Space.openChart B S hS F.1 U O)) ⟨_, hwO⟩
  refine ⟨O, w', hO, Space.injective_pointsToScheme B S hS _ ?_⟩
  have h := Space.pointsToScheme_pointsMap_yoneda B S hS
    ((Space.SmallEtale.toOver B S hS F.1).map (Space.openChartInclusion B S hS F.1 U O)) w'
  rwa [Space.toScheme_map_toOver_map_openChartInclusion, hw'] at h

/-- **Freeness in degree one restricts to a Zariski open chart.** If the derived pullback of `P`
to an étale chart `U` is free of rank `n` placed in degree one, so is its pullback to the chart
cut out by an open of `U`. -/
theorem exists_iso_single_free_openChart {F : AlgebraicSpaces B S hS}
    (U : Space.SmallEtale B S hS F.1)
    (O : ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS F.1).obj U)).Opens)
    {P : DerivedCategory (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS F))}
    {n : ℤ}
    (hP : Space.IsFreeOfRankInDegree
      ((Space.smallEtaleDerivedModulePullback B S hS (Space.chartToSpace B S hS F U)).obj P) 1 n) :
    ∃ m : ℕ, (m : ℤ) = n ∧ Nonempty ((Space.smallEtaleDerivedModulePullback B S hS
        (Space.chartToSpace B S hS F (Space.openChart B S hS F.1 U O))).obj P ≅
      (DerivedCategory.singleFunctor _ 1).obj (SheafOfModules.free
        (R := Space.ringedToposStructureRingSheaf B S hS
          (Space.chartSpace B S hS F (Space.openChart B S hS F.1 U O))) (ULift.{u} (Fin m)))) := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    hP.derivedPullback (Space.chartMap B S hS F (Space.openChartInclusion B S hS F.1 U O))
  exact ⟨m, hm, ⟨((Space.smallEtaleDerivedModulePullbackCongr B S hS
      (Space.chartMap_comp_chartToSpace B S hS F
        (Space.openChartInclusion B S hS F.1 U O)).symm).app P ≪≫
    ((Space.smallEtaleDerivedModulePullbackCompIso B S hS _ _).app P).symm) ≪≫ e⟩⟩

/-- **Points through a Zariski open of an étale chart of an étale chart.** The composite chart map
on points factors through the open inclusion and the two chart maps. -/
private theorem pointsMap_chartToSpace_comp_openChart {F : AlgebraicSpaces B S hS}
    (V : Space.SmallEtale B S hS F.1) (U : Space.SmallEtale B S hS (Space.chartSpace B S hS F V).1)
    (O : ((BigFppfOver.toScheme B S hS).obj
      ((Space.SmallEtale.toOver B S hS (Space.chartSpace B S hS F V).1).obj U)).Opens)
    (w' : Space.points B S hS (yoneda.obj ((Space.SmallEtale.toOver B S hS
      (Space.chartSpace B S hS F V).1).obj
        (Space.openChart B S hS (Space.chartSpace B S hS F V).1 U O)))) :
    Space.pointsMap B S hS _ (Space.chartToSpace B S hS (Space.chartSpace B S hS F V)
        (Space.openChart B S hS (Space.chartSpace B S hS F V).1 U O) ≫
          Space.chartToSpace B S hS F V).hom w' =
      Space.pointsMap B S hS _ (Space.chartToSpace B S hS F V).hom
        (Space.pointsMap B S hS _ (Space.chartToSpace B S hS _ U).hom
          (Space.pointsMap B S hS _ (Space.chartMap B S hS _
            (Space.openChartInclusion B S hS (Space.chartSpace B S hS F V).1 U O)).hom w')) := by
  have h₁ := Space.chartMap_comp_chartToSpace B S hS (Space.chartSpace B S hS F V)
    (Space.openChartInclusion B S hS (Space.chartSpace B S hS F V).1 U O)
  have h₂ := congrFun (Space.pointsMap_comp B S hS _
    (Space.chartToSpace B S hS (Space.chartSpace B S hS F V)
      (Space.openChart B S hS (Space.chartSpace B S hS F V).1 U O)).hom
    (Space.chartToSpace B S hS F V).hom) w'
  rw [← h₁] at h₂
  exact h₂.trans (congrArg _ (congrFun (Space.pointsMap_comp B S hS _ _ _) w'))

/-- **`𝒪[0] ⊕ 𝒪^{⊕ m}[-1]` splits off `𝒪[-1]`** for `m ≥ 1`: the second projection followed by a
coordinate projection of the free module. -/
theorem exists_isSplitEpi_biprod_single_free {Z : AlgebraicSpaces B S hS} (m : ℕ) (hm : 1 ≤ m) :
    ∃ π : (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Z)) ⊞
        (DerivedCategory.singleFunctor _ 1).obj
          (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
            (ULift.{u} (Fin m))) ⟶
        (DerivedCategory.singleFunctor _ 1).obj
          (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Z)),
      IsSplitEpi π := by
  classical
  let i : ULift.{u} (Fin m) := ⟨⟨0, hm⟩⟩
  let r : SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B S hS Z)
      (ULift.{u} (Fin m)) ⟶ SheafOfModules.unit _ :=
    Sigma.desc fun j => if j = i then 𝟙 _ else 0
  have hr : SheafOfModules.ιFree i ≫ r = 𝟙 _ := (Sigma.ι_desc _ _).trans (if_pos rfl)
  have : IsSplitEpi r := IsSplitEpi.mk' ⟨_, hr⟩
  exact ⟨biprod.snd ≫ (DerivedCategory.singleFunctor _ 1).map r, inferInstance⟩

/-- A split epimorphism between two isomorphisms is a split epimorphism. -/
private theorem isSplitEpi_iso_comp_comp_iso {C : Type*} [Category C] {P Q R T : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ T) (ha : IsIso a) (hb : IsSplitEpi b) (hc : IsIso c) :
    IsSplitEpi (a ≫ b ≫ c) := by
  have := hb
  infer_instance

/-- **Shifting a summand `𝒪_Y[-1]`.** A split epimorphism `Rf_*𝒪_X ⟶ 𝒪_Y[-1]` gives a split
epimorphism `Rf_*(𝒪_X[1]) ⟶ 𝒪_Y`, through `Rf_*(𝒪_X[1]) ≅ (Rf_*𝒪_X)[1]`. -/
theorem exists_isSplitEpi_derivedModulePushforward_structureSheafShifted
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (π : (Space.derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS X))) ⟶
      (DerivedCategory.singleFunctor _ 1).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B S hS Y)))
    (hπ : IsSplitEpi π) :
    ∃ π' : (Space.derivedModulePushforward B S hS f).obj (structureSheafShifted X).obj ⟶
        (Space.derivedStructureSheaf B S hS Y.1 Y.2).obj, IsSplitEpi π' := by
  let e₁ : (structureSheafShifted X).obj ≅
      ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X.1 X.2) 0).obj
        (SheafOfModules.unit _))⟦(1 : ℤ)⟧ :=
    (((DerivedCategory.singleFunctors (Space.Modules.{u, u} B S hS X.1 X.2)).shiftIso 1 (-1) 0
      (by norm_num)).app _).symm
  let e₂ := (Space.derivedModulePushforward B S hS f).mapIso e₁ ≪≫
    ((Space.derivedModulePushforward B S hS f).commShiftIso (1 : ℤ)).app _
  let e₃ : ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS Y.1 Y.2) 1).obj
        (SheafOfModules.unit _))⟦(1 : ℤ)⟧ ≅ (Space.derivedStructureSheaf B S hS Y.1 Y.2).obj :=
    ((DerivedCategory.singleFunctors (Space.Modules.{u, u} B S hS Y.1 Y.2)).shiftIso 1 0 1
      (by norm_num)).app _
  exact ⟨e₂.hom ≫ (shiftFunctor _ (1 : ℤ)).map π ≫ e₃.hom,
    isSplitEpi_iso_comp_comp_iso _ _ _ (Iso.isIso_hom e₂)
      (@instIsSplitEpiMap _ _ _ _ _ _ π hπ (shiftFunctor _ (1 : ℤ))) (Iso.isIso_hom e₃)⟩

end Generic

/-- Three isomorphisms followed by a split epimorphism form a split epimorphism. -/
private theorem isSplitEpi_comp_of_isIso' {C : Type*} [Category C] {P Q R T U : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ T) (d : T ⟶ U) (ha : IsIso a) (hb : IsIso b) (hc : IsIso c)
    (hd : IsSplitEpi d) : IsSplitEpi (a ≫ b ≫ c ≫ d) := by
  have := hd
  infer_instance

/-- An additive functor carries a biproduct to the biproduct of the images, read through given
isomorphisms of the images. -/
private def mapBiprodIso' {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive] (A P : C) {A' P' : D}
    (u : F.obj A ≅ A') (v : F.obj P ≅ P') : F.obj (A ⊞ P) ≅ A' ⊞ P' :=
  haveI := preservesBinaryBiproduct_of_preservesBiproduct F A P
  F.mapBiprod A P ≪≫ biprod.mapIso u v

/-- **Stacks 0E1J, étale locally around a point, on an affine chart.** For a prestable family
`f : X → S` and `s ∈ S` there are an affine scheme `T`, an étale `c : T ⟶ S`, a point `t ∈ T` over
`s` and `m : ℕ` with `Lc^*Rf_*𝒪_X ≅ 𝒪_T ⊕ 𝒪_T^{⊕ m}[-1]`. -/
theorem exists_affine_etale_iso_biprod {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    ∃ (T : BigFppfOver B integerBase hZ) (c : T ⟶ X.base)
      (t : (BigFppfOver.toScheme B integerBase hZ).obj T) (m : ℕ),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
      Space.IsEtale B integerBase hZ (schemeSpaceMap c).hom ∧
      (BigFppfOver.toScheme B integerBase hZ).map c t = s ∧
      Nonempty ((Space.smallEtaleDerivedModulePullback B integerBase hZ (schemeSpaceMap c)).obj
          ((Space.derivedModulePushforward B integerBase hZ X.toBase).obj
            ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
              (Space.ringedToposStructureRingSheaf B integerBase hZ X.total)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ
              (schemeSpace T))) ⊞
          (DerivedCategory.singleFunctor _ 1).obj
            (SheafOfModules.free (R := Space.ringedToposStructureRingSheaf B integerBase hZ
              (schemeSpace T)) (ULift.{u} (Fin m)))) := by
  obtain ⟨ι, V, hV, hP⟩ := Space.exists_coversTop_derivedModulePushforward_iso_biprod X.toBase
    X.proper X.flat X.finitePresentation
    (X.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX.2)
    (fun p j hj =>
      X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct p j hj)
  obtain ⟨x₀, hx₀⟩ := Space.surjective_pointsToScheme B integerBase hZ X.base s
  obtain ⟨i, v, hv⟩ := Space.SmallEtale.exists_mem_range_of_coversTop B integerBase hZ
    (schemeSpace X.base).2 hV x₀
  obtain ⟨P, ⟨e⟩, κ, W, hW, hfree⟩ := hP i
  obtain ⟨k, w, hw⟩ := Space.SmallEtale.exists_mem_range_of_coversTop B integerBase hZ
    (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V i)).2 hW v
  obtain ⟨n, hn⟩ := hfree k
  obtain ⟨O, w', hO, hw'⟩ := exists_isAffineOpen_openChart_point (W k) w
  obtain ⟨m, -, ⟨e'⟩⟩ := exists_iso_single_free_openChart (W k) O hn
  let C := Space.chartSpace B integerBase hZ (schemeSpace X.base) (V i)
  let W'' := Space.openChart B integerBase hZ C.1 (W k) O
  let ctot : Space.chartSpace B integerBase hZ C W'' ⟶ schemeSpace X.base :=
    Space.chartToSpace B integerBase hZ C W'' ≫
      Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V i)
  let T := (Space.SmallEtale.toOver B integerBase hZ C.1).obj W''
  let c : T ⟶ X.base := Yoneda.fullyFaithful.preimage ctot.hom
  have hc' : yoneda.map c = ctot.hom := Yoneda.fullyFaithful.map_preimage ctot.hom
  have hc : schemeSpaceMap c = ctot := ObjectProperty.hom_ext _ hc'
  refine ⟨T, c, Space.pointsToScheme B integerBase hZ T w', m, hO, ?_, ?_, ?_⟩
  · rw [hc]
    exact Space.isEtale_comp B integerBase hZ
      (Space.isEtale_chartToSpace B integerBase hZ C W'')
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V i))
  · obtain ⟨v, rfl⟩ := hv
    obtain ⟨w, rfl⟩ := hw
    rw [← hx₀, ← Space.pointsToScheme_pointsMap_yoneda, hc']
    congr 1
    rw [← hw']
    exact pointsMap_chartToSpace_comp_openChart (V i) (W k) O w'
  · let L := Space.smallEtaleDerivedModulePullback B integerBase hZ
      (Space.chartToSpace B integerBase hZ C W'')
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B integerBase hZ C)) 0).obj
        (SheafOfModules.unit (Space.ringedToposStructureRingSheaf B integerBase hZ C))
    let u₀ : L.obj A ≅ (DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Space.ringedToposStructureRingSheaf B integerBase hZ
          (Space.chartSpace B integerBase hZ C W''))) 0).obj (SheafOfModules.unit _) :=
      Space.smallEtaleDerivedModulePullbackUnitIso (Space.chartToSpace B integerBase hZ C W'')
    exact ⟨(Space.smallEtaleDerivedModulePullbackCongr B integerBase hZ hc).app _ ≪≫
      ((Space.smallEtaleDerivedModulePullbackCompIso B integerBase hZ _ _).app _).symm ≪≫
      L.mapIso e ≪≫ mapBiprodIso' L A P u₀ e'⟩

/-- **Stacks 0E1J around a fibre of positive genus, as a split epimorphism.** For a prestable
family `f : X → S` and a point `s` whose fibre has positive genus, there are an affine scheme `T`,
an étale `c : T ⟶ S` and a point `t ∈ T` over `s` such that, for the base change
`f' : X_T → T`, there is a split epimorphism `Rf'_*(𝒪_{X_T}[1]) ⟶ 𝒪_T`: étale locally
`Rf_*𝒪_X ≅ 𝒪 ⊕ 𝒪^{⊕ g}[-1]` with `g` the genus of the fibre (Stacks 0E1J), and the formation of
`Rf_*𝒪_X` commutes with base change (Stacks 0CTM). -/
theorem exists_etale_isSplitEpi_of_genus_ne_zero {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q)
    (hg : genus (CurveFamily.fibreMap B hZ X s v) ≠ 0) :
    ∃ (T : BigFppfOver B integerBase hZ) (c : T ⟶ X.base)
      (t : (BigFppfOver.toScheme B integerBase hZ).obj T),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
      Etale ((BigFppfOver.toScheme B integerBase hZ).map c) ∧
      (BigFppfOver.toScheme B integerBase hZ).map c t = s ∧
      ∃ π : (Space.derivedModulePushforward B integerBase hZ (X.baseChange c).toBase).obj
          (structureSheafShifted (X.baseChange c).total).obj ⟶
        (Space.derivedStructureSheaf B integerBase hZ (schemeSpace T).1 (schemeSpace T).2).obj,
        IsSplitEpi π := by
  have h := X.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX.2
  have hvan := fun p j hj =>
    X.isZero_rightDerived_globalSectionsFunctor_structureSheafModule_fiberProduct p j hj
  obtain ⟨T, c, t, m, hT, hc, ht, ⟨e⟩⟩ := exists_affine_etale_iso_biprod hX s
  refine ⟨T, c, t, hT, Space.etale_of_isEtale_yoneda_map B integerBase hZ (φ := c) hc, ht, ?_⟩
  -- the rank of the summand in degree one is the genus
  have hR := Space.isFiniteLocallyFreeOnSite_homology_one_derivedModulePushforward X.toBase
    X.proper X.flat X.finitePresentation h hvan
  have hRq := Space.isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite _ hR
  obtain ⟨z, hz⟩ := Space.surjective_pointsToScheme B integerBase hZ T t
  have hzs : Space.pointsMap B integerBase hZ _ (schemeSpaceMap c).hom z =
      (X.residueFieldPoint s).class B integerBase hZ _ := by
    apply Space.injective_pointsToScheme B integerBase hZ X.base
    refine (Space.pointsToScheme_pointsMap_yoneda B integerBase hZ c z).trans ?_
    rw [hz, ht]
    exact (X.schemePoint_residueFieldPoint s).symm
  have hq' : IsPullback q (yoneda.map v) X.toBase.hom
      (yonedaEquiv.symm (X.residueFieldPoint s).value) := by
    have hyon : yonedaEquiv.symm (X.residueFieldPoint s).value =
        yoneda.map (X.residueFieldPoint s).value :=
      (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map (X.residueFieldPoint s).value).symm
    exact hyon.symm ▸ hq
  have hrank := X.mem_rankLocus_firstDirectImage_of_isPullback h (X.residueFieldPoint s) v q hq'
  rw [Space.rankLocus_congr X.homologyDerivedPushforwardIsoFirstHigherDirectImage.symm] at hrank
  have hm := ne_zero_of_iso_biprod_single_free _
    (Space.isLE_derivedModulePushforward_structureModule_one X.toBase X.proper X.flat
      X.finitePresentation h hvan) hR hRq hg (schemeSpaceMap c) z (hzs ▸ hrank) e
  -- base change
  obtain ⟨π₀, hπ₀⟩ := exists_isSplitEpi_biprod_single_free (Z := schemeSpace T) m
    (Nat.one_le_iff_ne_zero.2 hm)
  have hbc := (Space.isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat X.toBase
    X.proper X.flat X.finitePresentation _ (Space.isPerfect_unit X.total)).2 (schemeSpaceMap c)
      (X.baseChange c).toBase ((X.baseChangeHom c).totalMap) (X.baseChangeHom c).cartesian
  let u := (Space.derivedModulePushforward B integerBase hZ (X.baseChange c).toBase).mapIso
    (Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := integerBase) (hS := hZ)
      (X.baseChangeHom c).totalMap)
  exact exists_isSplitEpi_derivedModulePushforward_structureSheafShifted _ _
    (isSplitEpi_comp_of_isIso' _ _ _ _ (Iso.isIso_inv u) (@IsIso.inv_isIso _ _ _ _ _ hbc)
      (Iso.isIso_hom e) hπ₀)

end C1764Prereq

end AlgebraicGeometry
