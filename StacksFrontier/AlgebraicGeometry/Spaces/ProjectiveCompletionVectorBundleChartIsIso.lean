module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinateQ
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinate
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundleChartIsoCoord

/-!
# The affine part of `𝐏(ℰ ⊕ 𝒪)` is the vector bundle `𝐕(ℰ)`

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r`. On an affine
étale chart `V` of `X` on which `ℰ` is free, the morphism `U ×_X V ⟶ 𝐕(ℰ) ×_X V` from the chart of
the affine part `U = 𝐏(ℰ ⊕ 𝒪) ∖ 𝐏(ℰ)` is an isomorphism: both sides are affine space over `V`,
and the coordinates agree (Stacks 0ERW, proof).

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.Space

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
  AlgebraicGeometry.Space.CartesianChartFamily.site
  AlgebraicGeometry.BigFppfOver.siteObjectOver
      AlgebraicGeometry.Space.CartesianChartFamily.siteToChart
  AlgebraicGeometry.BigFppfOver.siteMapOver

/-- The chart readings of `ℰ ⊕ 𝒪` and `ℰ` are quasi-coherent, and `ℰ ⊕ 𝒪 ⟶ ℰ` is an epi. -/
private theorem chart_instances {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (E : Modules.{u, u} B S hS X.1 X.2)
    (hE : (addUnit X.2 E).IsQuasicoherentOnSite) (hE' : E.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) :
    (chartBundleModule (addUnit X.2 E) V).IsQuasicoherent ∧
      (chartBundleModule E V).IsQuasicoherent ∧
      Epi (chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) V) :=
  ⟨@isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E) hE V,
    @isQuasicoherent_chartBundleModule B S hS X E hE' V,
    epi_chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) biprod.inl biprod.inl_fst V⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) [IsAffine (chartScheme V)]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The value of a ratio of inverse images along `ι : U ⟶ P` does not depend on the spelling of
`P`, of `ι`, `π` and of the two numerators. -/
theorem ratio_val_app_congr {U P P' : AlgebraicSpaces B S hS} (hP : P = P') {ι : U ⟶ P}
    {ι' : U ⟶ P'}
    (hι : HEq ι ι') {π : P ⟶ X} {π' : P' ⟶ X} (hπ : HEq π π')
    {L : Modules.{u, u} B S hS P.1 P.2} {L' : Modules.{u, u} B S hS P'.1 P'.2} (hL : HEq L L')
    {a : (modulePullback B S hS π).obj E ⟶ L} {a' : (modulePullback B S hS π').obj E ⟶ L'}
    (ha : HEq a a')
    {b : SheafOfModules.unit (structureRingSheaf B S hS P) ⟶ L}
    {b' : SheafOfModules.unit (structureRingSheaf B S hS P') ⟶ L'} (hb : HEq b b')
    (hs : IsIso ((modulePullback B S hS ι).map b)) (hs' : IsIso ((modulePullback B S hS ι').map b'))
    (W : SmallEtale B S hS U.1) {y : ((modulePullback B S hS (ι ≫ π)).obj E).val.obj (op W)}
    {y' : ((modulePullback B S hS (ι' ≫ π')).obj E).val.obj (op W)} (hy : HEq y y') :
    ((modulePullbackCompIso B S hS ι π).inv.app E ≫ (modulePullback B S hS ι).map a ≫
        @inv _ _ _ _ ((modulePullback B S hS ι).map b) hs ≫
        (modulePullbackUnitIso B S hS ι).hom).val.app (op W) y =
      ((modulePullbackCompIso B S hS ι' π').inv.app E ≫ (modulePullback B S hS ι').map a' ≫
        @inv _ _ _ _ ((modulePullback B S hS ι').map b') hs' ≫
        (modulePullbackUnitIso B S hS ι').hom).val.app (op W) y' := by
  subst hP
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq hπ
  obtain rfl := eq_of_heq hL
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hy
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `m ↦ (m, 0)` on `π^*ℰ`, in the spelling of the projective bundle. -/
theorem projectiveCompletionTautologicalInl_eq_bundle :
    projectiveCompletionTautologicalInl E hr =
      (modulePullback B S hS (@projectiveBundleProj B S hS X (addUnit X.2 E)
          (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map biprod.inl ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom := by
  with_reducible rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `AlgebraicGeometry.Space.projectiveCompletionTautologicalInl_eq_bundle` across the two
spellings of the source and target. -/
theorem heq_projectiveCompletionTautologicalInl_bundle :
    HEq ((modulePullback B S hS
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map biprod.inl ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom)
      (projectiveCompletionTautologicalInl E hr) :=
  (heq_of_eq (projectiveCompletionTautologicalInl_eq_bundle E hr)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `AlgebraicGeometry.Space.projectiveCompletionSectionHom_eq_bundle` across the two spellings
of the source and target. -/
theorem heq_projectiveCompletionSectionHom_bundle :
    HEq ((modulePullbackUnitIso B S hS
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
        (modulePullback B S hS
            (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) ≫
            (@projectiveBundleTautological B S hS X (addUnit X.2 E)
            (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom) (projectiveCompletionSectionHom E hr) :=
  (heq_of_eq (projectiveCompletionSectionHom_eq_bundle E hr)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The inverse image of a section of `ℰ` at the chart `U_V`, in the spelling of the projective
bundle. -/
theorem modulePullbackChartSection_affinePartChart_eq_bundle (x : E.val.obj (op V)) :
    modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
          ⟨affinePartChartOverChart E hr m, V,
              projectiveCompletionAffinePartOverChartToChart E hr m,
            affinePartChartOverChart_comm E hr m⟩ x =
      modulePullbackChartSection B S hS
          ((projectiveCompletionAffinePartHomBundle E hr) ≫
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))) E
        ⟨affinePartChartOverChart E hr m, V,
            (@CategoryStruct.comp _ _
            ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
            (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)),
          affinePartChartOverChart_comm_site E hr m⟩
        x :=
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- `AlgebraicGeometry.Space.modulePullbackChartSection_affinePartChart_eq_bundle` across the two
spellings of the module. -/
theorem heq_modulePullbackChartSection_bundle (x : E.val.obj (op V)) :
    HEq (modulePullbackChartSection B S hS
        ((projectiveCompletionAffinePartHomBundle E hr) ≫
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))) E
        ⟨affinePartChartOverChart E hr m, V,
            (@CategoryStruct.comp _ _
            ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
            (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)),
          affinePartChartOverChart_comm_site E hr m⟩
        x) (modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
          ⟨affinePartChartOverChart E hr m, V,
              projectiveCompletionAffinePartOverChartToChart E hr m,
            affinePartChartOverChart_comm E hr m⟩ x) :=
  (heq_of_eq (modulePullbackChartSection_affinePartChart_eq_bundle E hr m x)).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] [IsAffine (chartScheme V)] in
/-- The value of `q` on a chart section, in the spelling of the projective bundle. -/
theorem projectiveCompletionAffinePartQuotient_val_app_eq_bundle (x : E.val.obj (op V)) :
    ((modulePullbackCompIso B S hS (projectiveCompletionAffinePartHomBundle E hr)
        (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv.app E ≫
        (modulePullback B S hS (projectiveCompletionAffinePartHomBundle E hr)).map
          ((modulePullback B S hS
              (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map biprod.inl ≫
          (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom) ≫
        @inv _ _ _ _ ((modulePullback B S hS (projectiveCompletionAffinePartHomBundle E hr)).map
            ((modulePullbackUnitIso B S hS
            (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).inv ≫
        (modulePullback B S hS
            (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))).map
          (addUnitInr X.2 E : (SheafOfModules.unit (structureRingSheaf B S hS X) :
        Modules.{u, u} B S hS X.1 X.2) ⟶ addUnit X.2 E) ≫
            (@projectiveBundleTautological B S hS X (addUnit X.2 E)
            (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr)).hom))
          (isIso_modulePullback_projectiveCompletionAffinePartHom_sectionHom_bundle E hr) ≫
        (modulePullbackUnitIso B S hS (projectiveCompletionAffinePartHomBundle E hr)).hom).val.app
          (op (affinePartChartOverChart E hr m))
      (modulePullbackChartSection B S hS
          ((projectiveCompletionAffinePartHomBundle E hr) ≫
          (@projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr))) E
        ⟨affinePartChartOverChart E hr m, V,
            (@CategoryStruct.comp _ _
            ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
            (affinePartChartOverChart E hr m))
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).site V) ((SmallEtale.toOver B S hS X.1).obj V)
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m)
      ((@projectiveBundleChartFamily B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
        (isFiniteLocallyFreeOnSite_addUnit hr)).siteToChart V)),
          affinePartChartOverChart_comm_site E hr m⟩ x) =
    (projectiveCompletionAffinePartQuotient E hr
          (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E
            hr)).val.app (Opposite.op (affinePartChartOverChart E hr m))
        (modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
          ⟨affinePartChartOverChart E hr m, V,
              projectiveCompletionAffinePartOverChartToChart E hr m,
            affinePartChartOverChart_comm E hr m⟩ x) := by
  unfold projectiveCompletionAffinePartQuotient
  refine ratio_val_app_congr E ?_ ?_ ?_ ?_ ?_ ?_ _ _ _ ?_
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact heq_projectiveCompletionTautologicalInl_bundle E hr
  · exact heq_projectiveCompletionSectionHom_bundle E hr
  · exact heq_modulePullbackChartSection_bundle E hr m x


section Chart

variable {n : Type u} [DecidableEq n] [Finite n]
  (e : (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E).over V ≅
    SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) n)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- The coordinates of `U ×_X V ≅ 𝐏((ℰ ⊕ 𝒪)|_V) ∖ 𝐏(ℰ|_V) ≅ 𝐀^n_V` are those of the open
immersion `U ×_X V ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)`. -/
theorem affinePartOverChartIsoComplement_splitQuotientComplementIso_appTop_coord (j : n) :
    haveI := @isQuasicoherent_chartBundleModule B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) V
    haveI := @isQuasicoherent_chartBundleModule B S hS X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V
    haveI := epi_chartModuleMap (biprod.fst : addUnit X.2 E ⟶ E) biprod.inl biprod.inl_fst V
    ((affinePartOverChartIsoComplement E hr m).hom ≫
        ((completionChartUnitSplitting E V).splitQuotientComplementIso
            (chartBundleModuleFreeIso E V e
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))).hom).appTop
        (AffineSpace.coord (chartScheme V) j) =
      Stacks.RelativeProj.UnitSplitting.coordVector
          (chartBundleModuleFreeIso E V e
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
        ((completionChartUnitSplitting E V).splitCoordMap
            (@chartBundleHomOfSite B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
      (isFiniteLocallyFreeOnSite_addUnit hr) V
          ((SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj
          (affinePartChartOverChart E hr m))
      (@splitEpiComplementChartHom B S hS X (addUnit X.2 E) E
        (isQuasicoherentOnSite_addUnit hr)
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        biprod.fst biprod.inl biprod.inl_fst (isFiniteLocallyFreeOnSite_addUnit hr)
        hr.isFiniteLocallyFreeOnSite V m))
          (chartBundleHomOfSite_comp_chartBundleToChart
              (hE := isQuasicoherentOnSite_addUnit hr) _ _ _)
          (range_chartBundleHomOfSite_affinePart_subset E hr m)) j := by
  obtain ⟨_, _, _⟩ := chart_instances E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V
  have h1 := Stacks.RelativeProj.UnitSplitting.splitQuotientComplementIso_hom_appTop_coord
    (completionChartUnitSplitting E V)
        (chartBundleModuleFreeIso E V e
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)) j
  have h2 := Stacks.RelativeProj.UnitSplitting.splitCoordVector_comp
    (completionChartUnitSplitting E V)
        (chartBundleModuleFreeIso E V e (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
        (affinePartOverChartIsoComplement E hr m).hom _
    Stacks.RelativeProj.UnitSplitting.range_splitQuotientComplement_ι
    (Stacks.RelativeProj.UnitSplitting.range_comp_subset_splitQuotientComplement _ _
      Stacks.RelativeProj.UnitSplitting.range_splitQuotientComplement_ι) j
  have h3 := Stacks.RelativeProj.UnitSplitting.splitCoordVector_congr
    (completionChartUnitSplitting E V)
        (chartBundleModuleFreeIso E V e (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
        (affinePartOverChartIsoComplement_hom_ι E hr m)
    (Stacks.RelativeProj.UnitSplitting.range_comp_subset_splitQuotientComplement _ _
      Stacks.RelativeProj.UnitSplitting.range_splitQuotientComplement_ι)
    (range_chartBundleHomOfSite_affinePart_subset E hr m)
  have h4 := Stacks.RelativeProj.UnitSplitting.coordVector_splitCoordMap
    (completionChartUnitSplitting E V)
        (chartBundleModuleFreeIso E V e (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
        _ (chartBundleHomOfSite_comp_chartBundleToChart
      (hE := isQuasicoherentOnSite_addUnit hr) _ _ _)
    (range_chartBundleHomOfSite_affinePart_subset E hr m)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h1]
  exact h2.symm.trans ((congrFun h3 j).trans (congrFun h4 j).symm)

/-- The coordinates of `U ×_X V ⟶ E ×_X V ≅ 𝐀^n_V` are the values of `q` on the inverse images
of the basis sections of `ℰ(V)`. -/
theorem projectiveCompletionAffinePartChartToVectorBundleChart_vectorBundleChartIso_appTop_coord
    (j : n) :
    ((BigFppfOver.toScheme B S hS).map
        (projectiveCompletionAffinePartChartToVectorBundleChart E hr m) ≫
        (vectorBundleChartIsoOfRingEquiv B S hS X
            (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V
          (polynomialChartRingEquiv B S hS X
              (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e)).hom).appTop
        (AffineSpace.coord (chartScheme V) j) =
      (projectiveCompletionAffinePartQuotient E hr
          (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E
            hr)).val.app (Opposite.op (affinePartChartOverChart E hr m))
        (modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
          ⟨affinePartChartOverChart E hr m, V,
              projectiveCompletionAffinePartOverChartToChart E hr m,
            affinePartChartOverChart_comm E hr m⟩
          (SymAlgSections.sectionsBasis B S hS X
              (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e j)) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      vectorBundleChartIsoOfRingEquiv_hom_appTop_coord,
    polynomialChartRingEquiv_X]
  exact appTop_projectiveCompletionAffinePartChartToVectorBundleChart_gen E hr m _

omit [DecidableEq n] in
include e in
/-- **`U ×_X V ⟶ E ×_X V` is an isomorphism** over an affine chart `V` on which `ℰ` is free:
under `U ×_X V ≅ 𝐏((ℰ ⊕ 𝒪)|_V) ∖ 𝐏(ℰ|_V) ≅ 𝐀^n_V` and `E ×_X V ≅ 𝐀^n_V` it is the identity, both
being over `V` with the same coordinates (Stacks 0ERW, proof). -/
theorem isIso_toScheme_map_projectiveCompletionAffinePartChartToVectorBundleChart :
    IsIso ((BigFppfOver.toScheme B S hS).map
      (projectiveCompletionAffinePartChartToVectorBundleChart E hr m)) := by
  classical
  obtain ⟨_, _, _⟩ := chart_instances E (isQuasicoherentOnSite_addUnit hr)
    (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) V
  have key : (BigFppfOver.toScheme B S hS).map
        (projectiveCompletionAffinePartChartToVectorBundleChart E hr m) ≫
        (vectorBundleChartIsoOfRingEquiv B S hS X
            (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V
          (polynomialChartRingEquiv B S hS X
              (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e)).hom =
      (affinePartOverChartIsoComplement E hr m).hom ≫
        ((completionChartUnitSplitting E V).splitQuotientComplementIso
            (chartBundleModuleFreeIso E V e
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))).hom := by
    refine AffineSpace.hom_ext ?_ (fun j => ?_)
    · have h1 := vectorBundleChartIsoOfRingEquiv_hom_over B S hS X
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V
        (polynomialChartRingEquiv B S hS X
            (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e)
        (polynomialChartRingEquiv_C B S hS X
            (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e)
      have h2 := Stacks.RelativeProj.UnitSplitting.splitQuotientComplementIso_hom_over
        (completionChartUnitSplitting E V)
            (chartBundleModuleFreeIso E V e
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))
      rw [Category.assoc, h1, Category.assoc, h2, ← Functor.map_comp,
        projectiveCompletionAffinePartChartToVectorBundleChart_comp_hom, ← Category.assoc,
        affinePartOverChartIsoComplement_hom_ι, Functor.map_comp]
      rfl
    · have h1 :=
        projectiveCompletionAffinePartChartToVectorBundleChart_vectorBundleChartIso_appTop_coord
          E hr m e j
      have h2 := projectiveCompletionAffinePartQuotient_val_app_eq_bundle E hr m
        (SymAlgSections.sectionsBasis B S hS X
            (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e j)
      have h3 := projectiveCompletionAffinePartQuotient_chartSection_eq_coordVector_site E hr m e j
      have h4 := affinePartOverChartIsoComplement_splitQuotientComplementIso_appTop_coord E hr m e j
      exact h1.trans (h2.symm.trans (h3.trans h4.symm))
  have h : (BigFppfOver.toScheme B S hS).map
      (projectiveCompletionAffinePartChartToVectorBundleChart E hr m) =
      ((affinePartOverChartIsoComplement E hr m).hom ≫
        ((completionChartUnitSplitting E V).splitQuotientComplementIso
            (chartBundleModuleFreeIso E V e
            (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr))).hom) ≫
      (vectorBundleChartIsoOfRingEquiv B S hS X
          (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V
          (polynomialChartRingEquiv B S hS X
              (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e)).inv := by
    rw [← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

end Chart

end AlgebraicGeometry.Space

end
