module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SiteEquivalenceTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectnessLocalOnSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Pseudo-coherence and perfectness from an étale scheme chart to the slice at that chart

Let `X` be an algebraic space and `U` an étale scheme chart of `X`.  The small étale site of the
algebraic space `h_U` represented by the chart is the slice `X_étale/U` (Stacks 04M0,
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`), with the structure sheaves
agreeing.  Under that equivalence the restriction of an object `E` of `D(𝒪_X)` to the slice is
the étale restriction `E|_U` of Equation 03LW along the structure morphism of the chart.  This
file records that `m`-pseudo-coherence (Stacks 08FT) and perfectness (Stacks 08G5) of `E|_U` on
the small étale site of `h_U` give the same property of the restriction of `E` to the slice.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_over_of_chart`: if `E|_U` is `m`-pseudo-coherent
  on the small étale site of `h_U`, then the restriction of `E` to the slice `X_étale/U` is
  `m`-pseudo-coherent.
* `AlgebraicGeometry.Space.isPerfect_over_of_chart`: the same for perfectness.
* `AlgebraicGeometry.Space.isPerfect_of_forall_affineChart`: an object of `D(𝒪_X)` whose étale
  restriction to every affine étale chart is perfect is perfect.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_forall_affineChart_etaleModulePullback`: the
  same for `m`-pseudo-coherence.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The first coherence identity of the two structure maps of Stacks 04M0 at a chart, in the
spelling of the ringed sites. -/
theorem chartSliceRingMap_counit (U : SmallEtale B S hS X.1) :
    Functor.whiskerRight (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj =
      (chartSliceRingMapInverse B S hS X U).hom ≫
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.op.whiskerLeft
          (chartSliceRingMap B S hS X U).hom := by
  apply NatTrans.ext
  funext V
  change ((structureRingSheaf B S hS X).over U).obj.map
      ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit.app V.unop).op =
    ((structureRingSheaf B S hS X).over U).obj.map
        ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit.app V.unop).op ≫ 𝟙 _
  exact (Category.comp_id _).symm

/-- The second coherence identity of the two structure maps of Stacks 04M0 at a chart, in the
spelling of the ringed sites. -/
theorem chartSliceRingMap_unit (U : SmallEtale B S hS X.1) :
    (chartSliceRingMap B S hS X U).hom ≫
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.op.whiskerLeft
          (chartSliceRingMapInverse B S hS X U).hom ≫
        Functor.whiskerRight
          (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1
              (chartSpace B S hS X U).2).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1
          (chartSpace B S hS X U).2).O).obj := by
  apply NatTrans.ext
  funext V
  change ((structureRingSheaf B S hS X).over U).obj.map
        ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit.app
          ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj V.unop)).op ≫
      ((structureRingSheaf B S hS X).over U).obj.map
        ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.map
          ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).unit.app V.unop)).op =
    𝟙 _
  rw [← ((structureRingSheaf B S hS X).over U).obj.map_comp, ← op_comp]
  simp only [(SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor_unit_comp V.unop]
  exact ((structureRingSheaf B S hS X).over U).obj.map_id _

/-- The inverse structure map of Stacks 04M0 at a chart is invertible: it is the counit of the
equivalence on regular functions. -/
theorem isIso_chartSliceRingMapInverse (U : SmallEtale B S hS X.1) :
    IsIso (chartSliceRingMapInverse B S hS X U) := by
  rw [← ObjectProperty.isIso_hom_iff]
  change IsIso (Functor.whiskerRight
    (NatTrans.op (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).counit)
    ((structureRingSheaf B S hS X).over U).obj)
  infer_instance

/-- The restriction of an `𝒪_X`-module to the slice at a chart, read on the small étale site of
the chart through the comparison of Stacks 04M0, is its étale restriction along the structure
morphism of the chart.  Both have the sections of the module over the composite chart. -/
def chartSliceReindexOverIso (U : SmallEtale B S hS X.1) :
    SheafOfModules.overFunctor (structureRingSheaf B S hS X) U ⋙
        chartModuleSliceReindex B S hS X U ≅
      etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U) :=
  NatIso.ofComponents
    (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl)))
    (fun f => by ext; rfl)

/-- Restriction to the slice at a chart is the étale restriction to the chart, transported back
along the comparison of Stacks 04M0. -/
def chartSliceOverIso (U : SmallEtale B S hS X.1) :
    SheafOfModules.overFunctor (structureRingSheaf B S hS X) U ≅
      etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U) ⋙
        (chartModuleSliceEquiv B S hS X U).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (chartModuleSliceEquiv B S hS X U).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (chartSliceReindexOverIso B S hS X U) _

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafifyAll RingedSite.iterWEqAll
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- The transport of modules from the small étale site of a chart back to the slice is
additive. -/
instance chartModuleSliceEquiv_inverse_additive (U : SmallEtale B S hS X.1) :
    (chartModuleSliceEquiv B S hS X U).inverse.Additive where
  map_add := by intros; ext; rfl

/-- Étale restriction to a chart is additive. -/
instance etaleModulePullback_chartToSpace_additive (U : SmallEtale B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).Additive :=
  etaleModulePullback_additive B S hS (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)

/-- Étale restriction to a chart is left exact. -/
instance preservesFiniteLimits_etaleModulePullback_chartToSpace (U : SmallEtale B S hS X.1) :
    PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)) :=
  preservesFiniteLimits_etaleModulePullback B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- Étale restriction to a chart is right exact. -/
instance preservesFiniteColimits_etaleModulePullback_chartToSpace (U : SmallEtale B S hS X.1) :
    PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)) :=
  preservesFiniteColimits_etaleModulePullback B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- Étale restriction to a chart is additive, for a chart spelled as an object of the ringed
site. -/
instance etaleModulePullback_chartToSpace_additive' (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).Additive :=
  etaleModulePullback_additive B S hS (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)

/-- Étale restriction to a chart is left exact, for a chart spelled as an object of the ringed
site. -/
instance preservesFiniteLimits_etaleModulePullback_chartToSpace'
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)) :=
  preservesFiniteLimits_etaleModulePullback B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- Étale restriction to a chart is right exact, for a chart spelled as an object of the ringed
site. -/
instance preservesFiniteColimits_etaleModulePullback_chartToSpace'
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)) :=
  preservesFiniteColimits_etaleModulePullback B S hS (chartToSpace B S hS X U)
    (isEtale_chartToSpace B S hS X U)

/-- The `𝒪_X`-modules on a slice of the small étale site form an abelian category. -/
local instance (priority := high) modules_over_abelian'
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Abelian (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)) :=
  SheafOfModules.instAbelian _

/-- The `𝒪_X`-modules on a slice of the small étale site, in the spelling of the localized ringed
site, form an abelian category. -/
local instance (priority := high) modules_ringedSiteOver_abelian
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)) :=
  SheafOfModules.instAbelian _

/-- The derived restriction of `E` to the slice at a chart is the transport of its derived étale
restriction to the chart. -/
def chartSliceDerivedOverIso (U : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) U).mapDerivedCategory.obj E ≅
      (chartModuleSliceEquiv B S hS X U).inverse.mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj E) :=
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) U).mapDerivedCategory.mapIso
      eK.symm ≪≫
    ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) U).mapDerivedCategoryFactors.app
      K) ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.Hom.isoOfComponents
        (fun i => (chartSliceOverIso B S hS X U).app (K.X i))
        (fun i j _ => ((chartSliceOverIso B S hS X U).hom.naturality (K.d i j)).symm) :
        ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ≅
        ((chartModuleSliceEquiv B S hS X U).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
            (isEtale_chartToSpace B S hS X U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≪≫
    ((chartModuleSliceEquiv B S hS X U).inverse.mapDerivedCategoryFactors.app
      (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (chartModuleSliceEquiv B S hS X U).inverse.mapDerivedCategory.mapIso
      (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategoryFactors.app K).symm ≪≫
        (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.mapIso eK)

/-- If `E|_U` is perfect on the small étale site of the algebraic space represented by the chart
`U`, then the restriction of `E` to the slice `X_étale/U` is perfect. -/
theorem isPerfect_over_of_chart (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1
        (chartSpace B S hS X U).2).IsPerfect
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj E)) :
    RingedSite.IsPerfect.{u + 1, u, u, u, u + 1} ((smallEtaleRingedSite B S hS X.1 X.2).over U)
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          U).mapDerivedCategory.obj E) := by
  let eqv : (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).C ≌
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).C :=
    SmallEtale.chartLocalizationEquivalence B S hS X.1 U
  have : eqv.functor.IsContinuous
      (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).J
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J :=
    isContinuous_chartLocalization_chartSpace B S hS X U
  have : eqv.inverse.IsContinuous ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
      (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).J :=
    isContinuous_chartLocalizationEquivalence_inverse_chartSpace B S hS X U
  have : ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      HasSheafify (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W) AddCommGrpCat.{u} :=
    RingedSite.iterHasSheafifyAll (smallEtaleRingedSite B S hS X.1 X.2) U
  have : ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    RingedSite.iterWEqAll (smallEtaleRingedSite B S hS X.1 X.2) U
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    RingedSite.isPerfect_pushforward_of_siteEquivalence.{u + 1, u, u, u + 1, u + 1}
    (X := (smallEtaleRingedSite B S hS X.1 X.2).over U)
    (Y := smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2)
    eqv (chartSliceRingMap B S hS X U) (chartSliceRingMapInverse B S hS X U)
    (chartSliceRingMap_counit B S hS X U) (chartSliceRingMap_unit B S hS X U)
    (hψ := isIso_chartSliceRingMapInverse B S hS X U) _ hE
  exact ⟨K, hK, ⟨Iso.trans (C := DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)))
    e (chartSliceDerivedOverIso B S hS X U E).symm⟩⟩

/-- If `E|_U` is `m`-pseudo-coherent on the small étale site of the algebraic space represented by
the chart `U`, then the restriction of `E` to the slice `X_étale/U` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_over_of_chart (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1
        (chartSpace B S hS X U).2).IsPseudoCoherentFrom
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj E) m) :
    RingedSite.IsPseudoCoherentFrom.{u + 1, u, u, u, u + 1}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U)
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          U).mapDerivedCategory.obj E) m := by
  let eqv : (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).C ≌
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).C :=
    SmallEtale.chartLocalizationEquivalence B S hS X.1 U
  have : eqv.functor.IsContinuous
      (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).J
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J :=
    isContinuous_chartLocalization_chartSpace B S hS X U
  have : eqv.inverse.IsContinuous ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
      (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).J :=
    isContinuous_chartLocalizationEquivalence_inverse_chartSpace B S hS X U
  have : ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      HasSheafify (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W) AddCommGrpCat.{u} :=
    RingedSite.iterHasSheafifyAll (smallEtaleRingedSite B S hS X.1 X.2) U
  have : ∀ W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C,
      (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    RingedSite.iterWEqAll (smallEtaleRingedSite B S hS X.1 X.2) U
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    RingedSite.isPseudoCoherentFrom_pushforward_of_siteEquivalence.{u + 1, u, u, u + 1, u + 1}
    (X := (smallEtaleRingedSite B S hS X.1 X.2).over U)
    (Y := smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2)
    eqv (chartSliceRingMap B S hS X U) (chartSliceRingMapInverse B S hS X U)
    (chartSliceRingMap_counit B S hS X U) (chartSliceRingMap_unit B S hS X U)
    (hψ := isIso_chartSliceRingMapInverse B S hS X U) _ m hE
  exact ⟨K, hK, ⟨Iso.trans (C := DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)))
    e (chartSliceDerivedOverIso B S hS X U E).symm⟩⟩

/-- If the étale restriction of `E ∈ D(𝒪_X)` to every affine étale chart `V` of `X` is perfect on
the small étale site of the algebraic space represented by `V`, then `E` is perfect. -/
theorem isPerfect_of_forall_affineChart (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2).IsPerfect
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  refine isPerfect_of_locally B S hS X.1 X.2 E fun U => ?_
  refine ⟨fun W (_ : W ⟶ U) => IsAffineChart B S hS X.1 W,
    generate_isAffineChart_mem_topology B S hS X U, fun V _ hV => ?_⟩
  exact isPerfect_over_of_chart B S hS X V E (h V hV)

/-- If the étale restriction of `E ∈ D(𝒪_X)` to every affine étale chart `V` of `X` is
`m`-pseudo-coherent on the small étale site of the algebraic space represented by `V`, then `E` is
`m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_forall_affineChart_etaleModulePullback
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2).IsPseudoCoherentFrom
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := by
  refine RingedSite.isPseudoCoherentFrom_of_locally_general (smallEtaleRingedSite B S hS X.1 X.2)
    E m fun U => ?_
  refine ⟨fun W (_ : W ⟶ U) => IsAffineChart B S hS X.1 W,
    generate_isAffineChart_mem_topology B S hS X U, fun V _ hV => ?_⟩
  exact isPseudoCoherentFrom_over_of_chart B S hS X V E m (h V hV)

end AlgebraicGeometry.Space

end
