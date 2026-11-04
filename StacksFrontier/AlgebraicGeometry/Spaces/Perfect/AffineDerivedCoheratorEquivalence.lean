module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorInclusionAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseTerminalChartIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections

/-!
# The derived coherator of an affine algebraic space

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B`.  This
file proves the third assertion of [Stacks, Tag 08H0]: the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence, with quasi-inverse the
derived coherator `RQ_X`.  It also proves that the comparison map of `RQ_X` is invertible at
every complex of quasi-coherent modules, the affine case of [Stacks, Tag 09TG].

## Main results

* `AlgebraicGeometry.Space.isIso_spaceDerivedCoheratorUnit_app_of_isAffineSpace` — the
  comparison of `RQ_X` is invertible at every complex of quasi-coherent modules.
* `AlgebraicGeometry.Space.isIso_spaceDerivedInclusionAdjunction_counit_app_of_isAffineSpace` —
  the counit of `D(ι) ⊣ RQ_X` is invertible on `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isAffineSpace` —
  **[Stacks, Tag 08H0] (3)**: the comparison functor is an equivalence.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

-- These module-universe-polymorphic instances would be tried before the standard model and
-- stick at a universe constraint.
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Z : AlgebraicSpaces B S hS)
  {U₀ : SmallEtale B S hS Z.1} (hU₀ : IsTerminal U₀) (hU₀aff : IsAffineChart B S hS Z.1 U₀)

/-- Sections over the chart `U₀`. -/
abbrev chartEvaluation (U₀ : SmallEtale B S hS Z.1) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj.obj (op U₀)) :=
  SheafOfModules.evaluation _ (op U₀)

/-- The objects of `D(𝒪_Z)` with quasi-coherent cohomology, that is, the objects of
`D_QCoh(𝒪_Z)` (Stacks 071X). -/
abbrev derivedQuasicoherentProperty :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)))

/-- Sections over a chart form an additive functor. -/
instance chartEvaluation_additive (U₀ : SmallEtale B S hS Z.1) :
    (chartEvaluation B S hS Z U₀).Additive :=
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.evaluation_additive _ _

/-- Sections over a chart preserve finite limits. -/
instance chartEvaluation_preservesFiniteLimits (U₀ : SmallEtale B S hS Z.1) :
    PreservesFiniteLimits (chartEvaluation B S hS Z U₀) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _

/-! ### Sections over a terminal chart -/

include hU₀ in
/-- Over a terminal chart, morphisms out of the structure sheaf are the sections over the chart.
-/
def unitHomEquivChartEvaluation (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (SheafOfModules.unit _ ⟶ M) ≃ M.val.obj (op U₀) :=
  M.unitHomEquiv.trans (Presheaf.sectionsEquivObjOfIsTerminal hU₀ _)

/-- `unitHomEquivChartEvaluation` is natural in the target module. -/
lemma unitHomEquivChartEvaluation_comp {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (f : SheafOfModules.unit _ ⟶ M) (p : M ⟶ N) :
    unitHomEquivChartEvaluation B S hS Z hU₀ N (f ≫ p) =
      p.val.app (op U₀) (unitHomEquivChartEvaluation B S hS Z hU₀ M f) :=
  rfl

/-- The structure sheaf as a quasi-coherent module. -/
abbrev unitQuasicoherentSheaf : QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2 :=
  ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩

include hU₀ in
/-- **The sections over a terminal chart carry the counit of the coherator to an
isomorphism.** -/
lemma isIso_chartEvaluation_map_counit (N : Modules.{u, u} B S hS Z.1 Z.2) :
    IsIso ((chartEvaluation B S hS Z U₀).map
      ((spaceCoheratorAdjunction B S hS Z).counit.app N)) := by
  have hcomp : Function.Bijective (fun f : (quasicoherentSheavesι B S hS Z).obj
      (unitQuasicoherentSheaf B S hS Z) ⟶
      (quasicoherentSheavesι B S hS Z).obj ((spaceCoherator B S hS Z).obj N) =>
        f ≫ (spaceCoheratorAdjunction B S hS Z).counit.app N) := by
    have h1 : Function.Bijective (fun g : unitQuasicoherentSheaf B S hS Z ⟶
        (spaceCoherator B S hS Z).obj N =>
          (quasicoherentSheavesι B S hS Z).map g ≫
            (spaceCoheratorAdjunction B S hS Z).counit.app N) :=
      ((spaceCoheratorAdjunction B S hS Z).homEquiv _ _).symm.bijective
    have h2 : Function.Bijective (fun g : unitQuasicoherentSheaf B S hS Z ⟶
        (spaceCoherator B S hS Z).obj N => (quasicoherentSheavesι B S hS Z).map g) :=
      ⟨(quasicoherentSheavesι B S hS Z).map_injective,
        (quasicoherentSheavesι B S hS Z).map_surjective⟩
    exact (Function.Bijective.of_comp_iff _ h2).1 h1
  have key : ⇑((chartEvaluation B S hS Z U₀).map
      ((spaceCoheratorAdjunction B S hS Z).counit.app N)).hom =
      unitHomEquivChartEvaluation B S hS Z hU₀ N ∘
        (fun f => f ≫ (spaceCoheratorAdjunction B S hS Z).counit.app N) ∘
          (unitHomEquivChartEvaluation B S hS Z hU₀ _).symm := by
    funext x
    exact ((unitHomEquivChartEvaluation_comp B S hS Z hU₀ _ _).trans
      (congrArg _ (Equiv.apply_symm_apply _ _))).symm
  rw [ConcreteCategory.isIso_iff_bijective, key]
  exact (Equiv.bijective _).comp (hcomp.comp (Equiv.bijective _))

/-! ### Exactness of the sections over an affine chart on quasi-coherent modules -/

include hU₀aff in
/-- Sections over an affine chart carry an epimorphism of quasi-coherent modules to a surjection
(the uniform Stacks 03DW). -/
lemma preservesEpimorphisms_quasicoherentSheavesι_comp_chartEvaluation :
    (quasicoherentSheavesι B S hS Z ⋙ chartEvaluation B S hS Z U₀).PreservesEpimorphisms where
  preserves {M N} q _ := by
    have hk : (kernel ((quasicoherentSheavesι B S hS Z).map q)).IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso (PreservesKernel.iso _ q)
        (kernel q).property
    rw [ModuleCat.epi_iff_surjective]
    exact surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts (hF := Z.2)
      ((quasicoherentSheavesι B S hS Z).map q) inferInstance
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Z.1 Z.2 _ hk) U₀ hU₀aff

include hU₀aff in
/-- Sections over an affine chart are exact on quasi-coherent modules. -/
lemma preservesFiniteColimits_quasicoherentSheavesι_comp_chartEvaluation :
    PreservesFiniteColimits (quasicoherentSheavesι B S hS Z ⋙ chartEvaluation B S hS Z U₀) := by
  have := preservesEpimorphisms_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀aff
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (quasicoherentSheavesι B S hS Z ⋙ chartEvaluation B S hS Z U₀)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- A morphism of quasi-coherent modules is invertible if its sections over a terminal affine
chart are. -/
private lemma isIso_of_isIso_chartEvaluation_map (hU₀ : IsTerminal U₀)
    (hU₀aff : IsAffineChart B S hS Z.1 U₀) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : IsIso ((chartEvaluation B S hS Z U₀).map f)) : IsIso f :=
  isIso_of_bijective_val_app_isTerminal B S hS Z hM hN _ hU₀ hU₀aff
    ((ConcreteCategory.isIso_iff_bijective _).1 hf)

include hU₀ hU₀aff in
/-- Sections over a terminal affine chart reflect isomorphisms of quasi-coherent modules. -/
lemma reflectsIsomorphisms_quasicoherentSheavesι_comp_chartEvaluation :
    (quasicoherentSheavesι B S hS Z ⋙ chartEvaluation B S hS Z U₀).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have := isIso_of_isIso_chartEvaluation_map B S hS Z hU₀ hU₀aff M.property N.property _ hf
    exact isIso_of_reflects_iso f (quasicoherentSheavesι B S hS Z)

/-! ### Derived sections over the chart -/

/-- Sections over a chart have a right derived functor on the unbounded derived category. -/
instance hasRightDerivedFunctor_chartEvaluation :
    ((chartEvaluation B S hS Z U₀).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :=
  Stacks.DerivedCoherator.hasRightDerivedFunctor_of_isGrothendieckAbelian.{u} _

/-- Membership in `D_QCoh(𝒪_Z)` is invariant under isomorphism. -/
lemma derivedCategoryB_quasicoherent_of_iso {M N : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)}
    (e : M ≅ N)
    (hM : derivedQuasicoherentProperty B S hS Z M) : derivedQuasicoherentProperty B S hS Z N :=
  fun n => SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hM n)

/-- Derived sections `RΓ(U₀, -)` over the chart. -/
abbrev chartDerivedEvaluation (U₀ : SmallEtale B S hS Z.1) :
    DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj.obj (op U₀))) :=
  ((chartEvaluation B S hS Z U₀).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))

/-- The comparison map of `RΓ(U₀, -)`. -/
abbrev chartDerivedEvaluationUnit (U₀ : SmallEtale B S hS Z.1) :
    (chartEvaluation B S hS Z U₀).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ chartDerivedEvaluation B S hS Z U₀ :=
  ((chartEvaluation B S hS Z U₀).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))

/-- The hypercohomology edge morphism `H^q(U₀, M) ⟶ Γ(U₀, H^q M)`. -/
abbrev chartEvaluationEdge (U₀ : SmallEtale B S hS Z.1) (q : ℤ) :
    chartDerivedEvaluation B S hS Z U₀ ⋙ DerivedCategory.homologyFunctor _ q ⟶
      DerivedCategory.homologyFunctor _ q ⋙ chartEvaluation B S hS Z U₀ :=
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison
    (chartEvaluation B S hS Z U₀) (chartDerivedEvaluation B S hS Z U₀)
    (chartDerivedEvaluationUnit B S hS Z U₀) (exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2) q

include hU₀aff in
open Stacks.Cohomology.HypercohomologyEdge in
/-- **Stacks 0BKZ at a K-injective complex, over an affine chart**: if the cohomology sheaves of
a K-injective complex `I` are quasi-coherent, its sections over the affine chart `U₀` compute
the sections of its cohomology sheaves: the homology comparison is invertible. -/
lemma isIso_homologyComparison_chartEvaluation_of_isKInjective
    (I : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ m, (I.homology m).IsQuasicoherentOnSite) (q : ℤ) :
    IsIso (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison
      (chartEvaluation B S hS Z U₀) I q) := by
  obtain ⟨hex, hepi⟩ :=
    Stacks.Cohomology.HypercohomologyEdge.exact_and_epi_sections_of_acyclic_cover
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O) I hI
    (IsAffineChart B S hS Z.1) (hasEnoughObjects_isAffineChart B S hS Z.1)
    (fun V hV p hp m => isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS Z.1 Z.2
      V hV _ (hqc m) p hp) hU₀aff q
  have hex' : ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.cyclesHomologyShortComplex
      (chartEvaluation B S hS Z U₀) I q).map (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u})).Exact :=
    hex
  rw [ShortComplex.exact_map_iff_of_faithful] at hex'
  have hepi' : Epi
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.cyclesHomologyShortComplex
        (chartEvaluation B S hS Z U₀) I q).g := by
    rw [ModuleCat.epi_iff_surjective]
    exact (AddCommGrpCat.epi_iff_surjective _).1 hepi
  exact HomologyComparison.isIso_homologyComparison_of_exact_of_epi _ I q hex' hepi'

include hU₀aff in
open Stacks.Cohomology.HypercohomologyEdge in
/-- **Stacks 0BKZ over an affine chart.**  The edge morphism `H^q(U₀, M) ⟶ Γ(U₀, H^q M)` is
invertible for every object `M` of `D_QCoh(𝒪_Z)`. -/
lemma isIso_chartEvaluationEdge_app (M : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (hM : derivedQuasicoherentProperty B S hS Z M) (q : ℤ) :
    IsIso ((chartEvaluationEdge B S hS Z U₀ q).app M) := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2
    (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map s) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) s hs
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅ M :=
    (DerivedCategory.quotientCompQhIso _).app I ≪≫ (asIso (DerivedCategory.Q.map s)).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have hqc : ∀ m, (I.homology m).IsQuasicoherentOnSite := fun m =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (((DerivedCategory.homologyFunctor _ m).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactorsh _ m).app _ ≪≫
        (HomotopyCategory.homologyFunctorFactors _ _ m).app I) (hM m)
  have := isIso_homologyComparison_chartEvaluation_of_isKInjective B S hS Z hU₀aff I hI hqc q
  exact (NatTrans.isIso_app_iff_of_iso (chartEvaluationEdge B S hS Z U₀ q) e).1
    (HomologyComparison.isIso_derivedHomologyComparison_app_of_isKInjective
      (chartEvaluation B S hS Z U₀) (chartDerivedEvaluation B S hS Z U₀)
      (chartDerivedEvaluationUnit B S hS Z U₀)
      (exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2) q I hI)

/-! ### The affine case -/

include hU₀aff in
/-- `RΓ(U₀, -)` has invertible comparison at every complex of quasi-coherent modules. -/
lemma isIso_chartDerivedEvaluationUnit_app
    (K : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    IsIso ((chartDerivedEvaluationUnit B S hS Z U₀).app
      ((quasicoherentSheavesι B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj K)) := by
  obtain ⟨K⟩ := K
  have := preservesFiniteColimits_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀aff
  change IsIso ((chartDerivedEvaluationUnit B S hS Z U₀).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((quasicoherentSheavesι B S hS Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
  refine Stacks.DerivedCoherator.isIso_derivedUnit_of_isIso_derivedHomologyComparison
    (chartEvaluation B S hS Z U₀) (chartDerivedEvaluation B S hS Z U₀)
    (chartDerivedEvaluationUnit B S hS Z U₀) (exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2)
    _ (fun q => ?_) (fun q => Stacks.DerivedCoherator.isIso_homologyComparison_of_comp_exact
      (quasicoherentSheavesι B S hS Z) (chartEvaluation B S hS Z U₀) K q)
  exact isIso_chartEvaluationEdge_app B S hS Z hU₀aff _
    (derivedCategoryB_quasicoherent_of_iso B S hS Z
      ((quasicoherentSheavesι B S hS Z).mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      (derivedCategoryB_mapDerivedCategory_obj B S hS Z.1 Z.2 _)) q

include hU₀ hU₀aff in
/-- Over a terminal affine chart `U₀`, `RΓ(U₀, -)` reflects isomorphisms between objects of
`D_QCoh(𝒪_Z)`. -/
lemma isIso_of_isIso_chartDerivedEvaluation_map
    {M N : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)} (f : M ⟶ N)
    (hM : derivedQuasicoherentProperty B S hS Z M) (hN : derivedQuasicoherentProperty B S hS Z N)
    (hf : IsIso ((chartDerivedEvaluation B S hS Z U₀).map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro q
  have := isIso_chartEvaluationEdge_app B S hS Z hU₀aff M hM q
  have := isIso_chartEvaluationEdge_app B S hS Z hU₀aff N hN q
  have : IsIso ((chartEvaluationEdge B S hS Z U₀ q).app M ≫
      (DerivedCategory.homologyFunctor _ q ⋙ chartEvaluation B S hS Z U₀).map f) := by
    rw [← (chartEvaluationEdge B S hS Z U₀ q).naturality f, Functor.comp_map]
    infer_instance
  have h' : IsIso ((DerivedCategory.homologyFunctor _ q ⋙ chartEvaluation B S hS Z U₀).map f) :=
    IsIso.of_isIso_comp_left ((chartEvaluationEdge B S hS Z U₀ q).app M) _
  have h : IsIso ((chartEvaluation B S hS Z U₀).map
      ((DerivedCategory.homologyFunctor _ q).map f)) := by
    simpa only [Functor.comp_map] using h'
  exact isIso_of_isIso_chartEvaluation_map B S hS Z hU₀ hU₀aff (hM q) (hN q) _ h

include hU₀ hU₀aff in
/-- **The comparison map of the derived coherator of a space with a terminal affine chart is
invertible at every complex of quasi-coherent modules.** -/
theorem isIso_spaceDerivedCoheratorUnit_app_of_isTerminal
    (K : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    IsIso ((spaceDerivedCoheratorUnit B S hS Z).app
      ((quasicoherentSheavesι B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj K)) := by
  have := preservesFiniteColimits_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀aff
  have := reflectsIsomorphisms_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀ hU₀aff
  exact Stacks.DerivedCoherator.isIso_comparison_of_derivedSections
    (quasicoherentSheavesι B S hS Z) (spaceCoheratorAdjunction B S hS Z)
    (spaceDerivedCoherator B S hS Z) (spaceDerivedCoheratorUnit B S hS Z)
    (chartEvaluation B S hS Z U₀) (chartDerivedEvaluation B S hS Z U₀)
    (chartDerivedEvaluationUnit B S hS Z U₀)
    (isIso_chartEvaluation_map_counit B S hS Z hU₀)
    (isIso_chartDerivedEvaluationUnit_app B S hS Z hU₀aff) K

include hU₀ hU₀aff in
/-- **The counit of `D(ι) ⊣ RQ_Z` is invertible on `D_QCoh(𝒪_Z)`** for a space with a terminal
affine chart. -/
theorem isIso_spaceDerivedInclusionAdjunction_counit_app_of_isTerminal
    (M : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (hM : derivedQuasicoherentProperty B S hS Z M) :
    IsIso ((spaceDerivedInclusionAdjunction B S hS Z).counit.app M) := by
  have := preservesFiniteColimits_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀aff
  have := reflectsIsomorphisms_quasicoherentSheavesι_comp_chartEvaluation B S hS Z hU₀ hU₀aff
  exact Stacks.DerivedCoherator.isIso_inclusionDerivedAdjunction_counit_app_of_derivedSections
    (quasicoherentSheavesι B S hS Z) (spaceCoheratorAdjunction B S hS Z)
    (spaceDerivedCoherator B S hS Z) (spaceDerivedCoheratorUnit B S hS Z)
    (chartEvaluation B S hS Z U₀) (chartDerivedEvaluation B S hS Z U₀)
    (chartDerivedEvaluationUnit B S hS Z U₀)
    (isIso_chartEvaluation_map_counit B S hS Z hU₀)
    (isIso_chartDerivedEvaluationUnit_app B S hS Z hU₀aff)
    (derivedQuasicoherentProperty B S hS Z)
    (derivedCategoryB_mapDerivedCategory_obj B S hS Z.1 Z.2)
    (isIso_of_isIso_chartDerivedEvaluation_map B S hS Z hU₀ hU₀aff)
    M hM

/-- **The comparison map of the derived coherator of an affine algebraic space is invertible at
every complex of quasi-coherent modules.** -/
theorem isIso_spaceDerivedCoheratorUnit_app_of_isAffineSpace (hZ : IsAffineSpace B S hS Z.1)
    (K : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    IsIso ((spaceDerivedCoheratorUnit B S hS Z).app
      ((quasicoherentSheavesι B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) |>.obj K)) := by
  obtain ⟨U₀, ⟨hU₀⟩, hU₀aff⟩ := exists_isTerminal_isAffine_chart B S hS Z hZ
  exact isIso_spaceDerivedCoheratorUnit_app_of_isTerminal B S hS Z hU₀ hU₀aff K

/-- **The counit of `D(ι) ⊣ RQ_Z` is invertible on `D_QCoh(𝒪_Z)`** for an affine algebraic
space. -/
theorem isIso_spaceDerivedInclusionAdjunction_counit_app_of_isAffineSpace
    (hZ : IsAffineSpace B S hS Z.1) (M : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (hM : derivedQuasicoherentProperty B S hS Z M) :
    IsIso ((spaceDerivedInclusionAdjunction B S hS Z).counit.app M) := by
  obtain ⟨U₀, ⟨hU₀⟩, hU₀aff⟩ := exists_isTerminal_isAffine_chart B S hS Z hZ
  exact isIso_spaceDerivedInclusionAdjunction_counit_app_of_isTerminal B S hS Z hU₀ hU₀aff M hM

/-- **[Stacks, Tag 08H0] (3), equivalence.**  For an affine algebraic space `X`, the comparison
functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence. -/
theorem quasicoherentDerivedComparison_isEquivalence_of_isAffineSpace
    (hZ : IsAffineSpace B S hS Z.1) :
    (quasicoherentDerivedComparison B S hS Z.1 Z.2).IsEquivalence :=
  quasicoherentDerivedComparison_isEquivalence_of_isIso_counit B S hS Z
    (isIso_spaceDerivedInclusionAdjunction_counit_app_of_isAffineSpace B S hS Z hZ)

end AlgebraicGeometry.Space

end
