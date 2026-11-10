module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsRepresented

/-!
# Derived sections over an affine étale chart, naturally

Let `U` be an affine étale chart of an algebraic space `X`, with `u : h_U ⟶ X` the chart morphism.
`AlgebraicGeometry.Space.nonempty_derivedSections_iso_representedAffineDerivedSections` identifies
`RΓ(U, K)` with `RΓ(h_U, u^*K)` for each `K`. This file builds the identification as a natural
isomorphism of functors on `D(𝒪_X)`: the comparison `RΓ(U, -) ⟶ RΓ(h_U, u^*(-))` induced, by the
universal property of the right derived functor `RΓ(U, -)`, by the sections over the self chart
(`selfChartSectionsIso`), and its invertibility.

## Main definitions

* `AlgebraicGeometry.Space.representedChartToSpace`: the chart morphism `u : h_U ⟶ X`, with its
  source spelled as the represented algebraic space of the chart.
* `AlgebraicGeometry.Space.chartSectionsHomotopyComparison`: the comparison on the homotopy
  category.
* `AlgebraicGeometry.Space.chartDerivedSectionsComparison`: `RΓ(U, -) ⟶ RΓ(h_U, u^*(-))`.

## Main results

* `AlgebraicGeometry.Space.isIso_chartDerivedSectionsComparison`: the comparison is an
  isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasRightDerivedFunctor_chartSections

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
  (U : SmallEtale B S hS X.1)

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))]

/-- The chart morphism `u : h_U ⟶ X`, with its source spelled as the represented algebraic space
`h_U = ⟨yoneda.obj U, _⟩` of the chart, the source of the sections functor
`representedAffineSections`. -/
abbrev representedChartToSpace :
    (⟨yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U),
      isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj U)⟩ :
        AlgebraicSpaces B S hS) ⟶ X :=
  chartToSpace B S hS X U

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))] in
/-- The chart morphism `representedChartToSpace X U : h_U ⟶ X` is étale. -/
theorem isEtale_representedChartToSpace : IsEtale B S hS (representedChartToSpace X U).hom :=
  isEtale_chartToSpace B S hS X U

/-- Pullback of étale modules along `representedChartToSpace X U` is additive. -/
instance additive_etaleModulePullback_representedChartToSpace :
    (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
      (isEtale_representedChartToSpace X U)).Additive :=
  etaleModulePullback_additive B S hS _ _

/-- Pullback of étale modules along `representedChartToSpace X U` preserves finite limits. -/
instance preservesFiniteLimits_etaleModulePullback_representedChartToSpace :
    PreservesFiniteLimits
      (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)) :=
  preservesFiniteLimits_etaleModulePullback B S hS _ _

/-- Pullback of étale modules along `representedChartToSpace X U` preserves finite colimits. -/
instance preservesFiniteColimits_etaleModulePullback_representedChartToSpace :
    PreservesFiniteColimits
      (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)) :=
  preservesFiniteColimits_etaleModulePullback B S hS _ _

/-- Evaluation at `U` is restriction along `u` followed by sections over the self chart
(definitionally); this splits it on homotopy categories, followed by localization. -/
def chartSectionsHomotopySelfChartIso :=
  Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
          (isEtale_representedChartToSpace X U) ⋙
        selfChartEvaluation B S hS ((SmallEtale.toOver B S hS X.1).obj U)))
      (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- `selfChartSectionsIso` on homotopy categories. -/
def selfChartSectionsHomotopyIso (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] :
    (selfChartEvaluation B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (representedAffineSections B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory (selfChartSectionsIso B S hS T).hom (ComplexShape.up ℤ)
  inv := NatTrans.mapHomotopyCategory (selfChartSectionsIso B S hS T).inv (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- `selfChartSectionsIso` on homotopy categories, after `u^*` and before localization. -/
def chartSectionsHomotopySelfChartMap :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      ((etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)).mapHomotopyCategory (ComplexShape.up ℤ))
      (selfChartSectionsHomotopyIso ((SmallEtale.toOver B S hS X.1).obj U))) DerivedCategory.Qh

/-- The unit of the derived sections over `h_U`, after `u^*` on homotopy categories. -/
def chartSectionsHomotopyUnit :=
  Functor.whiskerLeft ((etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)).mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.totalRightDerivedUnit
        ((representedAffineSections B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-- The factorization of `(u^*)_D` through the homotopy category, before the derived sections over
`h_U`. -/
def chartSectionsHomotopyFactors :=
  Functor.isoWhiskerRight (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
        (isEtale_representedChartToSpace X U)).mapDerivedCategoryFactorsh
      (representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U))

/-- The degreewise identification of `chartSectionsEvaluationIso`, followed by the unit of the
derived sections over `h_U` and the factorization of `(u^*)_D` through the homotopy category. -/
def chartSectionsHomotopyComparison :
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⟶
      DerivedCategory.Qh ⋙
        (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
          (isEtale_representedChartToSpace X U)).mapDerivedCategory ⋙
        representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U) :=
  (chartSectionsHomotopySelfChartIso X U).inv ≫ (chartSectionsHomotopySelfChartMap X U).hom ≫
    chartSectionsHomotopyUnit X U ≫ (chartSectionsHomotopyFactors X U).inv

/-- **`RΓ(U, -) ⟶ RΓ(h_U, u^*(-))`**, induced by `chartSectionsHomotopyComparison` through the
universal property of the right derived functor `RΓ(U, -)`. -/
def chartDerivedSectionsComparison :
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⟶
      (etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
          (isEtale_representedChartToSpace X U)).mapDerivedCategory ⋙
        representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U) :=
  (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        U).rightDerivedDesc
    (Functor.totalRightDerivedUnit _ _ _) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
    (chartSectionsHomotopyComparison X U)

/-- The defining property of `chartDerivedSectionsComparison`. -/
theorem chartDerivedSectionsComparison_fac
    (K : HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :
    (Functor.totalRightDerivedUnit
        (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U)
        DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app K ≫
      (chartDerivedSectionsComparison X U).app (DerivedCategory.Qh.obj K) =
      (chartSectionsHomotopyComparison X U).app K :=
  Functor.rightDerived_fac_app _ _ _ _ _ _

/-- **`RΓ(U, -) ≅ RΓ(h_U, u^*(-))`**: the comparison `chartDerivedSectionsComparison` is an
isomorphism. -/
instance isIso_chartDerivedSectionsComparison : IsIso (chartDerivedSectionsComparison X U) := by
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have := isGrothendieckAbelian_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  suffices h : ∀ K, IsIso ((chartDerivedSectionsComparison X U).app K) from
    NatIso.isIso_of_isIso_app _
  intro K
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    (A := Modules.{u, u} B S hS X.1 X.2) DerivedCategory.Qh K
  refine (NatTrans.isIso_app_iff_of_iso _ e).mp ?_
  have hJ := isKInjective_etaleModulePullback_of_isEtale B S hS (representedChartToSpace X U)
    (isEtale_representedChartToSpace X U) I hI
  have h₁ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U)
    DerivedCategory.Qh
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U)
    (Functor.totalRightDerivedUnit _ _ _) I hI
  have h₂ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    ((representedAffineSections B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh (representedAffineDerivedSections B S hS T)
    (Functor.totalRightDerivedUnit _ _ _) _ hJ
  have : IsIso ((chartSectionsHomotopyUnit X U).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := h₂
  have : IsIso ((chartSectionsHomotopyComparison X U).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    IsIso.comp_isIso' (Iso.isIso_inv ((chartSectionsHomotopySelfChartIso X U).app _))
      (IsIso.comp_isIso' (Iso.isIso_hom ((chartSectionsHomotopySelfChartMap X U).app _))
        (IsIso.comp_isIso' h₂ (Iso.isIso_inv ((chartSectionsHomotopyFactors X U).app _))))
  rw [← chartDerivedSectionsComparison_fac] at this
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ this

end AlgebraicGeometry.Space

end
