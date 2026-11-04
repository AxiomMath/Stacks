module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkAffineHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence

/-!
# Derived sections over an affine étale chart are derived sections of the restriction

Let `U` be an affine étale chart of an algebraic space `X`, with ring of functions `R`, and let
`u : h_U ⟶ X` be the represented chart morphism. The derived sections `RΓ(U, K)` of
`K ∈ D(𝒪_X)` over the chart, the complex Tag 0CSX (3) is about, are the derived sections over
the affine algebraic space `h_U` of the restriction `u^*K`:

`RΓ(U, K) ≅ RΓ(h_U, u^*K)` in `D(R)`.

On modules, the sections of a module `F` on `h_U` over the self chart are its sections
`Γ(h_U, F)` over the top chart, `R`-linearly (the self chart and the top chart are isomorphic),
and the sections over the self chart of `u^*G` are the sections of `G` over `U`. On derived
categories both sides are computed on a K-injective complex `I`, because restriction along the
étale `u` has the exact left adjoint `u_!` and so preserves K-injective complexes.

## Main results

* `AlgebraicGeometry.Space.selfChartSectionsIso`: `F(h_U) ≅ Γ(h_U, F)` naturally and
  `R`-linearly.
* `AlgebraicGeometry.Space.nonempty_derivedSections_iso_representedAffineDerivedSections`:
  `RΓ(U, K) ≅ RΓ(h_U, u^*K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

section SelfChart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The top chart of `h_T` is isomorphic to the self chart: its scheme is the open subscheme
`⊤` of `T`. -/
instance isIso_toSelfChart_representedAffineTopChart :
    IsIso (toSelfChart B S hS T (representedAffineTopChart B S hS T)) := by
  have h : IsIso ((BigFppfOver.toScheme B S hS).map
      ((CostructuredArrow.proj yoneda (yoneda.obj T)).map
        ((IsEtaleChart B S hS (yoneda.obj T)).ι.map
          (toSelfChart B S hS T (representedAffineTopChart B S hS T))))) := by
    change IsIso (Scheme.topIso _).hom
    infer_instance
  have h₁ : IsIso ((CostructuredArrow.proj yoneda (yoneda.obj T)).map
      ((IsEtaleChart B S hS (yoneda.obj T)).ι.map
        (toSelfChart B S hS T (representedAffineTopChart B S hS T)))) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  have h₂ : IsIso ((IsEtaleChart B S hS (yoneda.obj T)).ι.map
      (toSelfChart B S hS T (representedAffineTopChart B S hS T))) :=
    isIso_of_reflects_iso _ (CostructuredArrow.proj yoneda (yoneda.obj T))
  exact isIso_of_reflects_iso _ (IsEtaleChart B S hS (yoneda.obj T)).ι

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- A global function `r` acts on `Γ(h_T, F)`, the sections over the top chart, through its
restriction to the top chart. -/
theorem smul_representedAffineSections
    (F : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (y : (representedAffineSections B S hS T).obj F) :
    r • y = sheafSectionSmul
      (R := smallEtaleRingSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
        F (representedAffineTopChart B S hS T) (representedAffineTopChartSection B S hS T r) y := by
  rw [← structureMap_app_top_eq]
  rfl

/-- Sections over the self chart of `h_T`, as modules over `Γ(T, 𝒪_T)`. -/
abbrev selfChartEvaluation :
    Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  SheafOfModules.evaluation.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O))
    (op (selfChart B S hS T))

/-- Evaluation at the self chart is an additive functor. -/
instance additive_selfChartEvaluation : (selfChartEvaluation B S hS T).Additive :=
  inferInstanceAs (SheafOfModules.evaluation.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O))
    (op (selfChart B S hS T))).Additive

/-- The sections of a module on `h_T` over the self chart, as a module over `Γ(T, 𝒪_T)`. -/
abbrev selfChartSections
    (F : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  (selfChartEvaluation B S hS T).obj F

/-- Restriction from the self chart to the top chart, `F(h_T) ⟶ Γ(h_T, F)`. -/
def selfChartToSections
    (F : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    selfChartSections B S hS T F ⟶ (representedAffineSections B S hS T).obj F :=
  ModuleCat.ofHom (R := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (X := selfChartSections B S hS T F) (Y := (representedAffineSections B S hS T).obj F)
  { toFun x := (show (representedAffineSections B S hS T).obj F from
      (F.val.map (toSelfChart B S hS T (representedAffineTopChart B S hS T)).op).hom x)
    map_add' x y :=
      (F.val.map (toSelfChart B S hS T (representedAffineTopChart B S hS T)).op).hom.map_add x y
    map_smul' r x := by
      refine (F.val.map_smul (toSelfChart B S hS T (representedAffineTopChart B S hS T)).op
        r x).trans ?_
      exact (smul_representedAffineSections B S hS T F r _).symm }

/-- Restriction from the self chart to the top chart is an isomorphism, the two charts being
isomorphic. -/
instance isIso_selfChartToSections
    (F : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    IsIso (selfChartToSections B S hS T F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso
    (F.val.presheaf.mapIso
      (asIso (toSelfChart B S hS T (representedAffineTopChart B S hS T))).op).hom

/-- **The sections over the self chart are the sections over `h_T`**, naturally and linearly
over `Γ(T, 𝒪_T)`. -/
def selfChartSectionsIso : selfChartEvaluation B S hS T ≅ representedAffineSections B S hS T :=
  NatIso.ofComponents (fun F => asIso (selfChartToSections B S hS T F)) fun {F G} φ => by
    ext x
    exact (PresheafOfModules.naturality_apply φ.val
      (toSelfChart B S hS T (representedAffineTopChart B S hS T)).op x).symm

end SelfChart

/-! ### Derived sections over an affine chart -/

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasRightDerivedFunctor_chartSections

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
  (U : SmallEtale B S hS X.1)

variable [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))]

/-- **`RΓ(U, K) ≅ RΓ(h_U, u^*K)`** for an affine étale chart `U` of `X`, `u : h_U ⟶ X` the
chart morphism and any `K ∈ D(𝒪_X)`. -/
theorem nonempty_derivedSections_iso_representedAffineDerivedSections
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    Nonempty ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
          U).obj K ≅
      (representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj K)) := by
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  let T := (SmallEtale.toOver B S hS X.1).obj U
  let u := chartToSpace B S hS X U
  have hu := isEtale_chartToSpace B S hS X U
  obtain ⟨I, hI, ⟨eI⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    (A := Modules.{u, u} B S hS X.1 X.2) DerivedCategory.Qh K
  have : I.IsKInjective := hI
  have hJ : CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS u hu).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    isKInjective_etaleModulePullback B S hS u hu (etaleModuleLowerShriekAdjunction B S hS u hu) I hI
  have := isGrothendieckAbelian_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have h₁ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) U)
    DerivedCategory.Qh
    (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) U)
    (Functor.totalRightDerivedUnit _ _ _) I hI
  have h₂ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    ((representedAffineSections B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh (representedAffineDerivedSections B S hS T)
    (Functor.totalRightDerivedUnit _ _ _) _ hJ
  let e₀ : ((representedAffineSections B S hS T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleModulePullback.{u, u} B S hS u hu).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≅
      ((SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
          (op U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
    (NatIso.mapHomologicalComplex (selfChartSectionsIso B S hS T) (ComplexShape.up ℤ)).symm.app
        (((etaleModulePullback.{u, u} B S hS u hu).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
  let e₁ : (etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModulePullback.{u, u} B S hS u hu).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
    (etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.mapIso
        (eI.symm ≪≫ (DerivedCategory.quotientCompQhIso _).app I) ≪≫
      (etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategoryFactors.app I ≪≫
      ((DerivedCategory.quotientCompQhIso _).app _).symm
  exact ⟨(Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
        U).mapIso eI.symm ≪≫
    (asIso ((Functor.totalRightDerivedUnit
      (Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) U)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso e₀.symm) ≪≫
    @asIso _ _ _ _ ((Functor.totalRightDerivedUnit
      ((representedAffineSections B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModulePullback.{u, u} B S hS u hu).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)))
      h₂ ≪≫
    (representedAffineDerivedSections B S hS T).mapIso e₁.symm⟩

end Derived

end AlgebraicGeometry.Space

end
