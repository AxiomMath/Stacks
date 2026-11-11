module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricDerivedInvariants
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.KernelInvariantsForget
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricGaloisProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantDerivedGlobalSections
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExactHom

/-!
# The derived comparison with its Galois action

Let `X` be a geometrically connected smooth curve over `k`, `k̄` an algebraic closure of `k`,
separable over `k`, and `Q = Aut(k̄/k)`, the quotient of `π₁(X)` by the image of `π₁(X_{k̄})`
(`AlgebraicGeometry.geometricGaloisProjection`). The derived comparison
`AlgebraicGeometry.geometricDerivedInvariantsIso` of `RΓ(π₁(X_{k̄}), M)` with `RΓ(X_{k̄}, ℱ_ρ)`
lifts to the bounded below derived category of discrete `Λ`-`Q`-modules:

`RH⁰(π₁(X_{k̄}), M) ≅ RΓ^{Gal}(X_{k̄}, ℱ_ρ)`,

with `RH⁰(π₁(X_{k̄}), -)` the right derived functor of `M ↦ M^{π₁(X_{k̄})}` with its residual
`Q`-action (`Stacks.GroupCohomology.derivedKernelInvariants`) and `RΓ^{Gal}(X_{k̄}, -)` the right
derived functor of `F ↦ Γ(X_{k̄}, F|_{X_{k̄}})` with its Galois action
(`Stacks.EtaleCohomology.galoisGlobalSections`).

The degree-zero comparison is Galois-equivariant because it is built from the canonical
identification of Tag 03VL (`AlgebraicGeometry.geometricGlobalSectionsInvariantsEquiv_galois`).

## Main definitions

* `AlgebraicGeometry.geometricGaloisInvariantsToSections` — the degree-zero comparison
  `N^{π₁(X_{k̄})} ⟶ Γ(X_{k̄}, ℱ_N)` as a morphism of discrete `Λ`-`Q`-modules.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology

universe u

namespace AlgebraicGeometry

/-- The underlying module of a discrete Galois module is a left exact functor (pinned at the module
universe). -/
local instance (priority := 3000) preservesFiniteLimits_galoisModulesUnderlying (Λ : Type) [Ring Λ]
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteLimits
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
      (K ≃ₐ[k] K)

/-- The underlying module of a discrete Galois module is a right exact functor (pinned at the
module universe). -/
local instance (priority := 3000) preservesFiniteColimits_galoisModulesUnderlying
    (Λ : Type) [Ring Λ]
    {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K] :
    PreservesFiniteColimits
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat.{0, u, u + 1} Λ
      (K ≃ₐ[k] K)

attribute [local instance 3000] enoughInjectives_continuousModule_etaleFundamentalGroup
  enoughInjectives_etaleModules_zero Stacks.EtaleCohomology.galoisModules_enoughInjectives

section ExactHelpers

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- **An exact functor commutes with the cohomology functors of the bounded below derived
categories**, naturally: `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` read through the
inclusion `DerivedCategory.Plus.ι`. -/
def _root_.CategoryTheory.Functor.mapDerivedCategoryPlusHomologyNatIso (n : ℤ) :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor B n ≅
      DerivedCategory.Plus.homologyFunctor A n ⋙ F :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryHomologyIso n)

/-- **`F̄(X[0]) ≅ F(X)[0]`, naturally in `X`**, for an exact `F`. -/
def _root_.CategoryTheory.Functor.singleFunctorCompMapDerivedCategoryPlusIso [EnoughInjectives A] :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
  NatIso.ofComponents F.mapDerivedCategoryPlusObjSingleIso fun g ↦
    Stacks.DerivedFunctor.mapDerivedCategoryPlusObjSingleIso_hom_naturality (S := F) g

end ExactHelpers

section GaloisLeftExact

attribute [local instance] Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits

/-- **`Γ^Gal(Y_K, -)` is left exact**, its underlying functor `Γ(Y_K, -|_{Y_K})` being so and the
underlying module functor reflecting finite limits. -/
instance _root_.Stacks.EtaleCohomology.preservesFiniteLimits_galoisGlobalSections (Λ : Type)
    [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k))) [QuasiCompact Y.hom]
    [QuasiSeparated Y.hom] (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K] :
    PreservesFiniteLimits (Stacks.EtaleCohomology.galoisGlobalSections Λ Y K) :=
  haveI := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)
  haveI : PreservesFiniteLimits (Stacks.EtaleCohomology.galoisGlobalSections Λ Y K ⋙
      Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)) :=
    inferInstanceAs (PreservesFiniteLimits (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
      (Stacks.Frobenius.fieldBaseChangeProj Y K) ⋙
        Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
            (Stacks.Frobenius.fieldBaseChange Y K)))
  preservesFiniteLimits_of_reflects_of_preserves _
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))

end GaloisLeftExact

section GaloisDegreeZero

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  [ConnectedSpace X.1] [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (Λ : Type) [Ring Λ] [Finite Λ]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- The structure morphism of `Over.mk f` is quasi-compact. -/
instance quasiCompact_overMk_of_isCurve : QuasiCompact (Over.mk f).hom :=
  inferInstanceAs (QuasiCompact f)

/-- The structure morphism of `Over.mk f` is quasi-separated. -/
instance quasiSeparated_overMk_of_isCurve : QuasiSeparated (Over.mk f).hom :=
  inferInstanceAs (QuasiSeparated f)


omit [Smooth f] [GeometricallyConnected f] [IsAlgClosure k K] [Algebra.IsSeparable k K]
    [IsAlgClosed K] [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] in
/-- The Galois action commutes with `Γ(X_K, ℱ_P) ⟶ Γ(X_K, ℱ_N)`. -/
lemma galoisAction_geometricSectionsIncl (σ : K ≃ₐ[k] K)
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
    (P : FiniteStableSubmodule N)
    (z : (geometricRepresentationSheaf.{u, 0} B X
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ
        f K ⋙
      Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).obj P.toFinite) :
    Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) K σ
        ((discreteRepresentationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj N)
        (geometricSectionsIncl B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y N P z) =
      geometricSectionsIncl B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y N P
        (Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) K σ
          ((representationSheaf.{u, 0} B X
              (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj P.toFinite) z) :=
  (((ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom
    (Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction_naturality Λ (Over.mk f) K σ
      (finiteSubmoduleExtensionIncl
          (representationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ) P)) z)).trans
    (ConcreteCategory.comp_apply _ _ _)).symm

omit [Smooth f] in
/-- The canonical identification carries `ρ(γ)` on invariants to the Galois action of the image of
`γ` on global sections. -/
lemma galoisAction_geometricInvariantsGlobalSectionsIsoCanonical_hom
    (ρ : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
    (γ : EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))
        (a : (finiteTypeContinuousModuleToRes Λ
        (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
      continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj ρ)
    (ha : (ρ.obj.obj.obj.ρ γ).asHom.hom a.1 ∈ continuousModuleInvariantsSubmodule Λ _
      ((finiteTypeContinuousModuleToRes Λ
        (geometricFundamentalGroupMap B X f K
            (contains_fieldBaseChange_of_isCurve B X f K) y)).obj ρ)) :
    Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction Λ (Over.mk f) K
        (geometricGaloisProjection B X f K y γ)
        ((representationSheaf.{u, 0} B X
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj ρ)
            ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app ρ a) =
      (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app ρ
          ⟨(ρ.obj.obj.obj.ρ γ).asHom.hom a.1, ha⟩ := by
  have h := geometricInvariantsGlobalSectionsIsoCanonical_inv_galois B X f K Λ y ρ γ
    ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app ρ a)
  have h1 : ∀ b, (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).inv.app ρ
      ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app ρ b) = b := fun b ↦ by
    simp [← ConcreteCategory.comp_apply]
  rw [h1] at h
  have h3 : ∀ c, (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app ρ
      ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).inv.app ρ c) = c := fun c ↦ by
    simp [← ConcreteCategory.comp_apply]
  exact (h3 _).symm.trans
    (congrArg _ (Subtype.ext (a2 := ⟨(ρ.obj.obj.obj.ρ γ).asHom.hom a.1, ha⟩) h))

/-- **The degree-zero comparison with its Galois action**: `N^{π₁(X_{k̄})} ⟶ Γ(X_{k̄}, ℱ_N)` as a
morphism of discrete `Λ`-`Aut(k̄/k)`-modules, natural in the continuous discrete
`Λ`-`π₁(X)`-module `N`. Its underlying map is `AlgebraicGeometry.geometricInvariantsToSections`
for the canonical identification of Tag 03VL. -/
def geometricGaloisInvariantsToSections :
    kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
        (surjective_geometricGaloisProjection B X f K y) ⟶
      discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
          Λ ⋙
        Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K where
  app N := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := (kernelInvariantsForgetIso.{0, u} Λ
          (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
          (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
          (ker_geometricGaloisProjection B X f K y).symm).hom.app N ≫
        (geometricInvariantsToSections B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y
          (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y)).app N
      comm := fun σ ↦ by
        obtain ⟨γ, rfl⟩ := surjective_geometricGaloisProjection B X f K y σ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hφ : ∀ g, geometricGaloisProjection B X f K y
            (geometricFundamentalGroupMap B X f K
                (contains_fieldBaseChange_of_isCurve B X f K) y g) = 1 := fun g ↦ by
          have : geometricFundamentalGroupMap B X f K
              (contains_fieldBaseChange_of_isCurve B X f K) y g ∈
              (geometricGaloisProjection B X f K y : _ →* (K ≃ₐ[k] K)).ker := by
            rw [ker_geometricGaloisProjection]
            exact ⟨g, rfl⟩
          exact this
        let P := FiniteStableSubmodule.orbitSpan N {x.1} (Set.finite_singleton _)
        have hP : x.1 ∈ P.1 := FiniteStableSubmodule.subset_orbitSpan N _ _ (Set.mem_singleton _)
        have hγP : (N.obj.obj.ρ γ).asHom.hom x.1 ∈ P.1 := P.2.1 γ x.1 hP
        have hρ := kernelInvariantsQuotientRepresentation_apply Λ
            (geometricGaloisProjection B X f K y)
          (surjective_geometricGaloisProjection B X f K y) N γ x
        let xσ := ModuleCat.Hom.hom
            (((kernelInvariantsFunctor Λ (geometricGaloisProjection B X f K y)
          (surjective_geometricGaloisProjection B X f K y)).obj N).obj.obj.ρ
            (geometricGaloisProjection B X f K y γ)).asHom x
        have h1 := geometricInvariantsToSections_app_apply B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y
          (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y) N P
          ((kernelInvariantsForgetIso.{0, u} Λ
              (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
              (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
              (ker_geometricGaloisProjection B X f K y).symm).hom.app N xσ) (hρ ▸ hγP)
        have h2 := geometricInvariantsToSections_app_apply B X Λ f K
            (contains_fieldBaseChange_of_isCurve B X f K) y
            (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y) N P
          ((kernelInvariantsForgetIso.{0, u} Λ
              (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
              (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
              (ker_geometricGaloisProjection B X f K y).symm).hom.app N x) hP
        have ha : (P.toFinite.obj.obj.obj.ρ γ).asHom.hom
            (⟨x.1, hP⟩ : P.1) ∈ continuousModuleInvariantsSubmodule Λ _
              ((finiteTypeContinuousModuleToRes Λ
                (geometricFundamentalGroupMap B X f K
                    (contains_fieldBaseChange_of_isCurve B X f K) y)).obj P.toFinite) :=
          fun g ↦ Subtype.ext (rho_mem_kernelInvariants Λ (geometricGaloisProjection B X f K y) N γ
            x.2 _ (hφ g))
        have h3 := galoisAction_geometricInvariantsGlobalSectionsIsoCanonical_hom B X f K Λ y
          P.toFinite γ (⟨⟨x.1, hP⟩, fun g ↦ Subtype.ext (x.2 _ (hφ g))⟩ :
              (finiteTypeContinuousModuleToRes Λ
              (geometricFundamentalGroupMap B X f K
              (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
              continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
                (EtaleFundamentalGroup
                    (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj P.toFinite) ha
        have h4 := galoisAction_geometricSectionsIncl B X f K Λ y
          (geometricGaloisProjection B X f K y γ) N P
          ((geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y).hom.app P.toFinite
            (⟨⟨x.1, hP⟩, fun g ↦ Subtype.ext (x.2 _ (hφ g))⟩ :
                (finiteTypeContinuousModuleToRes Λ
                (geometricFundamentalGroupMap B X f K
                (contains_fieldBaseChange_of_isCurve B X f K) y) ⋙
              continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
                (EtaleFundamentalGroup
                    (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).obj P.toFinite))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        refine h1.trans ?_
        refine Eq.trans ?_ (congrArg (fun z ↦ ModuleCat.Hom.hom
          (((discreteRepresentationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ ⋙
            Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K).obj N).obj.obj.ρ
              (geometricGaloisProjection B X f K y γ)).asHom z) h2.symm)
        refine Eq.trans ?_ h4.symm
        refine congrArg (geometricSectionsIncl B X Λ f K
            (contains_fieldBaseChange_of_isCurve B X f K) y N P) ?_
        refine Eq.trans ?_ h3.symm
        exact congrArg _ (Subtype.ext (Subtype.ext hρ)) })
  naturality {N N'} h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (geometricInvariantsToSections B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y
          (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y)).app N')
        ((kernelInvariantsForgetIso.{0, u} Λ
              (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
              (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
              (ker_geometricGaloisProjection B X f K y).symm).hom.naturality h)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg ((kernelInvariantsForgetIso.{0, u} Λ
              (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
              (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
              (ker_geometricGaloisProjection B X f K y).symm).hom.app N ≫ ·)
          ((geometricInvariantsToSections B X Λ f K (contains_fieldBaseChange_of_isCurve B X f K) y
              (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y)).naturality h)).trans
        (Category.assoc _ _ _).symm

/-- **On finite modules the degree-zero comparison with its Galois action is an isomorphism**, its
underlying map being one. -/
instance isIso_geometricGaloisInvariantsToSections_app_ι
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    IsIso ((geometricGaloisInvariantsToSections B X f K Λ y).app
      (((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)))).obj M)) := by
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)
  have : IsIso ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)).map
      ((geometricGaloisInvariantsToSections B X f K Λ y).app
        (((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom)))).obj M))) :=
    IsIso.comp_isIso' inferInstance
      (isIso_geometricInvariantsToSections_app_ι B X Λ f K
        (contains_fieldBaseChange_of_isCurve B X f K) y
        (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y) M)
  exact isIso_of_reflects_iso _ (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
    (K ≃ₐ[k] K))

end GaloisDegreeZero

/-- The group cohomology δ-functor of `π₁(X_K)` on finite representations is elementwise
effaceable. -/
private theorem elementwiseEffaceable_geometricGroupCohomology
    (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
    [IsCurve k f] (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    [Algebra.IsAlgebraic k K] [ConnectedSpace X.1] [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] (Λ : Type) [Ring Λ] [Finite Λ]
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)) :
    (geometricGroupCohomology B X Λ f K
      (contains_fieldBaseChange_of_isCurve B X f K) y).ElementwiseEffaceable :=
  have := forall_finite_finiteEtaleFiberFunctor_obj y
  have := forall_finite_finiteEtaleFiberFunctor_obj
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
  elementwiseEffaceable_restrictedCohomologyDelta Λ _
    (isInducing_geometricFundamentalGroupMap B X f K
      (contains_fieldBaseChange_of_isCurve B X f K) y)

section GaloisDerived

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
      Functor.isTriangulated_rightDerivedFunctorPlus

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  [ConnectedSpace X.1] [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  [CompactSpace X.1] [QuasiSeparatedSpace X.1]
  (Λ : Type) [Ring Λ] [Finite Λ]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- `Γ^Gal(X_K, -)` is additive, stated on `EtaleModules Λ X` (the source category as it arises
from the codomain of `discreteRepresentationSheaf`, not reducibly equal to `(Over.mk f).left`). -/
instance additive_galoisGlobalSections_overMk :
    Functor.Additive (C := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ X.1)
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) :=
  Stacks.EtaleCohomology.galoisGlobalSections_additive Λ (Over.mk f) K

/-- The functor `discreteRepresentationSheaf` at the image of the geometric point `y` of `X_K` in
`X` preserves finite limits. -/
instance preservesFiniteLimits_discreteRepresentationSheaf_geometric :
    PreservesFiniteLimits
        (discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ) :=
  preservesFiniteLimits_discreteRepresentationSheaf B X _ Λ

/-- The functor `discreteRepresentationSheaf` at the image of the geometric point `y` of `X_K` in
`X` preserves finite colimits. -/
instance preservesFiniteColimits_discreteRepresentationSheaf_geometric :
    PreservesFiniteColimits
        (discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ) :=
  preservesFiniteColimits_discreteRepresentationSheaf B X _ Λ

/-- **The derived comparison with its Galois action**, `RH⁰(π₁(X_K), N) ⟶ RΓ^{Gal}(X_K, ℱ_N)` at a
continuous discrete `Λ`-`π₁(X)`-module `N`. -/
def geometricGaloisDerivedComparisonApp
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y)).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ⟶
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj N)) :=
  (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
      (geometricGaloisInvariantsToSections B X f K Λ y)).app _ ≫
    Stacks.DerivedIndexing.exactPrecompMap
        (discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
        (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) N

/-- The derived comparison with its Galois action, natural in `N`. -/
def geometricGaloisDerivedComparison :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y)).rightDerivedFunctorPlus ⟶
      (discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ) ⋙
          DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (Stacks.EtaleCohomology.galoisGlobalSections Λ
          (Over.mk f) K).rightDerivedFunctorPlus where
  app N := geometricGaloisDerivedComparisonApp B X f K Λ y N
  naturality {_ N'} h :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ Stacks.DerivedIndexing.exactPrecompMap
          (discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
          (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) N')
        ((Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
            (geometricGaloisInvariantsToSections B X f K Λ y)).naturality
          ((DerivedCategory.Plus.singleFunctor _ 0).map h))).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg ((Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
            (geometricGaloisInvariantsToSections B X f K Λ y)).app _ ≫ ·)
          (Stacks.DerivedIndexing.exactPrecompMap_naturality
              (discreteRepresentationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
              (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) h)).trans
        (Category.assoc _ _ _).symm

omit [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- The derived comparison with its Galois action commutes with the connecting morphisms. -/
theorem canonicalδ_comp_geometricGaloisDerivedComparisonApp
    {S : ShortComplex (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)))} (hS : S.ShortExact) (q : ℕ) :
    Stacks.DerivedIndexing.canonicalδ
        (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y)) hS q ≫
        (DerivedCategory.Plus.homologyFunctor _ ((q + 1 : ℕ) : ℤ)).map
          (geometricGaloisDerivedComparisonApp B X f K Λ y S.X₁) =
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          (geometricGaloisDerivedComparisonApp B X f K Λ y S.X₃) ≫
        Stacks.DerivedIndexing.canonicalδ
            (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)
            (hS.map_of_exact
            (discreteRepresentationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) q := by
  have h1 := Stacks.DerivedIndexing.canonicalδ_comp_rightDerivedFunctorPlusNatTrans
      (geometricGaloisInvariantsToSections B X f K Λ y) hS q
  have h2 := Stacks.DerivedIndexing.canonicalδ_comp_exactPrecompMap
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) hS q
  exact (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) h1).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) h2).trans <| (Category.assoc _ _ _).symm.trans <|
        congrArg (· ≫ _) (Functor.map_comp _ _ _).symm

omit [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- In degree zero the derived comparison with its Galois action is the degree-zero comparison. -/
theorem rightDerivedPlusUnitSingle_comp_geometricGaloisDerivedComparisonApp
    (N : Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
        (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y))).app N ≫
        geometricGaloisDerivedComparisonApp B X f K Λ y N =
      (DerivedCategory.Plus.singleFunctor _ 0).map
          ((geometricGaloisInvariantsToSections B X f K Λ y).app N) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
            (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)).app
            ((discreteRepresentationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj N) := by
  have h₂ := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_natTrans
      (geometricGaloisInvariantsToSections B X f K Λ y) N
  have h₃ := Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_compTrans
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K) N
  dsimp only [geometricGaloisDerivedComparisonApp, Stacks.DerivedIndexing.exactPrecompMap]
  rw [← Category.assoc, h₂, Category.assoc, ← Category.assoc _
      ((Stacks.DerivedIndexing.rightDerivedPlusCompTrans _ _).app _), h₃, Category.assoc,
    ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

attribute [local instance] Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits
  Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits

/-- The invariants under `π₁(X_K)` with their residual Galois action form a left exact functor:
forgetting the action they are the invariants of the restriction. -/
instance preservesFiniteLimits_geometricKernelInvariants : PreservesFiniteLimits
    (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
    (surjective_geometricGaloisProjection B X f K y)) :=
  haveI := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)
  haveI : PreservesFiniteLimits
      ((kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y)) ⋙
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))) :=
    preservesFiniteLimits_of_natIso
        (kernelInvariantsForgetIso.{0, u} Λ
        (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
      (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
      (ker_geometricGaloisProjection B X f K y).symm).symm
  preservesFiniteLimits_of_reflects_of_preserves _
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))

/-- `M ↦ ℱ_M` on finite representations is additive, stated on `EtaleModules Λ (Over.mk f).left`
(the source of `Γ^Gal`, not reducibly equal to `EtaleModules Λ X`). -/
instance additive_finiteTypeContinuousModuleι_comp_discreteRepresentationSheaf :
    Functor.Additive (D := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ (Over.mk f).left)
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
          (discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) :=
  inferInstanceAs (Functor.Additive
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)))

/-- `M ↦ ℱ_M` on finite representations is left exact, stated on
`EtaleModules Λ (Over.mk f).left`. -/
instance preservesFiniteLimits_finiteTypeContinuousModuleι_comp_discreteRepresentationSheaf :
    PreservesFiniteLimits (D := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ (Over.mk f).left)
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
          (discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) :=
  inferInstanceAs (PreservesFiniteLimits
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)))

/-- `M ↦ ℱ_M` on finite representations is right exact, stated on
`EtaleModules Λ (Over.mk f).left`. -/
instance preservesFiniteColimits_finiteTypeContinuousModuleι_comp_discreteRepresentationSheaf :
    PreservesFiniteColimits (D := Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ (Over.mk f).left)
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
          (discreteRepresentationSheaf B X
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) :=
  inferInstanceAs (PreservesFiniteColimits
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)))

/-- The source δ-functor with its Galois action: `M ↦ Hⁱ(π₁(X_K), M)` with the residual action of
`Aut(K/k)`, on finite representations. -/
abbrev geometricGaloisSourceDelta : DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
          (Stacks.EtaleCohomology.GaloisModules Λ k K) :=
  (Stacks.DerivedIndexing.plusDelta
      (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
      (surjective_geometricGaloisProjection B X f K y))).precomp
      (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))

/-- The target δ-functor with its Galois action: `M ↦ Hⁱ(X_K, ℱ_M)` with its Galois action, on
finite representations. -/
abbrev geometricGaloisTargetDelta : DeltaFunctor (FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
          (Stacks.EtaleCohomology.GaloisModules Λ k K) :=
  (Stacks.DerivedIndexing.plusDelta
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)).precomp
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ))

/-- **The derived comparison with its Galois action on cohomology**, as a morphism of δ-functors
on finite representations. -/
def geometricGaloisComparisonDelta :
    geometricGaloisSourceDelta B X f K Λ y ⟶ geometricGaloisTargetDelta B X f K Λ y where
  app n :=
    { app M := (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
        ((geometricGaloisDerivedComparison B X f K Λ y).app
            ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
            (EtaleFundamentalGroup X.1
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M))
      naturality _ _ h :=
        ((DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map_comp _ _).symm.trans <|
          (congrArg (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map
            ((geometricGaloisDerivedComparison B X f K Λ y).naturality
                ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
                (EtaleFundamentalGroup X.1
                (y.map (fieldBaseChangeObjProj B X f K
                (contains_fieldBaseChange_of_isCurve B X f K)).hom))).map h))).trans
          ((DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).map_comp _ _) }
  comm {_} hS n := (canonicalδ_comp_geometricGaloisDerivedComparisonApp B X f K Λ y
    (hS.map_of_exact
        (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom)))) n).symm

/-- Forgetting the Galois action, the source δ-functor is the one of
`AlgebraicGeometry.geometricDerivedSourceDelta`, degreewise. -/
def geometricGaloisSourceForgetIso (n : ℕ) :
    ((geometricGaloisSourceDelta B X f K Λ y).mapExact
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))).functor n ≅
      (geometricDerivedSourceDelta B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y).functor n :=
  Functor.isoWhiskerLeft
      ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
          (surjective_geometricGaloisProjection B X f K y)).rightDerivedFunctorPlus)
          ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
          Λ (K ≃ₐ[k] K)).mapDerivedCategoryPlusHomologyNatIso (n : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
        DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight
          (derivedKernelInvariantsForgetIso.{0, u} Λ
          (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y)
        (geometricGaloisProjection B X f K y) (surjective_geometricGaloisProjection B X f K y)
        (ker_geometricGaloisProjection B X f K y).symm
        (isInducing_geometricFundamentalGroupMap B X f K
            (contains_fieldBaseChange_of_isCurve B X f K) y))
        (DerivedCategory.Plus.homologyFunctor _ (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft
        (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
        (Functor.isoWhiskerRight
      (continuousModuleRes.{0, u + 1, u + 1} Λ
          (geometricFundamentalGroupMap B X f K
          (contains_fieldBaseChange_of_isCurve B X f K)
          y)).singleFunctorCompMapDerivedCategoryPlusIso
      ((continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
          (EtaleFundamentalGroup
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (n : ℤ)))

/-- Forgetting the Galois action, the target δ-functor is the one of
`AlgebraicGeometry.geometricDerivedTargetDelta`, degreewise. -/
def geometricGaloisTargetForgetIso (n : ℕ) :
    ((geometricGaloisTargetDelta B X f K Λ y).mapExact
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))).functor n ≅
      (geometricDerivedTargetDelta B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y).functor n :=
  Functor.isoWhiskerLeft
      (((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
      (discreteRepresentationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f K
      (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) ⋙
      DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K).rightDerivedFunctorPlus)
          ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
          Λ (K ≃ₐ[k] K)).mapDerivedCategoryPlusHomologyNatIso (n : ℤ)).symm ≪≫
    Functor.isoWhiskerLeft
        (((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
        (discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) ⋙
        DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.isoWhiskerRight (Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso Λ
        (Over.mk f) K) (DerivedCategory.Plus.homologyFunctor _ (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
        (discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)) (Functor.isoWhiskerRight
      (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChangeProj
          (Over.mk f) K)).singleFunctorCompMapDerivedCategoryPlusIso
      ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
          (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (n : ℤ)))

/-- The source δ-functor of `AlgebraicGeometry.geometricDerivedSourceDelta` is group cohomology,
degreewise. -/
def geometricDerivedSourceGroupCohomologyIso (n : ℕ) :
    (geometricDerivedSourceDelta B X Λ f K
        (contains_fieldBaseChange_of_isCurve B X f K) y).functor n ≅
      (geometricGroupCohomology B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y).functor n :=
  Functor.isoWhiskerLeft
      (finiteTypeContinuousModuleToRes Λ
      (geometricFundamentalGroupMap B X f K (contains_fieldBaseChange_of_isCurve B X f K) y))
      (Stacks.DerivedIndexing.rightDerivedIso
      (continuousModuleRingInvariants.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y)) n).symm

omit [Smooth f] in
/-- Forgetting the Galois action, the source δ-functor is universal: it is group cohomology of
`π₁(X_K)` degreewise, which is effaceable one class at a time. -/
theorem isUniversal_mapExact_geometricGaloisSourceDelta :
    ((geometricGaloisSourceDelta B X f K Λ y).mapExact
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))).IsUniversal :=
  have := elementwiseEffaceable_geometricGroupCohomology B X f K Λ y
  have : ((geometricGaloisSourceDelta B X f K Λ y).mapExact
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
      Λ (K ≃ₐ[k] K))).ElementwiseEffaceable :=
    DeltaFunctor.ElementwiseEffaceable.of_iso fun n ↦
      geometricGaloisSourceForgetIso B X f K Λ y n ≪≫
          geometricDerivedSourceGroupCohomologyIso B X f K Λ y n
  DeltaFunctor.isUniversal_of_elementwiseEffaceable _

omit [IsAlgClosed K] in
/-- Forgetting the Galois action, the target δ-functor is universal: degreewise it is
`M ↦ Hⁱ(X_K, ℱ_M)`, which is group cohomology of `π₁(X_K)` under the source's hypotheses. -/
theorem isUniversal_mapExact_geometricGaloisTargetDelta (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    ((geometricGaloisTargetDelta B X f K Λ y).mapExact
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))).IsUniversal :=
  have := elementwiseEffaceable_geometricGroupCohomology B X f K Λ y
  have hT := isUniversal_geometricRepresentationCohomology_of_not_iso_projectiveLine B X f K Λ y
    hΛ hP
  have : ((geometricGaloisTargetDelta B X f K Λ y).mapExact
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
      Λ (K ≃ₐ[k] K))).ElementwiseEffaceable :=
    DeltaFunctor.ElementwiseEffaceable.of_iso fun n ↦
      have := isIso_geometricDerivedComparisonDelta_app B X Λ f K
          (contains_fieldBaseChange_of_isCurve B X f K) y
          (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y) hT n
      geometricGaloisTargetForgetIso B X f K Λ y n ≪≫
        (asIso ((geometricDerivedComparisonDelta B X Λ f K
            (contains_fieldBaseChange_of_isCurve B X f K) y
            (geometricInvariantsGlobalSectionsIsoCanonical B X f K Λ y)).app n)).symm ≪≫
        geometricDerivedSourceGroupCohomologyIso B X f K Λ y n
  DeltaFunctor.isUniversal_of_elementwiseEffaceable _

omit [CompactSpace X.1] [QuasiSeparatedSpace X.1] in
/-- In degree zero the comparison with its Galois action is an isomorphism on finite
representations. -/
theorem isIso_geometricGaloisComparisonDelta_app_zero :
    IsIso ((geometricGaloisComparisonDelta B X f K Λ y).app 0) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦ ?_)
  have hfac := rightDerivedPlusUnitSingle_comp_geometricGaloisDerivedComparisonApp B X f K Λ y
    ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M)
  have h1 := Stacks.DerivedIndexing.isIso_homologyFunctor_zero_map_rightDerivedPlusUnitSingle_app
    (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
        (surjective_geometricGaloisProjection B X f K y))
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M)
  have h2 := Stacks.DerivedIndexing.isIso_homologyFunctor_zero_map_rightDerivedPlusUnitSingle_app
    (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)
        ((discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M))
  have h4 : IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((geometricGaloisInvariantsToSections B X f K Λ y).app
              ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
              (EtaleFundamentalGroup X.1
              (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M)) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle
            (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)).app
            ((discreteRepresentationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj
            ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
            (EtaleFundamentalGroup X.1
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M)))) := by
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' inferInstance h2
  rw [← hfac, Functor.map_comp] at h4
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h4

/-- **The comparison with its Galois action is an isomorphism of δ-functors on finite
representations**, under the source's hypotheses: forgetting the action both sides are universal
δ-functors, the comparison is an isomorphism in degree zero, and forgetting the action reflects
isomorphisms. -/
theorem isIso_geometricGaloisComparisonDelta_app (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) (n : ℕ) :
    IsIso ((geometricGaloisComparisonDelta B X f K Λ y).app n) := by
  have := isUniversal_mapExact_geometricGaloisSourceDelta B X f K Λ y
  have := isUniversal_mapExact_geometricGaloisTargetDelta B X f K Λ y hΛ hP
  have : IsIso ((DeltaFunctor.mapExactHom
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
      (geometricGaloisComparisonDelta B X f K Λ y)).app 0) := by
    have := isIso_geometricGaloisComparisonDelta_app_zero B X f K Λ y
    rw [DeltaFunctor.mapExactHom_app]
    exact (inferInstance : IsIso (Functor.whiskerRight
      ((geometricGaloisComparisonDelta B X f K Λ y).app 0)
          (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))))
  let e := DeltaFunctor.IsUniversal.isoOfIso
    (asIso ((DeltaFunctor.mapExactHom
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
        (geometricGaloisComparisonDelta B X f K Λ y)).app 0))
  have h : DeltaFunctor.mapExactHom
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
      (geometricGaloisComparisonDelta B X f K Λ y) = e.hom :=
    DeltaFunctor.IsUniversal.hom_ext_zero _ (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
      (asIso ((DeltaFunctor.mapExactHom
          (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
          (geometricGaloisComparisonDelta B X f K Λ y)).app 0))).symm
  have : IsIso ((DeltaFunctor.mapExactHom
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
      (geometricGaloisComparisonDelta B X f K Λ y)).app n) := by
    rw [h]
    exact ⟨⟨e.inv.app n, congrArg (fun η ↦ DeltaFunctor.Hom.app η n) e.hom_inv_id,
      congrArg (fun η ↦ DeltaFunctor.Hom.app η n) e.inv_hom_id⟩⟩
  have := reflectsIsomorphisms_injectivesContinuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦ ?_)
  have : IsIso ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K)).map
      (((geometricGaloisComparisonDelta B X f K Λ y).app n).app M)) :=
    NatIso.isIso_app_of_isIso
        ((DeltaFunctor.mapExactHom
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))
      (geometricGaloisComparisonDelta B X f K Λ y)).app n) M
  exact isIso_of_reflects_iso _
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (K ≃ₐ[k] K))

/-- **The derived comparison with its Galois action is an isomorphism on finite representations**,
under the source's hypotheses. -/
theorem isIso_geometricGaloisDerivedComparison_app (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))
            (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
            (EtaleFundamentalGroup X.1
            (y.map (fieldBaseChangeObjProj B X f K
            (contains_fieldBaseChange_of_isCurve B X f K)).hom))) :
    IsIso ((geometricGaloisDerivedComparison B X f K Λ y).app
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M)) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  cases n with
  | ofNat m =>
    have := isIso_geometricGaloisComparisonDelta_app B X f K Λ y hΛ hP m
    exact NatIso.isIso_app_of_isIso ((geometricGaloisComparisonDelta B X f K Λ y).app m) M
  | negSucc m =>
    have h1 := Functor.isZero_rightDerivedPlus_of_neg
        (kernelInvariantsFunctor.{0, u + 1, u, u + 1} Λ (geometricGaloisProjection B X f K y)
        (surjective_geometricGaloisProjection B X f K y))
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M) (Int.negSucc m)
      (Int.negSucc_lt_zero m)
    have h2 := Functor.isZero_rightDerivedPlus_of_neg
        (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K)
        ((discreteRepresentationSheaf B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ).obj
        ((finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))).obj M))
      (Int.negSucc m) (Int.negSucc_lt_zero m)
    exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩

end GaloisDerived

section GaloisSourceHypotheses

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K] (Λ : Type) [Ring Λ] [Finite Λ]

/-- **The derived version of `H^i(X_{k̄}, ℱ_ρ) = H^i(π₁(X_{k̄}), M)` with its Galois action**
([Stacks, Tag 03VM], "Moreover, in this case there is a derived version too"): for a geometrically
connected smooth curve `X` over `k`, `k̄` an algebraic closure of `k`, separable over `k`, `Λ` a
finite ring with `#Λ` invertible in `k`, and `X_{k̄} ≇ 𝐏¹_{k̄}`, there is an isomorphism

`RH⁰(π₁(X_{k̄}), M) ≅ RΓ^{Gal}(X_{k̄}, ℱ_ρ)`

in the bounded below derived category of discrete `Λ`-modules with a continuous action of
`Aut(k̄/k)`, natural in the finite `Λ`-module `M` with continuous action `ρ` of `π₁(X)`. Here
`RH⁰(π₁(X_{k̄}), -)` is the right derived functor of the invariants under `π₁(X_{k̄})` with their
residual action of `π₁(X)/π₁(X_{k̄}) = Aut(k̄/k)`
(`Stacks.GroupCohomology.derivedKernelInvariants`), and `RΓ^{Gal}(X_{k̄}, -)` that of global
sections on `X_{k̄}` with their Galois action
(`Stacks.EtaleCohomology.galoisDerivedGlobalSections`). The degree-zero identification is the
canonical one of Tag 03VL. The case of an arbitrary field `k`, where `k̄` need not be separable
over `k`, is `AlgebraicGeometry.geometricGaloisDerivedInvariantsIsoOfAlgClosure`, which reduces to
this one over the perfect closure of `k` in `k̄`. -/
def geometricGaloisDerivedInvariantsIso
    (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : Stacks.Frobenius.fieldBaseChange (Over.mk f) K ≅
        projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f K
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom))) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedKernelInvariants.{0, u + 1, u, 0} Λ (geometricGaloisProjection B X f K y)
          (surjective_geometricGaloisProjection B X f K y) ≅
      representationSheaf.{u, 0} B X
          (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)
          Λ ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Stacks.EtaleCohomology.galoisDerivedGlobalSections Λ (Over.mk f) K :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f K
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI := quasiSeparatedSpace_of_quasiSeparated f
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  haveI : IsIso (Functor.whiskerLeft
      (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
      (geometricGaloisDerivedComparison B X f K Λ y)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦
      isIso_geometricGaloisDerivedComparison_app B X f K Λ y hΛ hP M
  asIso (Functor.whiskerLeft
      (finiteTypeContinuousModuleι.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X.1
      (y.map (fieldBaseChangeObjProj B X f K (contains_fieldBaseChange_of_isCurve B X f K)).hom)))
      (geometricGaloisDerivedComparison B X f K Λ y)) ≪≫
    Functor.isoWhiskerRight
        (discreteRepresentationSheafιIso B X
        (y.map (fieldBaseChangeObjProj B X f K
        (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ)
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (Stacks.EtaleCohomology.galoisGlobalSections Λ (Over.mk f) K).rightDerivedFunctorPlus)

end GaloisSourceHypotheses

end AlgebraicGeometry

end
