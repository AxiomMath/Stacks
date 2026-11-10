module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSelfMapCohomologyEndo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyIntComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactUnitSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyColimit

/-!
# Pullback along an integral self-map, read on the cohomology of the underlying abelian sheaf

Let `Λ` be a ring, not necessarily commutative, `φ : Y ⟶ Y` an integral morphism of schemes and
`N` a sheaf of `Λ`-modules on `Y_étale` with a linearization `α : N ⟶ φ_* N`. The pullback action
`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo` of `φ` on `Hⁱ(Y, N)` is `Hⁱ(Y, α)`
followed by `Hⁱ(Y, φ_* N) ≅ Hⁱ(Y, N)`. This file reads it on Mathlib's sheaf cohomology of the
underlying abelian sheaf, through `Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)`
(`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH`): it is the restriction map along
`φ` followed by the map induced by the adjoint `φ^{-1}(α) ≫ ε` of `α`
(`etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo`).

The comparison passes through `ℤ`. The identification `Hⁱ(B, g_* H) ≅ Hⁱ(A, H)` for an integral
`g` (`Stacks.EtaleCohomology.integralDirectImageCohomologyIso`) commutes with restriction of
scalars along `ℤ →+* Λ` (`integralDirectImageCohomologyIso_hom_restrictScalarsInt`); this rests on
the compatibility of `res_ρ` with the comparison `RΓ(A, -) ≅ Rg_* ⋙ RΓ(B, -)`
(`restrictScalars_derivedGlobalSectionsCompIso`), an instance of
`CategoryTheory.Functor.rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso`, and
of `res_ρ` with `(g_* H)[0] ≅ Rg_*(H[0])`. Over the commutative ring `ℤ` the action is read on
`Ext` out of the constant sheaf by
`Stacks.EtaleCohomology.extForgetSheafH_integralSelfMapCohomologyEndo`.

None of the declarations here is registered: they are inputs of the Galois equivariance of the
trace on `H²(C, -)` in the proof of [Stacks, Tag 03VK].

## Main results

* `Stacks.EtaleCohomology.restrictScalars_derivedGlobalSectionsCompIso`.
* `Stacks.EtaleCohomology.integralDirectImageCohomologyIso_hom_restrictScalarsInt`.
* `Stacks.EtaleCohomology.extConstantIntAddEquivSheafH_eq_extForgetSheafH`.
* `Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section RestrictScalars

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- **Global sections commute with restriction of scalars, read on the restriction maps**: the
identification `res_ρ Γ(X, M) ≅ Γ(X, res_ρ M)` followed by restriction to `U` is `res_ρ` of the
restriction to `U`. -/
theorem etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓRes (X : Scheme.{u})
    (M : EtaleModules.{u, 0} Λ' X) (U : X.Etaleᵒᵖ) :
    (etaleModuleGlobalSectionsRestrictScalars ρ X).hom.app M ≫
        Sheaf.ΓRes ((etaleModuleRestrictScalars ρ X).obj M) U =
      (ModuleCat.restrictScalars.{u + 1} ρ).map (Sheaf.ΓRes M U) := by
  have e : (etaleModuleGlobalSectionsRestrictScalars ρ X).hom.app M =
      (ModuleCat.restrictScalars.{u + 1} ρ).map
          ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ')
            terminalIsTerminal).hom.app M) ≫
        (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).inv.app ((etaleModuleRestrictScalars ρ X).obj M) := rfl
  have h2 := ΓNatIsoSheafSections_inv_app_comp_ΓRes (J := X.smallEtaleTopology)
    (A := ModuleCat.{u + 1} Λ) terminalIsTerminal ((etaleModuleRestrictScalars ρ X).obj M) U
  have h3 := Sheaf.ΓNatIsoSheafSections_hom_app_general (J := X.smallEtaleTopology)
    (A := ModuleCat.{u + 1} Λ') terminalIsTerminal M
  exact (congrArg (· ≫ Sheaf.ΓRes ((etaleModuleRestrictScalars ρ X).obj M) U) e).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans
      ((congrArg (fun z => (ModuleCat.restrictScalars.{u + 1} ρ).map z ≫ _) h3).trans
        (((ModuleCat.restrictScalars.{u + 1} ρ).map_comp _ _).symm.trans
          (congrArg (ModuleCat.restrictScalars.{u + 1} ρ).map (Sheaf.ΓRes_map M _))))))

/-- **The underived square**: the identification `Γ(B, g_* -) ≅ Γ(A, -)` commutes with
restriction of scalars. -/
theorem restrictScalars_directImageCompGlobalSections_inv {A B : Scheme.{u}} (g : A ⟶ B)
    (X : EtaleModules.{u, 0} Λ' A) :
    (ModuleCat.restrictScalars.{u + 1} ρ).map
        ((etaleModuleDirectImageCompGlobalSections.{u, 0} Λ' g).inv.app X) ≫
        (etaleModuleGlobalSectionsRestrictScalars ρ B).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' g).obj X) ≫
        (etaleModuleGlobalSections.{u, 0} Λ B).map
          ((etaleModuleDirectImageRestrictScalars ρ g).hom.app X) =
      (etaleModuleGlobalSectionsRestrictScalars ρ A).hom.app X ≫
        (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g).inv.app
          ((etaleModuleRestrictScalars ρ A).obj X) := by
  refine Sheaf.hom_ext_of_ΓRes fun U => ?_
  have hc : (etaleModuleGlobalSections.{u, 0} Λ B).map
        ((etaleModuleDirectImageRestrictScalars ρ g).hom.app X) ≫
        Sheaf.ΓRes ((etaleModuleDirectImage.{u, 0} Λ g).obj
          ((etaleModuleRestrictScalars ρ A).obj X)) U =
      Sheaf.ΓRes ((etaleModuleRestrictScalars ρ B).obj
        ((etaleModuleDirectImage.{u, 0} Λ' g).obj X)) U :=
    (Sheaf.ΓRes_naturality _ U).trans (Category.comp_id _)
  have hB := etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓRes ρ B
    ((etaleModuleDirectImage.{u, 0} Λ' g).obj X) U
  have hA := etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓRes ρ A X
    (op ((smallEtaleBaseChange g).obj U.unop))
  have h' := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ' g X U
  have h := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ g
    ((etaleModuleRestrictScalars ρ A).obj X) U
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hc).trans hB))).trans ?_)
  refine (((ModuleCat.restrictScalars.{u + 1} ρ).map_comp _ _).symm.trans
    (congrArg (ModuleCat.restrictScalars.{u + 1} ρ).map h')).trans ?_
  exact hA.symm.trans ((congrArg (_ ≫ ·) h).symm.trans (Category.assoc _ _ _).symm)

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The comparison `RΓ(A, -) ≅ Rg_* ⋙ RΓ(B, -)` commutes with restriction of scalars**: for `M`
in `D⁺(A_étale, Λ')` the two identifications of `res_ρ RΓ(A, M)` with `RΓ(B, Rg_*(res_ρ M))`
agree. -/
theorem restrictScalars_derivedGlobalSectionsCompIso {A B : Scheme.{u}} (g : A ⟶ B)
    (M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ' A)) :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ' g).hom.app M) ≫
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ B).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ' g).obj M) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app M) =
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ A).hom.app M ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).hom.app
          ((etaleModuleRestrictScalars ρ A).mapDerivedCategoryPlus.obj M) :=
  Functor.rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ' g)
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g)
    (etaleModuleDirectImageRestrictScalars ρ g) (etaleModuleGlobalSectionsRestrictScalars ρ B)
    (etaleModuleGlobalSectionsRestrictScalars ρ A)
    (fun I _ => rightAcyclic_directImage_of_isAcyclicEverywhere g _
      (isAcyclicEverywhere_restrictScalars' ρ I))
    (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (isAcyclicEverywhere_restrictScalars' ρ I))
    (fun I _ => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (isAcyclicEverywhere_restrictScalars' ρ I))
    (restrictScalars_directImageCompGlobalSections_inv ρ g) M

/-- `restrictScalars_derivedGlobalSectionsCompIso` for the inverse comparisons
`Rg_* ⋙ RΓ(B, -) ≅ RΓ(A, -)`. -/
theorem restrictScalars_derivedGlobalSectionsCompIso_inv {A B : Scheme.{u}} (g : A ⟶ B)
    (M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ' A)) :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ' g).inv.app M) ≫
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ A).hom.app M =
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ B).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ' g).obj M) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app M) ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
          ((etaleModuleRestrictScalars ρ A).mapDerivedCategoryPlus.obj M) := by
  have h' : (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
      ((etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ' g).hom.app M) ≫
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ B).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ' g).obj M) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app M) ≫
      (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
        ((etaleModuleRestrictScalars ρ A).mapDerivedCategoryPlus.obj M) =
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ A).hom.app M := by
    rw [reassoc_of% restrictScalars_derivedGlobalSectionsCompIso ρ g M, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [← h', ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The direct image along an integral morphism preserves finite limits. -/
private instance instPreservesFiniteLimitsDirectImage {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIntegralHom g] : PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} Λ g) :=
  (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).1

/-- The direct image along an integral morphism preserves finite colimits. -/
private instance instPreservesFiniteColimitsDirectImage {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIntegralHom g] : PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ g) :=
  (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).2

/-- **`(g_* H)[0] ≅ Rg_*(H[0])` commutes with restriction of scalars**, for an integral `g`
(so that `g_*` is exact). -/
theorem restrictScalars_exactSingleFunctorRightDerivedPlusIso_directImage {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIntegralHom g] (H : EtaleModules.{u, 0} Λ' A) :
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ' g).1
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ' g).2
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).1
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).2
    (etaleModuleRestrictScalars ρ B).mapDerivedCategoryPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (etaleModuleDirectImage.{u, 0} Λ' g) 0).hom.app H) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ g).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj H) ≫
        (etaleModuleDirectImage.{u, 0} Λ g).rightDerivedFunctorPlus.map
          (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ A) H).hom =
      (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ B)
          ((etaleModuleDirectImage.{u, 0} Λ' g).obj H)).hom ≫
        (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (etaleModuleDirectImage.{u, 0} Λ g) 0).hom.app
            ((etaleModuleRestrictScalars ρ A).obj H) := by
  rw [Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom,
    Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom]
  refine (Functor.rightDerivedPlusUnitSingle_comp_rightDerivedRestrictionIso_hom_app
    (etaleModuleDirectImageRestrictScalars ρ g) _ H).trans ?_
  exact congrArg (_ ≫ ·) ((congrArg (· ≫ _)
    ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ B) 0).map_id _)).trans
    (Category.id_comp _))

/-- The diagram chase of `restrictScalars_integralDirectImageDerivedMap`, abstract in the
objects. -/
private lemma integralDirectImage_restrictScalars_chase {𝒞 : Type*} [Category* 𝒞]
    {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ R₁ : 𝒞}
    {a₁ : P₀ ⟶ P₁} {a₂ : P₁ ⟶ P₂} {a₃ : P₂ ⟶ P₃} {a₄ : P₃ ⟶ P₄}
    {b₁ : P₁ ⟶ Q₁} {b₂ : Q₁ ⟶ Q₂} {b₃ : Q₂ ⟶ P₃} {c₁ : P₀ ⟶ Q₃} {c₂ : Q₃ ⟶ Q₁}
    {d₁ : Q₂ ⟶ Q₄} {d₂ : Q₄ ⟶ P₄} {s : Q₃ ⟶ R₁} {t : R₁ ⟶ Q₄}
    (hBI : a₂ ≫ a₃ = b₁ ≫ b₂ ≫ b₃) (hn₁ : a₁ ≫ b₁ = c₁ ≫ c₂) (hn₂ : b₃ ≫ a₄ = d₁ ≫ d₂)
    (hA : c₂ ≫ b₂ ≫ d₁ = s ≫ t) :
    (a₁ ≫ a₂) ≫ a₃ ≫ a₄ = (c₁ ≫ s) ≫ t ≫ d₂ := by
  simp only [Category.assoc]
  rw [reassoc_of% hBI, reassoc_of% hn₁, hn₂, reassoc_of% hA]

/-- **The morphism underlying `H^i(B, g_* H) ≅ H^i(A, H)` commutes with restriction of
scalars**, in `D⁺(Mod Λ)`: `res_ρ` of `RΓ(B, (g_* H)[0]) ≅ RΓ(B, Rg_*(H[0])) ≅ RΓ(A, H[0])`,
read through `res_ρ RΓ(-, -) ≅ RΓ(-, res_ρ -)` and `res_ρ(N[0]) ≅ (res_ρ N)[0]`, is the same
morphism for `res_ρ H`. -/
theorem restrictScalars_integralDirectImageDerivedMap {A B : Scheme.{u}} (g : A ⟶ B)
    [IsIntegralHom g] (H : EtaleModules.{u, 0} Λ' A) :
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ' g).1
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ' g).2
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).1
    haveI := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).2
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ' B).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, 0} Λ' g) 0).hom.app H) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ' g).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj H)) ≫
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ A).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj H) ≫
          (etaleModuleDerivedGlobalSections.{u, 0} Λ A).map
            (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ A) H).hom =
      ((etaleModuleDerivedGlobalSectionsRestrictScalars ρ B).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleDirectImage.{u, 0} Λ' g).obj H)) ≫
          (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
            (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ B)
              ((etaleModuleDirectImage.{u, 0} Λ' g).obj H)).hom) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, 0} Λ g) 0).hom.app
                ((etaleModuleRestrictScalars ρ A).obj H)) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleRestrictScalars ρ A).obj H)) := by
  have hBI := restrictScalars_derivedGlobalSectionsCompIso_inv ρ g
    ((DerivedCategory.Plus.singleFunctor _ 0).obj H)
  have hn₁ := (etaleModuleDerivedGlobalSectionsRestrictScalars ρ B).hom.naturality
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleDirectImage.{u, 0} Λ' g) 0).hom.app H)
  have hn₂ := ((etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.naturality
    (Functor.mapDerivedCategoryPlusObjSingleIso (etaleModuleRestrictScalars ρ A) H).hom).symm
  have hA := (((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map_comp _ _))).symm.trans
    ((congrArg (etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
      (restrictScalars_exactSingleFunctorRightDerivedPlusIso_directImage ρ g H)).trans
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map_comp _ _))
  exact (congrArg (· ≫ _) ((ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map_comp
    _ _)).trans (integralDirectImage_restrictScalars_chase hBI hn₁ hn₂ hA)

end RestrictScalars

section Int

variable {Λ : Type} [Ring Λ]

/-- **`H^i(B, g_* H) ≅ H^i(A, H)` does not depend on the coefficient ring**: for an integral
`g : A ⟶ B` and a sheaf `H` of modules over a ring `Λ`, the identification computed over `Λ`,
read as a map of abelian groups through `res_ℤ Hⁱ(-, -) ≅ Hⁱ(-, res_ℤ -)`
(`Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIntIso`), is the identification computed
over `ℤ` for the underlying sheaf of `ℤ`-modules. -/
theorem integralDirectImageCohomologyIso_hom_restrictScalarsInt {A B : Scheme.{u}} (g : A ⟶ B)
    [IsIntegralHom g] (H : EtaleModules.{u, 0} Λ A) (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map
        (integralDirectImageCohomologyIso Λ g H i).hom ≫
        (rightDerivedPlusRestrictScalarsIntIso A H i).hom =
      (rightDerivedPlusRestrictScalarsIntIso B ((etaleModuleDirectImage.{u, 0} Λ g).obj H) i).hom ≫
        (integralDirectImageCohomologyIso ℤ g
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) A).obj H) i).hom := by
  have h1 := (Stacks.DerivedFunctor.derivedHomologyIso
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) i).inv.naturality
    (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (etaleModuleDirectImage.{u, 0} Λ g) 0).hom.app H) ≫
      (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj H)))
  have hmain : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
              ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
                (etaleModuleDirectImage.{u, 0} Λ g) 0).hom.app H) ≫
            (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj H)))) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) A).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj H) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ A).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) A).mapDerivedCategoryPlusObjSingleIso
            H).hom) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) B).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleDirectImage.{u, 0} Λ g).obj H)) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ B).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) B).mapDerivedCategoryPlusObjSingleIso
            ((etaleModuleDirectImage.{u, 0} Λ g).obj H)).hom) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} ℤ B).map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (etaleModuleDirectImage.{u, 0} ℤ g) 0).hom.app
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) A).obj H)) ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} ℤ g).inv.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleRestrictScalars (Int.castRingHom Λ) A).obj H))) := by
    change (DerivedCategory.Plus.homologyFunctor _ i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ B).map
              ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
                (etaleModuleDirectImage.{u, 0} Λ g) 0).hom.app H) ≫
            (etaleModuleDerivedGlobalSectionsCompIso.{u, 0} Λ g).inv.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) ≫ _ = _
    simp only [← Functor.map_comp]
    exact congrArg _ (restrictScalars_integralDirectImageDerivedMap (Int.castRingHom Λ) g H)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hmain).trans (Category.assoc _ _ _).symm)))

variable (Y : Scheme.{u})

/-- The map `ℤ ⟶ ℤ`, `n ↦ n • 1`, between the lifted rings is the identity. -/
theorem uliftIntToULiftHom_int : uliftIntToULiftHom ℤ = 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  ext n
  change (n.down • (1 : ULift.{u + 1} ℤ)) = n
  ext
  simp

/-- **For `ℤ`-modules the map `ℤ_X ⟶ U ℤ_X` is the identification of constant sheaves.** -/
theorem etaleModuleUnderlyingAbelianConstantMap_int :
    etaleModuleUnderlyingAbelianConstantMap ℤ Y = (etaleModuleUnderlyingAbelianConstantIso Y).inv :=
  (congrArg (· ≫ _) ((congrArg (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    uliftIntToULiftHom_int).trans
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id _))).trans
    (Category.id_comp _)

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The two identifications `Ext^i(ℤ_Y, M) ≅ Hⁱ(Y, U M)` for a sheaf of `ℤ`-modules agree**:
`Stacks.EtaleCohomology.extConstantIntAddEquivSheafH` is `Stacks.EtaleCohomology.extForgetSheafH`
at `ℤ`. -/
theorem extConstantIntAddEquivSheafH_eq_extForgetSheafH (M : EtaleModules.{u, 0} ℤ Y) (i : ℕ)
    (y : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ Y.smallEtaleTopology)
      M i) :
    extConstantIntAddEquivSheafH Y M i y = extForgetSheafH ℤ Y M i y := by
  rw [extForgetSheafH_apply, etaleModuleUnderlyingAbelianConstantMap_int]
  rfl

end Int

section Action

/-- **The pullback action of an integral self-map, read on the cohomology of the underlying
abelian sheaf.** Let `Λ` be a ring, `φ : Y ⟶ Y` an integral morphism and `N` a sheaf of
`Λ`-modules on `Y_étale` with a linearization `α : N ⟶ φ_* N`. Under
`Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)` (`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH`, the
abelian sheaf being that of `res_ℤ N`), the action
`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo` of `φ` is the restriction map along `φ`
followed by `φ^{-1}(N_ab) ≅ (φ^{-1} res_ℤ N)_ab ⟶ N_ab`, the second map being the adjoint
`φ^{-1}(α) ≫ ε` of `α` read over `ℤ` (`Stacks.EtaleCohomology.etaleCohomologyMapTo`). -/
theorem etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo {Λ : Type} [Ring Λ]
    {Y : Scheme.{u}} (φ : Y ⟶ Y) [IsIntegralHom φ] (N : EtaleModules.{u, 0} Λ Y)
    (α : N ⟶ (etaleModuleDirectImage.{u, 0} Λ φ).obj N) (i : ℕ)
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyAddEquivSheafH Y N i ((integralSelfMapCohomologyEndo Λ φ N α i).hom x) =
      etaleCohomologyMapTo φ
        ((etaleModuleUnderlyingAbelianInverseImageIso ℤ φ).hom.app
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N) ≫
          (etaleModuleUnderlyingAbelian Y ℤ).map
            ((etaleModuleInverseImage.{u, 0} ℤ φ).map
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map α) ≫
              (etaleModuleInverseImageAdj.{u, 0} ℤ φ).counit.app
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N))) i
        (etaleModuleCohomologyAddEquivSheafH Y N i x) := by
  have : (Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} ℤ)).IsMonoidal :=
    isMonoidal_W_etaleModules ℤ Y
  let M := (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N
  let α' : M ⟶ (etaleModuleDirectImage.{u, 0} ℤ φ).obj M :=
    (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map α
  let R := rightDerivedPlusRestrictScalarsIntIso Y N (i : ℤ)
  let E := etaleModuleRightDerivedPlusIsoExt ℤ Y M i
  have hcomm : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map
      (integralSelfMapCohomologyEndo Λ φ N α i) ≫ R.hom =
      R.hom ≫ integralSelfMapCohomologyEndo ℤ φ M α' i :=
    (congrArg (· ≫ R.hom) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·)
        (integralDirectImageCohomologyIso_hom_restrictScalarsInt φ N (i : ℤ))).trans
        ((reassoc_of% (rightDerivedPlusRestrictScalarsIntIso_hom_naturality Y α (i : ℤ))) _)))
  have hR : R.hom.hom ((integralSelfMapCohomologyEndo Λ φ N α i).hom x) =
      (integralSelfMapCohomologyEndo ℤ φ M α' i).hom (R.hom.hom x) :=
    congrArg (fun f => f.hom x) hcomm
  have hE : ∀ y, etaleModuleCohomologyAddEquivSheafH Y N i y =
      extForgetSheafH ℤ Y M i (E.hom.hom (R.hom.hom y)) :=
    fun y => extConstantIntAddEquivSheafH_eq_extForgetSheafH Y M i _
  have hEE : E.inv.hom (E.hom.hom (R.hom.hom x)) = R.hom.hom x := by
    change (E.hom ≫ E.inv).hom _ = _
    rw [Iso.hom_inv_id]
    rfl
  have key := extForgetSheafH_integralSelfMapCohomologyEndo ℤ φ M α' i (E.hom.hom (R.hom.hom x))
  rw [hEE] at key
  rw [hE, hE, hR, etaleCohomologyMapTo_apply]
  exact key

end Action

end Stacks.EtaleCohomology

end
