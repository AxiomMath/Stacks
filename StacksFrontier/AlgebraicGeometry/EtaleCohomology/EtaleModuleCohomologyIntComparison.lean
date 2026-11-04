module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatTransSingle

/-!
# The étale cohomology of a sheaf of modules over a noncommutative ring, in abelian groups

Let `Λ` be a ring, not necessarily commutative, and `N` a sheaf of `Λ`-modules on the small étale
site of a scheme `Y`.  Its cohomology `Hⁱ(Y, N)`, computed with injective sheaves of
`Λ`-modules, is the étale cohomology of the underlying abelian sheaf:

`Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)`,

with Mathlib's `CategoryTheory.Sheaf.H` on the right.  The comparison passes through `ℤ`:
restriction of scalars along `ℤ →+* Λ` carries injective sheaves to sheaves acyclic everywhere
(`Stacks.EtaleCohomology.isAcyclicEverywhere_restrictScalars'`, which holds for every ring), so
`RΓ(Y, -)` commutes with it; over `ℤ` the cohomology is `Ext` out of the constant sheaf, which is
`Sheaf.H`.

`Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIso` is the comparison for a morphism of
commutative rings; the coefficient ring of the Trace Formula chapter is a finite ring, not
assumed commutative, which is why the comparison along `ℤ →+* Λ` is made again here.

## Main definitions

* `Stacks.EtaleCohomology.rightDerivedPlusRestrictScalarsIntIso` —
  `res_ℤ Hⁱ(Y, N) ≅ Hⁱ(Y, res_ℤ N)` as `ℤ`-modules.
* `Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH` — `Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerivedPlus_of_subsingleton_sheafH` — vanishing of the
  cohomology of the underlying abelian sheaf gives vanishing of the module cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

variable {Λ : Type} [Ring Λ] (Y : Scheme.{u})

/-- **`res_ℤ Hⁱ(Y, N) ≅ Hⁱ(Y, res_ℤ N)`** for a sheaf `N` of modules over an arbitrary ring `Λ`:
the cohomology of `N`, read as a `ℤ`-module, is the cohomology of the underlying sheaf of
`ℤ`-modules. -/
def rightDerivedPlusRestrictScalarsIntIso (N : EtaleModules.{u, 0} Λ Y) (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).obj
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus i).obj N) ≅
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N) :=
  ((Stacks.DerivedFunctor.derivedHomologyIso
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) i).app
      (DerivedCategory.Plus.ι.obj (((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≪≫
      (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).mapIso
        (Functor.mapDerivedCategoryPlusObjSingleIso
          (etaleModuleRestrictScalars (Int.castRingHom Λ) Y) N))

/-- **Multiplication by `a : Λ`, as a natural endomorphism of restriction of scalars to `ℤ`.**
On a `Λ`-module `M`, read as an abelian group, it is `m ↦ a • m`; it is `ℤ`-linear for every
`a`, central or not. -/
def restrictScalarsIntSMul (a : Λ) :
    ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) ⟶
      ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) where
  app M := ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).obj M)
      (Y := (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).obj M)
    { toFun := fun x => (a • (x : M) : M)
      map_add' := fun x y => smul_add a (x : M) (y : M)
      map_smul' := fun m x => by
        change a • ((m : Λ) • (x : M)) = (m : Λ) • (a • (x : M))
        rw [smul_smul, smul_smul, Int.cast_comm] }
  naturality _ _ g := by
    ext x
    exact (g.hom.map_smul a x).symm

open Stacks.DerivedFunctor in
/-- **The comparison `res_ℤ Hⁱ(Y, N) ≅ Hⁱ(Y, res_ℤ N)` carries multiplication by `a : Λ` to the
cohomology of multiplication by `a` on the sheaf.**  On the left `a` acts through the
`Λ`-module structure of the cohomology; on the right it is `Hⁱ(Y, -)` of the endomorphism
`a • -` of the underlying sheaf of abelian groups of `N`. -/
theorem rightDerivedPlusRestrictScalarsIntIso_hom_smul (N : EtaleModules.{u, 0} Λ Y) (i : ℤ)
    (a : Λ) :
    (restrictScalarsIntSMul a).app _ ≫ (rightDerivedPlusRestrictScalarsIntIso Y N i).hom =
      (rightDerivedPlusRestrictScalarsIntIso Y N i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
          ((etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a) Y).app
            N) := by
  have h1 := congr_app (derivedHomologyIso_naturality (restrictScalarsIntSMul (Λ := Λ) a) i)
    (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))
  have h2 := etaleModuleDerivedGlobalSectionsRestrictScalars_naturality (Int.castRingHom Λ)
    (restrictScalarsIntSMul a) Y ((DerivedCategory.Plus.singleFunctor _ 0).obj N)
  have h3 := mapDerivedCategoryPlusNatTrans_app_single
    (etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a) Y) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h1
  have h1' : (restrictScalarsIntSMul a).app _ ≫
      ((derivedHomologyIso (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) i).app
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))).inv =
      ((derivedHomologyIso (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) i).app
        (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((mapDerivedNatTrans (restrictScalarsIntSMul a)).app
          (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.app_hom, h1, Iso.app_inv, Iso.inv_hom_id_app_assoc]
  have hmain : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((mapDerivedNatTrans (restrictScalarsIntSMul a)).app
          (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj N)))) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N).hom) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N).hom) ≫
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
          ((etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a) Y).app
            N) := by
    show (DerivedCategory.Plus.homologyFunctor _ i).map
        ((mapDerivedCategoryPlusNatTrans (restrictScalarsIntSMul a)).app _) ≫ _ =
      _ ≫ (DerivedCategory.Plus.homologyFunctor _ i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a)
              Y).app N)))
    simp only [← Functor.map_comp]
    refine congrArg _ ?_
    rw [reassoc_of% h2, ← Functor.map_comp, h3, Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1').trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hmain).trans (Category.assoc _ _ _).symm)))

/-- **`res_ℤ Hⁱ(Y, N) ≅ Hⁱ(Y, res_ℤ N)` is natural in `N`.** -/
theorem rightDerivedPlusRestrictScalarsIntIso_hom_naturality {N N' : EtaleModules.{u, 0} Λ Y}
    (g : N ⟶ N') (i : ℤ) :
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).map
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus i).map g) ≫
      (rightDerivedPlusRestrictScalarsIntIso Y N' i).hom =
    (rightDerivedPlusRestrictScalarsIntIso Y N i).hom ≫
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g) := by
  have h1 := (Stacks.DerivedFunctor.derivedHomologyIso
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)) i).inv.naturality
    (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map g)))
  have h2 := (etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map g)
  have h3 := Stacks.DerivedFunctor.mapDerivedCategoryPlusObjSingleIso_hom_naturality
    (S := etaleModuleRestrictScalars (Int.castRingHom Λ) Y) g
  have hmain : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g)))) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N') ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N').hom) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ) i).map
        ((etaleModuleDerivedGlobalSectionsRestrictScalars (Int.castRingHom Λ) Y).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj N) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).mapDerivedCategoryPlusObjSingleIso
            N).hom) ≫
      ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus i).map
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g) := by
    show (DerivedCategory.Plus.homologyFunctor _ i).map
        ((ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).mapDerivedCategoryPlus.map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ Y).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g))) ≫ _ =
      _ ≫ (DerivedCategory.Plus.homologyFunctor _ i).map
        ((etaleModuleDerivedGlobalSections.{u, 0} ℤ Y).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g)))
    simp only [← Functor.map_comp]
    refine congrArg _ ?_
    rw [reassoc_of% h2, ← Functor.map_comp, h3, Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hmain).trans (Category.assoc _ _ _).symm)))

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)`** for a sheaf `N` of modules over an arbitrary ring `Λ`: the
cohomology computed in sheaves of `Λ`-modules is Mathlib's sheaf cohomology of the underlying
abelian sheaf. -/
def etaleModuleCohomologyAddEquivSheafH (N : EtaleModules.{u, 0} Λ Y) (i : ℕ) :
    ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N ≃+
      Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Y ℤ).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N)) i :=
  ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).mapIso
      (rightDerivedPlusRestrictScalarsIntIso Y N i) ≪≫
    etaleModuleRightDerivedPlusIsoExt ℤ Y _ i).addCommGroupIsoToAddEquiv.trans
    (extConstantIntAddEquivSheafH Y _ i)

omit [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The comparison of the cohomology of a sheaf of `ℤ`-modules with `Ext` out of the constant
sheaf is natural in the sheaf. -/
theorem etaleModuleRightDerivedPlusIsoExt_hom_naturality {M M' : EtaleModules.{u, 0} ℤ Y}
    (g : M ⟶ M') (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map
        (((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).map g) ≫
      (etaleModuleRightDerivedPlusIsoExt ℤ Y M' i).hom =
    (etaleModuleRightDerivedPlusIsoExt ℤ Y M i).hom ≫
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf ℤ
        Y.smallEtaleTopology) i).map g := by
  simp only [etaleModuleRightDerivedPlusIsoExt, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_symm,
    Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, (Stacks.DerivedIndexing.rightDerivedIso
    (etaleModuleGlobalSections.{u, 0} ℤ Y) i).inv.naturality g, Functor.map_comp_assoc]
  exact congrArg (_ ≫ ·) ((Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived
    ℤ Y.smallEtaleTopology i).inv.naturality g)

/-- The comparison of `Ext` out of the constant sheaf with `Sheaf.H` is natural in the sheaf. -/
theorem extConstantIntAddEquivSheafH_naturality {M M' : EtaleModules.{u, 0} ℤ Y} (g : M ⟶ M')
    (i : ℕ) (y : (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
        Y.smallEtaleTopology) i).obj M) :
    extConstantIntAddEquivSheafH Y M' i
        ((extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
          Y.smallEtaleTopology) i).map g y) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map g) i
        (extConstantIntAddEquivSheafH Y M i y) := by
  have : (etaleModuleUnderlyingAbelian Y ℤ).Additive :=
    ⟨fun {_ _ _ _} => by
      ext U : 3
      exact (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).map_add⟩
  have key : ∀ z : Abelian.Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} ℤ
      Y.smallEtaleTopology) M i,
      (Abelian.Ext.mk₀ (etaleModuleUnderlyingAbelianConstantIso.{u} Y).symm.hom).comp
          ((z.comp (Abelian.Ext.mk₀ g) (add_zero i)).mapExactFunctor
            (etaleModuleUnderlyingAbelian Y ℤ)) (zero_add i) =
        ((Abelian.Ext.mk₀ (etaleModuleUnderlyingAbelianConstantIso.{u} Y).symm.hom).comp
          (z.mapExactFunctor (etaleModuleUnderlyingAbelian Y ℤ)) (zero_add i)).comp
          (Abelian.Ext.mk₀ ((etaleModuleUnderlyingAbelian Y ℤ).map g)) (add_zero i) := by
    intro z
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero]
  exact key y

/-- If `f` on the cohomology of `N` and `φ` on the underlying `ℤ`-sheaves correspond under the
comparison with `Hⁱ(Y, res_ℤ N)`, then they correspond under `Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)`. -/
private theorem etaleModuleCohomologyAddEquivSheafH_apply_eq {N N' : EtaleModules.{u, 0} Λ Y}
    (i : ℕ)
    (f : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).obj
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) ⟶
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).obj
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N'))
    (φ : (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N ⟶
      (etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N')
    (hf : f ≫ (rightDerivedPlusRestrictScalarsIntIso Y N' i).hom =
      (rightDerivedPlusRestrictScalarsIntIso Y N i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} ℤ Y).rightDerivedPlus (i : ℤ)).map φ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyAddEquivSheafH Y N' i (f.hom x) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map φ) i
        (etaleModuleCohomologyAddEquivSheafH Y N i x) := by
  have hC := congrArg (fun f => f.hom x) hf
  simp only [ModuleCat.hom_comp] at hC
  have hB := congrArg (fun f => f.hom ((rightDerivedPlusRestrictScalarsIntIso Y N i).hom.hom x))
    (etaleModuleRightDerivedPlusIsoExt_hom_naturality Y φ i)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hB
  have hA := extConstantIntAddEquivSheafH_naturality Y φ i
    ((etaleModuleRightDerivedPlusIsoExt ℤ Y _ i).hom.hom
      ((rightDerivedPlusRestrictScalarsIntIso Y N i).hom.hom x))
  exact (congrArg (extConstantIntAddEquivSheafH Y _ i)
    ((congrArg (etaleModuleRightDerivedPlusIsoExt ℤ Y _ i).hom.hom hC).trans hB)).trans hA

/-- **`Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)` carries multiplication by `a : Λ` to the cohomology of
multiplication by `a` on the underlying abelian sheaf.**  This is what makes the comparison
`Λ`-equivariant, for the `Λ`-module structure on the abelian side given by functoriality. -/
theorem etaleModuleCohomologyAddEquivSheafH_smul (N : EtaleModules.{u, 0} Λ Y) (i : ℕ) (a : Λ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyAddEquivSheafH Y N i (a • x) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map
          ((etaleModuleRestrictScalarsNatTrans (Int.castRingHom Λ) (restrictScalarsIntSMul a)
            Y).app N)) i
        (etaleModuleCohomologyAddEquivSheafH Y N i x) :=
  etaleModuleCohomologyAddEquivSheafH_apply_eq Y i _ _
    (rightDerivedPlusRestrictScalarsIntIso_hom_smul Y N i a) x

/-- **`Hⁱ(Y, N) ≃+ Hⁱ(Y, N_ab)` is natural in `N`.** -/
theorem etaleModuleCohomologyAddEquivSheafH_naturality {N N' : EtaleModules.{u, 0} Λ Y}
    (g : N ⟶ N') (i : ℕ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyAddEquivSheafH Y N' i
        ((((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).map g).hom x) =
      Sheaf.H.map ((etaleModuleUnderlyingAbelian Y ℤ).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g)) i
        (etaleModuleCohomologyAddEquivSheafH Y N i x) :=
  etaleModuleCohomologyAddEquivSheafH_apply_eq Y i _ _
    (rightDerivedPlusRestrictScalarsIntIso_hom_naturality Y g i) x

/-- **Vanishing transfers from the underlying abelian sheaf**: if `Hⁱ(Y, N_ab) = 0` then
`Hⁱ(Y, N) = 0` for the sheaf of `Λ`-modules `N`. -/
theorem isZero_rightDerivedPlus_of_subsingleton_sheafH (N : EtaleModules.{u, 0} Λ Y) (i : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Y ℤ).obj
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N)) i)) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (etaleModuleCohomologyAddEquivSheafH Y N i).injective.subsingleton

end Stacks.EtaleCohomology

end
