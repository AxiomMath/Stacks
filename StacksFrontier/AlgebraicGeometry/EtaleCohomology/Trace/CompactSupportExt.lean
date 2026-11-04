module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# Compactly supported cohomology of the geometric fibre as `Ext` out of the constant sheaf

Let `k` be a field, `X` a `k`-scheme with a compactification `j : X ⟶ X̄` over `k`, `k̄` an
extension field of `k`, `Λ` a commutative ring and `K` a sheaf of `Λ`-modules on `X_étale`. The
canonical `RΓ_c(X_k̄, K) = RΓ(Spec k̄, Rπ_*((j_! K)|_{X̄_k̄}))` of
`Stacks.EtaleCohomology.compactSupportFrobeniusFunctor`, for `π : X̄_k̄ ⟶ Spec k̄`, is the derived
global sections `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` (Leray for `Γ(X̄_k̄, -) = Γ(Spec k̄, -) ∘ π_*`, whose
first factor preserves injectives), so

`Hⁱ_c(X_k̄, K) ≅ Hⁱ(X̄_k̄, (j_! K)|_{X̄_k̄}) ≅ Ext^i(Λ, (j_! K)|_{X̄_k̄})`,

the second isomorphism being the corepresentation of global sections by the constant sheaf
(`Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived`). This puts the groups
`Hⁱ_c(X_k̄, -)` of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) on the groups
`Ext^i(𝟙, -)` on which the cup product `Stacks.ExtCup.cup` is defined: it is step (b2) of the
purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt`: `Hⁱ(Y, M) ≅ Ext^i(Λ_Y, M)` for a
  sheaf of `Λ`-modules on the small étale site of a scheme, read in abelian groups.
* `Stacks.EtaleCohomology.compactSupportFrobeniusSingleIso`: `Hⁱ_c(X_k̄, K) ≅
  Hⁱ(X̄_k̄, (j_! K)|_{X̄_k̄})` for a sheaf placed in degree zero.
* `Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt`: `Hⁱ_c(X_k̄, K) ≅
  Ext^i(Λ, (j_! K)|_{X̄_k̄})`, read in abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Ext

variable (Λ : Type) [CommRing Λ] (Y : Scheme.{u})

/-- **Étale cohomology of a sheaf of modules is `Ext` out of the constant sheaf**:
`Hⁱ(Y, M) ≅ Ext^i(Λ_Y, M)` for a sheaf of `Λ`-modules `M` on the small étale site of `Y`, read in
abelian groups. The left side is the `i`-th cohomology of the derived global sections of `M`
placed in degree zero. -/
def etaleModuleRightDerivedPlusIsoExt (M : EtaleModules.{u, 0} Λ Y) (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj M) ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        Y.smallEtaleTopology) i).obj M :=
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleGlobalSections.{u, 0} Λ Y) i).app
        M).symm ≪≫
    ((Stacks.Cohomology.GlobalSections.extConstantModuleSheafIsoRightDerived Λ
      Y.smallEtaleTopology i).app M).symm

end Ext

section CompactSupport

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- A functor preserving zero morphisms carries a sheaf placed in degree zero to its image placed
in degree zero, as bounded below complexes. -/
def mapCochainComplexPlusSinglePlusIso {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] (F : A ⥤ B) [F.PreservesZeroMorphisms] (M : A) :
    F.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M) ≅
      (Stacks.DerivedIndexing.singlePlusFunctor B 0).obj (F.obj M) :=
  ObjectProperty.isoMk _ ((HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℤ) 0).app M)

/-- **`Hⁱ_c(X_k̄, K) ≅ Hⁱ(X̄_k̄, (j_! K)|_{X̄_k̄})`** for a sheaf of modules `K` placed in degree
zero: the canonical `RΓ_c(X_k̄, K) = RΓ(Spec k̄, Rπ_*((j_! K)|_{X̄_k̄}))` is the derived global
sections on `X̄_k̄`, because `Γ(X̄_k̄, -) = Γ(Spec k̄, -) ∘ π_*` and `π_*` preserves injectives. -/
def compactSupportFrobeniusSingleIso (K : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)) ≅
      ((etaleModuleGlobalSections.{u, 0} Λ
          (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedPlus i).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) :=
  let π := pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)
  let E := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let I := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let e₁ : I.mapCochainComplexPlus.obj (E.mapCochainComplexPlus.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K)) ≅
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj (I.obj (E.obj K)) :=
    I.mapCochainComplexPlus.mapIso (mapCochainComplexPlusSinglePlusIso E K) ≪≫
      mapCochainComplexPlusSinglePlusIso I (E.obj K)
  let e₂ := (rightDerivedFunctorPlusCompIsoOfIso (etaleModuleDirectImage.{u, 0} Λ π)
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar))
    (etaleModuleGlobalSectionsDirectImageIso π Λ)).symm
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
        ((etaleModuleDerivedDirectImage.{u, 0} Λ π).mapIso
          (DerivedCategory.Plus.Q.mapIso e₁)) ≪≫ e₂.app _)

/-- **`Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ, (j_! K)|_{X̄_k̄})`**, read in abelian groups, for a sheaf of
modules `K` placed in degree zero: the compactly supported cohomology of the geometric fibre is
an `Ext`-group out of the constant sheaf on `X̄_k̄`, which is where the cup product
`Stacks.ExtCup.cup` lives. -/
def compactSupportFrobeniusSingleIsoExt (K : EtaleModules.{u, 0} Λ X) (i : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
          ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K))) ≅
      (extFunctorObj (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) i).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) :=
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      (compactSupportFrobeniusSingleIso Λ f j kbar K i) ≪≫
    etaleModuleRightDerivedPlusIsoExt Λ _ _ i

end CompactSupport

end Stacks.EtaleCohomology

end
