module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hypercohomology of a module placed in degree zero, over a field

Let `f : X ⟶ Spec k` be a scheme over a field. For an `𝒪_X`-module `F` the `k`-linear
hypercohomology `H^n(X, F[0]) = H^n(RΓ(X, F[0]))`, computed on the unbounded derived category, is
the sheaf cohomology `H^n(X, F)` of `AlgebraicGeometry.cohomologyOverField`, computed from an
injective resolution, naturally in `F`.

## Main definitions

* `AlgebraicGeometry.hypercohomologySingleIsoCohomologyOverField` — the natural isomorphism
  `H^n(X, F[0]) ≅ H^n(X, F)` of functors to `k`-vector spaces, the right-hand side being
  `AlgebraicGeometry.cohomologyOverFieldFunctor`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `k`-linear global sections, with scalars restricted along `f.appLE ⊤ ⊤`, are `k`-linear global
sections. -/
def globalSectionsOverAppLEIso :
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom ≅
      globalSectionsOver f :=
  Functor.isoWhiskerLeft _ (eqToIso (congrArg (fun φ : Γ(Spec (.of k), ⊤) ⟶ Γ(X, ⊤) ↦
    ModuleCat.restrictScalars.{u} ((Scheme.ΓSpecIso (.of k)).inv ≫ φ).hom)
      (Scheme.Hom.app_eq_appLE f (U := ⊤)).symm))

/-- **`H^n(X, F[0]) ≅ H^n(X, F)`, naturally in `F`.** The degree-`n` cohomology of `k`-linear
unbounded derived global sections of `F` placed in degree zero is the sheaf cohomology of `F`,
computed from an injective resolution. -/
@[ega "III 6.2.1" "special case"]
def hypercohomologySingleIsoCohomologyOverField (n : ℕ) :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ) ≅
      cohomologyOverFieldFunctor k f n :=
  let G : ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⥤ ModuleCat.{u} k :=
    ModuleCat.restrictScalars.{u} ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  haveI : G.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  haveI : PreservesFiniteLimits G :=
    StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits _
  haveI : PreservesFiniteColimits G :=
    StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _
  let H : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} k := globalSectionsOver f
  haveI : H.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) n ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) G
      H (globalSectionsOverAppLEIso f) n).symm

end AlgebraicGeometry
