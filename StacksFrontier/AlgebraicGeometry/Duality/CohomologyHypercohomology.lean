module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf cohomology against hypercohomology, over the base field

Let `k` be a field, `f : X ⟶ Spec k` a scheme over `k` and `ℱ` a sheaf of `𝒪_X`-modules. There
are two `k`-vector spaces called `Hⁿ(X, ℱ)`:

* `AlgebraicGeometry.cohomologyOverField k f ℱ n`, the `n`-th classical right derived functor of
  global sections with its scalars restricted along the structure morphism; and
* `Stacks.Duality.derivedCohomologyOverField f (ℱ[0]) n`, the degree-`n` cohomology of
  `RΓ(X, -) : D(𝒪_X) ⥤ D(k)` applied to `ℱ` placed in degree zero.

This file identifies them as objects of `ModuleCat k`, naturally in `ℱ`.

## Main definitions

* `Stacks.Duality.rightDerivedCompRestrictScalarsIso`: an exact restriction of scalars commutes
  with right derived functors.
* `Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology`: the comparison
  `Rⁿ Γ(X, -) ≅ Hⁿ(RΓ(X, -)) ∘ (-)[0]` over an arbitrary base ring.
* `Stacks.Duality.cohomologyOverFieldFunctorIsoDerivedCohomology`: the comparison over `k`, as a
  natural isomorphism of functors `X.Modules ⥤ ModuleCat k`.
* `Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField`: its component at `ℱ`, an
  isomorphism `Hⁿ(X, ℱ) ≅ H^n(X, ℱ[0])` in `ModuleCat k`.
* `Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField`: the same as a
  `k`-linear equivalence.
* `Stacks.Duality.derivedCohomologyOverFieldDualAddEquiv`: maps `H^n(X, ℱ[0]) ⟶ k` correspond to
  the `k`-linear functionals on `AlgebraicGeometry.cohomologyOverField`.

## Main results

* `Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField_naturality`: the comparison
  intertwines `Hⁿ(X, φ)` with the map induced by `φ` on hypercohomology.
* `Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap`: the
  same with the left-hand map written as `AlgebraicGeometry.cohomologyOverFieldMap`.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe w₁ w₂ u

namespace Stacks.Duality

/-! ### Restriction of scalars out of a right derived functor -/

/-- An exact restriction of scalars may be pulled out of a right derived functor: if
`e : E ⋙ ModuleCat.restrictScalars φ ≅ H` then `Rⁿ E` followed by restriction of scalars along
`φ` is `Rⁿ H`, naturally in the object. The additivity of `E` and of `H` are named instance
arguments `hE` and `hH`. -/
def rightDerivedCompRestrictScalarsIso {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
    (E : C ⥤ ModuleCat.{u} S) [hE : E.Additive] (H : C ⥤ ModuleCat.{u} R) [hH : H.Additive]
    (e : E ⋙ ModuleCat.restrictScalars φ ≅ H) (n : ℕ) :
    E.rightDerived n ⋙ ModuleCat.restrictScalars φ ≅ H.rightDerived n :=
  letI : (ModuleCat.restrictScalars φ).PreservesHomology :=
    Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars φ
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso E (ModuleCat.restrictScalars φ) H e n

/-! ### The comparison over an arbitrary base ring -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- `Rⁿ Γ(X, -) ≅ Hⁿ(RΓ(X, -)) ∘ (-)[0]` over the base ring `A`: the degree-`n` cohomology of
unbounded derived global sections at a module placed in degree zero is the `n`-th classical right
derived functor of `A`-linear global sections, naturally in the module. -/
def rightDerivedGlobalSectionsIsoDerivedCohomology (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)] (n : ℕ) :
    (globalSectionsOver f).rightDerived n ≅
      DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) n).symm

/-! ### The comparison over a field -/

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- Global sections over `k` are evaluation on the whole space followed by restriction of scalars
along `f.appLE ⊤ ⊤`, as an isomorphism with `AlgebraicGeometry.globalSectionsOver f`. -/
def evaluationCompRestrictScalarsIsoGlobalSectionsOver :
    _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
        restrictScalarsOverBase k f ≅
      globalSectionsOver f :=
  Functor.isoWhiskerLeft _ (eqToIso (congrArg
    (fun m => ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ m).hom)
    (Scheme.Hom.appLE_eq_app f (U := ⊤))))

/-- Sheaf cohomology over a field is hypercohomology of the module in degree zero, as a natural
isomorphism of functors `X.Modules ⥤ ModuleCat k`:

`Hⁿ(X, -) ≅ (-)[0] ⋙ RΓ(X, -) ⋙ H^n`.

The left-hand side is `AlgebraicGeometry.cohomologyOverFieldFunctor`, the `n`-th classical right
derived functor of global sections read over `k`; the right-hand side is the functor whose value
at `ℱ` is `Stacks.Duality.derivedCohomologyOverField f (ℱ[0]) n`. -/
@[ega "III 6.2.1" "special case"]
def cohomologyOverFieldFunctorIsoDerivedCohomology (n : ℕ) :
    cohomologyOverFieldFunctor k f n ≅
      DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ) :=
  rightDerivedCompRestrictScalarsIso
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)))
      (globalSectionsOver f) (evaluationCompRestrictScalarsIsoGlobalSectionsOver k f) n
      (hE := AlgebraicGeometry.evaluationAdditive X)
      (hH := AlgebraicGeometry.globalSectionsOver_additive f) ≪≫
    rightDerivedGlobalSectionsIsoDerivedCohomology f n

/-- `Hⁿ(X, ℱ) ≅ H^n(X, ℱ[0])` in `ModuleCat k`: the `n`-th sheaf cohomology of `ℱ` over the base
field is the degree-`n` hypercohomology of `ℱ` placed in degree zero. -/
def cohomologyOverFieldIsoDerivedCohomologyOverField (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n ≅
      derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) (n : ℤ) :=
  (cohomologyOverFieldFunctorIsoDerivedCohomology k f n).app F

/-- `Hⁿ(X, ℱ) ≃ₗ[k] H^n(X, ℱ[0])`: the comparison
`Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField` as a `k`-linear equivalence. -/
def cohomologyOverFieldLinearEquivDerivedCohomologyOverField (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n ≃ₗ[k]
      derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) (n : ℤ) :=
  (cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).toLinearEquiv

/-- For an integer `m` with `m = n`, the morphisms
`derivedCohomologyOverField f (ℱ[0]) m ⟶ k` correspond additively to the `k`-linear functionals
`cohomologyOverField k f ℱ n →ₗ[k] k`. -/
def derivedCohomologyOverFieldDualAddEquiv (F : X.Modules) (n : ℕ) (m : ℤ) (hm : m = n) :
    (derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj F) m ⟶
        ModuleCat.of k k) ≃+ (cohomologyOverField k f F n →ₗ[k] k) := by
  subst hm
  exact (precompAddEquiv
      (cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).symm).trans ModuleCat.homAddEquiv

/-- The comparison is natural in the module: it intertwines `Hⁿ(X, φ)` with the map `φ` induces
on hypercohomology. -/
theorem cohomologyOverFieldIsoDerivedCohomologyOverField_naturality (n : ℕ) {F G : X.Modules}
    (φ : F ⟶ G) :
    (cohomologyOverFieldFunctor k f n).map φ ≫
        (cohomologyOverFieldIsoDerivedCohomologyOverField k f G n).hom =
      (cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).map φ :=
  (cohomologyOverFieldFunctorIsoDerivedCohomology k f n).hom.naturality φ

/-- The comparison intertwines `AlgebraicGeometry.cohomologyOverFieldMap` with the map induced
on hypercohomology. -/
theorem cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap (n : ℕ)
    {F G : X.Modules} (φ : F ⟶ G) :
    cohomologyOverFieldMap k f φ n ≫
        (cohomologyOverFieldIsoDerivedCohomologyOverField k f G n).hom =
      (cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).map φ := by
  with_unfolding_all
  exact cohomologyOverFieldIsoDerivedCohomologyOverField_naturality k f n φ

end Stacks.Duality

end
