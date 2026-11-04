module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The resolution property and perfect complexes

Let `X` be a scheme. This file defines the homotopy category `K^b(A)` of bounded complexes of
finite locally free `O_X`-modules, the full subcategory `D_perf(O_X)` of perfect objects of the
derived category, and the system of quasi-isomorphisms of `K^b(A)`.

## Main definitions

* `Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex`,
  `Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeHomotopyProperty` and
  `Stacks.Perfect.BoundedLocallyFreeComplexes.BoundedFiniteLocallyFreeHomotopyCategory`: the
  complexes of `K^b(A)`, the corresponding property of objects of the homotopy category, and
  `K^b(A)` itself.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`: the category
  `D_perf(O_X)`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms`: the system `S` of
  quasi-isomorphisms of `K^b(A)`.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.restrictModules_eq_restrictFunctor`: restriction of
  modules to an open subscheme `U` agrees with `AlgebraicGeometry.Scheme.Modules.restrictFunctor`
  along the inclusion of `U`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isClosedUnderIsomorphisms`:
  perfect objects form a strictly full subcategory of the derived category.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
  Stacks.Cohomology.PerfectComplexes

universe u d

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-! ### The two restriction functors agree -/

/-- **Restriction of modules to an open subscheme is restriction to the open ringed subspace.** -/
theorem restrictModules_eq_restrictFunctor (X : Scheme.{u}) (U : X.Opens) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace U =
      Scheme.Modules.restrictFunctor U.ι := by
  unfold AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules
    Scheme.Modules.restrictFunctor
  congr 1
  ext V x
  simp [Scheme.Opens.ι_appIso]
  rfl

/-! ### The categories `K^b(A)` and `D_perf(O_X)` -/

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- Bounded complexes of finite locally free modules on a scheme: the complexes of `K^b(A)`. -/
abbrev boundedFiniteLocallyFreeComplex (X : Scheme.{u}) :
    ObjectProperty (CochainComplex X.Modules ℤ) :=
  fun E => (CochainComplex.plus X.Modules E ∧ CochainComplex.minus X.Modules E) ∧
    ∀ i : ℤ, Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) (E.X i)

/-- The property of an object of the homotopy category of being the image of a bounded complex
of finite locally free modules. -/
abbrev boundedFiniteLocallyFreeHomotopyProperty (X : Scheme.{u}) :
    ObjectProperty (HomotopyCategory X.Modules (.up ℤ)) :=
  (boundedFiniteLocallyFreeComplex X).strictMap
    (HomotopyCategory.quotient X.Modules (.up ℤ))

/-- The homotopy category `K^b(A)` of bounded complexes of finite locally free modules. -/
@[stacks 0F8I "the category K^b(A)"]
abbrev BoundedFiniteLocallyFreeHomotopyCategory (X : Scheme.{u}) :=
  (boundedFiniteLocallyFreeHomotopyProperty X).FullSubcategory

/-- The full subcategory `D_perf(O_X)` of perfect objects of the derived category. -/
@[stacks 0F8I "the category of perfect objects"]
abbrev PerfectDerivedCategory (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)

/-- The system `S` of quasi-isomorphisms of `K^b(A)`. -/
@[stacks 0F8I "the system S of quasi-isomorphisms"]
abbrev quasiIsomorphisms (X : Scheme.{u}) :
    MorphismProperty (BoundedFiniteLocallyFreeHomotopyCategory X) :=
  (HomotopyCategory.quasiIso X.Modules (.up ℤ)).inverseImage
    (boundedFiniteLocallyFreeHomotopyProperty X).ι

/-- **Perfect objects form a strictly full subcategory of `D(O_X)`.** -/
@[stacks 0F8I "perfect objects are closed under isomorphism",
  stacks 0FDG "(1) D_perf(𝒪_X) is STRICTLY FULL in D(𝒪_X) — the first of the three adjectives \
Definition 0FDG (1) attaches to the subcategory whose K-group it names. The definitional clause \
itself is `AlgebraicGeometry.PerfectKZero`"]
instance perfectDerivedProperty_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K) :=
  @isClosedUnderIsomorphisms_isPerfect.{u, u, u + 1} X.toRingedSpace inferInstance

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
