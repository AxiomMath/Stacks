module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Objects supported on a subset form a triangulated subcategory

Let `X` be an algebraic space over a scheme `S` and `T` a subset of `|X|`. The `𝒪_X`-modules whose
support (Stacks 04KA) is contained in `T` form a Serre subcategory of the `𝒪_X`-modules, and the
objects of `D(𝒪_X)` supported on `T` in the sense of Stacks 08GF, that is whose cohomology
sheaves are all supported on `T`, form a triangulated subcategory of `D(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.supportedModules`: the `𝒪_X`-modules supported on `T`.

## Main results

* `AlgebraicGeometry.Space.supportedModules_isSerreClass`: the modules supported on `T` form a
  Serre class.
* `AlgebraicGeometry.Space.derivedCategoryB_supportedModules_isTriangulated`: the objects of
  `D(𝒪_X)` supported on `T` form a triangulated subcategory, for any model of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.cohomologySupportedOn_eq_derivedCategoryB`: at the standard model of
  `D(𝒪_X)`, `AlgebraicGeometry.Space.CohomologySupportedOn` is
  `DerivedCategoryB.derivedCategoryB` of `supportedModules`.

## References

* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The `𝒪_X`-modules supported on a subset `T` of `|X|`: those whose support, in the sense of
Stacks 04KA, is contained in `T`. -/
def supportedModules (T : Set (points B S hS X.1)) :
    ObjectProperty (Modules.{u, u} B S hS X.1 X.2) :=
  fun F ↦ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆ T

/-- The `𝒪_X`-modules supported on `T` form a Serre class. -/
theorem supportedModules_isSerreClass (T : Set (points B S hS X.1)) :
    (supportedModules B S hS X T).IsSerreClass :=
  { exists_zero := ⟨0, isZero_zero _, by
      simp [supportedModules,
        (supportOfSheaf_eq_empty_iff_isZero B S hS X 0).2 (isZero_zero _)]⟩
    prop_of_mono := fun f _ hY ↦
      (supportOfSheaf_toSheaf_subset_of_mono B S hS X f).trans hY
    prop_of_epi := fun f _ hX ↦
      (supportOfSheaf_toSheaf_subset_of_epi B S hS X f).trans hX
    prop_X₂_of_shortExact := fun hE h₁ h₃ ↦
      (supportOfSheaf_middle_subset_union B S hS X _ hE).trans (Set.union_subset h₁ h₃) }

/-- Local instance form of `supportedModules_isSerreClass`. -/
private instance (T : Set (points B S hS X.1)) : (supportedModules B S hS X T).IsSerreClass :=
  supportedModules_isSerreClass ..

/-- The objects of `D(𝒪_X)` supported on `T`, in the sense of Stacks 08GF, form a triangulated
subcategory, for any model of the derived category. -/
theorem derivedCategoryB_supportedModules_isTriangulated (T : Set (points B S hS X.1))
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)] :
    (DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (WeakSerre.isWeakSerre_of_isWeakSerreClass _)

/-- The objects of `D(𝒪_X)` supported on `T` are closed under isomorphisms. -/
theorem derivedCategoryB_supportedModules_isClosedUnderIsomorphisms (T : Set (points B S hS X.1))
    [HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2)] :
    (DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _)

/-- At the standard model, the objects supported on `T` in the sense of Stacks 08GF are those
of `DerivedCategoryB.derivedCategoryB` of `supportedModules`. -/
theorem cohomologySupportedOn_eq_derivedCategoryB (T : Set (points B S hS X.1)) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    (CohomologySupportedOn B S hS X.1 X.2 T : ObjectProperty _) =
      DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) :=
  rfl

end AlgebraicGeometry.Space

end
