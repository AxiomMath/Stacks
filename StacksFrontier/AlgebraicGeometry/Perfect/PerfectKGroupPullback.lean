module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback on the Grothendieck group of perfect complexes

Let `f : X ⟶ Y` be a morphism of ringed spaces. The derived pullback `Lf^*` carries perfect
objects of `D(𝒪_Y)` to perfect objects of `D(𝒪_X)`
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`) and is exact
(`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated`), so it restricts to an
exact functor between the triangulated subcategories of perfect objects and induces a
homomorphism

`f^* : K₀(D_perf(𝒪_Y)) ⟶ K₀(D_perf(𝒪_X))`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.perfectPullbackKZero`: the homomorphism `f^*` itself.

## Main results

* `AlgebraicGeometry.RingedSpace.perfectPullbackKZero_cls`: it sends the class of a perfect
  object to the class of its derived pullback.

## References

* [Stacks, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks, Tag 0FCQ](https://stacks.math.columbia.edu/tag/0FCQ)
* [Stacks, Tag 0FDM](https://stacks.math.columbia.edu/tag/0FDM)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry.RingedSpace

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The pullback on the Grothendieck group of perfect complexes.** For a morphism of ringed
spaces `f : X ⟶ Y`, the restriction of `Lf^*` to perfect objects induces

`f^* : K₀(D_perf(𝒪_Y)) ⟶ K₀(D_perf(𝒪_X))`. -/
def perfectPullbackKZero :
    K0 (ObjectProperty.FullSubcategory (IsPerfect.{u, u, u + 1} (X := Y))) →+
      K0 (ObjectProperty.FullSubcategory (IsPerfect.{u, u, u + 1} (X := X))) :=
  K0.mapSubcategory (IsPerfect.{u, u, u + 1} (X := Y)) (IsPerfect.{u, u, u + 1} (X := X))
    (derivedPullback f)
    (fun E hE => KFlatDerivedPullback.isPerfect_derivedPullback f E hE)
    (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f)
    (Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated f)

/-- `f^*` sends the class of a perfect object to the class of its derived pullback. -/
@[simp] theorem perfectPullbackKZero_cls
    (E : ObjectProperty.FullSubcategory (IsPerfect.{u, u, u + 1} (X := Y))) :
    perfectPullbackKZero f (K0.cls E) =
      K0.cls ⟨(derivedPullback f).obj E.obj,
        KFlatDerivedPullback.isPerfect_derivedPullback f E.obj E.property⟩ := by
  simp only [perfectPullbackKZero]
  exact K0.mapSubcategory_cls _ _ _ _ _ _ E

end

end AlgebraicGeometry.RingedSpace

end

end
