module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Perfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Triangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `D_perf(O_X)` is triangulated, and `K^b(A) ⥤ D_perf(O_X)` is exact

The perfect objects of the derived category of a scheme form a triangulated subcategory of
`D(O_X)`, and the canonical functor `K^b(A) ⥤ D_perf(O_X)` of Tag 0F8I is exact.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated`: the property
  of being perfect is a triangulated object property.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor_isTriangulated`: the canonical
  functor `K^b(A) ⥤ D_perf(O_X)` is exact.

## Implementation notes

Nothing in the first result is special to schemes: the statement is
`Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect` on the ringed space
underlying `X`, at the standard derived-category universe that the rest of Tag 0F8I also uses.
The universe arguments are written out because the level of the derived-category instance is a
`max` that unification will not read off the value.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **Perfect objects form a triangulated subcategory of `D(O_X)`.** This is the ringed-space
statement `Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`, read on the
ringed space underlying `X`. -/
@[stacks 0F8I "perfect objects form a triangulated subcategory",
  stacks 0FDG "(1) D_perf(𝒪_X) is TRIANGULATED in D(𝒪_X) — the adjective of Definition 0FDG (1) \
that makes `K₀` of the subcategory defined at all, `CategoryTheory.Pretriangulated.K0` taking a \
`[Pretriangulated]` instance. The definitional clause itself is \
`AlgebraicGeometry.PerfectKZero`",
  sga "6 I 5.8.4" "special case",
  sga "6 III 4.2" "Identity-morphism case"]
instance perfectDerivedProperty_isTriangulated (X : Scheme.{u}) :
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsTriangulated :=
  @Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect.{u, u + 1}
    X.toRingedSpace inferInstance

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end

/-!
## The canonical functor `K^b(A) ⥤ D_perf(O_X)` is exact

The canonical functor `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor` lands in
`D_perf(O_X)`, which `perfectDerivedProperty_isTriangulated` shows is a triangulated subcategory
of `D(O_X)`; this section shows that the canonical functor is exact.

The canonical functor is `CategoryTheory.ObjectProperty.lift` of the composite
`K^b(A) ⥤ K(O_X) ⥤ D(O_X)` along the perfectness of its values, so its exactness is
`CategoryTheory.ObjectProperty.isTriangulated_lift` once that composite is known exact — the
inclusion of a triangulated subcategory is exact and `DerivedCategory.Qh` is a localization
functor of a pre-triangulated category.

Both the commutation with the shift and the exactness have to be stated for the functor as
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor`, which is a `def`; instance
search works at reducible transparency and so cannot apply the
`CategoryTheory.ObjectProperty.lift` instances through it.
Each is therefore obtained by unfolding the definition and naming the Mathlib instance at the
arguments of this file, the commutation first because the statement of exactness mentions it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
  Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical functor `K^b(A) ⥤ D_perf(O_X)` commutes with the shift.** It is a lift of
`DerivedCategory.Qh` restricted to `K^b(A)`, and a lift along a full subcategory inherits the
commutation with the shift of the functor it lifts. -/
instance perfectComplexFunctor_commShift (X : Scheme.{u}) :
    (perfectComplexFunctor X).CommShift ℤ := by
  haveI : ((boundedFiniteLocallyFreeHomotopyProperty X).ι ⋙
      DerivedCategory.Qh).CommShift ℤ := inferInstance
  unfold perfectComplexFunctor
  exact Functor.CommShift.ofComp
    (ObjectProperty.liftCompιIso
      (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)
      ((boundedFiniteLocallyFreeHomotopyProperty X).ι ⋙ DerivedCategory.Qh)
      (perfect_of_boundedFiniteLocallyFree X)) ℤ

/-- **The canonical functor `K^b(A) ⥤ D_perf(O_X)` is exact.** The composite
`K^b(A) ⥤ K(O_X) ⥤ D(O_X)` is exact, being the inclusion of a triangulated subcategory
followed by the localization functor of the derived category, and the canonical functor is its
lift along the perfectness of its values, which is exact because `D_perf(O_X)` is a
triangulated subcategory. -/
@[stacks 0F8I "exactness of the canonical functor"]
instance perfectComplexFunctor_isTriangulated (X : Scheme.{u}) :
    (perfectComplexFunctor X).IsTriangulated := by
  let P : ObjectProperty (DerivedCategory X.Modules) :=
    fun K => IsPerfect (X := X.toRingedSpace) K
  let F := (boundedFiniteLocallyFreeHomotopyProperty X).ι ⋙ DerivedCategory.Qh
  have hF : ∀ K, P (F.obj K) := perfect_of_boundedFiniteLocallyFree X
  have : P.IsTriangulated := perfectDerivedProperty_isTriangulated X
  change (ObjectProperty.lift P F hF).IsTriangulated
  infer_instance

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
