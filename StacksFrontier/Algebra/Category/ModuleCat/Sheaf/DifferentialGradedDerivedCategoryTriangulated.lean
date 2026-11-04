module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived category of a sheaf of differential graded algebras is triangulated

Let `(C, O)` be a ringed site and let `(A, d)` be a sheaf of differential graded `O`-algebras.
The quasi-isomorphisms of `K(Mod(A, d))` are the class of arrows attached to the triangulated
subcategory of acyclic objects, which is [Stacks, Tag 0FT4]. That class admits a calculus of
fractions and is compatible with the triangulation of `K(Mod(A, d))`, so the derived category
`D(A, d)` — the localization at the quasi-isomorphisms — carries a triangulated structure for
which the localization functor is exact.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions`,
  `….quasiIsomorphisms_hasRightCalculusOfFractions`,
  `….quasiIsomorphisms_isCompatibleWithTriangulation`: the quasi-isomorphisms admit a two-sided
  calculus of fractions compatible with the triangulation.
* `SheafOfModules.DifferentialGradedModule.derivedCategory_isTriangulated`: **`D(A, d)` is a
  triangulated category**, and **the localization functor is exact**, by Mathlib's instance
  `CategoryTheory.Triangulated.Localization.isTriangulated_functor`.

## Implementation notes

Everything here is Mathlib's construction of a triangulated structure on a localization,
`CategoryTheory.Localization.Triangulated`, applied after rewriting along
`SheafOfModules.DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms` of [Stacks, Tag 0FT4]:
Mathlib supplies the calculus of fractions and the compatibility with the triangulation for the
class of arrows attached to a strictly full saturated triangulated subcategory, which is what the
acyclic objects are by [Stacks, Tag 0FT3]. The same pattern is used on the non-sheaf side in
`StacksFrontier/Algebra/DGA/DerivedCategory.lean`.

The three properties of the quasi-isomorphisms are declared as instances rather than theorems
because the pre-triangulated structure on `D(A, d)` is found by instance search from them.
Pre-triangulatedness itself is data, not a proposition, so it is not stated as a theorem;
`derivedCategory_isTriangulated` records it, its own statement presupposing the instance.

## References

* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FT3](https://stacks.math.columbia.edu/tag/0FT3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The quasi-isomorphisms contain the identities and are stable under composition. -/
instance quasiIsomorphisms_isMultiplicative' :
    (quasiIsomorphisms.{u, v, w} A).IsMultiplicative :=
  quasiIsomorphisms_isMultiplicative A

/-- The quasi-isomorphisms admit a left calculus of fractions: they are the class of arrows
attached to the triangulated subcategory of acyclic objects. -/
instance quasiIsomorphisms_hasLeftCalculusOfFractions :
    (quasiIsomorphisms.{u, v, w} A).HasLeftCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- The quasi-isomorphisms admit a right calculus of fractions, for the same reason. -/
instance quasiIsomorphisms_hasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, v, w} A).HasRightCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- **Stacks Project, Tag 0FT4.** The quasi-isomorphisms are compatible with the triangulation
of `K(Mod(A, d))`: they are the class of arrows attached to the triangulated subcategory of
acyclic objects. -/
@[stacks 0FT4 "Qis is compatible with the triangulation of K(Mod(A,d))"]
instance quasiIsomorphisms_isCompatibleWithTriangulation :
    (quasiIsomorphisms.{u, v, w} A).IsCompatibleWithTriangulation := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- **The derived category `D(A, d)` is a triangulated category**, with the images of the
distinguished triangles of `K(Mod(A, d))` as its distinguished triangles. Its pre-triangulated
structure is the one Mathlib puts on a localization at a class of morphisms compatible with the
triangulation, and is found by instance search; stating this makes that search run, since
`CategoryTheory.IsTriangulated` presupposes it. -/
@[stacks 0FT4 "D(A,d) is pre-triangulated, and triangulated"]
theorem derivedCategory_isTriangulated : IsTriangulated (derivedCategory.{u, v, w} A) :=
  inferInstance

add_to_stacks 0FT4 "the localization functor is exact"
  CategoryTheory.Triangulated.Localization.isTriangulated_functor
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Triangulated.Localization.isTriangulated_functor
add_to_sga "4½ Etat_0 Problem2" "exactness of Q, partial"
  CategoryTheory.Triangulated.Localization.isTriangulated_functor

end SheafOfModules.DifferentialGradedModule

end
