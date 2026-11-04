module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Vanishing of cohomology does not depend on the coefficients being remembered

For a sheaf of rings `R` on a topological space and an open `U`, the cohomology of a sheaf of
`R`-modules over `U` can be computed either in `ModuleCat (R(U))`, as the right derived functor
of `SheafOfModules.evaluation R (op U)`, or in `AddCommGrpCat`, as the cohomology group
`Hgroup R U n` of the underlying abelian sheaf.  The two are identified by
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, and in particular one of
them is a zero object exactly when the other is.

This equivalence is what lets a vanishing statement proved for one model be consumed by a
statement phrased in the other.

## Main results

* `Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

variable {X : Type u} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X) [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **Module-valued and group-valued cohomology over `U` vanish together.** The `n`-th right
derived functor of module-valued sections of `F` over `U` is a zero object precisely when the
cohomology group `Hⁿ(U, F)` is, because the two are identified by
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` after forgetting the module
structure, and forgetting it neither creates nor destroys the property of having at most one
element. -/
theorem isZero_rightDerived_evaluation_iff_isZero_hgroup (n : ℕ) (F : SheafOfModules.{u} R) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) ↔
      IsZero (Hgroup R U n F) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (Functor.map_isZero (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u})
      h).of_iso ((rightDerivedEvaluationForgetIso R U n).app F).symm
  · exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero
      (h.of_iso ((rightDerivedEvaluationForgetIso R U n).app F)))

end Stacks.Cohomology.ModuleComparison

end
