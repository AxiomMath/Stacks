module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.DirectSummands

/-!
# Saturation of `D_perf(O_X)` from Tag 08CS

Tag 0F8I asserts that `D_perf(O_X)` is a *saturated* subcategory of `D(O_X)`, that is, closed
under direct summands. That assertion is Tag 08CS, and this file derives saturation of
perfectness from the conclusion of 08CS on a ringed space.

**Tag 08CS is proved**, as `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`, by the 08CQ
route, and `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isSaturated` in
`StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupPerfect` is the scheme-level conclusion
with no hypothesis, obtained from the statement below. Where the notes in the sibling file
`SaturationFromPseudoCoherence.lean` say that 08CS, Tag 08CE or the converse half of Tag 08CQ is
not in the trees, that was true when they were written and is not true now.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod`: on a ringed space,
  perfectness is a saturated property of objects of `D(O_X)` as soon as both summands of a
  perfect biproduct are perfect.

## Implementation notes

`CategoryTheory.ObjectProperty.IsSaturated` is stated in terms of the isomorphism closure of the
property, and perfectness is already closed under isomorphism
(`Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect`), so the two fields are
the two halves of 08CS after rewriting by `CategoryTheory.ObjectProperty.isoClosure_eq_self`. The
general bridge from stability under retracts is not used: it exists twice in the trees
(`StacksFrontier.CategoryTheory.Triangulated.Quotient` and
`StacksFrontier.CategoryTheory.Triangulated.Generators`) and is `private` in both, and the
biproduct form is what 08CS supplies anyway.

The statement is at an arbitrary module universe, as Tag 08CM itself is, and for any model of
`D(O_X)`.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u v d

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- **Perfectness is a saturated property of objects of `D(O_X)`, given Tag 08CS.** Saturation
is stated for the isomorphism closure of the property; perfectness is closed under isomorphism,
so the closure is the property itself and the two fields are the two conclusions of 08CS. -/
theorem isSaturated_isPerfect_of_biprod {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (h : ∀ K L : DerivedCategory (OXMod.{u, v} X),
      IsPerfect (K ⊞ L) → IsPerfect K ∧ IsPerfect L) :
    ObjectProperty.IsSaturated
      (fun K : DerivedCategory (OXMod.{u, v} X) => IsPerfect K) where
  isoClosure_of_biprod_left {K L} _ hKL := by
    rw [ObjectProperty.isoClosure_eq_self] at hKL ⊢
    exact (h K L hKL).1
  isoClosure_of_biprod_right {K L} _ hKL := by
    rw [ObjectProperty.isoClosure_eq_self] at hKL ⊢
    exact (h K L hKL).2

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
