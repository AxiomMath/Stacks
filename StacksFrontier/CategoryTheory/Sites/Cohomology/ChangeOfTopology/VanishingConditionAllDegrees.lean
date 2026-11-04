module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionInduction

/-!
# The vanishing condition in every degree

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology
morphism and let `(V_n)` be the condition
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition`: the higher direct images
`R^i ε_{X,*} ℱ` vanish for `1 ≤ i ≤ n`, for every object `X` and every `ℱ` of the class `𝒜_X`.

The first assertion of Stacks 0EZF is that `(V_n)` holds for every `n`. The source obtains it by
induction: `(V_0)` is the empty condition, and Stacks 0EZE supplies the step `(V_n) ⇒ (V_{n+1})`.
Both halves of that induction are available in this development --
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_zero` and
`Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_succ` -- except that the
latter is granted the descent statement
`Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent` in degree `n + 1`, which
is the part of the proof of Stacks 0EZE that is not yet proved here.

This file closes the induction itself, so that the assertion `∀ n, (V_n)` is reduced to that one
descent statement, in each of its two equivalent forms.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_of_singleCoveringDescent`:
  if the descent statement for a single covering arrow of the distinguished class holds in every
  positive degree, then `(V_n)` holds for every `n`.
* `CohomologyComparison.vanishingCondition_of_singleCoveringDescentRange`, in the same
  namespace: the same from the purely derived form
  `Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescentRange` of the descent
  statement, in which no covering occurs.

## Status

Neither result below carries the Stacks attribute: both are conditional on the descent
statement. That statement is proved under `(V_n)` as
`Stacks.ComparingTopologies.CohomologyComparison.singleCoveringDescent`, and the unconditional
Stacks 0EZE and 0EZF are in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public section

universe v u

open CategoryTheory

namespace Stacks.ComparingTopologies

variable {C : Type u} [Category.{v} C]

namespace CohomologyComparison

/-- **The vanishing condition in every degree, granted the descent statement for a single
covering arrow of the distinguished class in every positive degree.** This is the induction by
which Stacks 0EZF obtains its first assertion: the base case `(V_0)` is the empty condition,
`vanishingCondition_zero`, and the step is `vanishingCondition_succ`, which is Stacks 0EZE
granted `SingleCoveringDescent` in the degree being reached. -/
theorem vanishingCondition_of_singleCoveringDescent (S : CohomologyComparison C)
    (hdesc : ∀ m : ℕ, S.SingleCoveringDescent (m + 1)) (n : ℕ) :
    S.vanishingCondition n := by
  induction n with
  | zero => exact S.vanishingCondition_zero
  | succ n hn => exact S.vanishingCondition_succ_of_singleCoveringDescent n hn (hdesc n)

/-- **The vanishing condition in every degree, granted the descent statement in its purely
derived form.** The two forms of the descent statement are equivalent in degree `n + 1` under
`(V_n)` by `singleCoveringDescent_iff_range`, and `(V_n)` is exactly what the induction has
available when it reaches degree `n + 1`. -/
theorem vanishingCondition_of_singleCoveringDescentRange (S : CohomologyComparison C)
    (hdesc : ∀ m : ℕ, S.SingleCoveringDescentRange (m + 1)) (n : ℕ) :
    S.vanishingCondition n := by
  induction n with
  | zero => exact S.vanishingCondition_zero
  | succ n hn => exact S.vanishingCondition_succ_of_range n hn (hdesc n)

end CohomologyComparison

end Stacks.ComparingTopologies

end
