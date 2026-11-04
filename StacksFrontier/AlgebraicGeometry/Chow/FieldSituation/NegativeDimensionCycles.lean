module

public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base

/-!
# There are no cycles of negative dimension over a field

Over the spectrum of a field the dimension function vanishes, so the relative dimension of a
point is a transcendence degree and in particular nonnegative. Hence a `k`-cycle with `k < 0` on a
scheme locally of finite type over a field is zero.

## Main results

* `Stacks.Chow.cycleGroup_eq_zero_of_neg` — every cycle of negative dimension over a field is
  zero.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Chow

/-- **Over a field there are no nonzero cycles of negative dimension.** The relative dimension
of every point over `Spec K` is the transcendence degree of its residue field, which is
nonnegative, so no point carries a nonzero coefficient of a `k`-cycle with `k < 0`. -/
theorem cycleGroup_eq_zero_of_neg (K : Type u) [Field K] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of K)) [LocallyOfFiniteType s] {k : ℤ} (hk : k < 0)
    (c : CycleGroup (fieldChowSituation K) s k) : c = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  by_contra hy
  have h := (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation K) s k c.1).1 c.2 y hy
  rw [relativeDimension, fieldChowSituation_dimensionFunction, zero_add] at h
  omega

end Stacks.Chow
