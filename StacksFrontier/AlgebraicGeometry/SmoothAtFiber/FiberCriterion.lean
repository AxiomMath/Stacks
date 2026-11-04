module

public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.OpenImmersionFiber
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Jacobian
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion

/-!
# Smoothness at a point passes to the scheme-theoretic fibre

Condition (2) of Stacks Tag 01V9 is the conjunction of flatness of the induced map of local
rings with smoothness at the point of the scheme-theoretic fibre through it.  This file derives
condition (2) from condition (1), smoothness of the morphism at the point, and from conditions
(5) and (6).

## Main results

* `Stacks.SmoothAtJacobian.smoothAt_fiberToSpecResidueField_of_smoothAt`: if `f` is smooth at
  `x` then the fibre of `f` through `x`, as a scheme over the residue field of `f x`, is smooth
  at `x`.
* `Stacks.SmoothAtJacobian.condition1_imp_condition2`: condition (1) of Tag 01V9 implies
  condition (2).
* `Stacks.SmoothAtJacobian.condition5_imp_condition2` and
  `Stacks.SmoothAtJacobian.condition6_imp_condition2`: conditions (5) and (6) of Tag 01V9 imply
  condition (2).

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 01VB](https://stacks.math.columbia.edu/tag/01VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SmoothAtJacobian

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- If `f` is smooth at `x`, then the scheme-theoretic fibre of `f` through `x`, viewed as a
scheme over the residue field of `f x`, is smooth at the point of it determined by `x`. -/
public theorem smoothAt_fiberToSpecResidueField_of_smoothAt
    (h : InfinitesimalLifting.SmoothAt f x) :
    InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x) := by
  obtain ⟨U, hxU, hU⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp f x).mp h
  have hfib : Smooth ((U.ι ≫ f).fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Smooth (pullback.snd (U.ι ≫ f) (S.fromSpecResidueField (f x))))
  rw [← Scheme.Hom.fiberMapOfComp_fiberToSpecResidueField U.ι f (f x)] at hfib
  obtain ⟨z, hz⟩ : f.asFiber x ∈ Set.range (Scheme.Hom.fiberMapOfComp U.ι f (f x)) := by
    rwa [Scheme.Hom.range_fiberMapOfComp, Set.mem_preimage, f.fiberι_asFiber x,
      Scheme.Opens.range_ι]
  rw [← hz]
  exact InfinitesimalLifting.smoothAt_of_smooth_comp (Scheme.Hom.fiberMapOfComp U.ι f (f x))
    (f.fiberToSpecResidueField (f x)) hfib z

/-- Condition (1) of Tag 01V9 implies condition (2): a morphism smooth at a point has flat
induced map of local rings there, and its fibre through the point is smooth at the point. -/
public theorem condition1_imp_condition2 (h : Condition1 f x) : Condition2 f x :=
  ⟨condition1_imp_flat_stalkMap f x h, smoothAt_fiberToSpecResidueField_of_smoothAt f x h⟩

/-- Condition (5) of Tag 01V9 implies condition (2). -/
public theorem condition5_imp_condition2 (h : Condition5 f x) : Condition2 f x :=
  condition1_imp_condition2 f x ((condition1_iff_condition5 f x).mpr h)

/-- Condition (6) of Tag 01V9 implies condition (2). -/
public theorem condition6_imp_condition2 (h : Condition6 f x) : Condition2 f x :=
  condition1_imp_condition2 f x (condition6_imp_condition1 f x h)

end Stacks.SmoothAtJacobian

end
