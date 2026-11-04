module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Setup
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycleProduct

/-!
# Tag 0B1V: reduction to a prime cycle in the second variable

The intersection product is linear in its second variable, a cycle on a quasi-compact scheme is
the finite sum of the multiples of the prime cycles of its components, and two cycles intersecting
properly have every pair of components intersecting properly. So to show that `α · β` is rationally
equivalent to zero for every `β` intersecting `α` properly, it suffices to treat the prime cycles
`β = [Z]`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsLocallyNoetherian X] [CompactSpace X] (hX : IsRegular X)

/-- **Reduction to prime cycles in the second variable.** If `α · [z] ∈ R_m` for every point `z`
of relative dimension `s` whose prime cycle meets `α` properly, then `α · β ∈ R_m` for every
`s`-cycle `β` meeting `α` properly. -/
theorem torFormulaCycleIntersectionProduct_mem_ratCycles_of_single [DecidableEq X] (m s : ℤ)
    (α : AlgebraicCycle X ℤ)
    (h : ∀ z : X, relativeDimension C.dimensionFunction p z = s →
      AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single z (1 : ℤ)) →
      torFormulaCycleIntersectionProduct C p hX m α
        (Function.locallyFinsuppWithin.single z (1 : ℤ)) ∈ ratCycles C p m)
    (β : CycleGroup C p s) (hαβ : AlgebraicCycle.IntersectProperly α β.1) :
    torFormulaCycleIntersectionProduct C p hX m α β.1 ∈ ratCycles C p m := by
  have hfin := finite_support_of_compactSpace β.1
  rw [AlgebraicCycle.eq_sum_zsmul_single hfin]
  show cycleIntersectionProductRightHom (torFormulaSubvarietyProductTotal C p hX m) α _ ∈ _
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun z hz => ?_
  have hz' : β.1 z ≠ 0 := hfin.mem_toFinset.mp hz
  rw [map_zsmul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  refine h z ((mem_cyclesOfDimension_iff_forall_point C p s β.1).mp β.2 z hz') ?_
  intro W V hW hV
  have hgen : V.isIrreducible.genericPoint = z := by
    by_contra hne
    exact hV (by rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right hne])
  refine hαβ W V hW ?_
  rw [hgen]
  exact hz'

end Stacks.Intersection.RationalEquivalenceProduct

end
