module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Presentation
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear

/-!
# Tag 0B1V: where a rationally trivial cycle lives

The components of a presentation `α = ∑ cᵢ ([Wᵢ,₀]_r - [Wᵢ,∞]_r)` are irreducible components of the
fibres `Wᵢ,₀` and `Wᵢ,∞`; and proper intersection with prime cycles is the numerical inequality on
the dimensions of the closures.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- **A point carrying a nonzero coefficient in the cycle of a closed subscheme is the generic
point of an irreducible component of its support.** -/
theorem closure_mem_componentSets_of_cycle_ne_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (D : X.IdealSheafData) (m : ℤ) {t : X}
    (ht : (cycleAssociatedToClosedSubscheme C p D.subschemeι m).1 t ≠ 0) :
    closure ({t} : Set X) ∈ componentSets (D.support : Set X) := by
  obtain ⟨ξ, hξ, -⟩ : ∃ ξ : genericPoints D.subscheme,
      D.subschemeι ξ.1 = t ∧ relativeDimension C.dimensionFunction p t = m := by
    by_contra hno
    exact ht (cycleAssociatedToClosedSubscheme_apply_eq_zero C p D.subschemeι m t hno)
  let e : D.subscheme ≃ₜ ↥(D.support : Set X) :=
    D.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι D))
  refine ⟨e '' closure {ξ.1}, image_mem_irreducibleComponents_of_homeomorph e ξ.2, ?_⟩
  rw [Set.image_image]
  show (D.subschemeι.base) '' closure {ξ.1} = _
  rw [← D.subschemeι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hξ]

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsVariety k p]

/-- **The components of a presentation lie in the family of fibre components.** -/
theorem closure_mem_fibreComponentSets_of_ne_zero [IsAlgClosed k] {ι : Type*} [Fintype ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) (c : ι → ℤ) (r : ℤ) {t : X}
    (ht : (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (zeroFiber p (W i)).subschemeι r).1 -
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
        (infinityFiber p (W i)).subschemeι r).1)) t ≠ 0) :
    closure ({t} : Set X) ∈ fibreComponentSets k p W := by
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply] at ht
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply] at hi
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  by_cases h0 : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
      (zeroFiber p (W i)).subschemeι r).1 t = 0
  · right
    refine closure_mem_componentSets_of_cycle_ne_zero (fieldChowSituation k) p _ r ?_
    intro hinf
    rw [h0, hinf, sub_zero, smul_zero] at hi
    exact hi rfl
  · left
    exact closure_mem_componentSets_of_cycle_ne_zero (fieldChowSituation k) p _ r h0

/-- **Proper intersection of the closures of two points, numerically.** -/
theorem intersectProperly_closure_iff {x y : X} {n r s : ℕ}
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞))
    (hx : topologicalKrullDim (closure ({x} : Set X)) = (r : WithBot ℕ∞))
    (hy : topologicalKrullDim (closure ({y} : Set X)) = (s : WithBot ℕ∞)) :
    AlgebraicGeometry.IntersectProperly
        ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
        ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ ↔
      topologicalKrullDim ↥(closure ({x} : Set X) ∩ closure ({y} : Set X)) +
          (n : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.intersectProperly_iff]
  show topologicalKrullDim ↥(closure ({x} : Set X) ∩ closure ({y} : Set X)) +
      topologicalKrullDim X ≤ topologicalKrullDim ↥(closure ({x} : Set X)) +
        topologicalKrullDim ↥(closure ({y} : Set X)) ↔ _
  rw [hn, hx, hy, Nat.cast_add]

end Stacks.Intersection.RationalEquivalenceProduct

end
