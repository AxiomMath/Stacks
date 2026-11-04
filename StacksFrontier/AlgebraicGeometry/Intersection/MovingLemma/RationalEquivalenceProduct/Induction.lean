module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Presentation

/-!
# Tag 0B1V: the induction on the excess of intersection

The proof of Tag 0B1V is an induction on how far a closed subvariety `Z` of dimension `s` is from
meeting a fixed finite family `𝒯` of closed subvarieties of dimension `r` properly: the *excess*
is the least `m` with `dim (Z ∩ T) + dim X ≤ r + s + m` for every `T ∈ 𝒯`. The base case `m = 0`
is supplied separately (it is Tag 0B60), and so is the inductive step, which writes `[Z]` as a
cycle `γ` with `α · γ` already known to be rationally trivial minus a combination of prime cycles
of smaller excess (it is the moving argument of Tags 0B0E, 0B1T and 0B1M). This file is the bare
induction, generic over both inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsLocallyNoetherian X] [CompactSpace X] [DecidableEq X] (hX : IsRegular X)

/-- **The induction on the excess.** Let `𝒯` be a family of closed subsets of dimension at most
`r`, `α` a cycle, and `R` the rationally trivial `g`-cycles. Suppose

* (base) `α · [Z] ∈ R` for every closed subvariety `Z = closure {z}` of dimension `s` meeting `α`
  and every member of `𝒯` properly;
* (step) every such `Z` of excess `m + 1` which does not meet some member of `𝒯` properly has
  `[Z] = γ - ∑_{j ∈ S} c_j [closure {w_j}]` with `α · γ ∈ R` and every `closure {w_j}` of dimension
  `s`, meeting `α` properly, and of excess `m`.

Then `α · [Z] ∈ R` for every closed subvariety `Z` of dimension `s` meeting `α` properly. -/
theorem torFormulaCycleIntersectionProduct_single_mem_ratCycles_of_induction (g : ℤ) (n r s : ℕ)
    (α : AlgebraicCycle X ℤ) (𝒯 : Set (Set X))
    (h𝒯 : ∀ T ∈ 𝒯, topologicalKrullDim ↥T ≤ (r : WithBot ℕ∞))
    (hbase : ∀ z : X, topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞) →
      AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single z 1) →
      (∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞)) →
      torFormulaCycleIntersectionProduct C p hX g α
        (Function.locallyFinsuppWithin.single z 1) ∈ ratCycles C p g)
    (hstep : ∀ (m : ℕ) (z : X), topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞) →
      AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single z 1) →
      (∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
        ((s + r + (m + 1) : ℕ) : WithBot ℕ∞)) →
      ¬ (∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞)) →
      ∃ (κ : Type u) (S : Finset κ) (w : κ → X) (c : κ → ℤ) (γ : AlgebraicCycle X ℤ),
        Function.locallyFinsuppWithin.single z 1 =
          γ - ∑ j ∈ S, c j • Function.locallyFinsuppWithin.single (w j) 1 ∧
        torFormulaCycleIntersectionProduct C p hX g α γ ∈ ratCycles C p g ∧
        ∀ j ∈ S, topologicalKrullDim (closure ({w j} : Set X)) = (s : WithBot ℕ∞) ∧
          AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single (w j) 1) ∧
          ∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({w j} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
            ((s + r + m : ℕ) : WithBot ℕ∞))
    (z : X) (hz : topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞))
    (hαz : AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single z 1)) :
    torFormulaCycleIntersectionProduct C p hX g α (Function.locallyFinsuppWithin.single z 1) ∈
      ratCycles C p g := by
  -- every subvariety has excess at most `n`
  have hinit : ∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
      ((s + r + n : ℕ) : WithBot ℕ∞) := by
    intro T hT
    calc topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞)
        ≤ (r : WithBot ℕ∞) + (n : WithBot ℕ∞) :=
          add_le_add_left ((topologicalKrullDim_le_of_subset Set.inter_subset_right).trans
            (h𝒯 T hT)) _
      _ ≤ ((s + r + n : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_add]
        exact_mod_cast (by omega : r + n ≤ s + r + n)
  have key : ∀ m : ℕ, ∀ z : X, topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞) →
      AlgebraicCycle.IntersectProperly α (Function.locallyFinsuppWithin.single z 1) →
      (∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) + (n : WithBot ℕ∞) ≤
        ((s + r + m : ℕ) : WithBot ℕ∞)) →
      torFormulaCycleIntersectionProduct C p hX g α
        (Function.locallyFinsuppWithin.single z 1) ∈ ratCycles C p g := by
    intro m
    induction m with
    | zero => exact hbase
    | succ m ih =>
      intro z hz hαz hm
      by_cases hprop : ∀ T ∈ 𝒯, topologicalKrullDim ↥(closure ({z} : Set X) ∩ T) +
          (n : WithBot ℕ∞) ≤ ((s + r : ℕ) : WithBot ℕ∞)
      · exact hbase z hz hαz hprop
      obtain ⟨κ, S, w, c, γ, heq, hγ, hS⟩ := hstep m z hz hαz hm hprop
      rw [heq]
      change cycleIntersectionProductRightHom (torFormulaSubvarietyProductTotal C p hX g) α _ ∈ _
      rw [map_sub, map_sum]
      refine AddSubgroup.sub_mem _ hγ (AddSubgroup.sum_mem _ fun j hj => ?_)
      rw [map_zsmul]
      obtain ⟨hw1, hw2, hw3⟩ := hS j hj
      exact AddSubgroup.zsmul_mem _ (ih (w j) hw1 hw2 hw3) _
  exact key n z hz hαz hinit

end Stacks.Intersection.RationalEquivalenceProduct

end
