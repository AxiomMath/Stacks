module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Devissage
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.IntersectProperlyLinear

/-!
# Cycles which can be moved to meet a family of cycles properly

Let `β i` be finitely many cycles on a scheme `X`. Call a `k`-cycle `α` *movable off the `β i`*
when some cycle rationally equivalent to `α` intersects every `β i` properly. The moving lemma
(Tag 0B1U) asserts that on a nonsingular projective variety every cycle is movable; its proof
reduces by linearity to the prime cycles `[Z]`, and this file provides that reduction.

## Main definitions

* `Stacks.Chow.IsMovableOff`: the property of a `k`-cycle of being rationally equivalent to one
  meeting every member of a family of cycles properly.

## Main results

* `Stacks.Chow.IsMovableOff.add`, `Stacks.Chow.IsMovableOff.neg`,
  `Stacks.Chow.IsMovableOff.sub`, `Stacks.Chow.IsMovableOff.zsmul`: the movable cycles form a
  subgroup.
* `Stacks.Chow.isMovableOff_of_forall_pointCycle`: on a quasi-compact scheme a cycle is movable as
  soon as the prime cycle of every point of its support is.

## References

* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (k : ℤ) {ι : Type*} (β : ι → AlgebraicCycle X ℤ)

/-- A `k`-cycle `α` is **movable off** the cycles `β i` when some `k`-cycle rationally
equivalent to `α` intersects every `β i` properly. -/
def IsMovableOff (α : CycleGroup C sX k) : Prop :=
  ∃ α' : CycleGroup C sX k, RationallyEquivalent C sX k α' α ∧
    ∀ i, AlgebraicCycle.IntersectProperly α'.1 (β i)

variable {C sX k β}

/-- Rational equivalence is reflexive. -/
private theorem rationallyEquivalent_self (α : CycleGroup C sX k) :
    RationallyEquivalent C sX k α α := by
  rw [RationallyEquivalent, sub_self]
  exact zero_mem _

/-- The zero cycle is movable. -/
public theorem IsMovableOff.zero : IsMovableOff C sX k β 0 :=
  ⟨0, rationallyEquivalent_self _,
    fun _ W _ hW _ ↦ absurd (by simp) hW⟩

/-- A sum of movable cycles is movable: move the two summands separately. -/
public theorem IsMovableOff.add {α₁ α₂ : CycleGroup C sX k} (h₁ : IsMovableOff C sX k β α₁)
    (h₂ : IsMovableOff C sX k β α₂) : IsMovableOff C sX k β (α₁ + α₂) := by
  obtain ⟨α₁', hr₁, hp₁⟩ := h₁
  obtain ⟨α₂', hr₂, hp₂⟩ := h₂
  refine ⟨α₁' + α₂', ?_, fun i ↦ AlgebraicCycle.intersectProperly_add_left (hp₁ i) (hp₂ i)⟩
  have h := (rationalEquivalences C sX k).add_mem hr₁ hr₂
  rwa [show α₁' - α₁ + (α₂' - α₂) = α₁' + α₂' - (α₁ + α₂) by abel] at h

/-- The negative of a movable cycle is movable. -/
public theorem IsMovableOff.neg {α : CycleGroup C sX k} (h : IsMovableOff C sX k β α) :
    IsMovableOff C sX k β (-α) := by
  obtain ⟨α', hr, hp⟩ := h
  refine ⟨-α', ?_, fun i ↦ ?_⟩
  swap
  · have h := AlgebraicCycle.intersectProperly_zsmul_left (-1) (hp i)
    rwa [neg_one_zsmul] at h
  have h := (rationalEquivalences C sX k).neg_mem hr
  rwa [show -(α' - α) = -α' - -α by abel] at h

/-- A difference of movable cycles is movable. -/
public theorem IsMovableOff.sub {α₁ α₂ : CycleGroup C sX k} (h₁ : IsMovableOff C sX k β α₁)
    (h₂ : IsMovableOff C sX k β α₂) : IsMovableOff C sX k β (α₁ - α₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

/-- An integer multiple of a movable cycle is movable. -/
public theorem IsMovableOff.zsmul {α : CycleGroup C sX k} (n : ℤ) (h : IsMovableOff C sX k β α) :
    IsMovableOff C sX k β (n • α) := by
  obtain ⟨α', hr, hp⟩ := h
  refine ⟨n • α', ?_, fun i ↦ AlgebraicCycle.intersectProperly_zsmul_left n (hp i)⟩
  have h := (rationalEquivalences C sX k).zsmul_mem hr n
  rwa [smul_sub] at h

/-- A cycle rationally equivalent to a movable cycle is movable. -/
public theorem IsMovableOff.of_rationallyEquivalent {α₁ α₂ : CycleGroup C sX k}
    (h : IsMovableOff C sX k β α₂) (h₁₂ : RationallyEquivalent C sX k α₂ α₁) :
    IsMovableOff C sX k β α₁ := by
  obtain ⟨α', hr, hp⟩ := h
  refine ⟨α', ?_, hp⟩
  have h := (rationalEquivalences C sX k).add_mem hr h₁₂
  rwa [show α' - α₂ + (α₂ - α₁) = α' - α₁ by abel] at h

/-- A cycle which itself intersects every `β i` properly is movable. -/
public theorem IsMovableOff.of_intersectProperly {α : CycleGroup C sX k}
    (h : ∀ i, AlgebraicCycle.IntersectProperly α.1 (β i)) : IsMovableOff C sX k β α :=
  ⟨α, rationallyEquivalent_self _, h⟩

/-- The induction behind `isMovableOff_of_forall_pointCycle`, on the size of the support. -/
private theorem isMovableOff_of_forall_pointCycle_aux [CompactSpace X] (S : Set X)
    (hpt : ∀ x ∈ S, ∀ (hx : relativeDimension C.dimensionFunction sX x = k),
      IsMovableOff C sX k β (pointCycle C sX k x hx)) :
    ∀ (m : ℕ) (α : CycleGroup C sX k), Function.support (α.1 : X → ℤ) ⊆ S →
      (Function.support (α.1 : X → ℤ)).ncard ≤ m → IsMovableOff C sX k β α := by
  classical
  intro m
  induction m with
  | zero =>
    intro α _ hα
    have hfin := finite_support_of_compactSpace C sX k α
    have hempty : Function.support (α.1 : X → ℤ) = ∅ :=
      (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hα)
    have hα0 : α = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      have hx : x ∉ Function.support (α.1 : X → ℤ) := by rw [hempty]; exact Set.notMem_empty x
      simpa using hx
    rw [hα0]
    exact IsMovableOff.zero
  | succ m ih =>
    intro α hαS hα
    have hfin := finite_support_of_compactSpace C sX k α
    rcases (Function.support (α.1 : X → ℤ)).eq_empty_or_nonempty with hempty | ⟨x, hx⟩
    · exact ih α hαS (by rw [hempty, Set.ncard_empty]; exact Nat.zero_le _)
    · have hxd : relativeDimension C.dimensionFunction sX x = k :=
        (mem_cyclesOfDimension_iff_forall_point C sX k α.1).mp α.2 x hx
      set α₀ : CycleGroup C sX k := α - α.1 x • pointCycle C sX k x hxd with hα₀
      have hsupp : Function.support (α₀.1 : X → ℤ) ⊆
          Function.support (α.1 : X → ℤ) \ {x} := by
        intro y hy
        have hy' : α.1 y - α.1 x * (if y = x then 1 else 0) ≠ 0 := by
          have : α₀.1 y = α.1 y - α.1 x * (if y = x then 1 else 0) := by
            rw [hα₀]
            show α.1 y - (α.1 x • (pointCycle C sX k x hxd).1) y = _
            rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, pointCycle_apply,
              smul_eq_mul]
          rw [← this]; exact hy
        by_cases hyx : y = x
        · subst hyx; simp at hy'
        · refine ⟨?_, hyx⟩
          simpa [hyx] using hy'
      have hcard : (Function.support (α₀.1 : X → ℤ)).ncard ≤ m := by
        have h1 := Set.ncard_le_ncard hsupp (hfin.sdiff)
        have h2 : (Function.support (α.1 : X → ℤ) \ {x}).ncard =
            (Function.support (α.1 : X → ℤ)).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem hx
        have h3 : 0 < (Function.support (α.1 : X → ℤ)).ncard := (Set.ncard_pos hfin).mpr ⟨x, hx⟩
        omega
      have hdec : α = α₀ + α.1 x • pointCycle C sX k x hxd := by rw [hα₀]; abel
      rw [hdec]
      exact (ih α₀ (fun y hy ↦ hαS (hsupp hy).1) hcard).add ((hpt x (hαS hx) hxd).zsmul _)

/-- **A cycle is movable once the prime cycles of the points of its support are.** On a
quasi-compact scheme a cycle has finite support, so it is a finite integral combination of the
prime cycles of those points, and movable cycles form a subgroup. -/
public theorem isMovableOff_of_forall_pointCycle [CompactSpace X] (α : CycleGroup C sX k)
    (hpt : ∀ (x : X) (hx : relativeDimension C.dimensionFunction sX x = k), α.1 x ≠ 0 →
      IsMovableOff C sX k β (pointCycle C sX k x hx)) :
    IsMovableOff C sX k β α :=
  isMovableOff_of_forall_pointCycle_aux (Function.support (α.1 : X → ℤ))
    (fun x hxS hx ↦ hpt x hx hxS) _ α subset_rfl le_rfl

end Stacks.Chow

end
