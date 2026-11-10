module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.Topology.Dimension.CatenaryAdditive

/-!
# The vanishing locus of the distance from a closed subset

For a closed subset `Z` of a Noetherian scheme `Y`, a point has distance zero from `Z`
exactly when it belongs to `Z`. Consequently the distance vanishes at every point whose
closure is contained in `Z`.

## Main results

* `Stacks.Algebraization.distanceFunction_eq_zero_iff_mem` characterizes the zero locus of
  the distance function.
* `Stacks.Algebraization.distanceFunction_eq_zero_of_closure_subset` is the special case of a
  closed subset containing the closure of the point.

## Implementation notes

Distance is infinite when the connected component of the point does not meet the closed
subset, so the forward implication splits on whether the component meets `Z`.
The second result is stated for any Noetherian scheme and closed subset, rather than only
for a closed subvariety of affine space: the argument uses only closedness.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
* [Stacks Project, Tag 0EJ1](https://stacks.math.columbia.edu/tag/0EJ1)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- A system from `Z` to a point outside `Z` has weight at least one: either it has a
descending leg, or its single ascending leg is strict. -/
private lemma positive_weight_of_not_mem (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) (hy : y ∉ (Z : Set Y))
    (s : DistanceSystem Y Z y) : 1 ≤ s.weight := by
  cases hk : s.k with
  | zero =>
      let i : Fin (s.k + 1) := ⟨0, by simp [hk]⟩
      have hyW : y ∈ (s.W i : Set Y) := by
        have hi : i = Fin.last s.k := Fin.ext (by simp [i, hk])
        rw [hi, s.W_last_eq_closure]
        exact subset_closure rfl
      have hne : s.V i ≠ s.W i := by
        intro heq
        apply hy
        apply s.V_zero_subset
        change y ∈ (s.V i : Set Y)
        rwa [heq]
      have hcod : 0 < s.upCodimension i :=
        s.upCodimension_pos_of_lt i (lt_of_le_of_ne (s.V_le_W i) hne)
      let f := fun b : Fin (s.k + 1) =>
          (∑ j : Fin (s.k + 1), if b.val ≤ j.val then s.upCodimension j else 0) -
          (∑ j : Fin s.k, if b.val ≤ j.val then s.downCodimension j else 0)
      have : IsEmpty (Fin s.k) := by rw [hk]; infer_instance
      have hweight : 1 ≤ (Finset.univ : Finset (Fin (s.k + 1))).sup f :=
        le_trans (Nat.succ_le_iff.mpr hcod)
          (Finset.le_sup_of_le (s := (Finset.univ : Finset (Fin (s.k + 1))))
            (f := f) (b := i) (by simp) (by simp [f, i, Fin.sum_univ_succ]))
      simpa [DistanceSystem.weight, hk, f] using hweight
  | succ k =>
      unfold DistanceSystem.weight
      exact le_trans (by omega : 1 ≤ s.k) (Nat.le_add_right _ _)

/-- **Stacks Project, Tag 0EIY.** A point has distance zero from a closed subset precisely
when it lies in that subset. -/
@[stacks 0EIY "zero_iff_mem"]
public theorem distanceFunction_eq_zero_iff_mem (Y : Scheme.{u}) [IsNoetherian Y]
    (Z : Closeds Y) (y : Y) :
    distanceFunction Y Z y = 0 ↔ y ∈ (Z : Set Y) := by
  classical
  constructor
  · intro hzero
    by_contra hy
    by_cases hmeet : (connectedComponent y ∩ (Z : Set Y)).Nonempty
    · rw [distanceFunction_eq_iInf_of_nonempty Y Z y hmeet] at hzero
      have hbound : (1 : ℕ∞) ≤ ⨅ s : DistanceSystem Y Z y, (s.weight : ℕ∞) :=
        le_iInf fun s => by exact_mod_cast positive_weight_of_not_mem Y Z y hy s
      norm_num [hzero] at hbound
    · rw [distanceFunction_eq_top_of_disjoint Y Z y hmeet] at hzero
      norm_num at hzero
  · intro hy
    let C : IrreducibleCloseds Y := IrreducibleCloseds.closureSingleton y
    let s : DistanceSystem Y Z y := {
      k := 0
      V := fun _ => C
      W := fun _ => C
      V_le_W := fun _ => le_rfl
      V_next_le_W := fun i => i.elim0
      V_zero_subset := closure_minimal (Set.singleton_subset_iff.mpr hy) Z.isClosed
      W_last_eq_closure := rfl
    }
    rw [distanceFunction_eq_iInf_of_nonempty Y Z y ⟨y, mem_connectedComponent, hy⟩]
    apply le_antisymm (le_trans (iInf_le _ s) ?_) bot_le
    simp [s, DistanceSystem.weight, DistanceSystem.upCodimension, topCodim_self_eq_zero]

/-- **Stacks Project, Tag 0EJ1.** The distance to a closed subset containing the closure of a
point is zero. -/
@[stacks 0EJ1 "subvariety_contains_w"]
public theorem distanceFunction_eq_zero_of_closure_subset
    (Y : Scheme.{u}) [IsNoetherian Y] (Z : Closeds Y) (y : Y)
    (h : closure ({y} : Set Y) ⊆ (Z : Set Y)) :
    distanceFunction Y Z y = 0 :=
  (distanceFunction_eq_zero_iff_mem Y Z y).2 (h (subset_closure (Set.mem_singleton y)))

end Stacks.Algebraization
