module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.E7
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.QuadraticForm

/-!
# Nonexistence of a completed E7 subgraph

A numerical type with more than eight components cannot contain eight distinct
minus-two indices forming a chain of seven vertices with an additional vertex
joined to the fourth vertex — that is, the affine Dynkin diagram `Ẽ₇`.

Applying the `E₇` classification to the two seven-vertex subdiagrams obtained by
deleting one or the other end of the chain shows that all eight weights agree
and pins down every intersection number except the one `a` joining the two ends.
On the standard positive `Ẽ₇` coefficient vector `(1, 2, 3, 4, 3, 2, 1; 2)` the
intersection form then evaluates to `2a ≥ 0`, while it is negative semidefinite;
so the form vanishes there, forcing the vector to be a multiple of the
multiplicity vector, hence nowhere zero, hence the eight indices exhaust the
components. That contradicts having more than eight of them.

## Main results

* `AlgebraicGeometry.NumericalType.not_exists_branched_chain_of_eight_minus_two_indices`:
  the indicated eight-vertex subgraph does not occur.

## Implementation notes

The eight named indices of the source are represented, in their displayed
order, by an injective map from `Fin 8`: `i 0, …, i 6` is the chain and `i 7`
the extra vertex joined to `i 3`. The seven required nonzero intersection
numbers are stated explicitly; no condition is imposed on the others.

## References

* [Stacks Project, Tag 0C8N](https://stacks.math.columbia.edu/tag/0C8N)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- **Stacks Project, Tag 0C8N.** If a numerical type has more than eight
components, it has no eight distinct minus-two indices forming a seven-vertex
chain with an extra vertex joined to the fourth vertex. -/
@[stacks 0C8N]
public lemma not_exists_branched_chain_of_eight_minus_two_indices
    (T : NumericalType) (hcount : 8 < T.componentCount) :
    ¬ ∃ i : Fin 8 → Fin T.componentCount,
      Function.Injective i ∧
      (∀ r, IsMinusTwoIndex T (i r)) ∧
      T.intersection (i 0) (i 1) ≠ 0 ∧
      T.intersection (i 1) (i 2) ≠ 0 ∧
      T.intersection (i 2) (i 3) ≠ 0 ∧
      T.intersection (i 3) (i 4) ≠ 0 ∧
      T.intersection (i 4) (i 5) ≠ 0 ∧
      T.intersection (i 5) (i 6) ≠ 0 ∧
      T.intersection (i 7) (i 3) ≠ 0 := by
  rintro ⟨i, hi, hminus, h01, h12, h23, h34, h45, h56, h73⟩
  let c : Fin 8 → ℤ := ![1, 2, 3, 4, 3, 2, 1, 2]
  have hquad : ∑ r, ∑ s, c r * T.intersection (i r) (i s) * c s =
      2 * T.intersection (i 0) (i 6) := by
    show ∑ r, ∑ s, (![1, 2, 3, 4, 3, 2, 1, 2] : Fin 8 → ℤ) r * T.intersection (i r) (i s) *
      (![1, 2, 3, 4, 3, 2, 1, 2] : Fin 8 → ℤ) s = 2 * T.intersection (i 0) (i 6)
    have hn : 7 < T.componentCount := by omega
    have key (v : Fin 7 → Fin 8) (hv : Function.Injective v)
        (hE : T.intersection (i (v 0)) (i (v 1)) ≠ 0 ∧ T.intersection (i (v 1)) (i (v 2)) ≠ 0 ∧
          T.intersection (i (v 2)) (i (v 3)) ≠ 0 ∧ T.intersection (i (v 3)) (i (v 4)) ≠ 0 ∧
          T.intersection (i (v 4)) (i (v 5)) ≠ 0 ∧ T.intersection (i (v 3)) (i (v 6)) ≠ 0) :=
      let e : Fin 7 ↪ Fin T.componentCount := ⟨i ∘ v, hi.comp hv⟩
      And.intro (e7_subgraph_classification T hn e (fun _ => hminus _) hE)
        (e7_subgraph_weight_eq T hn e (fun _ => hminus _) hE)
    have hE := key ![0, 1, 2, 3, 4, 5, 7] (by decide)
      ⟨h01, h12, h23, h34, h45, by rwa [T.intersection_symm]⟩
    have hF := key ![6, 5, 4, 3, 2, 1, 7] (by decide) (by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [T.intersection_symm]
      exacts [h56, h45, h34, h23, h12, h73])
    have hw : T.weight (i 6) = T.weight (i 0) :=
      (congrFun hF.2 6).symm.trans (congrFun hE.2 6)
    have h₁ (p q) := congrFun (congrFun hE.1 p) q
    have h₂ (p q) := congrFun (congrFun hF.1 p) q
    simp [Fin.forall_fin_succ] at h₁ h₂
    simp only [hw] at h₂
    simp [Fin.sum_univ_eight, h₁, h₂, T.intersection_symm (i 6) (i 0)]
    ring
  have hnonpos : ∑ r, ∑ s, c r * T.intersection (i r) (i s) * c s ≤ 0 := by
    have hQ := T.intersection_quadratic_nonpos (∑ r, (c r : ℚ) • Pi.single (i r) (1 : ℚ))
    rw [Matrix.dotProduct_mulVec_sum_single (ratIntersection T) i fun r => (c r : ℚ)] at hQ
    have hcast : ((∑ r, ∑ s, c r * T.intersection (i r) (i s) * c s : ℤ) : ℚ) ≤ 0 := by
      push_cast
      simpa [ratIntersection] using hQ
    exact_mod_cast hcast
  have ha : 0 ≤ T.intersection (i 0) (i 6) :=
    T.intersection_nonneg _ _ fun h => absurd (hi h) (by decide)
  have hzero := le_antisymm hnonpos (by omega)
  exact no_positive_supported_kernel T 8 ⟨i, hi⟩ hcount (by omega) c
    (by intro r; fin_cases r <;> norm_num [c]) hzero

end AlgebraicGeometry.NumericalType
