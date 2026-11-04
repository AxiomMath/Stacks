module

public import StacksFrontier.Algebra.Polynomial.PowerProductMultiset

/-!
# Frobenius roots from power sums, and duality with complex conjugation

Two facts of linear algebra over `ℂ` behind the duality step of Laumon's purity of the Fourier
family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4):

* the nonzero elements of a finite multiset of complex numbers are determined by its power sums
  `∑ wᴺ`, `N ≥ 1` (`Stacks.EtaleCohomology.mem_of_forall_sum_map_pow_eq`): this turns a trace
  formula into an identity of Frobenius roots;
* if `z ↦ q / z` sends the roots of `P` to roots of `Q` (Poincaré duality) and `w ↦ q ^ β · w̄`
  sends the nonzero roots of `Q` to roots of `P` (the trace formula and the purity of the
  coefficients), then `z ↦ q ^ (β + 1) / z̄` permutes the roots of `P`
  (`Stacks.EtaleCohomology.isRoot_zpow_div_conj_of_dual`).

## Main results

* `Stacks.EtaleCohomology.mem_of_forall_sum_map_pow_eq`.
* `Stacks.EtaleCohomology.mem_of_forall_sum_map_pow_eq_conj`.
* `Stacks.EtaleCohomology.isRoot_zpow_div_conj_of_dual`.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

/-- A power sum over a submultiset of `A + B` is the sum over `(A + B).toFinset` weighted by
multiplicities. -/
theorem sum_map_pow_eq_sum_count {A B C : Multiset ℂ} (hC : C ≤ A + B) (N : ℕ) :
    (C.map (· ^ N)).sum = ∑ z ∈ (A + B).toFinset, (C.count z : ℂ) * z ^ N := by
  classical
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_subset (Multiset.toFinset_subset.2 (Multiset.subset_of_le hC))
    (fun z _ hz => ?_) |>.trans (Finset.sum_congr rfl fun z _ => by rw [nsmul_eq_mul])
  rw [Multiset.count_eq_zero.2 (fun h => hz (Multiset.mem_toFinset.2 h)), zero_nsmul]

/-- **Power sums determine the nonzero elements**: if two finite multisets of complex numbers have
the same power sums `∑ wᴺ` for all `N ≥ 1`, every nonzero element of one belongs to the other. -/
public theorem mem_of_forall_sum_map_pow_eq {A B : Multiset ℂ}
    (h : ∀ N : ℕ, 0 < N → (B.map (· ^ N)).sum = (A.map (· ^ N)).sum) {w : ℂ} (hw : w ∈ B)
    (hw0 : w ≠ 0) : w ∈ A := by
  classical
  have hc := Stacks.PowerProduct.coeff_eq_of_sum_pow_eq (A + B).toFinset
    (fun z => (B.count z : ℂ)) (fun z => (A.count z : ℂ))
    (fun N hN => by
      rw [← sum_map_pow_eq_sum_count (Multiset.le_add_left B A),
        ← sum_map_pow_eq_sum_count (Multiset.le_add_right A B)]
      exact h N hN)
    w (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inr hw))) hw0
  have hA : A.count w = B.count w := by exact_mod_cast hc.symm
  exact Multiset.count_pos.1 (hA ▸ Multiset.count_pos.2 hw)

/-- **Power sums twisted by complex conjugation**: if `∑_{w ∈ B} wᴺ = ∑_{z ∈ A} (c · z̄)ᴺ` for all
`N ≥ 1`, every nonzero `w ∈ B` is `c · z̄` for some `z ∈ A`. -/
public theorem mem_of_forall_sum_map_pow_eq_conj {A B : Multiset ℂ} {c : ℂ}
    (h : ∀ N : ℕ, 0 < N →
      (B.map (· ^ N)).sum = (A.map fun z => (c * starRingEnd ℂ z) ^ N).sum)
    {w : ℂ} (hw : w ∈ B) (hw0 : w ≠ 0) : ∃ z ∈ A, w = c * starRingEnd ℂ z := by
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 <|
    mem_of_forall_sum_map_pow_eq (A := A.map fun z => c * starRingEnd ℂ z)
      (fun N hN => by rw [h N hN, Multiset.map_map]; rfl) hw hw0
  exact ⟨z, hz, rfl⟩

/-- **Duality and conjugation give the symmetry `z ↦ q ^ (β + 1) / z̄`**: if for every root `z` of
`P` we have `z ≠ 0` and `q / z` is a root of `Q`, and for every nonzero root `w` of `Q` the number
`q ^ β · w̄` is a root of `P`, then for every root `z` of `P`, `z ≠ 0` and `q ^ (β + 1) / z̄` is a
root of `P`. -/
public theorem isRoot_zpow_div_conj_of_dual {P Q : Polynomial ℂ} {q : ℕ} (hq : q ≠ 0) {β : ℤ}
    (hPD : ∀ z : ℂ, P.IsRoot z → z ≠ 0 ∧ Q.IsRoot ((q : ℂ) / z))
    (hconj : ∀ w : ℂ, w ≠ 0 → Q.IsRoot w → P.IsRoot ((q : ℂ) ^ β * starRingEnd ℂ w))
    (z : ℂ) (hz : P.IsRoot z) : z ≠ 0 ∧ P.IsRoot ((q : ℂ) ^ (β + 1) / starRingEnd ℂ z) := by
  obtain ⟨hz0, hQ⟩ := hPD z hz
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  refine ⟨hz0, ?_⟩
  have h := hconj _ (div_ne_zero hq0 hz0) hQ
  rwa [map_div₀, map_natCast, ← mul_div_assoc, ← zpow_add_one₀ hq0] at h

end Stacks.EtaleCohomology

end
