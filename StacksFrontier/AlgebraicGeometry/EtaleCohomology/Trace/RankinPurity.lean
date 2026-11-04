module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PositiveExponentialSums

/-!
# Purity at a closed point from Rankin's bound and a determinantal weight

This is how Weil II 1.5.1 ends at one closed point `y` of degree `d`. Let `f` be the geometric
Frobenius at `y` acting on the stalk of an `ι`-real lisse sheaf `E`. Suppose that for every
`i ≥ 1` the trace formula for `E^{⊗ 2i}` in degree `d n` dominates the contribution of `y`
(Lemme 1.5.2, `Stacks.EtaleCohomology.norm_le_of_forall_rankin`), and that `y` has the
determinantal weight `w`, i.e. `‖ι det f‖ = q ^ (d w / 2 · dim E)`. Then `E` is pure of weight `w`
at `y`: every Frobenius eigenvalue has absolute value `q ^ (d w / 2)`. Rankin gives the upper
bound, and the determinant forces equality
(`Stacks.EtaleCohomology.norm_eq_of_forall_norm_le_of_norm_det_eq`).

## Main results

* `Stacks.EtaleCohomology.norm_eq_of_forall_rankin_of_norm_det_eq` — the purity statement.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.5.1, 1.5.2.
-/

@[expose] public noncomputable section

open Filter Topology

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Purity at a closed point** (end of Weil II 1.5.1). Let `f` be an endomorphism of a
finite-dimensional `K`-space with eigenvalues `α` (the roots of `charpoly f` mapped by `ι`).
If for every `i ≥ 1` there are finite families `A i`, `B i` (the Frobenius eigenvalues on
`H²_c` and `H¹_c` of `E^{⊗ 2i}`), the elements of `A i` of absolute value at most
`q ^ (1 + i w)`, whose power sums in degree `d n` dominate `d · (∑ α ^ n) ^ (2 i)` for large `n`,
and if `‖ι det f‖ = (q ^ (d w / 2)) ^ dim V`, then every eigenvalue has absolute value
`q ^ (d w / 2)`. -/
theorem norm_eq_of_forall_rankin_of_norm_det_eq [FiniteDimensional K V] (ι : K →+* ℂ)
    (f : Module.End K V) {d : ℕ} (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q) {w : ℝ}
    (A B : ℕ → Multiset ℂ) (hA : ∀ i, ∀ a ∈ A i, ‖a‖ ≤ q ^ (1 + i * w))
    (h : ∀ i, 0 < i → ∀ᶠ n : ℕ in atTop,
      (d : ℝ) * ((((f.charpoly.map ι).roots.map (· ^ n)).sum) ^ (2 * i)).re ≤
        (((A i).map (· ^ (d * n))).sum - ((B i).map (· ^ (d * n))).sum).re)
    (hdet : ‖ι (LinearMap.det f)‖ = (q ^ (d * w / 2)) ^ Module.finrank K V) :
    ∀ z ∈ (f.charpoly.map ι).roots, ‖z‖ = q ^ (d * w / 2) := by
  classical
  set s := (f.charpoly.map ι).roots
  have hsum : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ x : s, (x : ℂ) ^ n := fun n => by
    rw [Finset.sum_eq_multiset_sum]
    exact (congrArg Multiset.sum (Multiset.map_univ s (· ^ n))).symm
  have hle : ∀ z ∈ s, ‖z‖ ≤ q ^ (d * w / 2) := by
    intro z hz
    have hc : 0 < s.count z := Multiset.count_pos.mpr hz
    have := norm_le_of_forall_rankin (α := fun x : s => (x : ℂ)) hd hq A B hA (fun i hi => by
      filter_upwards [h i hi] with n hn
      simpa only [hsum] using hn) (s.mkToType z ⟨0, hc⟩)
    simpa [Multiset.coe_mk] using this
  exact norm_eq_of_forall_norm_le_of_norm_det_eq ι f hle hdet

end Stacks.EtaleCohomology
