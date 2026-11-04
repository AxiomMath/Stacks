module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Simultaneously avoiding finitely many prime ideals

Given a residue class modulo an ideal which is not contained in any member of a finite family of
prime ideals, one can choose a representative of that class lying outside every prime in the
family.

## Main results

* `Ideal.exists_lift_avoiding_primes`: a representative of a residue class avoiding a given
  finite family of prime ideals.

## References

* [Stacks Project, Tag 09NK](https://stacks.math.columbia.edu/tag/09NK)
-/

@[expose] public section

universe u

namespace Ideal

/-- If an ideal is contained in none of a finite family of prime ideals, every
class modulo that ideal has a representative outside all of the primes. -/
@[stacks 09NK]
public theorem exists_lift_avoiding_primes
    {A : Type u} [CommRing A] (I : Ideal A) {r : ℕ} (p : Fin r → Ideal A)
    (hp : ∀ i, (p i).IsPrime) (hI : ∀ i, ¬ I ≤ p i) (fbar : A ⧸ I) :
    ∃ f : A, (∀ i, f ∉ p i) ∧ Ideal.Quotient.mk I f = fbar := by
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective fbar
  classical
  let M := Finset.univ.filter (fun i : Fin r => MaximalFor (fun _ => True) p i)
  have hmax : ∀ i : Fin r, ∃ j ∈ M, p i ≤ p j := by
    intro i
    obtain ⟨j, hij, hj⟩ :=
      Finset.exists_le_maximal (s := Finset.univ.image p) (a := p i) (by simp)
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj.1
    refine ⟨k, ?_, hij⟩
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨trivial, fun l _ hkl => hj.2 (by simp) hkl⟩
  let S : Finset (Fin r) := M.filter (fun i => f ∈ p i)
  let T : Finset (Fin r) := M.filter (fun i => f ∉ p i)
  let J : Ideal A := I * T.prod p
  have hJ : ∀ i ∈ S, ¬ J ≤ p i := by
    intro i hi hle
    rcases (Ideal.IsPrime.mul_le (hp i)).mp hle with hIle | hprod
    · exact (hI i) hIle
    · rcases (Ideal.IsPrime.prod_le (hp i)).mp hprod with ⟨j, hj, hjle⟩
      have hmaxj : MaximalFor (fun _ : Fin r => True) p j := by
        simpa [M] using (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      exact (Finset.mem_filter.mp hj).2 (hmaxj.2 trivial hjle (Finset.mem_filter.mp hi).2)
  have hnot : ¬ (J : Set A) ⊆ ⋃ q ∈ (S.image p : Set (Ideal A)), (q : Set A) := by
    intro hsub
    obtain ⟨q, hq, hqJ⟩ := (Ideal.subset_union_prime_finite
      ((S.image p).finite_toSet) (⊥ : Ideal A) ⊥ (fun q hq _ _ =>
        Finset.forall_mem_image.mpr (fun i _ => hp i) q hq)).mp hsub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact hJ i hi hqJ
  obtain ⟨g, hgJ, hg⟩ := Set.not_subset.mp hnot
  have hgS : ∀ i ∈ S, g ∉ p i := fun i hi hgi =>
    hg (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_image_of_mem p hi)) hgi)
  refine ⟨f + g, ?_, ?_⟩
  · intro i hfi
    obtain ⟨j, hj, hij⟩ := hmax i
    by_cases hjf : f ∈ p j
    · exact (hgS j (Finset.mem_filter.mpr ⟨hj, hjf⟩))
        ((Submodule.add_mem_iff_right _ hjf).mp (hij hfi))
    · have hgt : g ∈ p j := ((Ideal.IsPrime.prod_le (hp j)).mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, hjf⟩, le_rfl⟩) (Ideal.mul_le_right hgJ)
      exact hjf ((Submodule.add_mem_iff_left _ hgt).mp (hij hfi))
  · rw [map_add, add_eq_left, Ideal.Quotient.eq_zero_iff_mem]
    exact (show J ≤ I from Ideal.mul_le_left) hgJ

end Ideal

end
