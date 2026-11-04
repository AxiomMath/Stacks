module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Simultaneous transcendence in residue fields

For finitely many incomparable prime ideals, an ideal avoiding every prime contains an element
whose image in each residue field is transcendental over a prescribed subfield, provided none of
the residue field extensions is algebraic.

## Main results

* `Ideal.exists_mem_ideal_transcendental_residue`: an ideal avoiding finitely many incomparable
  prime ideals contains an element whose image in each residue field is transcendental over a
  prescribed subfield, provided none of the residue field extensions is algebraic.

## References

* [Stacks Project, Tag 0GTE](https://stacks.math.columbia.edu/tag/0GTE)
-/

@[expose] public section

namespace Ideal

/-- An ideal avoiding finitely many incomparable prime ideals contains an element whose image is
transcendental over each of the prescribed subfields of the residue fields. -/
@[stacks 0GTE]
theorem exists_mem_ideal_transcendental_residue
    (R : Type*) [CommRing R] (ι : Type*) [Finite ι]
    (p : ι → PrimeSpectrum R)
    (k : ∀ i, Subfield (p i).asIdeal.ResidueField)
    (hinc : ∀ i j, i ≠ j → ¬ (p i).asIdeal ≤ (p j).asIdeal)
    (htrans : ∀ i, ¬ Algebra.IsAlgebraic (k i) (p i).asIdeal.ResidueField)
    (J : Ideal R) (hJ : ∀ i, ¬ J ≤ (p i).asIdeal) :
    ∃ x ∈ J, ∀ i, Transcendental (k i)
      (algebraMap R (p i).asIdeal.ResidueField x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hchoice : ∀ i, ∃ x ∈ J,
      Transcendental (k i) (algebraMap R (p i).asIdeal.ResidueField x) ∧
      ∀ j, j ≠ i → x ∈ (p j).asIdeal := by
    intro i
    let s := Finset.univ.erase i
    let L : Ideal R := J * ∏ j ∈ s, (p j).asIdeal
    have hp : (p i).asIdeal.IsPrime := inferInstance
    have hprodnot : ¬ (∏ j ∈ s, (p j).asIdeal) ≤ (p i).asIdeal := by
      intro hprod
      rcases (hp.prod_le).mp hprod with ⟨j, hj, hjp⟩
      exact hinc j i (Finset.mem_erase.mp hj).1 hjp
    have hLnot : ¬ L ≤ (p i).asIdeal := fun hL => (hp.mul_le.mp hL).elim (hJ i) hprodnot
    obtain ⟨c, hcL, hcp⟩ := SetLike.not_le_iff_exists.mp hLnot
    have hcJ : c ∈ J := Ideal.mul_le_left hcL
    obtain ⟨m, hmIdeal, hmnot⟩ := SetLike.not_le_iff_exists.mp hprodnot
    obtain ⟨ξ, hξ⟩ : ∃ ξ : (p i).asIdeal.ResidueField, ¬ IsAlgebraic (k i) ξ :=
      not_forall.mp fun hall => htrans i ⟨hall⟩
    let A := R ⧸ (p i).asIdeal
    let K := (p i).asIdeal.ResidueField
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective A ξ
    obtain ⟨u₀, hu₀⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v₀, hv₀⟩ := Ideal.Quotient.mk_surjective v
    let U : K := algebraMap A K (Ideal.Quotient.mk _ u₀)
    let V : K := algebraMap A K (Ideal.Quotient.mk _ v₀)
    let C : K := algebraMap R K c
    let M : K := algebraMap R K m
    have hUmap : U = algebraMap R K u₀ := Ideal.algebraMap_quotient_residueField_mk _ u₀
    have hVmap : V = algebraMap R K v₀ := Ideal.algebraMap_quotient_residueField_mk _ v₀
    have hfrac : U / V = ξ := by
      simpa [U, V, hu₀, hv₀] using huv
    have hC : C ≠ 0 := fun h => hcp (Ideal.algebraMap_residueField_eq_zero.mp h)
    have hM : M ≠ 0 := fun h => hmnot (Ideal.algebraMap_residueField_eq_zero.mp h)
    have hmj : ∀ j, j ≠ i → m ∈ (p j).asIdeal := fun j hji =>
      (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩))) hmIdeal
    have hwJ : ∀ w : R, c * w * m ∈ J := fun w => J.mul_mem_right _ (J.mul_mem_right _ hcJ)
    have hwP : ∀ w : R, ∀ j, j ≠ i → c * w * m ∈ (p j).asIdeal := fun w j hji =>
      (p j).asIdeal.mul_mem_left _ (hmj j hji)
    have hwmap : ∀ w : R, algebraMap R K (c * w * m) = C * algebraMap R K w * M := by
      simp [C, M]
    have hab : algebraMap R K (c * u₀ * m) / algebraMap R K (c * v₀ * m) = ξ := by
      rw [hwmap, hwmap, ← hUmap, ← hVmap, mul_div_mul_right _ _ hM, mul_div_mul_left _ _ hC, hfrac]
    by_cases haT : Transcendental (k i) (algebraMap R K (c * u₀ * m))
    · exact ⟨_, hwJ u₀, haT, hwP u₀⟩
    · refine ⟨c * v₀ * m, hwJ v₀, fun hb => hξ ?_, hwP v₀⟩
      rw [← hab, div_eq_mul_inv]
      exact (not_not.mp haT).mul hb.inv
  choose x hxJ hxT hxP using hchoice
  refine ⟨∑ i, x i, Submodule.sum_mem J fun i _ => hxJ i, fun i => ?_⟩
  rw [map_sum, Finset.sum_eq_single i
    (fun j _ hji => Ideal.algebraMap_residueField_eq_zero.mpr (hxP j i (Ne.symm hji))) (by simp)]
  exact hxT i

end Ideal

end
