module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import Mathlib
public import Mathlib.Data.Rat.Cast.Order

/-!
# The genus of a numerical type

The genus of a numerical type is the integer

`1 + ∑ mᵢ wᵢ (gᵢ - 1) - (∑ mᵢ aᵢᵢ) / 2`,

the division being exact because the diagonal sum is even.

## Main definitions

* `AlgebraicGeometry.NumericalType.genus`: the genus of a numerical type, as an integer.

## Main results

* `AlgebraicGeometry.NumericalType.cast_genus`: the rational expression
  defining the genus is the image of that integer. The summand
  `mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)` is the *contribution* of the `i`-th component.

## References

* [Stacks Project, Tag 0C71](https://stacks.math.columbia.edu/tag/0C71)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

private lemma sum_symmetric_zmod_two {ι : Type*}
    (s : Finset ι) (f : ι → ι → ZMod 2)
    (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = ∑ i ∈ s, f i i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
    rw [← ih, Finset.sum_congr rfl (fun i _ => hf i a)]
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination (∑ i ∈ s, f a i) * htwo

private lemma zmod_two_mul_self (x : ZMod 2) : x * x = x := by revert x; decide

private lemma diagonal_sum_dvd_two (T : NumericalType) :
    (2 : ℤ) ∣ ∑ i, T.multiplicity i * T.intersection i i := by
  let f : Fin T.componentCount → Fin T.componentCount → ZMod 2 :=
    fun i j => (T.intersection i j : ZMod 2) * T.multiplicity i * T.multiplicity j
  have hf : ∀ i j, f i j = f j i := fun i j => by
    simp only [f, T.intersection_symm i j]
    ring
  have hr (i : Fin T.componentCount) :
      ∑ j, (T.intersection i j : ZMod 2) * T.multiplicity j = 0 := by
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using
      congrArg (fun x : ℤ => (x : ZMod 2)) (T.intersection_mul_multiplicity i)
  have htotal : ∑ i, ∑ j, f i j = 0 := calc
    _ = ∑ i, (T.multiplicity i : ZMod 2) *
        (∑ j, (T.intersection i j : ZMod 2) * T.multiplicity j) := by
      simp only [f, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by simp [hr]
  have hdiag :
      ∑ i, (T.multiplicity i : ZMod 2) * (T.intersection i i : ZMod 2) = 0 := calc
    _ = ∑ i, f i i := Finset.sum_congr rfl fun i _ => by
      simp only [f, mul_assoc, zmod_two_mul_self]
      ring
    _ = 0 := (sum_symmetric_zmod_two _ _ hf).symm.trans htotal
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    (by simpa only [Int.cast_sum, Int.cast_mul] using hdiag)

/-- The integer genus of a numerical type. -/
@[stacks 0C72 "a numerical type of genus g"]
public def genus (T : NumericalType) : ℤ :=
  1 + (∑ i, T.multiplicity i * (T.weight i * (T.componentGenus i - 1))) -
    (∑ i, T.multiplicity i * T.intersection i i) / 2

/-- The rational expression defining the genus of a numerical type is the image of
an integer. -/
@[stacks 0C71]
public lemma cast_genus (T : NumericalType) :
    (genus T : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := by
  have hcast :
      (((∑ i, T.multiplicity i * T.intersection i i) / 2 : ℤ) : ℚ) =
        (∑ i, T.multiplicity i * T.intersection i i : ℤ) / 2 :=
    Int.cast_div (diagonal_sum_dvd_two T) (by norm_num)
  rw [genus]
  push_cast [hcast]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_div, mul_div_assoc]
  ring

end AlgebraicGeometry.NumericalType
