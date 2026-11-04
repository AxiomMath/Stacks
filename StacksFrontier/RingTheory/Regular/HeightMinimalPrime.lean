module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The height of a minimal prime of a regular sequence

Let `R` be a Noetherian ring and `f₁, …, f_r` a weakly regular sequence in `R`. A prime `𝔭` minimal
over `(f₁, …, f_r)` has height exactly `r`: at most `r` by Krull's height theorem, and at least `r`
because `f₁, …, f_r` is a regular sequence in the local ring `R_𝔭`, along which the dimension drops
by one at each step.

This is the commutative algebra behind the codimension of a regular immersion (Stacks 063I and
Stacks 00KW).

## Main results

* `Ideal.height_eq_length_of_mem_minimalPrimes_ofList` — `ht 𝔭 = r`.

## References

* [Stacks Project, Tag 00KW](https://stacks.math.columbia.edu/tag/00KW)
* [Stacks Project, Tag 0BBZ](https://stacks.math.columbia.edu/tag/0BBZ)
-/

@[expose] public section

open RingTheory.Sequence Ideal

namespace Ideal

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- **A prime minimal over a weakly regular sequence of length `r` has height `r`.** -/
@[ega "IV 5.12.8" "more general", ega "IV 5.2.5" "more general"]
theorem height_eq_length_of_mem_minimalPrimes_ofList {rs : List R}
    (reg : IsWeaklyRegular R rs) {p : Ideal R} [p.IsPrime] (hp : p ∈ (ofList rs).minimalPrimes) :
    p.height = rs.length := by
  classical
  refine le_antisymm ?_ ?_
  · have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (p := p) (s := rs.toFinset)
      (by simpa using hp)
    exact h.trans (by exact_mod_cast List.toFinset_card_le rs)
  · let S := Localization.AtPrime p
    have mem : ∀ r ∈ rs, r ∈ p := fun r hr => hp.1.2 (subset_span hr)
    have reg' := reg.isRegular_of_isLocalization_of_mem S p mem
    have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ reg'
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, List.length_map] at hdim
    have hnt : Nontrivial (S ⧸ ofList (rs.map (algebraMap R S))) :=
      Ideal.Quotient.nontrivial_iff.mpr (by simpa using reg'.2.symm)
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ ofList (rs.map (algebraMap R S))) :=
      ringKrullDim_nonneg_of_nontrivial
    have : ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) := by
      rw [← hdim]
      exact le_add_of_nonneg_left h0
    exact_mod_cast this

end Ideal

end
