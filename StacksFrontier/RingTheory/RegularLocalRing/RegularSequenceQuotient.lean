module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.RegularLocalRing.RegularParameterFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cutting a Noetherian local ring by a regular sequence in its maximal ideal

Let `(R, m)` be a Noetherian local ring and let `f₁, …, f_k` be a weakly regular sequence all of
whose entries lie in `m`. Weak regularity already implies regularity here, because the ideal
`(f₁, …, f_k)` is contained in the Jacobson radical and so cannot be the unit ideal. Two
consequences are recorded, together with the package of both that a caller usually wants.

First, the Krull dimension drops by exactly the length of the sequence,
`dim R/(f₁, …, f_k) + k = dim R`. Second, Stacks 00NU in its iterated form: if the quotient
`R/(f₁, …, f_k)` is a regular local ring, then so is `R`.

Combining these with the factorization of a regular parameter system shows that such a sequence is
an initial segment of a regular system of parameters of `R`: there is a list `rs` generating `m`,
which is a system of parameters, whose first `k` entries are exactly `f₁, …, f_k`.

## Main results

* `ringKrullDim_quotient_ofList_add_length_eq`: the dimension of the quotient by a regular
  sequence in the maximal ideal, plus the length of the sequence, is the dimension of the ring.
* `isRegularLocalRing_of_isRegularLocalRing_quotient_ofList`: **Stacks 00NU**, iterated — a
  Noetherian local ring with a regular sequence in its maximal ideal cutting out a regular local
  ring is itself a regular local ring.
* `exists_isSystemOfParameters_append_of_isRegular_quotient`: in that situation the sequence is
  the initial segment of a regular system of parameters of `R`.

## Implementation notes

The hypothesis taken on the sequence is `RingTheory.Sequence.IsWeaklyRegular`, which is weaker
than `RingTheory.Sequence.IsRegular`; together with the assumption that every entry lies in the
maximal ideal the two coincide, by
`RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`. A caller holding the
stronger hypothesis passes `.toIsWeaklyRegular`.

A sequence is a `List`, as in `IsLocalRing.IsSystemOfParameters`, and the ideal it generates is
`Ideal.ofList`. A *regular system of parameters* is the conjunction
`IsLocalRing.IsSystemOfParameters rs ∧ Ideal.ofList rs = IsLocalRing.maximalIdeal R`, so both
conjuncts are carried explicitly.

## References

* [Stacks Project, Tag 00NU](https://stacks.math.columbia.edu/tag/00NU)
-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {fs : List R}

/-- **The dimension drop along a regular sequence.** If `f₁, …, f_k` is a weakly regular sequence
in the maximal ideal of a Noetherian local ring `R`, then
`dim R/(f₁, …, f_k) + k = dim R`. -/
theorem ringKrullDim_quotient_ofList_add_length_eq
    (hm : ∀ f ∈ fs, f ∈ maximalIdeal R) (hreg : IsWeaklyRegular R fs) :
    ringKrullDim (R ⧸ Ideal.ofList fs) + fs.length = ringKrullDim R :=
  ringKrullDim_add_length_eq_ringKrullDim_of_isRegular fs
    (IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R hm hreg)

/-- **Stacks 00NU, iterated.** Let `R` be a Noetherian local ring and `f₁, …, f_k` a weakly
regular sequence contained in the maximal ideal of `R`. If `R/(f₁, …, f_k)` is a regular local
ring, then so is `R`. -/
theorem isRegularLocalRing_of_isRegularLocalRing_quotient_ofList
    (hm : ∀ f ∈ fs, f ∈ maximalIdeal R) (hreg : IsWeaklyRegular R fs)
    (h : IsRegularLocalRing (R ⧸ Ideal.ofList fs)) : IsRegularLocalRing R :=
  isRegularLocalRing_of_isRegular R fs
    (IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R hm hreg) h

/-- **A regular sequence cutting out a regular local ring is an initial segment of a regular system
of parameters.** Let `R` be a Noetherian local ring and `f₁, …, f_k` a weakly regular sequence
contained in the maximal ideal of `R` such that `R/(f₁, …, f_k)` is a regular local ring. Then `R`
is a regular local ring, and there is a system of parameters `rs` of `R` generating the maximal
ideal whose first `k` entries are `f₁, …, f_k`. -/
@[ega "0 17.1.7" "partial",
  ega "0 17.1.9" "(a) ⇒ (b)",
  ega "IV 16.9.12" "sufficiency",
  sga "2 IV 5.3" "partial"]
theorem exists_isSystemOfParameters_append_of_isRegular_quotient
    (hm : ∀ f ∈ fs, f ∈ maximalIdeal R) (hreg : IsWeaklyRegular R fs)
    (h : IsRegularLocalRing (R ⧸ Ideal.ofList fs)) :
    IsRegularLocalRing R ∧
      ∃ rs : List R, IsLocalRing.IsSystemOfParameters rs ∧
        Ideal.ofList rs = IsLocalRing.maximalIdeal R ∧
        fs.length ≤ rs.length ∧ rs.take fs.length = fs := by
  have hR : IsRegularLocalRing R :=
    isRegularLocalRing_of_isRegularLocalRing_quotient_ofList hm hreg h
  refine ⟨hR, ?_⟩
  have := hR
  obtain ⟨ts, hsop, hgen⟩ :=
    IsRegularLocalRing.exists_isSystemOfParameters_append_of_isRegularLocalRing_quotient h
      (ringKrullDim_quotient_ofList_add_length_eq hm hreg)
  exact ⟨fs ++ ts, hsop, hgen, by simp, by simp⟩

end
