module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

import StacksCore.Tactic.StacksAttribute

/-!
# Associated primes and nonzerodivisors

Let `R` be a Noetherian ring, let `M` be an `R`-module whose set of associated primes is finite,
and let `I ⊆ R` be an ideal. Then `I` contains an element acting regularly on `M` if and only if
`I` is contained in no associated prime of `M`. Over a Noetherian ring a module is zero if and only
if it has no associated prime, and a finite type algebra over a field of positive Krull dimension
contains an element which is both a nonzerodivisor and a nonunit.

## Main results

* `Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le`: for `R` Noetherian and
  `Ass(M)` finite, `I` contains a nonzerodivisor on `M` if and only if `I ≤ 𝔮` for no
  `𝔮 ∈ Ass(M)`.
* `infinite_setOf_isMaximal`: a finite type algebra over a field of positive Krull dimension has
  infinitely many maximal ideals.
* `exists_mem_nonZeroDivisors_not_isUnit`: a finite type algebra over a field of positive Krull
  dimension has an element which is a nonzerodivisor and a nonunit.

## Implementation notes

"`x` is not a zerodivisor on `M`" is `IsSMulRegular M x`, and `Ass(M)` is
`associatedPrimes R M`. The criterion assumes that `Ass(M)` is finite rather than that `M` is
finite; for a finite module over a Noetherian ring this is `associatedPrimes.finite`. The two
directions of "`M = 0` if and only if `Ass(M) = ∅`" are `associatedPrimes.eq_empty_of_subsingleton`
and `associatedPrimes.nonempty`.

## References

* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 0587](https://stacks.math.columbia.edu/tag/0587)
* [Stacks Project, Tag 0GEC](https://stacks.math.columbia.edu/tag/0GEC)

## Tags

associated prime, nonzerodivisor, regular element, prime avoidance, Noetherian ring
-/

@[expose] public section

namespace Stacks.AssociatedPrimes.Avoidance

/-- **Prime avoidance for associated primes.** An ideal contained in the union of the associated
primes of `M`, of which there are finitely many, is contained in one of them. -/
private lemma subset_biUnion_associatedPrimes_iff_exists_le {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommMonoid M] [Module R M] (hM : (associatedPrimes R M).Finite) :
    (I : Set R) ⊆ ⋃ 𝔮 ∈ associatedPrimes R M, (𝔮 : Set R) ↔
      ∃ 𝔮 ∈ associatedPrimes R M, I ≤ 𝔮 :=
  Ideal.subset_union_prime_finite hM ⊥ ⊥ fun _ h𝔮 _ _ => h𝔮.isPrime

/-- Over a Noetherian ring, an ideal `I` contains a nonzerodivisor on a module `M` with finitely
many associated primes if and only if `I` is contained in no associated prime of `M`. -/
public theorem solution {R : Type*}
    [CommRing R] [IsNoetherianRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (hM : (associatedPrimes R M).Finite) :
    (∃ x ∈ I, IsSMulRegular M x) ↔
      ∀ 𝔮 ∈ associatedPrimes R M, ¬ I ≤ 𝔮 := by
  rw [← not_iff_not]
  push Not
  rw [← subset_biUnion_associatedPrimes_iff_exists_le I M hM,
    biUnion_associatedPrimes_eq_compl_regular]
  rfl

end Stacks.AssociatedPrimes.Avoidance

@[expose] public section

/-- Let `R` be a Noetherian ring, `M` an `R`-module with finitely many associated primes and
`I ⊆ R` an ideal. Then `I` contains an element that is a nonzerodivisor on `M` if and only if `I`
is contained in no associated prime of `M`. -/
@[stacks 00LL, sga "2 III 2.1" "(ii) <=> (iv)"]
public theorem Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le {R : Type*}
    [CommRing R] [IsNoetherianRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (hM : (associatedPrimes R M).Finite) :
    (∃ x ∈ I, IsSMulRegular M x) ↔
      ∀ 𝔮 ∈ associatedPrimes R M, ¬ I ≤ 𝔮 :=
  Stacks.AssociatedPrimes.Avoidance.solution I M hM

end

end

@[expose] public section

add_to_stacks 0587 "the direction M = 0 implies Ass(M) = 0"
  associatedPrimes.eq_empty_of_subsingleton
add_to_stacks 0587 "the converse, contrapositively: a nontrivial module has an associated prime"
  associatedPrimes.nonempty

end

@[expose] public section

/-- A finite type algebra `S` over a field `k` with `0 < dim S` has infinitely many maximal
ideals. -/
@[ega "IV 5.5.3" "special case"]
lemma infinite_setOf_isMaximal {k : Type*} [Field k] {S : Type*} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (h : 0 < ringKrullDim S) :
    {m : Ideal S | m.IsMaximal}.Infinite := by
  have hj : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hkdle : Ring.KrullDimLE 0 S := Ring.krullDimLE_zero_iff.mpr fun P hP => by
    have hT : {J : Ideal S | P ≤ J ∧ J.IsMaximal}.Finite := hfin.subset fun _ hJ => hJ.2
    have hle : hT.toFinset.inf id ≤ P := by
      rw [Finset.inf_id_eq_sInf, hT.coe_toFinset, ← Ideal.jacobson, hj.out hP.isRadical]
    obtain ⟨m, hm, hmP⟩ := (hP.inf_le' (f := id)).mp hle
    rw [hT.mem_toFinset] at hm
    exact le_antisymm hmP hm.1 ▸ hm.2
  rw [Ring.krullDimLE_iff, Nat.cast_zero] at hkdle
  exact absurd (lt_of_lt_of_le h hkdle) (by simp)

/-- For a finite type algebra `S` over a field `k` with `0 < dim S`, some element of `S` is
simultaneously a nonzerodivisor and a nonunit. -/
@[stacks 0GEC, sga "3 VIA 1.1.2" "special case"]
theorem exists_mem_nonZeroDivisors_not_isUnit {k : Type*} [Field k] {S : Type*} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (h : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := by
  have := Algebra.FiniteType.isNoetherianRing k S
  have hfin := associatedPrimes.finite S S
  obtain ⟨m, hm, hmA⟩ := ((infinite_setOf_isMaximal (k := k) h).sdiff hfin).nonempty
  have hm : m.IsMaximal := hm
  obtain ⟨f, hfm, hf⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le m S hfin).mpr
      fun p hp hle => hmA (hm.eq_of_le hp.isPrime.ne_top hle ▸ hp)
  exact ⟨f, (isLeftRegular_iff_isRegular.mp hf).mem_nonZeroDivisors,
    fun hu => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hfm hu)⟩

end
