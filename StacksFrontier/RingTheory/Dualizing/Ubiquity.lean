module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinRingDualizing

/-!
# The ubiquity of dualizing complexes: fields, the integers, Dedekind domains

[Stacks, Tag 0BFR] lists five classes of rings that have a dualizing complex. This file settles
three of them: the fields, the ring `ℤ`, and the Dedekind domains.

A field `k` is a regular local ring, hence Gorenstein, so `k[0]` is a dualizing complex for `k`;
this is the source's class (1). For a Dedekind domain `A` — class (4), and class (3) because `ℤ`
is one — the source argues that every ideal of `A` is a finite projective module, so that every
`A`-module has injective dimension at most `1`, whence `A[0]` is a dualizing complex. The route
taken here is the same bound by way of the global dimension: a Dedekind domain is a regular ring
(`IsRegularRing`) of Krull dimension at most one, and over a regular ring of finite Krull
dimension `d` the global dimension equals `d` ([Stacks, Tag 00OE]), so each cyclic module `A/I`
has projective dimension at most `d` and `Ext^{d+1}(A/I, A)` vanishes; by Baer's criterion in the
form of `ModuleCat.hasInjectiveDimensionLE_of_quotients` the module `A` then has injective
dimension at most `d`, which by [Stacks, Tag 0DW9 (2)] is exactly the assertion that `A[0]` is a
dualizing complex.

## Main results

* `Dualizing.exists_isDualizingComplex` — **[Stacks, Tag 0BFR]** for the class of fields.
* `Dualizing.exists_isDualizingComplex_int` — **[Stacks, Tag 0BFR]** for `ℤ`.
* `Dualizing.exists_isDualizingComplex_of_isDedekindDomain` — **[Stacks, Tag 0BFR]** for the
  class of Dedekind domains.
* `Dualizing.hasInjectiveDimensionLE_of_isRegularRing` — over a regular ring of Krull dimension
  `d` the regular module has injective dimension at most `d`.
* `Dualizing.isDualizingComplex_single_self_of_isDedekindDomain` — a Dedekind domain in degree
  zero is a dualizing complex for itself.

## Implementation notes

The existence claims are stated in the derived category of modules whose universe agrees with
that of the ring; this is the universe-polymorphic form of the source's category of modules.

`IsDedekindDomain` is Mathlib's class: a Noetherian integrally closed domain in which every
nonzero prime is maximal. Like the source's notion it does not exclude fields, so the Dedekind
case is stated with no extra hypothesis and the proof splits on `IsField A` only to name the
Krull dimension (`0` for a field, `1` otherwise).

The remaining two classes of [Stacks, Tag 0BFR] are elsewhere: the Noetherian complete local
rings are `Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal` in
`StacksFrontier/RingTheory/Dualizing/UbiquityCompleteLocal.lean`, and the closure of the list under
the four operations of clause (5) is in
`StacksFrontier/RingTheory/Dualizing/UbiquityStability.lean`. The statement conjoining all five
clauses is `Dualizing.exists_isDualizingComplex_ubiquity` in
`StacksFrontier/RingTheory/Dualizing/UbiquityFiveClasses.lean`.

## References

* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 00OE](https://stacks.math.columbia.edu/tag/00OE)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Stacks Project, Tag 0BFR (fields).** Every field has a dualizing complex. -/
@[stacks 0BFR "fields"]
theorem exists_isDualizingComplex (k : Type u) [Field k] :
    ∃ K : DerivedCategory (ModuleCat.{u} k), IsDualizingComplex K :=
  ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k),
    IsRegularLocalRing.isGorensteinLocalRing k⟩

/-- **Over a regular ring of Krull dimension `d` the regular module has injective dimension at
most `d`.** The global dimension of such a ring is `d` ([Stacks, Tag 00OE]), so every cyclic
module has projective dimension at most `d` and therefore `Ext^{d + 1}(A/I, A) = 0` for every
ideal `I`; Baer's criterion in the form `ModuleCat.hasInjectiveDimensionLE_of_quotients` turns
that vanishing into the bound on the injective dimension of `A`. -/
theorem hasInjectiveDimensionLE_of_isRegularRing (A : Type u) [CommRing A] [IsRegularRing A]
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    HasInjectiveDimensionLE (ModuleCat.of A A : ModuleCat.{u} A) d := by
  have hinput : IsRegularRing A ∧ ringKrullDim A = (d : WithBot ℕ∞) := ⟨‹IsRegularRing A›, hdim⟩
  have hgl : (⨆ M : ModuleCat.{u} A, projectiveDimension M) = (d : WithBot ℕ∞) :=
    ((isRegularRing_tfae (R := A) d).out 1 2).mpr hinput
  refine ModuleCat.hasInjectiveDimensionLE_of_quotients (ModuleCat.of A A) d fun I => ?_
  let M : ModuleCat.{u} A := ModuleCat.of A (Shrink.{u, u} (A ⧸ I))
  have hpdlt : projectiveDimension M < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    change projectiveDimension M < (d : WithBot ℕ∞) + 1
    exact (ENat.WithBot.lt_add_one_iff (n := projectiveDimension M) (m := d)).2
      ((le_iSup (fun N : ModuleCat.{u} A => projectiveDimension N) M).trans hgl.le)
  have : HasProjectiveDimensionLT M (d + 1) := projectiveDimension_lt_iff.mp hpdlt
  exact HasProjectiveDimensionLT.subsingleton M (d + 1) (d + 1) le_rfl (ModuleCat.of A A)

/-- A Dedekind domain has Krull dimension at most one: its nonzero primes are maximal. -/
theorem ringKrullDim_le_one_of_isDedekindDomain (A : Type u) [CommRing A] [IsDedekindDomain A] :
    ringKrullDim A ≤ 1 := by
  rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
  exact Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun I hI hp =>
    Ring.DimensionLEOne.maximalOfPrime hI hp

/-- **A Dedekind domain in degree zero is a dualizing complex for itself.** A Dedekind domain is
a regular ring of Krull dimension `0` (if it is a field) or `1`, so the regular module has
injective dimension at most that number by
`Dualizing.hasInjectiveDimensionLE_of_isRegularRing`, which is the criterion
`Dualizing.isDualizingComplex_single_self_iff` for `A[0]` to be dualizing. -/
theorem isDualizingComplex_single_self_of_isDedekindDomain (A : Type u) [CommRing A]
    [IsDedekindDomain A] :
    IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  refine (isDualizingComplex_single_self_iff A).2 ?_
  by_cases hfield : IsField A
  · exact ⟨0, hasInjectiveDimensionLE_of_isRegularRing A 0
      (by simpa using ringKrullDim_eq_zero_of_isField hfield)⟩
  · refine ⟨1, hasInjectiveDimensionLE_of_isRegularRing A 1 ?_⟩
    refine (eq_of_le_of_not_lt (ringKrullDim_le_one_of_isDedekindDomain A) fun hlt =>
      hfield ?_).trans (by simp)
    have hzero : ringKrullDim A ≤ 0 := Order.le_of_lt_succ hlt
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at hzero
    exact Ring.KrullDimLE.isField_of_isDomain

/-- **Stacks Project, Tag 0BFR (Dedekind domains).** A Dedekind domain has a dualizing complex,
namely the ring itself in degree zero. -/
@[stacks 0BFR "Dedekind domains"]
theorem exists_isDualizingComplex_of_isDedekindDomain (A : Type u) [CommRing A]
    [IsDedekindDomain A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K :=
  ⟨_, isDualizingComplex_single_self_of_isDedekindDomain A⟩

/-- **Stacks Project, Tag 0BFR (the integers).** The ring `ℤ` has a dualizing complex, namely
`ℤ[0]`: it is a Dedekind domain. -/
@[stacks 0BFR "the integers"]
theorem exists_isDualizingComplex_int :
    ∃ K : DerivedCategory (ModuleCat.{0} ℤ), IsDualizingComplex K :=
  exists_isDualizingComplex_of_isDedekindDomain ℤ

end Dualizing
