module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Regular
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Slicing a Cohen–Macaulay local ring by an element of a prescribed ideal

Let `(R, 𝔪_R)` be a Noetherian local Cohen–Macaulay ring, let `u : A →+* R` be a ring map and
let `I` be an ideal of `A` whose image generates a proper ideal of `R`. If the image ideal `u(I)R`
already cuts the dimension down, `dim(R / u(I)R) < dim(R)`, then some single element of `I` does
the same job and does it as well as possible: there is `f ∈ I` such that `u f` is a
nonzerodivisor on `R` and `R / u(f)R` is again Cohen–Macaulay, of dimension exactly
`dim(R) - 1`.

The mechanism is that `u(I)R` cannot be contained in any minimal prime `𝔫` of `R`: a
Cohen–Macaulay local ring is equidimensional, so `dim(R/𝔫) = dim(R)` (Lemma 00NA with
`height 𝔫 = 0`), while `u(I)R ⊆ 𝔫` would force `dim(R/𝔫) ≤ dim(R/u(I)R) < dim(R)`. Since `R` is
Noetherian there are only finitely many such `𝔫`, so prime avoidance (Lemma 00DS) applied to `I`
and the finitely many primes `u⁻¹(𝔫)` of `A` produces one `f ∈ I` with `u f` outside every
minimal prime of `R`. An element of `𝔪_R` avoiding all minimal primes cuts the dimension by
exactly one (Lemma 0B52, equality case), and in a Cohen–Macaulay local ring that numerical
identity is precisely what makes it a regular sequence of length one, with Cohen–Macaulay
quotient (Lemma 02JN).

This is the commutative-algebra core of the groupoid slicing lemma, Stacks 0461: there `R` is
`B_𝔮 / s(𝔪)B_𝔮` for two ring maps `s, t : A →+* B`, a maximal ideal `𝔪` of `A` and a prime `𝔮`
of `B` containing both `s(𝔪)` and `t(𝔪)`, the map `u` is `t` followed by the localisation and
the quotient, `dim(R)` is the source's `d₂` and `dim(R/u(I)R)` the source's `d₁`. Nothing about
that situation is used beyond the data listed above, so the statements here are about an abstract
ring map into a Cohen–Macaulay local ring.

## Main results

* `Ideal.exists_mem_forall_notMem_of_finite`: prime avoidance (Lemma 00DS) for an ideal and a
  finite set of primes none of which contains it.
* `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes`: the
  dimension of a Noetherian local ring drops by exactly one on dividing by an element of the
  maximal ideal avoiding every minimal prime (Lemma 0B52, equality case, at `M = R`).
* `Module.IsMaximalCohenMacaulay.exists_mem_notMem_minimalPrimes_of_ringKrullDim_quotient_lt`:
  the minimal-prime avoidance step, Lemmas 00NA and 00DS combined.
* `Module.IsMaximalCohenMacaulay.isSMulRegular_of_notMem_minimalPrimes`: an element of the
  maximal ideal of a Cohen–Macaulay local ring avoiding every minimal prime is a nonzerodivisor
  (Lemma 02JN).
* `Module.IsMaximalCohenMacaulay.quotient_span_singleton_of_notMem_minimalPrimes`: the quotient
  by such an element is Cohen–Macaulay of dimension one less (Lemma 02JN).
* `Module.IsMaximalCohenMacaulay.exists_mem_isSMulRegular_map_quotient_isMaximalCohenMacaulay`:
  the three conclusions together, the statement this file exists for.
* `IsCohenMacaulayLocalRing.exists_mem_maximalIdeal_isSMulRegular_map_of_ringKrullDim_lt`: the
  same for a local homomorphism out of a local ring, at `I = 𝔪_A`, keeping only the
  nonzerodivisor and the dimension drop.

## Implementation notes

Cohen–Macaulayness of a Noetherian local ring is `Module.IsMaximalCohenMacaulay R R`, that is
`depth_{𝔪_R}(R) = dim(R)` (Definition 00NF at `M = R`, equal to Definition 00N8 by
`Module.supportDim_self_eq_ringKrullDim`); this is the spelling used by the neighbouring statements
for Lemmas 00NA, 00N9, 00R4 and 02JN, so no bridge is needed to compose with them. The variant
along a local homomorphism is instead stated with `IsCohenMacaulayLocalRing` (Definition 00N8),
the two being identified by `isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay`.

Krull dimensions are `ringKrullDim`, valued in `WithBot ℕ∞`, and the source's `dim(R/fR) = d₂ - 1`
is stated additively as `dim(R/fR) + 1 = dim(R)`, as in
`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` and in the statement of Lemma 02JN; the
strict
inequality `dim(R/fR) < dim(R)` is recorded separately because it is what the source's conclusion
(a) literally says. The `IsLocalRing` structure on the quotient `R ⧸ (u f)` is bound
existentially, again following the statement of Lemma 02JN, since `f` is itself existentially bound
and so the instance cannot be an instance argument of the statement.

The ideal `I` of `A` is not assumed maximal, and `A` is not assumed Noetherian or local: the
argument only ever uses that `I` is not contained in the finitely many primes `u⁻¹(𝔫)`, which is
what prime avoidance needs. In the application `I` is a maximal ideal.

## References

* [StacksProject 0461](https://stacks.math.columbia.edu/tag/0461)
* [StacksProject 00NA](https://stacks.math.columbia.edu/tag/00NA)
* [StacksProject 00N8](https://stacks.math.columbia.edu/tag/00N8)
* [StacksProject 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [StacksProject 0B52](https://stacks.math.columbia.edu/tag/0B52)
* [StacksProject 02JN](https://stacks.math.columbia.edu/tag/02JN)

## Tags

Cohen-Macaulay ring, prime avoidance, minimal prime, Krull dimension, nonzerodivisor, slicing
-/

@[expose] public section

universe u

/-- **Prime avoidance for a finite family.** If an ideal `I` of a commutative ring is contained in
none of the finitely many prime ideals belonging to a set `S`, then some element of `I` lies
outside every member of `S`. -/
@[sga "3 V 4.1" "more general"]
theorem Ideal.exists_mem_forall_notMem_of_finite {A : Type u} [CommRing A] {I : Ideal A}
    {S : Set (Ideal A)} (hfin : S.Finite) (hprime : ∀ p ∈ S, p.IsPrime)
    (hnle : ∀ p ∈ S, ¬I ≤ p) : ∃ f ∈ I, ∀ p ∈ S, f ∉ p := by
  classical
  rcases hfin.toFinset.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
  · refine ⟨0, I.zero_mem, fun p hp => ?_⟩
    exact absurd (hfin.mem_toFinset.mpr hp) (by simp [hempty])
  · have hiff := Ideal.subset_union_prime (s := hfin.toFinset) (f := id) p₀ p₀
      (fun q hq _ _ => hprime q (hfin.mem_toFinset.mp hq)) (I := I)
    have hnotsub : ¬((I : Set A) ⊆ ⋃ q ∈ (hfin.toFinset : Set (Ideal A)), (id q : Set A)) := by
      intro hsub
      obtain ⟨q, hq, hle⟩ := hiff.mp hsub
      exact hnle q (hfin.mem_toFinset.mp hq) hle
    obtain ⟨f, hfI, hfnot⟩ := Set.not_subset.mp hnotsub
    refine ⟨f, hfI, fun p hp hmem => hfnot ?_⟩
    simp only [Set.mem_iUnion, id]
    exact ⟨p, by simpa using hfin.mem_toFinset.mpr hp, hmem⟩

open scoped Pointwise in
/-- **Dividing by an element outside every minimal prime drops the dimension by one.** For `R` a
Noetherian local ring and `x ∈ 𝔪_R` lying in no minimal prime of `R`, one has
`dim(R/xR) + 1 = dim(R)`. This is the equality case of Lemma 0B52 read at the module `M = R`. -/
@[ega "0 16.2.3.1" "clause (ii), M = A", ega "0 16.3.7" "Local ring, special case"]
theorem ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hn : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R)
  have hsmul : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hsmul).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (by rw [hann]; exact hn) hx

/-- **An element of the maximal ideal outside every minimal prime is a regular sequence of length
one.** In a Noetherian local Cohen–Macaulay ring `R`, an `x ∈ 𝔪_R` lying in no minimal prime of
`R` forms an `R`-regular sequence `[x]`, by the numerical criterion of Lemma 02JN. -/
theorem Module.IsMaximalCohenMacaulay.isRegular_singleton_of_notMem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hn : ∀ p ∈ minimalPrimes R, x ∉ p) :
    RingTheory.Sequence.IsRegular R [x] := by
  refine (hR.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim [x] (by simpa using hx)).1.mpr
    ?_
  rw [Ideal.ofList_singleton]
  simpa using
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes hx hn

/-- **Nonzerodivisors in a Cohen–Macaulay local ring.** An element of the maximal ideal of a
Noetherian local Cohen–Macaulay ring which lies in no minimal prime of the ring is a
nonzerodivisor on it. -/
theorem Module.IsMaximalCohenMacaulay.isSMulRegular_of_notMem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hn : ∀ p ∈ minimalPrimes R, x ∉ p) :
    IsSMulRegular R x :=
  ((RingTheory.Sequence.isRegular_cons_iff R x []).mp
    (hR.isRegular_singleton_of_notMem_minimalPrimes hx hn)).1

/-- **The slice of a Cohen–Macaulay local ring is Cohen–Macaulay.** For `R` a Noetherian local
Cohen–Macaulay ring and `x ∈ 𝔪_R` lying in no minimal prime of `R`, the quotient `R/xR` is a
Cohen–Macaulay local ring with `dim(R/xR) + 1 = dim(R)`. -/
@[ega "0 16.5.5" "special case"]
theorem Module.IsMaximalCohenMacaulay.quotient_span_singleton_of_notMem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hn : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ∃ _ : IsLocalRing (R ⧸ Ideal.span {x}),
      Module.IsMaximalCohenMacaulay (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) ∧
        ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have htake : ([x] : List R).take 1 = [x] := rfl
  have key :=
    ((hR.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim [x] (by simpa using hx)).2
      (hR.isRegular_singleton_of_notMem_minimalPrimes hx hn)).2 1 (by simp)
  rw [htake] at key
  rw [← Ideal.ofList_singleton]
  obtain ⟨hloc, hcm, hdim⟩ := key
  exact ⟨hloc, hcm, by simpa using hdim⟩

/-- **Minimal-prime avoidance in a Cohen–Macaulay local ring.** Let `R` be a Noetherian local
Cohen–Macaulay ring, `u : A →+* R` a ring map and `I` an ideal of `A` such that the ideal
`u(I)R` already cuts the dimension, `dim(R/u(I)R) < dim(R)`. Then there is `f ∈ I` whose image
`u f` lies in no minimal prime of `R`. -/
@[stacks 0461 "step 2 of the proof: the minimal-prime avoidance, from equidimensionality of a
Cohen--Macaulay local ring (Tag 00NA) and prime avoidance (Tag 00DS). The ideal is not assumed
maximal and the source ring is not assumed Noetherian or local", ega "0 16.5.5" "special case"]
theorem Module.IsMaximalCohenMacaulay.exists_mem_notMem_minimalPrimes_of_ringKrullDim_quotient_lt
    {A R : Type u} [CommRing A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (u : A →+* R) (I : Ideal A)
    (hlt : ringKrullDim (R ⧸ I.map u) < ringKrullDim R) :
    ∃ f ∈ I, ∀ p ∈ minimalPrimes R, u f ∉ p := by
  classical
  -- Each minimal prime `p` of `R` has `dim(R/p) = dim(R)`, by Lemma 00NA at `height p = 0`.
  have hequi : ∀ p ∈ minimalPrimes R, ringKrullDim (R ⧸ p) = ringKrullDim R := by
    intro p hp
    have : p.IsPrime := hp.isPrime
    have hheight : p.height = 0 := Ideal.height_eq_zero_iff.mpr hp
    rw [hR.ringKrullDim_eq_height_add_ringKrullDim_quotient p, hheight]
    simp
  -- Hence `I` is contained in no `u⁻¹(p)`: that would make `R/p` a quotient of `R/u(I)R`.
  have hnle : ∀ q ∈ Ideal.comap u '' minimalPrimes R, ¬I ≤ q := by
    rintro q ⟨p, hp, rfl⟩ hle
    have hmap : I.map u ≤ p := Ideal.map_le_iff_le_comap.mpr hle
    have hquot : ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ I.map u) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hmap)
        (Ideal.Quotient.factor_surjective hmap)
    exact absurd (hequi p hp ▸ hquot) (not_le.mpr hlt)
  -- Prime avoidance over the finitely many primes `u⁻¹(p)`.
  obtain ⟨f, hfI, hf⟩ :=
    Ideal.exists_mem_forall_notMem_of_finite (I := I)
      ((minimalPrimes.finite_of_isNoetherianRing R).image _)
      (fun q hq => by
        obtain ⟨p, hp, rfl⟩ := hq
        have : p.IsPrime := hp.isPrime
        exact Ideal.comap_isPrime u p)
      hnle
  exact ⟨f, hfI, fun p hp hmem => hf _ ⟨p, hp, rfl⟩ hmem⟩

/-- A value of `WithBot ℕ∞` which is neither `⊥` nor `⊤` is strictly below its successor. -/
private lemma lt_add_one_of_ne_bot_of_ne_top {a : WithBot ℕ∞} (hbot : a ≠ ⊥) (htop : a ≠ ⊤) :
    a < a + 1 := by
  obtain ⟨b, rfl⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hb : b ≠ ⊤ := fun h => htop (by rw [h, WithBot.coe_top])
  rw [show (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add,
    WithBot.coe_lt_coe]
  exact (ENat.lt_add_one_iff hb).mpr le_rfl

/-- **Slicing a Cohen–Macaulay local ring, the commutative-algebra core of Stacks 0461.** Let
`(R, 𝔪_R)` be a Noetherian local Cohen–Macaulay ring, let `u : A →+* R` be a ring map and let `I`
be an ideal of `A` with `u(I)R ⊆ 𝔪_R` and `dim(R/u(I)R) < dim(R)`. Then there is `f ∈ I` such
that `dim(R/u(f)R) < dim(R)`, the element `u f` is a nonzerodivisor on `R`, and `R/u(f)R` is a
Cohen–Macaulay local ring of dimension `dim(R) - 1`. -/
@[stacks 0461 "the commutative-algebra core, conclusions (a), (b) and (c), over an abstract
Noetherian local Cohen--Macaulay ring and a ring map into it; no groupoid, scheme or
localisation data appears, and the dimension drop is stated additively",
  ega "0 16.5.5" "special case"]
theorem Module.IsMaximalCohenMacaulay.exists_mem_isSMulRegular_map_quotient_isMaximalCohenMacaulay
    {A R : Type u} [CommRing A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Module.IsMaximalCohenMacaulay R R) (u : A →+* R) (I : Ideal A)
    (hu : I.map u ≤ IsLocalRing.maximalIdeal R)
    (hlt : ringKrullDim (R ⧸ I.map u) < ringKrullDim R) :
    ∃ f ∈ I, ringKrullDim (R ⧸ Ideal.span {u f}) < ringKrullDim R ∧ IsSMulRegular R (u f) ∧
      ∃ _ : IsLocalRing (R ⧸ Ideal.span {u f}),
        Module.IsMaximalCohenMacaulay (R ⧸ Ideal.span {u f}) (R ⧸ Ideal.span {u f}) ∧
          ringKrullDim (R ⧸ Ideal.span {u f}) + 1 = ringKrullDim R := by
  obtain ⟨f, hfI, hf⟩ :=
    hR.exists_mem_notMem_minimalPrimes_of_ringKrullDim_quotient_lt u I hlt
  have hmem : u f ∈ IsLocalRing.maximalIdeal R := hu (Ideal.mem_map_of_mem u hfI)
  obtain ⟨hloc, hcm, hdim⟩ := hR.quotient_span_singleton_of_notMem_minimalPrimes hmem hf
  refine ⟨f, hfI, ?_, hR.isSMulRegular_of_notMem_minimalPrimes hmem hf, hloc, hcm, hdim⟩
  have := hloc
  exact hdim ▸ lt_add_one_of_ne_bot_of_ne_top ringKrullDim_ne_bot ringKrullDim_ne_top

/-- **Slicing along a local homomorphism.** Let `φ : A →+* C` be a local homomorphism of local
rings with `C` Noetherian and Cohen–Macaulay, and suppose the ideal `φ(𝔪_A)C` already cuts the
dimension, `dim(C/φ(𝔪_A)C) < dim(C)`. Then some `a ∈ 𝔪_A` has `φ a` a nonzerodivisor on `C` with
`dim(C/φ(a)C) + 1 = dim(C)`. -/
@[stacks 0461 "the commutative-algebra core along a local homomorphism, at the maximal ideal
of the source, in the Tag 00N8 spelling of Cohen--Macaulayness; this is the form the geometric
argument consumes"]
theorem IsCohenMacaulayLocalRing.exists_mem_maximalIdeal_isSMulRegular_map_of_ringKrullDim_lt
    (A C : Type u) [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] (hC : IsCohenMacaulayLocalRing C) (φ : A →+* C) (hφ : IsLocalHom φ)
    (hlt : ringKrullDim (C ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) < ringKrullDim C) :
    ∃ a ∈ IsLocalRing.maximalIdeal A, IsSMulRegular C (φ a) ∧
      ringKrullDim (C ⧸ Ideal.span {φ a}) + 1 = ringKrullDim C := by
  have := hφ
  obtain ⟨a, ha, -, hreg, hloc, -, hdim⟩ :=
    ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay C).mp
      hC).exists_mem_isSMulRegular_map_quotient_isMaximalCohenMacaulay φ
        (IsLocalRing.maximalIdeal A) (IsLocalRing.map_maximalIdeal_le φ) hlt
  exact ⟨a, ha, hreg, hdim⟩

end
