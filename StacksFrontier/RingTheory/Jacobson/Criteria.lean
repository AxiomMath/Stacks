module

public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# A Jacobson criterion for Noetherian rings

Let `R` be a Noetherian ring in which every prime ideal is either maximal or contained in
infinitely many prime ideals. Then `R` is a Jacobson ring: every radical ideal is an
intersection of maximal ideals. The polynomial ring `k[x, y]` over a field and the ring `ℤ`
both satisfy the criterion, while `k[[t]]` does not: its only non-maximal prime `(0)` is
contained in just one further prime.

Suppose `R` is not Jacobson. Among the primes `𝔭` with `𝔭.jacobson ≠ 𝔭` choose a maximal one;
it exists because `R` is Noetherian. It is not maximal, so it is contained in infinitely many
primes, and there is an `x ∈ 𝔭.jacobson` with `x ∉ 𝔭`. Every prime `𝔮 ⊋ 𝔭` satisfies
`𝔮.jacobson = 𝔮` by the maximal choice, so `x ∈ 𝔭.jacobson ⊆ 𝔮.jacobson = 𝔮`: the nonzero
element `x` of the Noetherian domain `R/𝔭` lies in every nonzero prime. Hence `dim R/𝔭 ≤ 1`,
because for a maximal ideal `𝔪` of `R/𝔭` the basic open `D(x)` of `Spec (R/𝔭)_𝔪` is the single
point `(0)`, which is impossible for a Noetherian local domain of dimension at least two by
Stacks 02IG. So every prime `𝔮 ⊋ 𝔭` is maximal, and then every such `𝔮` is a minimal
prime over `𝔭 + (x)`: a prime `𝔮'` with `𝔭 + (x) ⊆ 𝔮' ⊆ 𝔮` contains `x ∉ 𝔭`, hence strictly
contains `𝔭`, hence is maximal, hence equals `𝔮`. A Noetherian ring has only finitely many
minimal primes over an ideal, so `𝔭` is contained in only finitely many primes -- the
contradiction.

## Main results

* `isJacobsonRing_of_forall_isMaximal_or_infinite_setOf_isPrime`: a Noetherian ring each of
  whose primes is maximal or contained in infinitely many primes is a Jacobson ring.
* `Stacks.Jacobson.NoetherianCriterion.solution`: the same statement, proved in the namespace.
* `Stacks.Jacobson.NoetherianCriterion.isMaximal_of_isPrime_lt_of_forall_mem`: in a Noetherian
  ring, if some `x ∉ 𝔭` lies in every prime strictly containing the prime `𝔭`, then every prime
  strictly containing `𝔭` is maximal. This is the dimension bound `dim R/𝔭 ≤ 1` of the argument,
  read back in `R`.

## Implementation notes

The source states the criterion in two parts: (1) a Noetherian domain of dimension `1` with
infinitely many primes is Jacobson, and (2) a Noetherian ring in which every prime is maximal or
contained in infinitely many primes is Jacobson. Part (2) is stated here, because part (1) is the
instance of it in which the domain hypothesis does the work: in a domain with `Ring.KrullDimLE 1`
every nonzero prime is maximal (`Ideal.IsPrime.isMaximal_of_ne_bot`), so `⊥` is the only
non-maximal prime, and `{q | ⊥ ≤ q ∧ q.IsPrime}` is all of the spectrum, infinite by hypothesis.
The source argues topologically and deduces part (2) from part (1) applied to `R/𝔭`; the proof of
part (1) is the finiteness of the maximal spectrum of `R/(x)` for `x` in every maximal ideal,
which is the finiteness of the minimal primes over `𝔭 + (x)` used here, so making the finiteness
the last step avoids passing through the quotient a second time.

Everything after the choice of `𝔭` and `x` is `finite_setOf_isPrime_of_forall_mem`: in a
Noetherian ring, a prime `𝔭` admitting an `x ∉ 𝔭` that lies in every prime strictly containing
`𝔭` is contained in only finitely many primes. It is stated for that datum alone rather than for
the Jacobson radical, since the Jacobson hypothesis enters only through `x`; `solution` is then
the choice of `𝔭` by Noetherian induction, the choice of `x`, and one application of it.

The dimension bound is split off from the ring `R` in two steps. At the level of `R` it is
`isMaximal_of_lt_of_forall_mem`: under the same datum every prime strictly containing `𝔭` is
maximal, which is `dim R/𝔭 ≤ 1` for the domain `R/𝔭`, and this is the only place the quotient
appears. That dimension bound is `krullDimLE_one_of_forall_mem`, a Noetherian domain in which
some nonzero element lies in every nonzero prime has dimension at most `1`, proved by localizing
at each maximal ideal; the local case is the source's use of Stacks 02IG.

"Contained in infinitely many prime ideals" is `{q : Ideal R | p ≤ q ∧ q.IsPrime}.Infinite`,
with the conjuncts in the order of `Ideal.radical_eq_sInf`. That set contains `p` itself, one
element more than the set of primes strictly containing `p`, so the choice between `≤` and `<`
cannot change its infinitude. It is equivalent to `Infinite (PrimeSpectrum (R ⧸ p))` and to
`(PrimeSpectrum.zeroLocus (p : Set R)).Infinite`. "Jacobson" is Mathlib's `IsJacobsonRing`; the
source's topological formulation, that `Spec R` is the closure of its set of closed points, is
`PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`.

Both hypotheses are needed: without the disjunction `k[[t]]` is Noetherian and not Jacobson, and
without `IsNoetherianRing R` a valuation domain whose value group is `⨁_{n : ℕ} ℤ` ordered
lexicographically from the left has primes forming an increasing chain `𝔭₀ ⊂ 𝔭₁ ⊂ ⋯` below its
unique maximal ideal, so every non-maximal prime is contained in infinitely many primes while the
ring, being local of positive dimension, is not Jacobson.

## References

* [Stacks Project, Tag 00KX](https://stacks.math.columbia.edu/tag/00KX)
* [Stacks Project, Tag 02IG](https://stacks.math.columbia.edu/tag/02IG)
-/

namespace Stacks.Jacobson.NoetherianCriterion

/-- A Noetherian local domain in which some nonzero element `x` lies in every nonzero prime ideal
has dimension at most `1`: otherwise `D(x) = {(0)}` would be a finite nonempty open subset of the
spectrum, contradicting Stacks 02IG. -/
@[ega "IV 10.5.1" "d) ⇒ f)"]
private theorem krullDimLE_one_of_isLocalRing_of_forall_mem (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] {x : A} (hx : x ≠ 0)
    (hmem : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → x ∈ q) : Ring.KrullDimLE 1 A := by
  refine Ring.krullDimLE_iff.mpr (le_of_not_gt fun h => ?_)
  refine PrimeSpectrum.infinite_of_two_le_ringKrullDim A (Order.succ_le_of_lt h) _
    (PrimeSpectrum.basicOpen x).isOpen ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hx⟩
    ((Set.finite_singleton (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A)).subset fun P hP =>
      Set.mem_singleton_iff.mpr (PrimeSpectrum.ext ?_))
  by_contra hne
  exact (PrimeSpectrum.mem_basicOpen x P).mp hP (hmem P.asIdeal P.isPrime hne)

/-- A Noetherian domain in which some nonzero element `x` lies in every nonzero prime ideal has
dimension at most `1`: the property passes to the localization at each maximal ideal. -/
private theorem krullDimLE_one_of_forall_mem (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] {x : A} (hx : x ≠ 0)
    (hmem : ∀ q : Ideal A, q.IsPrime → q ≠ ⊥ → x ∈ q) : Ring.KrullDimLE 1 A := by
  refine Ring.krullDimLE_of_isLocalization_maximal (fun P _ => Localization.AtPrime P)
    fun P _ => ?_
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  refine krullDimLE_one_of_isLocalRing_of_forall_mem _
    (x := algebraMap A (Localization.AtPrime P) x) (fun hc => hx (hinj (by simpa using hc)))
    fun Q hQ hQbot => ?_
  refine hmem (Q.under A) inferInstance fun hc => hQbot ?_
  rw [← IsLocalization.map_under P.primeCompl (Localization.AtPrime P) Q, hc, Ideal.map_bot]

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- If some `x ∉ p` lies in every prime strictly containing the prime `p`, then every prime
strictly containing `p` is maximal: `x` is a nonzero element of the Noetherian domain `R ⧸ p`
lying in every nonzero prime, so `dim R ⧸ p ≤ 1`. -/
private theorem isMaximal_of_lt_of_forall_mem {p : Ideal R} [p.IsPrime] {x : R} (hxp : x ∉ p)
    (hx : ∀ q : Ideal R, q.IsPrime → p < q → x ∈ q) {q : Ideal R} (hq : q.IsPrime) (hpq : p < q) :
    q.IsMaximal := by
  have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have : q.IsPrime := hq
  have hdim : Ring.KrullDimLE 1 (R ⧸ p) := by
    refine krullDimLE_one_of_forall_mem _ (x := Ideal.Quotient.mk p x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxp) fun Q hQ hQbot => ?_
    have hle : p ≤ Q.comap (Ideal.Quotient.mk p) := fun y hy => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact hx _ (hQ.comap _) (hle.lt_of_ne fun hc => hQbot <| by
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hc,
        Ideal.map_quotient_self])
  have hQbot : q.map (Ideal.Quotient.mk p) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hpq.not_ge
  have hmax := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective (K := q.map (Ideal.Quotient.mk p))
    (H := Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim _ hQbot
      (Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hpq.le)))
  rwa [Ideal.comap_map_mk hpq.le] at hmax

/-- **A prime avoided by an element of every larger prime has only maximal primes above it.** In a
Noetherian ring, if some `x ∉ 𝔭` lies in every prime strictly containing the prime `𝔭`, then
every prime strictly containing `𝔭` is maximal; this is the bound `dim R ⧸ 𝔭 ≤ 1`. -/
alias isMaximal_of_isPrime_lt_of_forall_mem := isMaximal_of_lt_of_forall_mem

/-- In a Noetherian ring, a prime `p` admitting an `x ∉ p` that lies in every prime strictly
containing `p` is contained in only finitely many primes: those primes are `p` itself and the
minimal primes over `p + (x)`, since a prime `q ⊋ p` is maximal and hence equal to any minimal
prime over `p + (x)` below it. -/
private theorem finite_setOf_isPrime_of_forall_mem {p : Ideal R} [p.IsPrime] {x : R} (hxp : x ∉ p)
    (hx : ∀ q : Ideal R, q.IsPrime → p < q → x ∈ q) :
    {q : Ideal R | p ≤ q ∧ q.IsPrime}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R
    (p ⊔ Ideal.span {x})).insert p).subset ?_
  rintro q ⟨hpq, hq⟩
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ?_
  obtain ⟨q', hq', hq'q⟩ := Ideal.exists_minimalPrimes_le (I := p ⊔ Ideal.span {x})
    (sup_le hpq (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hx q hq hlt))))
  have hxq' : x ∈ q' := hq'.1.2 (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hpq' : p < q' := (le_sup_left.trans hq'.1.2).lt_of_ne fun hc => hxp (hc ▸ hxq')
  exact ((isMaximal_of_lt_of_forall_mem hxp hx hq'.1.1 hpq').eq_of_le hq.ne_top hq'q) ▸ hq'

/-- A Noetherian ring in which every prime ideal is either maximal or contained in infinitely
many prime ideals is a Jacobson ring: a prime `p` maximal among those with `p.jacobson ≠ p`, and
an `x ∈ p.jacobson` with `x ∉ p`, would make `p` contained in only finitely many primes. -/
public theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R]
    (h : ∀ p : Ideal R, p.IsPrime →
      p.IsMaximal ∨ {q : Ideal R | p ≤ q ∧ q.IsPrime}.Infinite) :
    IsJacobsonRing R := by
  rw [isJacobsonRing_iff_prime_eq]
  by_contra hcon
  push Not at hcon
  -- A prime `p` maximal among those with `p.jacobson ≠ p`, and an `x ∈ p.jacobson` with `x ∉ p`.
  obtain ⟨p, ⟨hp, hpjac⟩, hpmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {I : Ideal R | I.IsPrime ∧ I.jacobson ≠ I} hcon
  have : Ideal.IsPrime p := hp
  obtain ⟨x, hxjac, hxp⟩ := SetLike.not_le_iff_exists.mp
    (fun hle => hpjac (le_antisymm hle Ideal.le_jacobson))
  -- Every prime `q ⊋ p` has `q.jacobson = q` by maximality of `p`, hence contains `x`.
  have hxq : ∀ q : Ideal R, q.IsPrime → p < q → x ∈ q := fun q hq hpq =>
    (by_contra fun hne => hpmax q ⟨hq, hne⟩ hpq : q.jacobson = q) ▸
      Ideal.jacobson_mono hpq.le hxjac
  exact (h p hp).resolve_left (fun hm => hpjac (@Ideal.jacobson_eq_self_of_isMaximal _ _ p hm))
    (finite_setOf_isPrime_of_forall_mem hxp hxq)

end Stacks.Jacobson.NoetherianCriterion

/-- A Noetherian ring in which every prime ideal is either maximal or contained in infinitely
many prime ideals is a Jacobson ring. -/
@[stacks 00KX,
  ega "IV 10.5.2" "sufficiency",
  ega "IV 10.5.5" "(ii) sufficiency, affine",
  ega "IV 10.4.3" "Artinian, PID clauses"]
public theorem isJacobsonRing_of_forall_isMaximal_or_infinite_setOf_isPrime (R : Type*)
    [CommRing R] [IsNoetherianRing R] (h : ∀ p : Ideal R, p.IsPrime →
      p.IsMaximal ∨ {q : Ideal R | p ≤ q ∧ q.IsPrime}.Infinite) :
    IsJacobsonRing R :=
  Stacks.Jacobson.NoetherianCriterion.solution R h
