module

public import StacksFrontier.RingTheory.Artinian.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Characterizations of Artinian rings

Let `R` be a commutative ring. Being Artinian is equivalent to nine other conditions: being
Noetherian of Krull dimension zero, having finite length over oneself, being a finite product of
local rings each of which is Artinian (equivalently Noetherian of dimension zero, equivalently of
finite length over itself, equivalently Noetherian with nilpotent maximal ideal), being Noetherian
with discrete prime spectrum, being Noetherian with finitely many maximal ideals and nilpotent
Jacobson radical, and being Noetherian with no strict inclusions among the primes.

## Main results

* `Stacks.Artinian.Characterizations.solution`: the ten characterizations are equivalent.

## Implementation notes

Items (1), (2) and (3) are the two Hopkins–Levitzki equivalences
`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero` and `isArtinianRing_iff_isFiniteLength`,
both upstream.

The product decomposition of item (4) is the canonical one: the index type is `MaximalSpectrum R`,
the factors are the localizations `Localization.AtPrime 𝔪`, and the isomorphism is the bijective
`algebraMap R (∀ 𝔪, Localization.AtPrime 𝔪)` of [StackProject 00JA] and [StackProject 00JB],
whose hypothesis there — discreteness of `Spec(R)` — is an instance for an Artinian ring. In the
converse direction a finite product of Artinian rings is Artinian, and Artinianness transports
along a ring isomorphism, so no separate argument is needed.

Items (6), (7) and (8) differ from item (4) only in the condition imposed on the factors, and for
each of them that condition is equivalent to Artinianness of the factor: for (6) and (7) by the
two Hopkins–Levitzki equivalences again, uniformly in the ring, and for (8) — where locality is
what makes it true — by `isArtinianRing_iff_isNilpotent_maximalIdeal`. The passage from one of
these items to another is the same reindexing three times over, so it is proved once as
`exists_pi_isLocalRing_congr`, which takes the two conditions as predicates on a local ring —
hence as functions of a type together with its two instances — and needs nothing about them beyond
their pointwise equivalence. For item (8) that pointwise equivalence is
`isArtinianRing_iff_isNoetherianRing_and_isNilpotent_maximalIdeal`, the upstream lemma with
Noetherianness moved from a hypothesis into the statement, which is the form in which the two
conditions can be compared as properties of an unadorned local ring.

Items (5), (9) and (10) each replace the second conjunct of an earlier item, the Noetherian
conjunct being untouched, so each is one equivalence of conditions on a Noetherian ring:
`discreteTopology_primeSpectrum_iff_krullDimLE_zero` carries item (2) to item (5),
`discreteTopology_primeSpectrum_iff_finite_and_isNilpotent_jacobson` carries item (5) to item (9),
and `krullDimLE_zero_iff_forall_isPrime_le_imp_eq` — which needs no hypothesis on `R` beyond
commutativity — carries item (2) to item (10).

The source proves item (7) from Lemma [StackProject 00KI], namely that for a Noetherian local ring
finite length is the same as `d = 0`; the invariant `d` has no definition in this repository, so
item (7) is stated in the finite-length form and that lemma is not needed.

## References

* [StackProject 00KJ](https://stacks.math.columbia.edu/tag/00KJ)
-/



namespace Stacks.Artinian.Characterizations

/-- A commutative semiring has Krull dimension zero exactly when its prime ideals are pairwise
incomparable.

This is `Ring.krullDimLE_zero_iff` — every prime is maximal — restated as a condition on pairs of
primes; the passage from a prime to a maximal ideal above it is `Ideal.exists_le_maximal`. -/
private theorem krullDimLE_zero_iff_forall_isPrime_le_imp_eq (R : Type*) [CommSemiring R] :
    Ring.KrullDimLE 0 R ↔ ∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q :=
  ⟨fun h p q hp hq hpq ↦ (Ring.krullDimLE_zero_iff.mp h p hp).eq_of_le hq.ne_top hpq,
    fun h ↦ Ring.KrullDimLE.mk₀ fun I hI ↦ by
      obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI.ne_top
      exact h I m hI hm.isPrime hIm ▸ hm⟩

/-- The prime spectrum of a Noetherian commutative ring is discrete exactly when the ring has
Krull dimension zero.

Discreteness of `Spec(R)` is finiteness of `Spec(R)` together with dimension zero
(`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`), and in the presence of
Noetherianness the finiteness is automatic: dimension zero then makes `R` Artinian. -/
private theorem discreteTopology_primeSpectrum_iff_krullDimLE_zero (R : Type*) [CommRing R]
    [IsNoetherianRing R] : DiscreteTopology (PrimeSpectrum R) ↔ Ring.KrullDimLE 0 R :=
  ⟨fun h ↦ (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp h).2,
    fun h ↦ have : IsArtinianRing R :=
      isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨‹_›, h⟩
    inferInstance⟩

/-- The prime spectrum of a Noetherian commutative ring is discrete exactly when the ring has
finitely many maximal ideals and nilpotent Jacobson radical.

Discreteness of `Spec(R)` is finiteness of the set of maximal ideals together with containment of
their intersection in the nilradical
(`PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`); that intersection
is `Ring.jacobson R`, and over a Noetherian ring it is a finitely generated ideal, hence nilpotent
exactly when it lies in the nilradical. -/
@[sga "3 VIIB 1.6.D" "partial"]
private theorem discreteTopology_primeSpectrum_iff_finite_and_isNilpotent_jacobson (R : Type*)
    [CommRing R] [IsNoetherianRing R] :
    DiscreteTopology (PrimeSpectrum R) ↔
      Finite (MaximalSpectrum R) ∧ IsNilpotent (Ring.jacobson R) := by
  rw [PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical,
    ← Ring.jacobson_eq_sInf_isMaximal,
    ← Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (Ring.jacobson R))]
  exact and_congr_left' (MaximalSpectrum.equivSubtype R).finite_iff.symm

/-- A local ring is Artinian if and only if it is Noetherian and its maximal ideal is nilpotent.

This is `isArtinianRing_iff_isNilpotent_maximalIdeal` with Noetherianness moved from a hypothesis
into the statement, which is the form in which the two conditions can be compared as properties of
an unadorned local ring. -/
private theorem isArtinianRing_iff_isNoetherianRing_and_isNilpotent_maximalIdeal (S : Type*)
    [CommRing S] [IsLocalRing S] :
    IsArtinianRing S ↔ IsNoetherianRing S ∧ IsNilpotent (IsLocalRing.maximalIdeal S) :=
  ⟨fun h ↦ ⟨inferInstance, (isArtinianRing_iff_isNilpotent_maximalIdeal S).mp h⟩,
    fun ⟨_, h⟩ ↦ (isArtinianRing_iff_isNilpotent_maximalIdeal S).mpr h⟩

/-- The items of Tag 00KJ that assert a decomposition of `R` into a finite product of local rings
differ only in the condition imposed on the factors, so a condition-by-condition equivalence of
two such conditions turns one item into the other. -/
private theorem exists_pi_isLocalRing_congr {R : Type u} [CommRing R]
    (P Q : (S : Type u) → [CommRing S] → [IsLocalRing S] → Prop)
    (h : ∀ (S : Type u) [CommRing S] [IsLocalRing S], P S ↔ Q S) :
    (∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (hS : ∀ i, CommRing (S i))
        (hL : ∀ i, IsLocalRing (S i)), (∀ i, @P (S i) (hS i) (hL i)) ∧
          Nonempty (R ≃+* ∀ i, S i)) ↔
      ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (hS : ∀ i, CommRing (S i))
        (hL : ∀ i, IsLocalRing (S i)), (∀ i, @Q (S i) (hS i) (hL i)) ∧
          Nonempty (R ≃+* ∀ i, S i) :=
  exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun hS ↦
    exists_congr fun hL ↦ and_congr_left' <| forall_congr' fun i ↦ @h _ (hS i) (hL i)

/-- For a commutative ring `R` the following are equivalent: `R` is Artinian; `R` is Noetherian of
Krull dimension zero; `R` has finite length as a module over itself; `R` is a finite product of
Artinian local rings; `R` is Noetherian with discrete prime spectrum; `R` is a finite product of
Noetherian local rings of Krull dimension zero; `R` is a finite product of local rings each of
finite length over itself; `R` is a finite product of Noetherian local rings with nilpotent
maximal ideal; `R` is Noetherian with finitely many maximal ideals and nilpotent Jacobson radical;
and `R` is Noetherian with no strict inclusions among its prime ideals. -/
public theorem solution (R : Type u) [CommRing R] :
    List.TFAE
      [ IsArtinianRing R,
        IsNoetherianRing R ∧ Ring.KrullDimLE 0 R,
        IsFiniteLength R R,
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsArtinianRing (S i)) ∧ Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ DiscreteTopology (PrimeSpectrum R),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsNoetherianRing (S i) ∧ Ring.KrullDimLE 0 (S i)) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsFiniteLength (S i) (S i)) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)),
          (∀ i, IsNoetherianRing (S i) ∧ IsNilpotent (IsLocalRing.maximalIdeal (S i))) ∧
            Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ Finite (MaximalSpectrum R) ∧ IsNilpotent (Ring.jacobson R),
        IsNoetherianRing R ∧ ∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q ] := by
  tfae_have 1 ↔ 2 := isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
  tfae_have 1 ↔ 3 := isArtinianRing_iff_isFiniteLength R
  tfae_have 1 → 4 := fun _ ↦
    ⟨MaximalSpectrum R, inferInstance, fun 𝔪 ↦ Localization.AtPrime 𝔪.asIdeal,
      fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
      ⟨RingEquiv.ofBijective _ (MaximalSpectrum.algebraMap_pi_bijective R _)⟩⟩
  tfae_have 4 → 1 := by
    rintro ⟨ι, _, S, _, _, _, ⟨e⟩⟩
    exact e.symm.isArtinianRing
  tfae_have 4 ↔ 6 := exists_pi_isLocalRing_congr (fun S _ _ ↦ IsArtinianRing S)
    (fun S _ _ ↦ IsNoetherianRing S ∧ Ring.KrullDimLE 0 S)
    fun _ _ _ ↦ isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
  tfae_have 4 ↔ 7 := exists_pi_isLocalRing_congr (fun S _ _ ↦ IsArtinianRing S)
    (fun S _ _ ↦ IsFiniteLength S S) fun S _ _ ↦ isArtinianRing_iff_isFiniteLength S
  tfae_have 4 ↔ 8 := exists_pi_isLocalRing_congr (fun S _ _ ↦ IsArtinianRing S)
    (fun S _ _ ↦ IsNoetherianRing S ∧ IsNilpotent (IsLocalRing.maximalIdeal S))
    fun S _ _ ↦ isArtinianRing_iff_isNoetherianRing_and_isNilpotent_maximalIdeal S
  tfae_have 2 ↔ 5 := and_congr_right fun _ ↦
    (discreteTopology_primeSpectrum_iff_krullDimLE_zero R).symm
  tfae_have 5 ↔ 9 := and_congr_right fun _ ↦
    discreteTopology_primeSpectrum_iff_finite_and_isNilpotent_jacobson R
  tfae_have 2 ↔ 10 := and_congr_right' (krullDimLE_zero_iff_forall_isPrime_le_imp_eq R)
  tfae_finish

end Stacks.Artinian.Characterizations

/-!
# Characterizations of Artinian rings

Let `R` be a commutative ring. Being Artinian is a very restrictive condition, and it admits
many equivalent formulations: it is the same thing as being Noetherian of Krull dimension zero,
as having finite length as a module over oneself, as being Noetherian with discrete prime
spectrum, and as being a finite product of local rings each of which is Artinian — equivalently
Noetherian of dimension zero, equivalently of finite length over itself, equivalently Noetherian
with nilpotent maximal ideal. Two further formulations are elementary: Noetherian with finitely
many maximal ideals and nilpotent Jacobson radical, and Noetherian with no strict inclusions
among the prime ideals.

## Main results

* `isArtinianRing_tfae`: the ten characterizations above are equivalent.

## Implementation notes

The source's items (1)–(10) appear in that order in the `List.TFAE`. Four points of form:

The source's dimension condition `dim(R) = 0` is `Ring.KrullDimLE 0 R` rather than
`ringKrullDim R = 0`. The two agree for a nontrivial ring
(`ringKrullDimZero_iff_ringKrullDim_eq_zero`), but the trivial ring is Artinian while its Krull
dimension is `⊥`, so the literal equality would make the equivalence false; `Ring.KrullDimLE`
is also the spelling Mathlib uses for this tag's neighbour [StackProject 00KH].

"`R` is a finite product of local rings with property `P`" is the existence of a finite index
type `ι`, a family of commutative local rings `S i` in the universe of `R` satisfying `P`, and a
ring isomorphism `R ≃+* ∀ i, S i`; this is the shape Mathlib gives such a clause in
`isSemisimpleRing_iff_pi_matrix_divisionRing`, with an arbitrary finite `ι` in place of `Fin n`
so that neither direction has to reindex (the canonical decomposition is indexed by
`MaximalSpectrum R`). Only the existence of a decomposition is asserted, as in the source; the
statement that the *canonical* map `R → ∏_𝔪 R_𝔪` is an isomorphism is the neighbouring
[StackProject 00JA] and [StackProject 00JB], where that map is pinned.

Item (5) asks for a discrete `Spec(R)`, without repeating the source's "finite": the prime
spectrum is quasi-compact, so a discrete `Spec(R)` is automatically finite
(`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`). The finiteness in item (9) is
not automatic and is stated: `ℤ` is Noetherian with nilpotent Jacobson radical `(0)`.

Item (7) asks that each factor be a local ring of finite length over itself, in place of the
source's Noetherian local `R_i` with `d(R_i) = 0`. For a Noetherian local ring the two
conditions agree, and that is Lemma [StackProject 00KI] — the reduction by which the source
proves item (7). The invariant `d` of [StackProject 00KA] is the degree of the Hilbert–Samuel
polynomial and has no definition in this repository, so it cannot be named here; when it
acquires one, that lemma converts between the two forms. Noetherianness of the factors is
implied by finite length and is not repeated in the item.

Faithfulness. (1) The only hypothesis is `CommRing R`, and every one of the ten items is a
condition on that `R`. (2) The base is the source's throughout: `IsFiniteLength R R` is finite
length of `R` as a module over itself, the factors `S i` are rings in the universe of `R`, and
the decomposition is an isomorphism of rings, no auxiliary base ring or localization
intervening. (3) The source asserts the existence of a product decomposition rather than
naming a map, so the product items are existential; the canonical map it does name elsewhere is
pinned in [StackProject 00JB]. (4) The instantiation is not degenerate: `R = ZMod 6` satisfies
all ten items with the decomposition `ZMod 6 ≃+* ZMod 2 × ZMod 3` over a two-element index type,
and `R = ℤ` satisfies none of them.

## References

* [StackProject 00KJ](https://stacks.math.columbia.edu/tag/00KJ)
-/



/-- **Characterizations of Artinian rings.** For a commutative ring `R` the following are
equivalent: `R` is Artinian; `R` is Noetherian of Krull dimension zero; `R` has finite length as
a module over itself; `R` is a finite product of Artinian local rings; `R` is Noetherian with
discrete prime spectrum; `R` is a finite product of Noetherian local rings of dimension zero;
`R` is a finite product of Noetherian local rings of finite length; `R` is a finite product of
Noetherian local rings with nilpotent maximal ideal; `R` is Noetherian with finitely many
maximal ideals and nilpotent Jacobson radical; and `R` is Noetherian with no strict inclusions
among its primes. -/
@[stacks 00KJ "Items (1)-(10); see the module docstring for the form of (2), (5), (6) and (7).",
  ega "0 14.1.9" "affine case: X = Spec R",
  ega "0 16.1.10" "case M = A",
  ega "I 6.2.2" "affine case",
  ega "IV 10.4.3" "partial",
  sga "3 VIIB 0.1.1" "partial",
  sga "3 VIIB 3.2" "U = C"]
public theorem isArtinianRing_tfae (R : Type u) [CommRing R] :
    List.TFAE
      [ IsArtinianRing R,
        IsNoetherianRing R ∧ Ring.KrullDimLE 0 R,
        IsFiniteLength R R,
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsArtinianRing (S i)) ∧ Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ DiscreteTopology (PrimeSpectrum R),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsNoetherianRing (S i) ∧ Ring.KrullDimLE 0 (S i)) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)), (∀ i, IsFiniteLength (S i) (S i)) ∧
            Nonempty (R ≃+* ∀ i, S i),
        ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : ∀ i, IsLocalRing (S i)),
          (∀ i, IsNoetherianRing (S i) ∧ IsNilpotent (IsLocalRing.maximalIdeal (S i))) ∧
            Nonempty (R ≃+* ∀ i, S i),
        IsNoetherianRing R ∧ Finite (MaximalSpectrum R) ∧ IsNilpotent (Ring.jacobson R),
        IsNoetherianRing R ∧ ∀ p q : Ideal R, p.IsPrime → q.IsPrime → p ≤ q → p = q ] :=
    by apply Stacks.Artinian.Characterizations.solution
