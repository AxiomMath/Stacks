module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.Unramified.Locus
public import StacksFrontier.AlgebraicGeometry.Discriminant.DedekindNormDifferent
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.NumberFields
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The different and the discriminant of an extension of number fields

Fix an extension of number fields `L/K` and let `f : Spec(𝒪_L) → Spec(𝒪_K)` be the induced
morphism (Stacks Tag 024Z). The points where `f` is unramified in the sense of schemes are the
points where it is unramified in the conventional sense; the conventional ramification locus in
`Spec(𝒪_L)` is the vanishing set of the different; the discriminant of `L/K` is the norm of the
different, and its vanishing set is the set of primes of `𝒪_K` which ramify in `L`. Off the
different `f` is flat and unramified, hence étale; when `L/K` is Galois, the open `X ⊆ Spec(𝒪_L)`
complementary to the different is the preimage of the open `Y ⊆ Spec(𝒪_K)` complementary to the
discriminant, and `X → Y` is a surjective finite étale morphism, a finite étale covering.

## Main definitions

* `AlgebraicGeometry.differentOpen` and `AlgebraicGeometry.discriminantOpen` are the opens `X`
  and `Y` of the example.

## Main results

* `AlgebraicGeometry.stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff`: the two notions of
  unramifiedness agree at every point of `Spec(𝒪_L)`.
* `AlgebraicGeometry.zeroLocus_differentIdeal`: the vanishing set of the different is the
  conventional ramification locus.
* `AlgebraicGeometry.algebraDiscriminantIdeal_ringOfIntegers_eq_relNorm_differentIdeal`: the
  discriminant is the norm of the different.
* `AlgebraicGeometry.zeroLocus_algebraDiscriminantIdeal`: the vanishing set of the discriminant
  is the set of primes of `𝒪_K` which ramify in `L`.
* `AlgebraicGeometry.flat_ringOfIntegersSpecMap`: `f` is flat.
* `AlgebraicGeometry.stalkwiseUnramified_flat_and_etale_differentOpen`: the morphism
  `X → Spec(𝒪_K)` is unramified, flat and étale.
* `AlgebraicGeometry.isFinite_and_etale_morphismRestrict_discriminantOpen`: in the Galois case
  `X → Y` is a surjective finite étale morphism.

## Implementation notes

The different is Mathlib's `differentIdeal`, the Dedekind different, the inverse of the trace
dual. The discriminant is the discriminant ideal
`Stacks.Discriminant.algebraDiscriminantIdeal` of the finite locally free algebra `𝒪_L` over
`𝒪_K`, the zeroth Fitting ideal of the cokernel of the trace pairing, which cuts out the
discriminant of the finite locally free morphism `f`. That it is the norm of the different is
`Stacks.Discriminant.algebraDiscriminantIdeal_eq_relNorm_differentIdeal`, proved for any finite
separable extension of Dedekind domains. The remaining assertion of the example, that the
different is the annihilator of `Ω[𝒪_L⁄𝒪_K]`, is
`NumberField.differentIdeal_eq_annihilator_kaehlerDifferential_general`.

The conventional notion of an unramified prime is ramification index one together with a
separable residue field extension, at a nonzero prime; at the generic point there is nothing to
ramify. Unramifiedness in the sense of schemes is `AlgebraicGeometry.StalkwiseUnramifiedAt`.

The open subscheme `X ⊆ Spec(𝒪_L)` is the complement of the vanishing set of the different, and
`X → Spec(𝒪_K)` is the composite `(differentOpen K L).ι ≫ f`. The morphism `X → Y` of the Galois
case is `f ∣_ Y`, whose source is `f ⁻¹ᵁ Y`; in the Galois case `f ⁻¹ᵁ Y = X`.

Flatness is global, and is obtained from the fact that a torsion-free module over a Dedekind
domain is flat. The source's reason, that any local homomorphism of discrete valuation rings is
flat, is false as written — the composite of a discrete valuation ring onto its residue field `κ`
with `κ → κ⟦X⟧` is a local homomorphism of discrete valuation rings which is not flat — and holds
for injective ones: `RingHom.Flat.of_injective_of_isDiscreteValuationRing` and
`IsDiscreteValuationRing.not_flat_residue_powerSeries`.

## References

* [The Stacks Project, Tag 024Z](https://stacks.math.columbia.edu/tag/024Z)
-/

@[expose] public section

open CategoryTheory NumberField PrimeSpectrum

namespace AlgebraicGeometry

universe u

noncomputable section

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The morphism on spectra of rings of integers is finite. -/
instance : IsFinite (ringOfIntegersSpecMap K L) :=
  (IsFinite.SpecMap_iff _).2 (IsIntegralClosure.finite (𝓞 K) K L (𝓞 L))

/-- The morphism on spectra of rings of integers is flat. -/
@[stacks 024Z "the morphism Spec(O_L) -> Spec(O_K) is flat (on all of Spec(O_L), so in \
particular on X)"]
instance flat_ringOfIntegersSpecMap : Flat (ringOfIntegersSpecMap K L) :=
  (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The points of `Spec(𝒪_L)` where `f : Spec(𝒪_L) → Spec(𝒪_K)` is unramified in the sense of
schemes are the points where it is unramified in the conventional sense: the generic point, and the
nonzero primes with ramification index one and separable residue field extension. -/
@[stacks 024Z "the points where f is unramified in our sense are the points where f is \
unramified in the conventional sense, at every point of Spec(O_L)"]
theorem stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff (q : PrimeSpectrum (𝓞 L)) :
    StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L) q ↔
      (q.asIdeal ≠ ⊥ →
        (letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under (𝓞 K)) q.asIdeal
         Ideal.ramificationIdx q.asIdeal (𝓞 K) = 1 ∧
          Algebra.IsSeparable (q.asIdeal.under (𝓞 K)).ResidueField q.asIdeal.ResidueField)) := by
  by_cases hq : q.asIdeal = ⊥
  · obtain ⟨Q, hQ⟩ := q
    change Q = ⊥ at hq
    subst hq
    exact iff_of_true (unramifiedAt_genericPoint K L) fun h => absurd rfl h
  · exact (unramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable K L q hq).trans
      ⟨fun h _ => h, fun h => h hq⟩

/-- Scheme-theoretic unramifiedness of `Spec(𝒪_L) → Spec(𝒪_K)` at a point is unramifiedness of
the algebra `𝒪_L` over `𝒪_K` at the corresponding prime. -/
theorem stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff_isUnramifiedAt
    (q : PrimeSpectrum (𝓞 L)) :
    StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L) q ↔
      Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal := by
  rw [stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff]
  by_cases hq : q.asIdeal = ⊥
  · obtain ⟨Q, hQ⟩ := q
    change Q = ⊥ at hq
    subst hq
    exact iff_of_true (fun h => absurd rfl h) Algebra.isUnramifiedAt_bot
  · let p := q.asIdeal.under (𝓞 K)
    let : Finite (𝓞 K ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.under_ne_bot _ hq)
    let : PerfectField p.ResidueField := inferInstance
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver p q.asIdeal
    let : IsScalarTower (𝓞 K) (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
      inferInstance
    exact ⟨fun h => (Ideal.ramificationIdx_eq_one_iff (q := q.asIdeal)).1 (h hq).1,
      fun h _ => ⟨(Ideal.ramificationIdx_eq_one_iff (q := q.asIdeal)).2 h, inferInstance⟩⟩

/-- At a prime where the algebra of rings of integers is unramified, the morphism on spectra is
étale: it is flat everywhere, and essentially of finite type on local rings. -/
theorem isEtaleAt_ringOfIntegersSpecMap_of_isUnramifiedAt
    (q : PrimeSpectrum (𝓞 L)) (hq : Algebra.IsUnramifiedAt (𝓞 K) q.asIdeal) :
    IsEtaleAt (ringOfIntegersSpecMap K L) q :=
  ⟨Flat.stalkMap (ringOfIntegersSpecMap K L) q,
    (stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff_isUnramifiedAt K L q).2 hq,
    LocallyOfFiniteType.stalkMap (ringOfIntegersSpecMap K L) q⟩

section Different

attribute [local instance] FractionRing.liftAlgebra

/-- The vanishing set of the different is the complement of the unramified locus of the algebra
`𝒪_L` over `𝒪_K`. -/
theorem zeroLocus_differentIdeal_eq_compl_unramifiedLocus :
    zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) =
      (Algebra.unramifiedLocus (𝓞 K) (𝓞 L))ᶜ := by
  ext q
  rw [mem_zeroLocus, SetLike.coe_subset_coe, ← Ideal.dvd_iff_le, dvd_differentIdeal_iff]
  rfl

/-- The vanishing set of the different is the set of points where `Spec(𝒪_L) → Spec(𝒪_K)` is not
unramified in the sense of schemes. -/
theorem zeroLocus_differentIdeal_eq_setOf_not_stalkwiseUnramifiedAt :
    zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) =
      {q : PrimeSpectrum (𝓞 L) | ¬ StalkwiseUnramifiedAt (ringOfIntegersSpecMap K L) q} := by
  rw [zeroLocus_differentIdeal_eq_compl_unramifiedLocus]
  ext q
  exact (not_congr (stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff_isUnramifiedAt K L q)).symm

/-- In the conventional sense, the locus of ramification in `Spec(𝒪_L)` is the vanishing set of the
different: a point of `Spec(𝒪_L)` lies in the vanishing set of the different exactly when it is a
nonzero prime whose ramification index is not one or whose residue field extension is not
separable. -/
@[stacks 024Z "in the conventional sense, the locus of ramification in Spec(O_L) is the \
vanishing set of the different"]
theorem zeroLocus_differentIdeal :
    zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) =
      {q | q.asIdeal ≠ ⊥ ∧
        ¬ (letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under (𝓞 K)) q.asIdeal
           Ideal.ramificationIdx q.asIdeal (𝓞 K) = 1 ∧
            Algebra.IsSeparable (q.asIdeal.under (𝓞 K)).ResidueField
              q.asIdeal.ResidueField)} := by
  rw [zeroLocus_differentIdeal_eq_setOf_not_stalkwiseUnramifiedAt]
  ext q
  exact (not_congr (stalkwiseUnramifiedAt_ringOfIntegersSpecMap_iff K L q)).trans not_imp

/-- Removing the closed subset defined by the different from `Spec(𝒪_L)` leaves an open subscheme
on which the morphism to `Spec(𝒪_K)` is étale. -/
@[sga "1 I 9.12" "special case"]
theorem isEtaleAt_of_notMem_zeroLocus_differentIdeal (q : PrimeSpectrum (𝓞 L))
    (hq : q ∉ zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L))) :
    IsEtaleAt (ringOfIntegersSpecMap K L) q := by
  refine isEtaleAt_ringOfIntegersSpecMap_of_isUnramifiedAt K L q ?_
  rw [zeroLocus_differentIdeal_eq_compl_unramifiedLocus] at hq
  have h : q ∈ Algebra.unramifiedLocus (𝓞 K) (𝓞 L) := by simpa using hq
  exact h

/-- The discriminant of `L/K`, an ideal of `𝒪_K` — the discriminant ideal of the finite locally
free algebra `𝒪_L` over `𝒪_K`, the zeroth Fitting ideal of the cokernel of its trace pairing — is
the norm of the different. -/
@[stacks 024Z "the discriminant is an ideal in O_K, namely it is the norm of the different"]
theorem algebraDiscriminantIdeal_ringOfIntegers_eq_relNorm_differentIdeal :
    Stacks.Discriminant.algebraDiscriminantIdeal (𝓞 K) (𝓞 L) =
      Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L)) :=
  Stacks.Discriminant.algebraDiscriminantIdeal_eq_relNorm_differentIdeal (𝓞 K) (𝓞 L)

/-- A nonzero prime of the base divides the relative norm of a nonzero ideal exactly when some
prime above it divides that ideal. -/
@[sga "3 V 4.1.1" "special case"]
private theorem dvd_relNorm_iff_exists_liesOver
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) (I : Ideal (𝓞 L)) (hI : I ≠ ⊥) :
    p ∣ Ideal.relNorm (𝓞 K) I ↔
      ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver p ∧ P ∣ I := by
  classical
  have hpm : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  have hpp : Prime p := Ideal.prime_of_isPrime hp inferInstance
  constructor
  · intro h
    have key : ∀ s : Multiset (Ideal (𝓞 L)), (∀ Q ∈ s, Prime Q) →
        p ∣ Ideal.relNorm (𝓞 K) s.prod → ∃ Q ∈ s, Q.LiesOver p := by
      intro s
      induction s using Multiset.induction_on with
      | empty =>
        intro _ hdvd
        rw [Multiset.prod_zero, map_one] at hdvd
        exact absurd (Ideal.isUnit_iff.mp (isUnit_of_dvd_one hdvd)) hpm.ne_top
      | cons Q t ih =>
        intro hs hdvd
        rw [Multiset.prod_cons, map_mul] at hdvd
        rcases hpp.dvd_or_dvd hdvd with h1 | h2
        · have hQ : Prime Q := hs Q (Multiset.mem_cons_self _ _)
          have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
          have hQm : Q.IsMaximal := Ideal.IsPrime.isMaximal hQp hQ.ne_zero
          have hqbot : Q.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot _ hQ.ne_zero
          have hqm : (Q.under (𝓞 K)).IsMaximal :=
            Ideal.IsPrime.isMaximal inferInstance hqbot
          rw [Ideal.relNorm_eq_pow_of_isMaximal Q (Q.under (𝓞 K))] at h1
          have hpq : p ∣ Q.under (𝓞 K) := hpp.dvd_of_dvd_pow h1
          have heq : Q.under (𝓞 K) = p := hqm.eq_of_le hpm.ne_top (Ideal.dvd_iff_le.mp hpq)
          exact ⟨Q, Multiset.mem_cons_self _ _, ⟨heq.symm⟩⟩
        · obtain ⟨Q', hQ'mem, hQ'lo⟩ := ih (fun R hR ↦ hs R (Multiset.mem_cons_of_mem hR)) h2
          exact ⟨Q', Multiset.mem_cons_of_mem hQ'mem, hQ'lo⟩
    rw [← Ideal.prod_normalizedFactors_eq_self hI] at h
    obtain ⟨Q, hQmem, hQlo⟩ := key _
      (fun Q hQ ↦ UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ) h
    exact ⟨Q, Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor Q hQmem), hQlo,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQmem⟩
  · rintro ⟨P, hP, hlo, hdvd⟩
    have hPbot : P ≠ ⊥ := by
      rintro rfl
      rw [← Ideal.zero_eq_bot, zero_dvd_iff, Ideal.zero_eq_bot] at hdvd
      exact hI hdvd
    have hPm : P.IsMaximal := hP.isMaximal hPbot
    have h1 : Ideal.relNorm (𝓞 K) P ∣ Ideal.relNorm (𝓞 K) I := map_dvd _ hdvd
    rw [Ideal.relNorm_eq_pow_of_isMaximal P p] at h1
    exact dvd_trans (dvd_pow_self p (Ideal.inertiaDeg_pos P (𝓞 K)).ne') h1

/-- The vanishing set of the discriminant is the image in `Spec(𝒪_K)` of the vanishing set of the
different. -/
theorem zeroLocus_algebraDiscriminantIdeal_eq_image :
    zeroLocus (Stacks.Discriminant.algebraDiscriminantIdeal (𝓞 K) (𝓞 L) : Set (𝓞 K)) =
      comap (algebraMap (𝓞 K) (𝓞 L)) ''
        zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) := by
  have hd : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  rw [algebraDiscriminantIdeal_ringOfIntegers_eq_relNorm_differentIdeal]
  ext p
  rw [mem_zeroLocus, SetLike.coe_subset_coe, ← Ideal.dvd_iff_le]
  rcases eq_or_ne p.asIdeal ⊥ with hp | hp
  · constructor
    · intro hcon
      rw [hp, ← Ideal.zero_eq_bot, zero_dvd_iff, Ideal.zero_eq_bot,
        Ideal.relNorm_eq_bot_iff] at hcon
      exact absurd hcon hd
    · rintro ⟨q, hq, rfl⟩
      have hqd : differentIdeal (𝓞 K) (𝓞 L) ≤ q.asIdeal := hq
      have hq0 : q.asIdeal ≠ ⊥ := fun h => hd (le_bot_iff.mp (h ▸ hqd))
      exact absurd hp (Ideal.under_ne_bot _ hq0)
  · rw [dvd_relNorm_iff_exists_liesOver K L p.asIdeal hp _ hd]
    constructor
    · rintro ⟨P, hP, hlo, hdvd⟩
      refine ⟨⟨P, hP⟩, Ideal.dvd_iff_le.mp hdvd, ?_⟩
      ext1
      exact hlo.over.symm
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.asIdeal, q.isPrime, ⟨rfl⟩, Ideal.dvd_iff_le.mpr hq⟩

/-- The vanishing set of the discriminant is precisely the set of points of `Spec(𝒪_K)` which
ramify in `L`: the primes of `𝒪_K` lying under a nonzero prime of `𝒪_L` whose ramification index is
not one or whose residue field extension is not separable. -/
@[stacks 024Z "the vanishing set of the discriminant is precisely the set of points of \
Spec(O_K) which ramify in L"]
theorem zeroLocus_algebraDiscriminantIdeal :
    zeroLocus (Stacks.Discriminant.algebraDiscriminantIdeal (𝓞 K) (𝓞 L) : Set (𝓞 K)) =
      {p | ∃ q : PrimeSpectrum (𝓞 L), comap (algebraMap (𝓞 K) (𝓞 L)) q = p ∧
        q.asIdeal ≠ ⊥ ∧
        ¬ (letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under (𝓞 K)) q.asIdeal
           Ideal.ramificationIdx q.asIdeal (𝓞 K) = 1 ∧
            Algebra.IsSeparable (q.asIdeal.under (𝓞 K)).ResidueField
              q.asIdeal.ResidueField)} := by
  rw [zeroLocus_algebraDiscriminantIdeal_eq_image, zeroLocus_differentIdeal]
  ext p
  exact ⟨fun ⟨q, hq, h⟩ => ⟨q, h, hq⟩, fun ⟨q, h, hq⟩ => ⟨q, hq, h⟩⟩

/-- `X`: the complement in `Spec(𝒪_L)` of the closed subset defined by the different. -/
def differentOpen : (Scheme.Spec.obj (Opposite.op (CommRingCat.of (𝓞 L)))).Opens :=
  ⟨(zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)))ᶜ,
    (isClosed_zeroLocus _).isOpen_compl⟩

/-- `Y`: the complement in `Spec(𝒪_K)` of the closed subset defined by the discriminant. -/
def discriminantOpen : (Scheme.Spec.obj (Opposite.op (CommRingCat.of (𝓞 K)))).Opens :=
  ⟨(zeroLocus (Stacks.Discriminant.algebraDiscriminantIdeal (𝓞 K) (𝓞 L) : Set (𝓞 K)))ᶜ,
    (isClosed_zeroLocus _).isOpen_compl⟩

/-- Denote by `X` the complement of the closed subset defined by the different in `Spec(𝒪_L)`. The
morphism `X → Spec(𝒪_K)` is unramified; it is furthermore flat, and hence it is actually étale. -/
@[stacks 024Z "the morphism X -> Spec(O_K) is unramified, flat, and hence etale"]
theorem stalkwiseUnramified_flat_and_etale_differentOpen :
    StalkwiseUnramified ((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L) ∧
      Flat ((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L) ∧
        Etale ((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L) := by
  have hetale : Etale ((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L) := by
    rw [etale_iff_forall_isEtaleAt]
    intro x
    have hx : (x.1 : PrimeSpectrum (𝓞 L)) ∉
        zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) := x.2
    have h := isEtaleAt_of_notMem_zeroLocus_differentIdeal K L x.1 hx
    have hiso : IsIso ((differentOpen K L).ι.stalkMap x) := inferInstance
    change (((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L).stalkMap x).hom.Flat ∧
      (((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L).stalkMap x).hom.FormallyUnramified ∧
      (((differentOpen K L).ι ≫ ringOfIntegersSpecMap K L).stalkMap x).hom.EssFiniteType
    rw [Scheme.Hom.stalkMap_comp]
    exact ⟨(@RingHom.RespectsIso.cancel_right_isIso _ RingHom.Flat.respectsIso _ _ _
        (ringOfIntegersSpecMap K L |>.stalkMap x.1) ((differentOpen K L).ι.stalkMap x)
        hiso).mpr h.1,
      (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.FormallyUnramified.respectsIso _ _ _
        (ringOfIntegersSpecMap K L |>.stalkMap x.1) ((differentOpen K L).ι.stalkMap x)
        hiso).mpr h.2.1,
      (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.EssFiniteType.respectsIso _ _ _
        (ringOfIntegersSpecMap K L |>.stalkMap x.1) ((differentOpen K L).ι.stalkMap x)
        hiso).mpr h.2.2⟩
  exact ⟨⟨fun x ↦ ((etale_iff_forall_isEtaleAt _).mp hetale x).2.1⟩,
    (Etale.iff_flat_and_formallyUnramified.mp hetale).1, hetale⟩

/-- In a Galois extension, if one prime of `𝒪_L` above a prime of `𝒪_K` is unramified then so
is every prime above it: the Galois group permutes them transitively, so they share their
ramification index. -/
theorem isUnramifiedIn_of_isUnramifiedAt_of_isGalois [IsGalois K L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (h : Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Algebra.IsUnramifiedIn (𝓞 L) (Q.under (𝓞 K)) := by
  intro P hP hlo
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · exact Algebra.isUnramifiedAt_bot
  let _ : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  have _ : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hQu : Q.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot _ hQ
  have hPu : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot _ hPbot
  let _ : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ring.HasFiniteQuotients.finiteQuotient hQu
  let _ : Finite (𝓞 K ⧸ P.under (𝓞 K)) := Ring.HasFiniteQuotients.finiteQuotient hPu
  let _ : PerfectField (Q.under (𝓞 K)).ResidueField := inferInstance
  let _ : PerfectField (P.under (𝓞 K)).ResidueField := inferInstance
  refine Ideal.ramificationIdx_eq_one_iff.1 ?_
  rw [← Ideal.ramificationIdx_eq_of_isGaloisGroup (Q.under (𝓞 K)) Q P (L ≃ₐ[K] L)]
  exact Ideal.ramificationIdx_eq_one_iff.2 h

/-- In the Galois case the vanishing set of the different is the preimage of the vanishing set
of the discriminant. -/
theorem zeroLocus_differentIdeal_eq_preimage_of_isGalois [IsGalois K L] :
    zeroLocus (differentIdeal (𝓞 K) (𝓞 L) : Set (𝓞 L)) =
      comap (algebraMap (𝓞 K) (𝓞 L)) ⁻¹'
        zeroLocus (Stacks.Discriminant.algebraDiscriminantIdeal (𝓞 K) (𝓞 L) : Set (𝓞 K)) := by
  rw [zeroLocus_algebraDiscriminantIdeal_eq_image]
  refine Set.Subset.antisymm (Set.subset_preimage_image _ _) ?_
  rintro Q ⟨P, hP, hPQ⟩
  rw [zeroLocus_differentIdeal_eq_compl_unramifiedLocus] at hP ⊢
  intro hQ
  apply hP
  have hP0 : P.asIdeal ≠ ⊥ := by
    intro h0
    apply hP
    obtain ⟨P', hP'⟩ := P
    change P' = ⊥ at h0
    subst h0
    exact Algebra.isUnramifiedAt_bot
  have hQ0 : Q.asIdeal ≠ ⊥ := by
    intro h0
    have h1 : (comap (algebraMap (𝓞 K) (𝓞 L)) Q).asIdeal = ⊥ := by
      rw [comap_asIdeal, h0, Ideal.comap_bot_of_injective _
        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
    rw [← hPQ] at h1
    exact Ideal.under_ne_bot _ hP0 h1
  have hin := isUnramifiedIn_of_isUnramifiedAt_of_isGalois K L Q.asIdeal hQ0 hQ
  have hunder : Q.asIdeal.under (𝓞 K) = P.asIdeal.under (𝓞 K) :=
    (congrArg PrimeSpectrum.asIdeal hPQ).symm
  rw [hunder] at hin
  exact hin P.asIdeal P.isPrime ⟨rfl⟩

/-- In the Galois case `X` is the preimage of `Y`. -/
theorem preimage_discriminantOpen_of_isGalois [IsGalois K L] :
    ringOfIntegersSpecMap K L ⁻¹ᵁ discriminantOpen K L = differentOpen K L :=
  TopologicalSpace.Opens.ext <| Set.ext fun x =>
    not_congr (Set.ext_iff.mp (zeroLocus_differentIdeal_eq_preimage_of_isGalois K L) x).symm

/-- The morphism `X → Y` is étale, because it is étale at every point of `X`. -/
theorem etale_morphismRestrict_discriminantOpen [IsGalois K L] :
    Etale (ringOfIntegersSpecMap K L ∣_ discriminantOpen K L) := by
  rw [etale_iff_forall_isEtaleAt]
  intro x
  have hx : (x.1 : PrimeSpectrum (𝓞 L)) ∈ differentOpen K L := by
    rw [← preimage_discriminantOpen_of_isGalois K L]
    exact x.2
  have h := isEtaleAt_of_notMem_zeroLocus_differentIdeal K L x.1 hx
  have e := morphismRestrictStalkMap (ringOfIntegersSpecMap K L) (discriminantOpen K L) x
  exact ⟨(RingHom.Flat.respectsIso.arrow_mk_iso_iff e).mpr h.1,
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff e).mpr h.2.1,
    (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff e).mpr h.2.2⟩

/-- The morphism `Spec(𝒪_L) → Spec(𝒪_K)` is surjective: every prime of `𝒪_K` lies under a prime
of `𝒪_L`, the extension being integral and injective. -/
theorem surjective_ringOfIntegersSpecMap : Surjective (ringOfIntegersSpecMap K L) := by
  rw [surjective_iff]
  intro (p : PrimeSpectrum (𝓞 K))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) p.asIdeal ⊥
    ((Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).le.trans
      bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

/-- The restriction of a surjective morphism over an open of its target is surjective. -/
theorem surjective_morphismRestrict_ringOfIntegersSpecMap
    (U : (Scheme.Spec.obj (Opposite.op (CommRingCat.of (𝓞 K)))).Opens) :
    Surjective (ringOfIntegersSpecMap K L ∣_ U) := by
  have hs := (surjective_iff _).mp (surjective_ringOfIntegersSpecMap K L)
  rw [surjective_iff]
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hs y
  have hxU : x ∈ ringOfIntegersSpecMap K L ⁻¹ᵁ U := show ringOfIntegersSpecMap K L x ∈ U from
    hx ▸ hy
  exact ⟨⟨x, hxU⟩, Subtype.ext ((morphismRestrict_base_coe _ U ⟨x, hxU⟩).trans hx)⟩

/-- If `L/K` is finite Galois and `Y` is the complement of the closed subset defined by the
discriminant in `Spec(𝒪_K)`, then the preimage of `Y` is the complement `X` of the closed subset
defined by the different in `Spec(𝒪_L)`, and `X → Y` is a finite étale morphism, which is moreover
surjective: a finite étale covering. -/
@[stacks 024Z "if L/K is finite Galois, X is the preimage of Y and X -> Y is finite etale (and \
surjective): a finite etale covering"]
theorem isFinite_and_etale_morphismRestrict_discriminantOpen [IsGalois K L] :
    ringOfIntegersSpecMap K L ⁻¹ᵁ discriminantOpen K L = differentOpen K L ∧
      IsFinite (ringOfIntegersSpecMap K L ∣_ discriminantOpen K L) ∧
        Etale (ringOfIntegersSpecMap K L ∣_ discriminantOpen K L) ∧
          Surjective (ringOfIntegersSpecMap K L ∣_ discriminantOpen K L) :=
  ⟨preimage_discriminantOpen_of_isGalois K L, inferInstance,
    etale_morphismRestrict_discriminantOpen K L,
    surjective_morphismRestrict_ringOfIntegersSpecMap K L _⟩

end Different

end

end AlgebraicGeometry
