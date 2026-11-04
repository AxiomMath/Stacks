module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.TameRamification
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksCore.Tactic.StacksAttribute

/-!
# Tame ramification of the standard tamely ramified morphism in codimension one

The standard tamely ramified morphism attached to a ring `A`, an element `f : A` and an
exponent `e` is the spectrum of `C = A[X] / (X ^ e - f)` over `Spec(A)`, and the associated
cover is obtained by inverting `f`; see
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.Basic`. Ramification of that
cover in codimension one is a condition at the generic points of the prime divisors of
`Spec(A)` outside `Spec(A_f)`: the local ring there is a discrete valuation ring `A_p` with
uniformizer `f`, and the condition is that every field factor of the generic fibre of the
cover over that point is tamely ramified with respect to `A_p`.

This file treats the extension at such a point. The base change of `C` along `A → K`, for `K`
the fraction field of the discrete valuation ring, is the Kummer algebra `K[X] / (X ^ e - f)`
of Tag 09EV; since `f` is a uniformizer the polynomial `X ^ e - f` is Eisenstein, so the
generic fibre is a single field factor, and it is tamely ramified with respect to `A`
exactly because `e` is invertible.

## Main definitions

* `AlgebraicGeometry.standardTamelyRamifiedGenericFibreEquiv` identifies the base change
  `K ⊗[A] C` with the Kummer extension `K[f ^ (1 / e)]`.
* `AlgebraicGeometry.standardTamelyRamifiedGenericFibreEquivOne` identifies that base change
  with `K` itself for the exponent `e = 1`.

## Main results

* `AlgebraicGeometry.isDiscreteValuationRing_of_mem_minimalPrimes` derives the discrete
  valuation ring and its uniformizer from the hypotheses of the tag on the base: if `A` is
  Noetherian, `f` is a nonzerodivisor and `A / fA` is reduced, then the localization at a
  minimal prime over `f` is a discrete valuation ring with uniformizer `f`.
* `AlgebraicGeometry.maximalIdeal_eq_span_singleton_of_mem_minimalPrimes` and
  `AlgebraicGeometry.isDomain_of_maximalIdeal_eq_span_singleton` are the two halves of that
  derivation.
* `AlgebraicGeometry.ringChar_residue_coprime_of_isUnit` converts invertibility of `e` in a
  local ring into the residue-characteristic coprimality condition used by Tag 09EV.
* `AlgebraicGeometry.standardTamelyRamifiedGenericFibre_isTamelyRamified` states that the
  generic fibre is tamely ramified with respect to the discrete valuation ring, for `e ≥ 2`.
* `AlgebraicGeometry.isTamelyRamified_self` covers the remaining exponent `e = 1`, where the
  generic fibre is `K`: the trivial extension is tamely ramified.
* `AlgebraicGeometry.exists_two_le_isUnit_natCast` produces the auxiliary exponent used there.
* `AlgebraicGeometry.standardTamelyRamifiedGenericFibreFactor_isTamelyRamified` states the
  condition for every exponent `e ≥ 1` and for every field factor of the generic fibre, which
  is the form in which tameness in codimension one quantifies over the fibre.
* `AlgebraicGeometry.isTamelyRamified_of_algEquiv` transports tameness along a `K`-algebra
  isomorphism, which is what identifies a field factor with the generic fibre.

## Implementation notes

The identification of the generic fibre uses Mathlib's base-change equivalence for adjoining
a root, `AdjoinRoot.tensorAlgEquiv`, followed by `K ⊗[A] A ≃ₐ[K] K`; both are the canonical
maps, so the composite is the canonical base-change isomorphism. The irreducibility of
`X ^ e - f` over `K` and the separability of the resulting extension are not hypotheses: they
are produced from `Irreducible f`, `2 ≤ e` and `IsUnit (e : A)` inside the statement of
`standardTamelyRamifiedGenericFibre_isTamelyRamified`, which is why that statement carries no
instance arguments. They are needed there because the field structure on `K[X] / (X ^ e - f)`,
and the separability required to even state tame ramification, depend on them.

## References

* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
* [Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
* [Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9)
-/

@[expose] public noncomputable section

open Polynomial TensorProduct Stacks.KummerExtension

namespace AlgebraicGeometry

universe u v w

/-! ### The base of a standard tamely ramified morphism

Tag 0EYF assumes that `A` is Noetherian, that `f` is a nonzerodivisor and that `A / fA` is
reduced, and asserts that these hypotheses *imply* that `A_p` is a discrete valuation ring with
uniformizer `f` for every minimal prime `p` over `f`. That implication is proved here, so that
the discrete valuation ring and the uniformizer used in the tameness statements below are
produced from the hypotheses of the tag rather than assumed. -/

section MinimalPrime

/-- A Noetherian local ring whose maximal ideal is generated by a single nonzerodivisor is a
domain. By the Krull intersection theorem the powers of the maximal ideal meet in `0`, so every
nonzero element is a unit times a power of the generator; a product of two such elements is
again one, because the generator is a nonzerodivisor. -/
public theorem isDomain_of_maximalIdeal_eq_span_singleton {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {π : R} (hπ : π ∈ nonZeroDivisors R)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    IsDomain R := by
  classical
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ n = Ideal.span {π ^ n} := fun n => by
    rw [hm, Ideal.span_singleton_pow]
  have hbot : ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have key : ∀ x : R, x ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, x ∉ IsLocalRing.maximalIdeal R ^ n := by
      by_contra h
      push Not at h
      have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n := (Submodule.mem_iInf _).mpr h
      rw [hbot] at hmem
      exact hx (by simpa using hmem)
    have hN : x ∉ IsLocalRing.maximalIdeal R ^ Nat.find hex := Nat.find_spec hex
    have hN0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, pow_zero, Ideal.one_eq_top] at hN
      exact hN Submodule.mem_top
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hxk : x ∈ IsLocalRing.maximalIdeal R ^ k := by
      by_contra hcon
      have hle : Nat.find hex ≤ k := Nat.find_le hcon
      omega
    rw [hpow] at hxk
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxk
    refine ⟨k, a, ?_, by rw [← ha]; ring⟩
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hamem
    rw [hm, Ideal.mem_span_singleton'] at hamem
    obtain ⟨b, hb⟩ := hamem
    rw [hk, hpow] at hN
    exact hN (Ideal.mem_span_singleton'.mpr ⟨b, by rw [← ha, ← hb]; ring⟩)
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨n, u, hu, rfl⟩ := key a hcon.1
    obtain ⟨m, v, hv, rfl⟩ := key b hcon.2
    refine (hu.mul hv).ne_zero ((mem_nonZeroDivisors_iff.mp (pow_mem hπ (n + m))).2 (u * v) ?_)
    linear_combination hab
  exact NoZeroDivisors.to_isDomain R

variable {A : Type u} [CommRing A]

/-- The maximal ideal of the localization of `A` at a minimal prime `p` over `f` is generated by
the image of `f`. The radical of `f A_p` is the maximal ideal because `p` is minimal over `f`,
and `f A_p` is already radical because `A / fA` is reduced. -/
public theorem maximalIdeal_eq_span_singleton_of_mem_minimalPrimes {f : A}
    (hred : _root_.IsReduced (A ⧸ Ideal.span ({f} : Set A)))
    {p : Ideal A} [p.IsPrime] (hp : p ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p] [IsLocalRing S] :
    IsLocalRing.maximalIdeal S = Ideal.span {algebraMap A S f} := by
  have hrad : (Ideal.span ({f} : Set A)).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr hred
  have h1 : ((Ideal.span ({f} : Set A)).map (algebraMap A S)).radical
      = p.map (algebraMap A S) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := S) p _ hp
  have h2 : ((Ideal.span ({f} : Set A)).map (algebraMap A S)).radical
      = (Ideal.span ({f} : Set A)).map (algebraMap A S) := by
    rw [← IsLocalization.map_radical p.primeCompl S, Ideal.radical_eq_iff.mpr hrad]
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p S, ← h1, h2, Ideal.map_span,
    Set.image_singleton]

/-- **Tag 0EYF, the base of the standard tamely ramified morphism.** Let `A` be a Noetherian
ring, let `f : A` be a nonzerodivisor such that `A / fA` is reduced, and let `p` be a minimal
prime over `f`. Then the localization `A_p` is a discrete valuation ring and `f` is a
uniformizer of it. This is the implication asserted in the first sentences of the tag; it is
what licenses the discrete valuation ring hypotheses in the tameness statements below. -/
@[stacks 0EYF "the hypotheses on the base imply that A_p is a DVR with uniformizer f, for every \
minimal prime p over f"]
public theorem isDiscreteValuationRing_of_mem_minimalPrimes [IsNoetherianRing A] {f : A}
    (hf : f ∈ nonZeroDivisors A) (hred : _root_.IsReduced (A ⧸ Ideal.span ({f} : Set A)))
    {p : Ideal A} [p.IsPrime] (hp : p ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p] :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible (algebraMap A S f) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S ‹_›
  have hm := maximalIdeal_eq_span_singleton_of_mem_minimalPrimes hred hp S
  have hfS : algebraMap A S f ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap (S := S) p.primeCompl hf
  have : IsDomain S := isDomain_of_maximalIdeal_eq_span_singleton hfS hm
  have hne : algebraMap A S f ≠ 0 := nonZeroDivisors.ne_zero hfS
  have hnf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hne
  exact ⟨‹_›, ((IsDiscreteValuationRing.TFAE S hnf).out 5 1).mp
      (⟨algebraMap A S f, hm⟩ : (IsLocalRing.maximalIdeal S).IsPrincipal),
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hm⟩

end MinimalPrime

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The residue characteristic of a local ring, when nonzero, is prime. -/
private theorem prime_ringChar_residue {R : Type*} [CommRing R] [IsLocalRing R]
    (h0 : ringChar (R ⧸ IsLocalRing.maximalIdeal R) ≠ 0) :
    (ringChar (R ⧸ IsLocalRing.maximalIdeal R)).Prime := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have := ringChar.charP (R ⧸ IsLocalRing.maximalIdeal R)
  exact CharP.char_prime_of_ne_zero (R ⧸ IsLocalRing.maximalIdeal R) h0

/-- If `e` is invertible in a local ring `A`, then the residue characteristic of `A` is zero
or prime to `e`. -/
public theorem ringChar_residue_coprime_of_isUnit {R : Type*} [CommRing R] [IsLocalRing R]
    (e : ℕ) (he : IsUnit (e : R)) :
    ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0 ∨
      Nat.Coprime (ringChar (R ⧸ IsLocalRing.maximalIdeal R)) e := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  by_cases h0 : ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hp := prime_ringChar_residue h0
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
  have hzero : ((e : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 :=
    (ringChar.spec _ e).mpr hdvd
  rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) e] at hzero
  exact (he.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))).ne_zero hzero

variable (f : A) (e : ℕ)

/-- The polynomial `X ^ e - f` pushed into `(K ⊗[A] A)[X]`. This is the polynomial whose
root algebra `AdjoinRoot` describes the base change of `A[X] / (X ^ e - f)` along `A → K`. -/
public def kummerPolyTensor : Polynomial (K ⊗[A] A) :=
  (Polynomial.X ^ e - Polynomial.C f).map
    (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := A)).toRingHom

/-- Pushing `kummerPolyTensor` forward along `K ⊗[A] A ≃ₐ[K] K` gives the Kummer polynomial
`X ^ e - f` over `K`. -/
public theorem map_kummerPolyTensor_rid :
    (kummerPolyTensor K f e).map (Algebra.TensorProduct.rid A K K).toRingHom
      = kummerPoly K f e := by
  rw [kummerPolyTensor, Polynomial.map_map, kummerPoly]
  have : ((Algebra.TensorProduct.rid A K K).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := A)).toRingHom)
      = algebraMap A K := by
    ext a
    simp [Algebra.algebraMap_eq_smul_one]
  rw [this]
  simp

/-- **The generic fibre of the standard morphism is the Kummer extension.** Base changing
`C = A[X] / (X ^ e - f)` along `A → K` gives `K[X] / (X ^ e - f)`, i.e. the Kummer algebra
`K[f ^ (1 / e)]` of Tag 09EV. -/
@[stacks 0EYF "standard_cover_generic_fibre"]
public def standardTamelyRamifiedGenericFibreEquiv :
    K ⊗[A] standardTamelyRamifiedAlgebra A f e ≃ₐ[K] K1 K f e :=
  (AdjoinRoot.tensorAlgEquiv (R := A) (T := K) (Polynomial.X ^ e - Polynomial.C f)
      (kummerPolyTensor K f e) rfl).trans
    (AdjoinRoot.mapAlgEquiv (R := K) (Algebra.TensorProduct.rid A K K)
      (kummerPolyTensor K f e) (kummerPoly K f e)
      ⟨1, by simpa using map_kummerPolyTensor_rid K f e⟩)

/-- **Tag 0EYF, tameness in codimension one.** Let `A` be a discrete valuation ring with
uniformizer `f`; this is the local ring of `Spec(A)` at the generic point of a prime divisor
contained in the complement of `Spec(A_f)`. Let `K` be its fraction field and let `e ≥ 2` be
invertible in `A`. The generic fibre of the standard morphism over that point is the field
`K[f ^ (1 / e)] = K[X] / (X ^ e - f)` (`standardTamelyRamifiedGenericFibreEquiv`), and that
field extension of `K` is tamely ramified with respect to `A`. -/
@[stacks 0EYF "the generic fibre of the standard cover at a codimension-one point is tamely \
ramified with respect to the local ring, for an exponent e ≥ 2",
  sga "1 XIII 5.1" "r = 1, tame part"]
public theorem standardTamelyRamifiedGenericFibre_isTamelyRamified
    (hf : Irreducible f) (he : 2 ≤ e) (hinv : IsUnit (e : A)) :
    letI : Fact (Irreducible (kummerPoly K f e)) :=
      ⟨kummerPoly_irreducible K f e (by omega) hf⟩
    letI : Algebra.IsSeparable K (K1 K f e) :=
      isSeparable_K1 K f e he hf (ringChar_residue_coprime_of_isUnit (R := A) e hinv)
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K (K1 K f e) :=
  @isTamelyRamified_K1 A _ _ _ K _ _ _ f e
    ⟨kummerPoly_irreducible K f e (by omega) hf⟩
    (isSeparable_K1 K f e he hf (ringChar_residue_coprime_of_isUnit (R := A) e hinv))
    he hf (ringChar_residue_coprime_of_isUnit (R := A) e hinv)

/-! ### The degenerate exponent `e = 1`

For `e = 1` the algebra `A[X] / (X - f)` is `A` and the standard morphism is an isomorphism,
so its generic fibre at a codimension-one point is `K` itself. Tameness is then the statement
that the trivial extension `K / K` is tamely ramified with respect to `A`, which holds because
a discrete valuation ring always admits a Kummer extension of some exponent invertible in it,
and every intermediate extension of a tamely ramified extension is tamely ramified. -/

/-- A discrete valuation ring admits an exponent `n ≥ 2` that is invertible in it: take `2` in
residue characteristic zero and `p + 1` in residue characteristic `p`. -/
public theorem exists_two_le_isUnit_natCast (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  by_cases h0 : ringChar (R ⧸ IsLocalRing.maximalIdeal R) = 0
  · exact ⟨2, le_refl 2, isUnit_natCast_of_coprime_ringChar 2 two_ne_zero (Or.inl h0)⟩
  have hp := prime_ringChar_residue h0
  refine ⟨ringChar (R ⧸ IsLocalRing.maximalIdeal R) + 1, by have := hp.two_le; omega,
    isUnit_natCast_of_coprime_ringChar _ (by omega) (Or.inr ?_)⟩
  simpa [Nat.Coprime] using Nat.coprime_succ_self_right
    (n := ringChar (R ⧸ IsLocalRing.maximalIdeal R))

/-- **The trivial extension is tamely ramified.** `K / K` is tamely ramified with respect to
the discrete valuation ring `A`. -/
@[stacks 0EYF "trivial_extension_tame"]
public theorem isTamelyRamified_self :
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K K := by
  obtain ⟨n, hn, hunit⟩ := exists_two_le_isUnit_natCast A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let : Fact (Irreducible (kummerPoly K π n)) :=
    ⟨kummerPoly_irreducible K π n (by omega) hπ⟩
  let : Algebra.IsSeparable K (K1 K π n) :=
    isSeparable_K1 K π n hn hπ (ringChar_residue_coprime_of_isUnit (R := A) n hunit)
  exact IsDiscreteValuationRing.isTamelyRamified_of_isTamelyRamified_tower A K K
    (K1 K π n) (standardTamelyRamifiedGenericFibre_isTamelyRamified K π n hπ hn hunit)

/-- **Tag 0EYF, the exponent `e = 1`.** The generic fibre of the standard morphism for `e = 1`
is `K` itself; combined with `isTamelyRamified_self` this is tameness in codimension one for
the degenerate exponent. -/
@[stacks 0EYF "standard_cover_generic_fibre_one"]
public def standardTamelyRamifiedGenericFibreEquivOne :
    K ⊗[A] standardTamelyRamifiedAlgebra A f 1 ≃ₐ[K] K :=
  (standardTamelyRamifiedGenericFibreEquiv K f 1).trans
    ((AdjoinRoot.algEquivOfEq K (kummerPoly K f 1)
        (Polynomial.X - Polynomial.C (algebraMap A K f)) (by rw [kummerPoly, pow_one])).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (algebraMap A K f)))

/-! ### Every field factor of the generic fibre is tamely ramified

Tameness in codimension one is a condition on *every* field factor of the generic fibre of the
cover at the codimension-one point, not only on the generic fibre itself. A field factor is a
field `L` receiving a surjection of `K`-algebras from the generic fibre `K ⊗[A] C`; since the
generic fibre is a single field, such an `L` is `K`-isomorphic to it, and tameness transports
along that isomorphism. -/

/-- Tame ramification with respect to a discrete valuation ring transports along a `K`-algebra
isomorphism of finite separable extensions. -/
public theorem isTamelyRamified_of_algEquiv {M : Type w} [Field M] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [Module.Finite K M] [Algebra.IsSeparable K M]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (σ : M ≃ₐ[K] L)
    (hM : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K M) :
    ∃ (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L),
      IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K L := by
  let : Module.Finite K L := Module.Finite.equiv σ.toLinearEquiv
  let : Algebra.IsSeparable K L := AlgEquiv.Algebra.isSeparable σ
  let : Algebra L M := σ.symm.toRingHom.toAlgebra
  have hmap : (algebraMap L M) = (σ.symm : L →+* M) := rfl
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun k => by
    rw [hmap]
    exact (σ.symm.commutes k).symm
  let : IsScalarTower A L M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hmap, IsScalarTower.algebraMap_apply A K L a,
      IsScalarTower.algebraMap_apply A K M a]
    exact (σ.symm.commutes _).symm
  have hsurj : Function.Surjective (algebraMap L M) := by
    rw [hmap]
    exact σ.symm.surjective
  let : Module.Finite L M := Module.Finite.of_surjective (Algebra.linearMap L M) hsurj
  let : Algebra.IsSeparable L M :=
    AlgEquiv.Algebra.isSeparable
      (AlgEquiv.ofBijective (Algebra.ofId L M) ⟨(algebraMap L M).injective, hsurj⟩)
  exact ⟨‹_›, ‹_›, IsDiscreteValuationRing.isTamelyRamified_of_isTamelyRamified_tower A K L M hM⟩

/-- Tameness of `M` transfers to any field `L` receiving a surjective `K`-algebra map from a
ring `N` that is `K`-isomorphic to `M`. -/
private theorem exists_isTamelyRamified_of_surjective {M : Type w} [Field M] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [Module.Finite K M] [Algebra.IsSeparable K M]
    {N : Type*} [Ring N] [Algebra K N] (τ : N ≃ₐ[K] M)
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (φ : N →ₐ[K] L) (hφ : Function.Surjective φ)
    (hM : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K M) :
    ∃ (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L),
      IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K L :=
  isTamelyRamified_of_algEquiv K
    (AlgEquiv.ofBijective (φ.comp τ.symm.toAlgHom)
      ⟨((φ.comp τ.symm.toAlgHom : M →ₐ[K] L) : M →+* L).injective,
        hφ.comp τ.symm.surjective⟩) hM

/-- **Tag 0EYF, tameness in codimension one for every field factor.** Let `A` be a discrete
valuation ring with uniformizer `f` — by `isDiscreteValuationRing_of_mem_minimalPrimes` this is
the local ring of `Spec(A)` at the generic point of a prime divisor outside `Spec(A_f)` — let
`K` be its fraction field, and let `e ≥ 1` be invertible in `A`. Then every field factor of the
generic fibre `K ⊗[A] C` of the standard cover, that is, every field `L` receiving a surjection
of `K`-algebras from it, is a finite separable extension of `K` which is tamely ramified with
respect to `A`. -/
@[stacks 0EYF "every field factor of the generic fibre of the standard cover at a \
codimension-one point is tamely ramified with respect to the local ring"]
public theorem standardTamelyRamifiedGenericFibreFactor_isTamelyRamified
    (hf : Irreducible f) (he : 1 ≤ e) (hinv : IsUnit (e : A))
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (φ : K ⊗[A] standardTamelyRamifiedAlgebra A f e →ₐ[K] L)
    (hφ : Function.Surjective φ) :
    ∃ (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L),
      IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo A K L := by
  rcases eq_or_lt_of_le he with rfl | h2
  · exact exists_isTamelyRamified_of_surjective K (standardTamelyRamifiedGenericFibreEquivOne K f)
      φ hφ (isTamelyRamified_self K)
  · have he2 : 2 ≤ e := h2
    let : Fact (Irreducible (kummerPoly K f e)) :=
      ⟨kummerPoly_irreducible K f e (by omega) hf⟩
    let : Algebra.IsSeparable K (K1 K f e) :=
      isSeparable_K1 K f e he2 hf (ringChar_residue_coprime_of_isUnit (R := A) e hinv)
    exact exists_isTamelyRamified_of_surjective K (standardTamelyRamifiedGenericFibreEquiv K f e)
      φ hφ (standardTamelyRamifiedGenericFibre_isTamelyRamified K f e hf he2 hinv)

end

end AlgebraicGeometry
