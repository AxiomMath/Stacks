module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.KrullDimension.Polynomial

public import StacksFrontier.RingTheory.NoetherNormalization
public import StacksFrontier.RingTheory.RegularRing.Dimension
import StacksCore.Tactic.EgaSgaAttribute

universe u v w x

@[expose] public section

/-!
# Dimension of a finite type domain over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type which is a domain and let `K` be its
field of fractions. This file proves Stacks 00P0: the Krull dimension of `S` is the transcendence
degree of `K` over `k`, and the local ring of `S` at any maximal ideal has that same dimension.

Noether normalization (Stacks 00OY) provides an injective finite `k`-algebra map
`P = k[Y_0, …, Y_{r - 1}] → S` with `r = dim S`. Transcendence degree is unchanged along an
algebraic extension of domains, so `trdeg_k K = trdeg_k S = trdeg_k P = r`, which is the first
assertion. For the second, let `𝔪 ⊆ S` be maximal and `𝔮 = 𝔪 ∩ P`. Then `𝔮` is maximal, hence of
height `r`, and `P` is a normal domain, so `P → S` satisfies going down and
`height 𝔪 = height 𝔮 + height 𝔪(S ⧸ 𝔮S) ≥ r` (Stacks 00ON, in Mathlib
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`). The reverse inequality is
`height 𝔪 ≤ dim S = r`.

## Main results

* `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg` (Stacks 00P0):
  `dim S = trdeg_k K`, and `dim S_𝔪 = trdeg_k K` for every maximal ideal `𝔪` of `S`.

## Implementation notes

The transcendence degree computation is `trdeg_eq_natCast_of_isAlgebraic`: for a tower
`R ⊆ S ⊆ A` of rings with `A` a domain algebraic over `S`, a transcendence degree of `S` over `R`
which is a natural number is also the transcendence degree of `A` over `R`. It is
`lift_trdeg_add_eq` (Stacks 030H) together with `trdeg_eq_zero`, with the `Cardinal.lift`s — what
lets the three rings live in three different universes — cancelled inside, since the value is a
natural number. Applied to `k ⊆ P ⊆ S` and then to `k ⊆ S ⊆ K` it computes `trdeg_k K` from
`trdeg_k P = r`, which is `MvPolynomial.trdeg_of_isDomain`.

That every maximal ideal `𝔮` of `P` has height `r` is `height_eq_of_isMaximal_mvPolynomial`,
proved by induction on the number of variables. For `r = 0` the ring is `k`, of dimension `0`. The
step is `height_eq_of_isMaximal_polynomial`: over a Noetherian Jacobson ring `R` all of whose
maximal ideals have height `n`, a maximal ideal `Q` of `R[X]` has height `n + 1`, because its
contraction to `R` is maximal (Zariski's lemma, `Polynomial.isMaximal_comap_C_of_isJacobsonRing`)
and `Polynomial.height_eq_height_add_one` adds the one. It is applied to `𝔮` transported along
`k[Y_0, …, Y_r] ≅ k[Y_0, …, Y_{r - 1}][X]`, heights being invariant under a ring equivalence.

The second half is `height_eq_of_module_finite_mvPolynomial`, stated for a Noetherian domain `S`
carrying a `P = MvPolynomial (Fin r) k`-algebra structure with `Module.Finite P S`,
`FaithfulSMul P S` and `dim S = r` — that is all the normalization is used for. What Stacks 00OY
contributes is that structure: `P` becomes the base of `S` through the algebra structure
`(MvPolynomial.aeval y).toAlgebra`, so that `algebraMap P S` is the map `MvPolynomial.aeval y`
the tag produces, and the tower `k ⊆ P ⊆ S` then holds because `aeval y` is a `k`-algebra map.

Both halves bound a height by a Krull dimension, in the form `height_le_of_ringKrullDim_eq`: a
prime of a ring of dimension `n : ℕ` has height at most `n`, the coercion `ℕ∞ → WithBot ℕ∞` of
`Ideal.height_le_ringKrullDim_of_isPrime` being undone inside.

The source's proof invokes Stacks 00OR — all local rings of `S` at maximal ideals have the same
dimension, read off maximal chains of primes in a regular ring — to reduce the second assertion
to the first. The going down formula for heights along `P → S` (Stacks 00ON) is used in its
place: it is in Mathlib, and it computes `height 𝔪` for one maximal `𝔪` at a time rather than
comparing two of them, so no separate reduction step is needed.

## References

* [StacksProject 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

namespace Stacks.KrullDimension.TranscendenceDegree


open Cardinal in
/-- If `A` is a domain algebraic over `S` and `R ⊆ S ⊆ A` is a tower of rings with injective
structure maps, then a transcendence degree `n : ℕ` of `S` over `R` is also that of `A`
over `R`. -/
private lemma trdeg_eq_natCast_of_isAlgebraic (R : Type*) (S : Type v) (A : Type w)
    [CommRing R] [Nontrivial R] [CommRing S] [CommRing A] [NoZeroDivisors A] [Algebra R S]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A] [FaithfulSMul R S] [FaithfulSMul S A]
    [Algebra.IsAlgebraic S A] {n : ℕ} (h : Algebra.trdeg R S = n) :
    Algebra.trdeg R A = n := by
  have h' := lift_trdeg_add_eq R S A
  rw [trdeg_eq_zero (R := S) (A := A), lift_zero, add_zero, h] at h'
  exact lift_injective.{v} (by simpa using h'.symm)

/-- A prime ideal of a ring of Krull dimension `n : ℕ∞` has height at most `n`. -/
private lemma height_le_of_ringKrullDim_eq {R : Type*} [CommRing R] {n : ℕ∞}
    (h : ringKrullDim R = n) (I : Ideal R) [I.IsPrime] : I.height ≤ n := by
  have h' := Ideal.height_le_ringKrullDim_of_isPrime (I := I)
  rw [h] at h'
  exact_mod_cast h'

open Polynomial in
/-- If every maximal ideal of a Noetherian Jacobson ring `R` has height `n`, then every maximal
ideal of `R[X]` has height `n + 1`. -/
private lemma height_eq_of_isMaximal_polynomial {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {n : ℕ} (hR : ∀ p : Ideal R, p.IsMaximal → p.height = n)
    (Q : Ideal R[X]) [Q.IsMaximal] : Q.height = n + 1 := by
  have hq : (Q.comap (C : R →+* R[X])).IsMaximal := isMaximal_comap_C_of_isJacobsonRing Q
  have : Q.LiesOver (Q.comap (C : R →+* R[X])) := ⟨by rw [Ideal.under_def, algebraMap_eq]⟩
  rw [height_eq_height_add_one (Q.comap (C : R →+* R[X])) Q, hR _ hq]

/-- Every maximal ideal of a polynomial ring in `r` variables over a field has height `r`. -/
private lemma height_eq_of_isMaximal_mvPolynomial (k : Type u) [Field k] {r : ℕ}
    (𝔮 : Ideal (MvPolynomial (Fin r) k)) [𝔮.IsMaximal] : 𝔮.height = r := by
  induction r with
  | zero =>
    simpa using height_le_of_ringKrullDim_eq (n := 0)
      (by simp [ringKrullDim_eq_zero_of_field]) 𝔮
  | succ r ih =>
    have e := (MvPolynomial.finSuccEquiv k r).toRingEquiv
    have : (Ideal.map e 𝔮).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← RingEquiv.height_map e 𝔮, height_eq_of_isMaximal_polynomial fun p hp => @ih p hp]
    push_cast
    ring

/-- Every maximal ideal of a Noetherian domain of Krull dimension `r` which is finite and faithful
over the polynomial algebra in `r` variables over a field has height `r`. -/
private lemma height_eq_of_module_finite_mvPolynomial (k : Type u) [Field k] {r : ℕ} {S : Type v}
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra (MvPolynomial (Fin r) k) S]
    [Module.Finite (MvPolynomial (Fin r) k) S] [FaithfulSMul (MvPolynomial (Fin r) k) S]
    (hdim : ringKrullDim S = r) (𝔪 : Ideal S) [𝔪.IsMaximal] : 𝔪.height = r := by
  have : Algebra.IsIntegral (MvPolynomial (Fin r) k) S := Algebra.IsIntegral.of_finite _ _
  set 𝔮 : Ideal (MvPolynomial (Fin r) k) := 𝔪.comap (algebraMap _ S)
  have : 𝔮.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  have : 𝔪.LiesOver 𝔮 := ⟨rfl⟩
  refine le_antisymm (height_le_of_ringKrullDim_eq hdim 𝔪) ?_
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔮 𝔪,
    height_eq_of_isMaximal_mvPolynomial k 𝔮]
  exact le_self_add

/-- The statement of Stacks 00P0: for a domain `S` of finite type over a field `k` with field of
fractions `K`, `dim S = trdeg_k K`, and the localization of `S` at every maximal ideal has the same
dimension. A Noether normalization `k[Y_0, …, Y_{r - 1}] → S` with `r = dim S` gives
`trdeg_k K = r`, and every maximal ideal of `S` has height `r` by going down. -/
public theorem solution
    (k : Type u) [Field k] (S : Type v) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (K : Type w) [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ringKrullDim S = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal S) [𝔪.IsMaximal] (A : Type x) [CommRing A] [Algebra S A]
          [IsLocalization.AtPrime A 𝔪],
        ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) := by
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k S).FG)
  obtain ⟨r, y, -, hinj, hfin, hdim⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top k t.finite_toSet ht
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
  let inst : Algebra (MvPolynomial (Fin r) k) S := (MvPolynomial.aeval y : _ →ₐ[k] S).toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin r) k) S :=
    IsScalarTower.of_algebraMap_eq fun x => by simp [inst, RingHom.algebraMap_toAlgebra]
  have : Module.Finite (MvPolynomial (Fin r) k) S := hfin
  have : FaithfulSMul (MvPolynomial (Fin r) k) S :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hS : Algebra.trdeg k S = (r : Cardinal.{v}) :=
    trdeg_eq_natCast_of_isAlgebraic k (MvPolynomial (Fin r) k) S
      (by simp [MvPolynomial.trdeg_of_isDomain])
  have htr : Cardinal.toENat (Algebra.trdeg k K) = (r : ℕ∞) := by
    rw [trdeg_eq_natCast_of_isAlgebraic k S K hS]
    simp
  refine ⟨?_, fun 𝔪 _ A _ _ _ => ?_⟩
  · rw [hdim, htr]
    rfl
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 A, htr,
      height_eq_of_module_finite_mvPolynomial k hdim 𝔪]

end Stacks.KrullDimension.TranscendenceDegree

/-!
# Dimension of a finite type domain over a field

Let `k` be a field, let `S` be a `k`-algebra of finite type which is a domain, and let `K` be the
field of fractions of `S`. Then the Krull dimension of `S` is the transcendence degree of `K` over
`k`, and so is the dimension of the local ring of `S` at every maximal ideal (Stacks 00P0).

The proof is the source's: all local rings of `S` at maximal ideals have the same dimension
(Lemma 00OR), so it suffices to compute `dim S`; Noether normalization (Lemma 00OY) produces an
injective finite `k`-algebra map `k[y_1, …, y_d] → S` with `d = dim S`, and a finite extension of
domains induces a finite, hence algebraic, extension `k(y_1, …, y_d) ⊆ K` of fraction fields, so
`trdeg_k K = d`.

## Main results

* `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg`: both assertions of the source,
  for an arbitrary field of fractions `K` of `S` and an arbitrary model of the local ring.

## Implementation notes

`Algebra.trdeg k K` is a `Cardinal` while `ringKrullDim S` lives in `WithBot ℕ∞`, so the equality
is stated through `Cardinal.toENat`. This loses nothing: `Cardinal.toENat` is injective on the
finite cardinals and sends the infinite ones to `⊤`, so the equation says exactly that `dim S` is
the transcendence degree whatever the latter is. That the transcendence degree is in fact finite
is not part of the assertion but comes for free from `trdeg_lt_aleph0`, since `k ⊆ K` is
essentially of finite type (`Algebra.EssFiniteType.of_isLocalization` and
`Algebra.EssFiniteType.comp`).

The field of fractions is an abstract one, `IsFractionRing S K` together with
`IsScalarTower k S K`, rather than the concrete `FractionRing S`, so that the lemma applies to
any other model of `K`, such as the residue field `κ(𝔭)` of a prime of a finite type algebra,
without transporting along `IsLocalization.algEquiv`. For the same reason the local ring is an
abstract `IsLocalization.AtPrime A 𝔪` in its own universe, as in Lemma 00OQ;
`Localization.AtPrime 𝔪` is one instantiation, and `IsLocalization.AtPrime.ringKrullDim_eq_height`
rewrites the second conjunct into the equivalent statement `𝔪.height = trdeg_k K` about `S`
alone.

The source's "finite type `k`-algebra" is `Algebra.FiniteType k S`, and its "integral domain" is
`IsDomain S`, which also supplies the nontriviality that keeps `ringKrullDim S ≠ ⊥`. The two
assertions are carried by one theorem, neither being an instance of the other: the first computes
a global dimension, the second a family of local ones.

Faithfulness. (1) No hypothesis is dead: `Field k` and `Algebra.FiniteType k S` are used by both
conjuncts — for `S = k[x_1, x_2, …]` the dimension is infinite while the transcendence degree of
`K` over `k` is `ℵ₀`, and over the base `ℤ` in place of a field `S = ℤ` has dimension `1` and
`K = ℚ` transcendence degree `0` — `IsDomain S` is the source's "integral domain" and is used by
both, there being no field of fractions and no common dimension of the local rings at maximal
ideals without it (`S = k[x] × k[y, z]` has them of dimensions `1` and `2`), and the scalar tower
is what makes `Algebra.trdeg k K` the transcendence degree of `K` over the *given* `k`-structure
of `S`. (2) The scalars and base are the source's: the transcendence degree is taken
over `k`, of the fraction field of `S` itself, and both Krull dimensions are those of `S` and of
its localizations as `S`-algebras; no base change occurs. (3) The maps the source names are
pinned: `IsFractionRing S K` pins `K` as a localization of `S` at its nonzero divisors along
`algebraMap S K`, and `IsLocalization.AtPrime A 𝔪` pins `A` as the localization of `S` at the
complement of `𝔪`, rather than positing the existence of some field or some local ring of the
right dimension. (4) The instantiation is not degenerate: for `k = ℚ` and `S = ℚ[x]` one has
`K = ℚ(x)`, `trdeg = 1 = dim S`, and every localization at a maximal ideal `(f)` is a discrete
valuation ring, of dimension `1`; for `S = ℚ[x, y]/(y ^ 2 - x ^ 3)` the transcendence degree is
again `1` and the conclusion holds also at the maximal ideal `(x, y)` of the cusp, where the local
ring is not regular. For `S = k` both conjuncts read `0 = 0`, so the statement is consistent but
not vacuous.

## References

* [StacksProject 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

@[expose] public section


/-- **Stacks 00P0.** Let `k` be a field, let `S` be a finite type `k`-algebra which is a domain,
and let `K` be its field of fractions. Then the Krull dimension of `S` is the transcendence
degree of `K` over `k`, and the local ring of `S` at every maximal ideal has that same
dimension. -/
@[stacks 00P0 "The transcendence degree is compared through `Cardinal.toENat`, the field of
fractions is an abstract `IsFractionRing` and the local ring an abstract
`IsLocalization.AtPrime`. See the module docstring.", ega "IV 5.5.8" "special case"]
public theorem ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg
    (k : Type u) [Field k] (S : Type v) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (K : Type w) [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ringKrullDim S = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) ∧
      ∀ (𝔪 : Ideal S) [𝔪.IsMaximal] (A : Type x) [CommRing A] [Algebra S A]
          [IsLocalization.AtPrime A 𝔪],
        ringKrullDim A = (Cardinal.toENat (Algebra.trdeg k K) : WithBot ℕ∞) :=
  Stacks.KrullDimension.TranscendenceDegree.solution k S K

end


/-!
# Finite type domains over a field are equidimensional

Let `k` be a field and let `S` be a `k`-algebra of finite type which is a domain. This file proves
Stacks 00OS: the height of every maximal ideal `𝔪` of `S` equals `dim S`, and every maximal chain
of primes of `S` has length `dim S`.

Write `S = k[x_1, …, x_n]/𝔭` with `𝔭 = ker φ`, `φ : R = k[x_1, …, x_n] → S` the presentation, and
let `Spec φ : Spec S → Spec R` be the induced map. It is an order embedding onto the primes
containing `𝔭`, an upper set, so it takes covering pairs to covering pairs. Two facts about the
image of a chain of primes of `S` under it then bracket the length of the chain, both between
`𝔭` and the image of its top prime:

* an arbitrary chain gains at least its length in height, because height grows by at least one at
  each step of a strictly increasing chain — an order-theoretic inequality, valid in any preorder;
* a chain of covering pairs gains exactly its length, by Stacks 00OR in the regular ring `R`.

A chain of covering pairs of `S` running from `⊥` to a prime whose image has the largest height in
`R` is therefore at least as long as every chain of primes of `S`, that is, its length is `dim S`.
That is `length_eq_ringKrullDim_of_covBy`, and the second assertion of 00OS is its instance at the
presentation: a maximal chain runs from `⊥` to a maximal ideal, whose image is a maximal ideal of
`R`, of height `dim R` by Stacks 00P0 applied to `R` itself.

The first assertion of 00OS — the source's `dim S = dim S_𝔪` — is Stacks 00P0, whose proof is
independent of the second, read through `IsLocalization.AtPrime.ringKrullDim_eq_height`.

## Main results

* `Stacks.KrullDimension.Equidimensional.solution`: the statement of Stacks 00OS.

## Implementation notes

*The source's Proposition 00OQ is not used.* It is invoked for two facts: that `k[x_1, …, x_n]` is
regular, which is `MvPolynomial.isRegularRing_of_isRegularRing` in Mathlib, and that every maximal
ideal of `k[x_1, …, x_n]` has height `n`, which is the second assertion of Stacks 00P0 applied to
`k[x_1, …, x_n]` itself. Neither needs the projective dimension computation of 00OQ.

*The inequality half does not need regularity.* The source deduces it from 00OR, by refining an
arbitrary chain to a chain of covering pairs between the same two primes. That refinement exists
only in a well-founded order, whereas the inequality it is used for holds in any preorder: it is
`length_add_height_head_le_height_last`, proved here by splicing a chain below the head onto the
given chain. So no well-foundedness enters this file.

*Three facts used here are missing from Mathlib.* Besides the order-theoretic inequality above,
these are that a polynomial ring in finitely many variables over a field has finite Krull
dimension (`finiteRingKrullDim_mvPolynomial`) and that `Spec` of a surjective ring map has
order-connected image, hence preserves covering pairs (`covBy_comap_of_surjective`, built from
Mathlib's `Ideal.primeSpectrumOrderIsoZeroLocusOfSurj`).

## References

* [StacksProject 00OS](https://stacks.math.columbia.edu/tag/00OS)
-/



namespace Stacks.KrullDimension.Equidimensional

/-- Height grows by at least one at each step of a strictly increasing chain: the height of the
last term is at least the length of the chain plus the height of the first. -/
private lemma length_add_height_head_le_height_last {α : Type*} [Preorder α] (l : LTSeries α) :
    (l.length : ℕ∞) + Order.height l.head ≤ Order.height l.last := by
  have : Nonempty { p : LTSeries α // p.last = l.head } := ⟨RelSeries.singleton _ _, rfl⟩
  rw [Order.height_eq_iSup_last_eq, iSup_subtype', ENat.add_iSup]
  exact iSup_le fun p ↦ by
    simpa [add_comm] using Order.length_le_height_last (p := p.1.smash l p.2)

/-- `Spec` of a surjective ring map, as an order embedding of prime spectra: Mathlib's
`Ideal.primeSpectrumOrderIsoZeroLocusOfSurj` read in the ambient `Spec R`. -/
private noncomputable def comapOrderEmbedding {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) : PrimeSpectrum S ↪o PrimeSpectrum R :=
  (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f hf rfl).toOrderEmbedding.trans
    (OrderEmbedding.subtype _)

private lemma coe_comapOrderEmbedding {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) :
    (comapOrderEmbedding f hf : PrimeSpectrum S → PrimeSpectrum R) = PrimeSpectrum.comap f := rfl

/-- The image of `Spec` of a surjective ring map is the set of primes containing the kernel, an
upper set, so `Spec` of a surjective ring map takes a covering pair of primes to a covering
pair. -/
private lemma covBy_comap_of_surjective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) {p q : PrimeSpectrum S} (hpq : p ⋖ q) :
    PrimeSpectrum.comap f p ⋖ PrimeSpectrum.comap f q := by
  refine CovBy.image (comapOrderEmbedding f hf) hpq ?_
  have hrange : Set.range (comapOrderEmbedding f hf) =
      PrimeSpectrum.zeroLocus (RingHom.ker f : Set R) := by
    rw [coe_comapOrderEmbedding]
    exact range_comap_of_surjective S f hf
  rw [hrange]
  exact IsUpperSet.ordConnected fun a b hab ha ↦ (PrimeSpectrum.mem_zeroLocus ..).mpr
    (((PrimeSpectrum.mem_zeroLocus ..).mp ha).trans hab)

/-- A polynomial ring in finitely many variables over a field has finite Krull dimension. -/
private lemma finiteRingKrullDim_mvPolynomial (k : Type u) [Field k] (ι : Type*) [Finite ι] :
    FiniteRingKrullDim (MvPolynomial ι k) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add]
  refine ⟨by simp, ?_⟩
  rw [← WithBot.coe_natCast, ← WithBot.coe_top, ne_eq, WithBot.coe_inj]
  exact ENat.natCast_ne_top _

/-- **Stacks 00P0**, read as a statement about heights: in a finite type domain over a field every
maximal ideal has height the dimension of the ring, since `dim S_𝔪 = dim S`. -/
private lemma ringKrullDim_eq_height_of_isMaximal (k : Type u) [Field k] (T : Type v) [CommRing T]
    [IsDomain T] [Algebra k T] [Algebra.FiniteType k T] (𝔪 : Ideal T) [𝔪.IsMaximal] :
    ringKrullDim T = (𝔪.height : WithBot ℕ∞) := by
  obtain ⟨h₁, h₂⟩ :=
    ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg k T (FractionRing T)
  rw [h₁, ← h₂ 𝔪 (Localization.AtPrime 𝔪),
    IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (Localization.AtPrime 𝔪)]

/-- **The heart of Stacks 00OS.** Let `S` be a quotient of a regular ring `R` of finite Krull
dimension, along `f`, and let `t` be a chain of primes of `S` all of whose steps are covering
pairs, running from the zero ideal to a prime whose preimage in `R` has the largest possible
height, `dim R`. Then the length of `t` is `dim S`.

Pushing `t` forward to `R` gives `length t + height (f⁻¹ t.head) = dim R` by Stacks 00OR, while an
arbitrary chain of primes of `S` pushed forward gives `length + height (f⁻¹ t.head) ≤ dim R`;
cancelling the finite `height (f⁻¹ t.head)` shows `t` is at least as long as every chain. -/
private lemma length_eq_ringKrullDim_of_covBy {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [IsRegularRing R] [FiniteRingKrullDim R] (f : R →+* S) (hf : Function.Surjective f)
    (t : RelSeries {(p, q) : PrimeSpectrum S × PrimeSpectrum S | p ⋖ q})
    (hhead : t.head.asIdeal = ⊥)
    (hlast : ((PrimeSpectrum.comap f t.last).asIdeal.height : WithBot ℕ∞) = ringKrullDim R) :
    (t.length : WithBot ℕ∞) = ringKrullDim S := by
  have hB : (PrimeSpectrum.comap f t.last).asIdeal.height
      = t.length + (PrimeSpectrum.comap f t.head).asIdeal.height := by
    simpa using IsRegularRing.height_last_eq_length_add_height_head
      (t.map ⟨PrimeSpectrum.comap f, fun h ↦ covBy_comap_of_surjective f hf h⟩)
  have hfin : (PrimeSpectrum.comap f t.head).asIdeal.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have key : ∀ l : LTSeries (PrimeSpectrum S), l.length ≤ t.length := fun l ↦ by
    have h₁ : (l.length : ℕ∞) + (PrimeSpectrum.comap f t.head).asIdeal.height
        ≤ (PrimeSpectrum.comap f l.last).asIdeal.height :=
      calc (l.length : ℕ∞) + (PrimeSpectrum.comap f t.head).asIdeal.height
          ≤ (l.length : ℕ∞) + (PrimeSpectrum.comap f l.head).asIdeal.height := by
            gcongr
            exact Ideal.comap_mono (hhead.trans_le bot_le)
        _ ≤ (PrimeSpectrum.comap f l.last).asIdeal.height := by
            simp only [PrimeSpectrum.height_eq_orderHeight]
            exact length_add_height_head_le_height_last
              (l.map (PrimeSpectrum.comap f) (RingHom.strictMono_comap_of_surjective hf))
    have h₂ : (PrimeSpectrum.comap f l.last).asIdeal.height
        ≤ (PrimeSpectrum.comap f t.last).asIdeal.height := by
      exact TranscendenceDegree.height_le_of_ringKrullDim_eq hlast.symm _
    have h₃ : (l.length : ℕ∞) + (PrimeSpectrum.comap f t.head).asIdeal.height
        ≤ (t.length : ℕ∞) + (PrimeSpectrum.comap f t.head).asIdeal.height := hB ▸ h₁.trans h₂
    exact Nat.cast_le.mp ((WithTop.add_le_add_iff_right hfin).mp h₃)
  refine le_antisymm (Order.LTSeries.length_le_krullDim (t.ofLE fun _ h ↦ CovBy.lt h)) ?_
  exact iSup_le fun l ↦ by exact_mod_cast key l

/-- The statement of Stacks 00OS: for a domain `S` of finite type over a field `k`, every maximal
ideal of `S` has height `dim S`, and every maximal chain of primes of `S` (a series of covering
pairs from a minimal prime to a maximal ideal) has length `dim S`. The chain is pushed forward to
a presentation `k[x_1, …, x_n] → S`, where heights are additive along covering chains. -/
public theorem solution (k : Type*) [Field k] (S : Type*) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] :
    (∀ (𝔪 : Ideal S) [𝔪.IsMaximal], ringKrullDim S = (𝔪.height : WithBot ℕ∞)) ∧
      ∀ s : RelSeries {(p, q) : PrimeSpectrum S × PrimeSpectrum S | p ⋖ q},
        IsMin s.head → IsMax s.last → (s.length : WithBot ℕ∞) = ringKrullDim S := by
  refine ⟨fun 𝔪 _ ↦ ringKrullDim_eq_height_of_isMaximal k S 𝔪, fun t hmin hmax ↦ ?_⟩
  -- the presentation `S = k[x_1, …, x_n]/𝔭`
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k S›
  have hφ : Function.Surjective (f : MvPolynomial (Fin n) k →+* S) := hf
  have := finiteRingKrullDim_mvPolynomial k (Fin n)
  have : t.last.asIdeal.IsMaximal := PrimeSpectrum.isMax_iff.mp hmax
  have : (PrimeSpectrum.comap (f : MvPolynomial (Fin n) k →+* S) t.last).asIdeal.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hφ
  exact length_eq_ringKrullDim_of_covBy _ hφ t (by simp [hmin.eq_bot])
    (ringKrullDim_eq_height_of_isMaximal k _ _).symm

end Stacks.KrullDimension.Equidimensional

/-!
# Finite type domains over a field are equidimensional

Let `k` be a field and let `S` be a `k`-algebra of finite type which is a domain. Then `S` has
the same dimension everywhere: for every maximal ideal `𝔪` of `S`,
$$
  \dim S = \dim S_𝔪 = \operatorname{height} 𝔪,
$$
and, in words, every maximal chain of primes of `S` — a chain `𝔭_0 ⊊ 𝔭_1 ⊊ ⋯ ⊊ 𝔭_e` which
starts at a minimal prime, ends at a maximal ideal, and admits no refinement, so that consecutive
members are a covering pair `𝔭_i ⋖ 𝔭_{i + 1}` — has length exactly `dim S`. Since `S` is a
domain, such a chain necessarily starts at the zero ideal.

The reason is that `S = k[x_1, …, x_n]/𝔭` for a prime `𝔭`, and in the regular ring
`k[x_1, …, x_n]` every maximal chain of primes between `𝔭` and `𝔮` has length
`height 𝔮 - height 𝔭` (tag 00OR, via tag 00OQ); as maximal ideals of the polynomial ring have
height `n`, every maximal chain of primes of `S` has length `n - height 𝔭`, and this common
value is then both `dim S` and the height of any maximal ideal of `S`.

## Main results

* `Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim`: both
  assertions of the source — `dim S = height 𝔪` for every maximal ideal `𝔪`, and every maximal
  chain of primes of `S` has length `dim S`.

## Implementation notes

*`dim S_𝔪` is written `𝔪.height`.* The Krull dimension of the local ring of `S` at `𝔪` is the
height of `𝔪` for any model of that local ring, by
`IsLocalization.AtPrime.ringKrullDim_eq_height`, so the model-independent `Ideal.height` says the
source's `dim(S_𝔪)` with no localization data in the statement. Reading the conclusion at `A`
with `[IsLocalization.AtPrime A 𝔪]` is that one rewrite.

*Both assertions are kept, as a conjunction.* The source's "in words" clause is formally stronger
than the displayed equality: the equality says that all maximal ideals have height `dim S`,
whereas the clause pins the length of each individual maximal chain. Stating only the equality
would lose that, so both are asserted, of the same `S`, in one theorem.

*Maximal chains are `RelSeries` for the covering relation, with extremal ends.* A maximal chain of
primes of `S` is an `s : RelSeries {(p, q) : PrimeSpectrum S × PrimeSpectrum S | p ⋖ q}` with
`IsMin s.head` and `IsMax s.last`: non-refinability in the middle is the covering relation `⋖`
(the spelling of tag 00OR and of the `Ring.IsCatenary` definition of tag 00NK), and
non-extendability at the two ends is minimality and maximality in `PrimeSpectrum S`. By
`PrimeSpectrum.isMax_iff` the second condition is `s.last.asIdeal.IsMaximal`, and since `S` is a
domain the first is `s.head.asIdeal = ⊥`. `RelSeries.length` counts steps, so the chain
`𝔭_0 ⋖ ⋯ ⋖ 𝔭_e` has length `e`, matching the source's count.

*The dimension is `ringKrullDim`, valued in `WithBot ℕ∞`.* Equating it to a natural number, as
the second assertion does, asserts finiteness of `dim S` along the way, which is part of the
content.

Faithfulness to [StacksProject 00OS].

1. No hypothesis is dead: `Algebra.FiniteType k S` over a field is what makes the dimension
   finite and the ring catenary, and `IsDomain S` is what makes it equidimensional. In the
   non-domain `S = k[x, y, z]/(xy, xz)`, the plane `x = 0` meeting the line `y = z = 0`, we have
   `dim S = 2`, yet the maximal ideal `(x - 1, y, z)` — a point of the line off the plane — has
   height `1`, and the chain from the minimal prime `(y, z)` to `(x, y, z)` is maximal of
   length `1`, so both assertions fail. Neither hypothesis of the source is dropped.
2. The base and the ring are the source's: `k` is a field, `S` is a `k`-algebra of finite type,
   and both the dimension and the heights are computed in `S` itself, not in a polynomial ring
   presenting it nor in a localization.
3. The quantities are pinned rather than asserted to exist: the conclusion is an equation
   determining `𝔪.height` for each maximal `𝔪`, and an equation determining the length of each
   given maximal chain — not a bound, and not the existence of some chain of that length.
4. The instantiation is not degenerate: for `S = k[x, y]` we have `dim S = 2`, every maximal
   ideal has height `2`, and the chain `(0) ⋖ (x) ⋖ (x, y)` has length `2`, so the assertions are
   not about the dimension-zero case only; `S = k` is the degenerate instance, where both read
   `0 = 0`.

## References

* [StacksProject 00OS](https://stacks.math.columbia.edu/tag/00OS)

## Tags

dimension, Krull dimension, height, finite type algebra, maximal chain of primes,
equidimensional, catenary
-/

@[expose] public section

namespace Algebra.FiniteType

/-- **Stacks 00OS.** Let `k` be a field and let `S` be a finite type `k`-algebra which is a
domain. Then `dim S = dim S_𝔪 = height 𝔪` for every maximal ideal `𝔪` of `S`, and every maximal
chain of primes of `S` — one starting at a minimal prime, ending at a maximal ideal, and with all
steps covering pairs — has length `dim S`. -/
@[stacks 00OS "`dim(S_𝔪)` is written `𝔪.height`, the Krull dimension of any model of the local
ring at `𝔪`; the source's \"in words\" clause is kept as a second conjunct, a maximal chain of
primes being a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum S` whose head is
minimal and whose last is maximal. See the module docstring."]
public theorem ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim (k : Type*)
    [Field k] (S : Type*) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S] :
    (∀ (𝔪 : Ideal S) [𝔪.IsMaximal], ringKrullDim S = (𝔪.height : WithBot ℕ∞)) ∧
      ∀ s : RelSeries {(p, q) : PrimeSpectrum S × PrimeSpectrum S | p ⋖ q},
        IsMin s.head → IsMax s.last → (s.length : WithBot ℕ∞) = ringKrullDim S :=
  Stacks.KrullDimension.Equidimensional.solution k S

end Algebra.FiniteType

end
