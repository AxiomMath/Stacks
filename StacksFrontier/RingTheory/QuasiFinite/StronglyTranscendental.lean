module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Polynomial.Basis
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
public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZariskisMainTheorem
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# A strongly transcendental element obstructs quasi-finiteness everywhere

Let `R ⊂ S` be an inclusion of reduced rings, let `x ∈ S` be strongly transcendental over `R`, and
suppose `S` is finite over `R[x]`. Then `R → S` is quasi-finite at no prime of `S`.

## Main results

* `Stacks.QuasiFinite.StrongTranscendence.solution`: Stacks 00Q2.

## Implementation notes

The statement is the contrapositive of Mathlib's
`Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`, which is stated with quasi-finiteness at
the prime as an instance hypothesis and strong transcendence denied in the conclusion. Mathlib's
form needs neither `[IsReduced R]` nor `[FaithfulSMul R S]`, so the source's inclusion `R ⊂ S` of
*reduced* rings enters only through `[IsReduced S]`; the proof is the instantiation.

Mathlib's route is the source's, reorganized. Strong transcendence of `x` descends to the quotient
by a minimal prime `𝔮' ⊆ 𝔮` (`isStronglyTranscendental_mk_of_mem_minimalPrimes`, Stacks 00Q0),
where `R/𝔭 ⊂ S/𝔮'` is an inclusion of domains and the domain case (Stacks 00Q1) applies; Mathlib
proves that case by passing to the fraction fields and to the integral closure of `R` in `Frac R`.
What travels the other way is the *weak* quasi-finiteness of `𝔮`, which descends along the
surjection `S → S/𝔮'` (`Algebra.WeaklyQuasiFiniteAt.of_surjectiveOnStalks`, Stacks 00PN) and then
restricts scalars to `R/𝔭`. That weakening is the point: recovering `Algebra.QuasiFiniteAt` from it
costs `[Algebra.FiniteType R S]` (`Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt`), the finite type
hypothesis the source's Stacks 00PN needs and this statement does not impose.

## References

* [StacksProject 00Q2](https://stacks.math.columbia.edu/tag/00Q2)
* [StacksProject 00Q0](https://stacks.math.columbia.edu/tag/00Q0)
* [StacksProject 00Q1](https://stacks.math.columbia.edu/tag/00Q1)
* [StacksProject 00PN](https://stacks.math.columbia.edu/tag/00PN)
-/

@[expose] public section

namespace Stacks.QuasiFinite.StrongTranscendence

/-- Stacks 00Q2 in the form proved: for an inclusion `R ⊂ S` of reduced rings and `x ∈ S`
strongly transcendental over `R` with `S` finite over `R[x]`, the map `R → S` is not quasi-finite
at the prime `q`. This is the contrapositive of Mathlib's
`Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S] [IsReduced R] [IsReduced S]
    [Algebra R S] [FaithfulSMul R S] {x : S} (hx : IsStronglyTranscendental R x)
    (hx' : (Polynomial.aeval (R := R) x).toRingHom.Finite) (q : Ideal S) [q.IsPrime] :
    ¬ Algebra.QuasiFiniteAt R q := fun _ =>
  Algebra.not_isStronglyTranscendental_of_quasiFiniteAt hx' q hx

end Stacks.QuasiFinite.StrongTranscendence

end

/-!
# A strongly transcendental element obstructs quasi-finiteness everywhere

Let `R ⊂ S` be an inclusion of reduced rings, let `x ∈ S` be strongly transcendental over `R`,
and suppose `S` is finite over the subring `R[x]`. Then `R → S` is quasi-finite at *no* prime of
`S` at all.

The reason is that strong transcendence survives passage to a minimal prime. Given a prime
`𝔮 ⊂ S`, choose a minimal prime `𝔮' ⊆ 𝔮` and put `𝔭 = R ∩ 𝔮'`. Because `R` and `S` are reduced and
`𝔮'` is minimal, the image of `x` in `S/𝔮'` is again strongly transcendental, now over the subring
`R/𝔭` (Lemma 00Q0). Here `R/𝔭 ⊂ S/𝔮'` is an inclusion of *domains* and `S/𝔮'` is still finite over
`(R/𝔭)[x]`, so `R/𝔭 → S/𝔮'` is quasi-finite at no prime by the domain case (Lemma 00Q1). Finally
`S ⊗_R R/𝔭 → S/𝔮'` is surjective and `R → S` is of finite type, so if `R → S` were quasi-finite at
`𝔮` then `R/𝔭 → S/𝔮'` would be quasi-finite at `𝔮/𝔮'` (Lemma 00PN) — a contradiction.

## Main results

* `Algebra.not_quasiFiniteAt_of_isStronglyTranscendental`: Stacks 00Q2.

## Implementation notes

*"Not quasi-finite at any prime" is stated for an arbitrary prime rather than as a `∀` inside the
conclusion.* The prime `q` is a parameter of the theorem, with `[q.IsPrime]` an instance argument
exactly as in `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`; a universally quantified
prime in the conclusion would say the same thing while forcing every call site to supply the
primality instance by hand.

*Quasi-finiteness is `Algebra.QuasiFiniteAt R q`*, Mathlib's `Algebra.QuasiFinite R (S_q)`: the
fibres of `Spec S_q → Spec R` are finite over their residue fields. For an algebra essentially of
finite type this is the source's "`q` is isolated in its fibre"
(`Ideal.exists_notMem_forall_mem_of_ne_of_liesOver`), and no finite type hypothesis is needed to
state it, so none is imposed here — the source imposes none either.

*"`S` finite over `R[x]`" is finiteness of the evaluation map*
`(Polynomial.aeval x).toRingHom.Finite`, Mathlib's `RingHom.Finite` for `R[X] → S`, `X ↦ x`. This
is the source's hypothesis literally: `R[x]` is the image of that map, and `S` is a finite module
over the image exactly when it is a finite module over `R[X]` acting through it. Writing instead
`Module.Finite (R[X]) S` would require choosing an `Algebra R[X] S` instance, which is not
canonical data attached to `x`; going through the map keeps `x` the only choice made.

*The contrapositive of this statement is Mathlib's
`Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`*, which needs neither `[IsReduced R]` nor
`[FaithfulSMul R S]`. Those two are the source's `R ⊂ S` inclusion of *reduced* rings and are kept
because the wording of the tag is the contract here; they cost nothing, since `[IsReduced R]` is
implied by `[IsReduced S]` together with `[FaithfulSMul R S]` (a nilpotent of `R` maps to a
nilpotent of `S`, hence to `0`, hence is `0`), and `[FaithfulSMul R S]` is what `R ⊂ S` means
(`FaithfulSMul.algebraMap_injective`). A user in the more general situation should cite Mathlib's
lemma directly rather than weaken this one.

Faithfulness to [StacksProject 00Q2]:

1. No hypothesis is idle for the source's assertion. `hx` cannot be dropped: for `R = S = k` a
   field and `x = 0`, the map `k[X] → k` is finite and `k → k` is quasi-finite at the unique prime,
   so the conclusion fails — and consistently, `0` is not strongly transcendental over `k`, because
   `X` evaluates to `0` at it while `X ≠ 0` in `k[X]`. `hx'` enters the route above twice: it is
   what makes `S/𝔮'` finite over `(R/𝔭)[x]`, the finiteness hypothesis of the domain case
   (Lemma 00Q1), and it is what makes `R → S` of finite type, the hypothesis under which
   quasi-finiteness descends along `S ⊗_R R/𝔭 → S/𝔮'` (Lemma 00PN). `[IsReduced S]` is used where
   the minimal prime `𝔮'` is quotiented out (Lemma 00Q0). `[IsReduced R]` and `[FaithfulSMul R S]`
   are the source's `R ⊂ S`, discussed in the implementation notes above.
2. The scalars and the base are the source's. `IsStronglyTranscendental R x`,
   `Polynomial.aeval (R := R) x` and `Algebra.QuasiFiniteAt R q` are all taken over `R` itself for
   the given `Algebra R S` — not over a localization, a quotient, or `R[x]`. In particular the
   conclusion denies quasi-finiteness of `R → S`, not of `R[x] → S`, which does hold by `hx'`.
3. Nothing is left merely to exist. The polynomial ring is the canonical `R[X]` and the map to `S`
   is pinned as `Polynomial.aeval x`, the unique `R`-algebra map sending `X ↦ x`, rather than an
   unnamed finite map with `x` in its image; the prime is a named `q` and the conclusion is a
   negation about that `q`, so there is no existential to instantiate.
4. The instantiation is not degenerate. Take `R = ℤ`, `S = ℤ[t]` and `x = t`: then
   `Polynomial.aeval t` is an isomorphism, so `hx'` holds; `ℤ → ℤ[t]` is injective and both rings
   are reduced; and `t` is strongly transcendental over `ℤ` because `ℤ[t]` is a domain, so
   `p(t) · u = 0` forces `p(t) = 0` — hence `p = 0` — or `u = 0`. `Spec ℤ[t]` is nonempty, so the
   conclusion is a nonvacuous denial, and this instance is `Polynomial.not_quasiFiniteAt`. The same
   works over any reduced `R` with `S = R[t]`, a reduced ring being Armendariz.

## References

* [StacksProject 00Q2](https://stacks.math.columbia.edu/tag/00Q2)
* [StacksProject 00Q0](https://stacks.math.columbia.edu/tag/00Q0)
* [StacksProject 00Q1](https://stacks.math.columbia.edu/tag/00Q1)
* [StacksProject 00PN](https://stacks.math.columbia.edu/tag/00PN)

## Tags

strongly transcendental, quasi-finite, reduced ring, finite ring map, Zariski's main theorem
-/

@[expose] public section

namespace Algebra

/-- **Stacks 00Q2.** Let `R ⊂ S` be an inclusion of reduced rings, let `x ∈ S` be strongly
transcendental over `R`, and assume `S` is finite over `R[x]`. Then `R → S` is not quasi-finite
at any prime `q` of `S`. -/
@[stacks 00Q2 "`R ⊂ S` is `[FaithfulSMul R S]` with both rings `[IsReduced]`; `S` finite over
`R[x]` is `(Polynomial.aeval x).toRingHom.Finite`; and \"not quasi-finite at any prime\" is
`¬ Algebra.QuasiFiniteAt R q` for an arbitrary prime `q` of `S`. The contrapositive is Mathlib's
`Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`, which drops `[IsReduced R]` and
`[FaithfulSMul R S]`. See the module docstring."]
public theorem not_quasiFiniteAt_of_isStronglyTranscendental {R S : Type*} [CommRing R]
    [CommRing S] [IsReduced R] [IsReduced S] [Algebra R S] [FaithfulSMul R S] {x : S}
    (hx : IsStronglyTranscendental R x) (hx' : (Polynomial.aeval (R := R) x).toRingHom.Finite)
    (q : Ideal S) [q.IsPrime] : ¬ QuasiFiniteAt R q :=
      by apply Stacks.QuasiFinite.StrongTranscendence.solution <;> assumption

end Algebra

end

end

@[expose] public section


open Polynomial

/-- An element `x : S` is *strongly transcendental over `R`* if for every
`u : S` and every polynomial `p : R[X]`, the equation `u * p(x) = 0` in `S`
forces `u * (algebraMap R S) (p.coeff i) = 0` for every coefficient index
`i`. This is the algebraic version of the Stacks definition. -/
@[stacks 00PZ]
def StronglyTranscendental (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (x : S) : Prop :=
  ∀ (u : S) (p : Polynomial R),
    u * (Polynomial.aeval x) p = 0 → ∀ i, u * algebraMap R S (p.coeff i) = 0

/-- Bridge between the local per-coefficient `StronglyTranscendental` and
Mathlib's polynomial-multiplied `IsStronglyTranscendental`. -/
lemma stronglyTranscendental_iff_isStronglyTranscendental
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : S) :
    StronglyTranscendental R S x ↔ IsStronglyTranscendental R x := by
  unfold StronglyTranscendental IsStronglyTranscendental
  refine ⟨fun h u p hp => ?_, fun h u p hp i => ?_⟩
  · ext i
    simpa [mul_comm] using h u p (by rwa [mul_comm]) i
  · simpa [mul_comm] using congrArg (·.coeff i) (h u p (by rwa [mul_comm]))

/-- **Stacks 10.123.7 (remark).** Let `R ⊆ S` be a ring inclusion with `S` an
integral domain, and let `x ∈ S`. Let `K = Frac(R)` and `L = Frac(S)` be the
fraction fields, arranged into a compatible tower `R → S → L` and `R → K → L`.
Then `x` is strongly transcendental over `R` if and only if the image of `x`
in `L` is transcendental over `K`. -/
theorem stronglyTranscendental_iff_transcendental_frac
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S]
    (K L : Type*) [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    (x : S) :
    StronglyTranscendental R S x ↔ Transcendental K (algebraMap S L x) := by
  -- Derive `IsDomain R` from the injection `R ↪ S` and `IsDomain S`.
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  rw [stronglyTranscendental_iff_isStronglyTranscendental,
      IsStronglyTranscendental.iff_of_isFractionRing (R := R) (S := S) L]
  -- Reduce `Transcendental R y ↔ Transcendental K y` via
  -- `IsFractionRing.isAlgebraic_iff R K L`.
  unfold Transcendental
  rw [IsFractionRing.isAlgebraic_iff R K L]

end

/-!
# A strongly transcendental element obstructs quasi-finiteness

Stacks tag 00Q1 (Lemma 10.123.9), Section 10.123 "Zariski's Main Theorem".

Let `R ⊆ S` be an inclusion of integral domains and let `x ∈ S`. Assume that `x`
is strongly transcendental over `R` (Stacks tag 00PZ) and that `S` is finite as a
module over the subring `R[x]`, the `R`-subalgebra of `S` generated by `x`. Then
`R → S` is not quasi-finite at any prime `q ⊂ S`.

## Conventions

Given an inclusion of rings `R ⊆ S` and an element `x ∈ S`, the element `x` is
*strongly transcendental over `R`* when for all `u ∈ S` and every polynomial
`p ∈ R[X]`, the equation `u * (eval x p) = 0` in `S` implies `u * (coeff i p) = 0`
in `S` for every `i`. This is `StronglyTranscendental R S x`.

For a ring map `R → S` and a prime `q ⊂ S`, the map is *quasi-finite at* `q` when
the localization `S_q` is a quasi-finite `R`-algebra, which is
`Algebra.QuasiFiniteAt R q := Algebra.QuasiFinite R (Localization.AtPrime q)`;
here `Algebra.QuasiFinite R S` requires every fibre `κ(P) ⊗_R S` to be a
finite-dimensional `κ(P)`-vector space.

The inclusion of domains `R ⊆ S` is modelled by making `R` and `S` integral
domains, `S` an `R`-algebra, and `algebraMap R S` injective. The subring `R[x]` is
`Algebra.adjoin R {x}`, and "`S` is finite over `R[x]`" is
`Module.Finite (Algebra.adjoin R {x}) S`. "Not quasi-finite at any prime" is the
statement `∀ q : Ideal S, [q.IsPrime] → ¬ Algebra.QuasiFiniteAt R q`.

## Strategy

The Stacks proof reduces to the normal case and runs a going-down and
isolated-point argument over the closed fibre `p = R ∩ q`. Less is needed here:
`Algebra.QuasiFinite R T` requires the fibre to be finite-dimensional over *every*
prime `P` of `R`, so to negate quasi-finiteness it suffices to exhibit one prime
`P` with an infinite-dimensional fibre, and the generic point `P = ⊥`, prime
because `R` is a domain, will do.

Write `S_q := Localization.AtPrime q` and `K := Frac R = (⊥ : Ideal R).ResidueField`.
The fibre over `⊥` is `(⊥ : Ideal R).Fiber S_q = K ⊗[R] S_q`, and the claim is that
it is not finite-dimensional over `K`.

1. `R[x]` is `R`-free of infinite rank. Transcendence of `x` makes
   `aeval x : R[X] → S` injective, so the powers `{x^n}` are `R`-linearly
   independent and `R[x] = Algebra.adjoin R {x} ≅ R[X]` as `R`-modules. Hence
   `R[x]` is not a finite `R`-module, and `K ⊗[R] R[x] ≅ K[X]` is
   infinite-dimensional over `K`.
2. `R[x] → S_q` is injective: `R[x] = Algebra.adjoin R {x} ↪ S` is the canonical
   subalgebra inclusion, and `S ↪ S_q` is injective because `S` is a domain.
3. `K = Frac R` is a flat `R`-module, being a localization of `R`, so `K ⊗[R] (-)`
   preserves injections and the induced map `K ⊗[R] R[x] → K ⊗[R] S_q` is
   injective.
4. A `K`-submodule of a finite-dimensional `K`-space is finite-dimensional, so if
   `K ⊗[R] S_q` were finite over `K` then so would be its `K`-subspace
   `≅ K ⊗[R] R[x] ≅ K[X]`, which is infinite-dimensional. Contradiction.
5. `QuasiFiniteAt R q` would give `Module.Finite K ((⊥).Fiber S_q)` via
   `finite_fiber (P := ⊥)`, contradicting the previous step.

Step 1 is the only place the transcendence hypothesis is used; steps 2 to 4 are
generic flatness and dimension bookkeeping.

Both `StronglyTranscendental` and `Algebra.QuasiFiniteAt` already exist, so no new
definitions are introduced here.
-/

@[expose] public section

open scoped TensorProduct

/-- Transcendence of `x` makes the adjoin infinite-dimensional after base change:
`x` strongly transcendental over the domain `R` makes `aeval x : R[X] → S`
injective, so `Algebra.adjoin R {x}` is `R`-linearly isomorphic to the polynomial
ring `R[X]` and in particular is not a finite `R`-module. Equivalently the
`K`-module `K ⊗[R] (Algebra.adjoin R {x})` is not `Module.Finite` over
`K = (⊥ : Ideal R).ResidueField = Frac R`.

Strong transcendence with `u = 1` and injectivity of `algebraMap R S` give
`aeval x p = 0 → p = 0`, so `aeval x` is injective and the powers `x^n` are
`R`-independent. Base change along the flat localization map `R → K` preserves this
independence, giving an injection `K[X] ↪ K ⊗[R] R[x]` whose source is
infinite-dimensional over `K`; hence so is the target. -/
theorem bot_fiber_aux_transcendental_free
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (x : S) (hx : StronglyTranscendental R S x) :
    ¬ Module.Finite (⊥ : Ideal R).ResidueField
        ((⊥ : Ideal R).ResidueField ⊗[R] (Algebra.adjoin R {x})) := by
  -- aeval x is injective
  have hinjP : Function.Injective (Polynomial.aeval x : Polynomial R →ₐ[R] S) := by
    refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
    ext i
    simpa using hinj (by simpa using hx 1 p (by simpa using hp) i)
  -- build R-basis of adjoin indexed by ℕ
  let e : Polynomial R ≃ₗ[R] ↥(Algebra.adjoin R {x}) :=
    ((AlgEquiv.ofInjective _ hinjP).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval R x).symm)).toLinearEquiv
  let bR : Module.Basis ℕ R ↥(Algebra.adjoin R {x}) := (Polynomial.basisMonomials R).map e
  -- base change basis over K
  let K := (⊥ : Ideal R).ResidueField
  let bK : Module.Basis ℕ K (K ⊗[R] ↥(Algebra.adjoin R {x})) :=
    Algebra.TensorProduct.basis K bR
  intro hfin
  have : Finite ℕ := Module.Finite.finite_basis bK
  exact not_finite ℕ

/-- The composite `Algebra.adjoin R {x} ↪ S → Localization.AtPrime q` is
injective: the first map is the subalgebra inclusion, and the second is injective
because a domain injects into any of its localizations at a prime. -/
theorem bot_fiber_aux_adjoin_localization_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (x : S) (q : Ideal S) [q.IsPrime] :
    Function.Injective
      (fun a : Algebra.adjoin R {x} =>
        (algebraMap S (Localization.AtPrime q)) (a : S)) :=
  fun _ _ hab => Subtype.val_injective
    (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors q) hab)

/-- The generic fibre of `S_q` over `R` is not finite-dimensional. Since
`K = Frac R = (⊥).ResidueField` is a flat `R`-module, being a localization, the
injection `R[x] ↪ S_q` base-changes to an injection
`K ⊗[R] R[x] → K ⊗[R] S_q = (⊥).Fiber S_q`. An infinite-dimensional `K`-space
cannot inject into a finite-dimensional one, so the fibre is not `Module.Finite`
over `K`. -/
theorem bot_fiber_not_finite
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (x : S) (hx : StronglyTranscendental R S x)
    (q : Ideal S) [q.IsPrime] :
    ¬ Module.Finite (⊥ : Ideal R).ResidueField
        ((⊥ : Ideal R).Fiber (Localization.AtPrime q)) := by
  -- K = Frac R = (⊥).ResidueField is flat over R
  have : Module.Flat R (⊥ : Ideal R).ResidueField := IsLocalization.flat _ (nonZeroDivisors R)
  -- R-linear map adjoin → S_q
  let g : Algebra.adjoin R {x} →ₗ[R] Localization.AtPrime q :=
    ((Algebra.linearMap S _).restrictScalars R).comp (Algebra.adjoin R {x}).val.toLinearMap
  exact fun _ => bot_fiber_aux_transcendental_free hinj x hx
    (Module.Finite.of_injective (g.baseChange (⊥ : Ideal R).ResidueField)
      (Module.Flat.lTensor_preserves_injective_linearMap g
        (bot_fiber_aux_adjoin_localization_injective x q)))

/-- Stacks tag 00Q1 (Lemma 10.123.9). If `R ⊆ S` is an inclusion of integral
domains, `x ∈ S` is strongly transcendental over `R`, and `S` is finite as a
module over the subring `R[x] = Algebra.adjoin R {x}`, then `R → S` is not
quasi-finite at any prime `q` of `S`. -/
theorem stronglyTranscendental_finite_not_quasiFiniteAt
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (x : S)
    (hx : StronglyTranscendental R S x) :
    ∀ (q : Ideal S) [q.IsPrime], ¬ Algebra.QuasiFiniteAt R q := by
  intro q _ hqf
  -- `QuasiFiniteAt R q` forces every fiber finite; specialize to the generic
  -- point `P = ⊥` (prime since `R` is a domain).
  -- ... but the generic fiber is infinite-dimensional (the transcendental `R[x]`
  -- survives base change to `K = Frac R`). Contradiction.
  exact bot_fiber_not_finite hinj x hx q (hqf.finite_fiber (P := ⊥))

end
