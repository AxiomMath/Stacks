module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Associated and weakly associated primes agree at a finitely generated prime

Proof of `isAssociatedPrime_tfae_of_fg` (Stacks 058A): for a finitely generated ideal `p` of a
commutative semiring `R` and an `R`-module `M`, the conditions "`p` is prime and is the annihilator
`Ann(m) = (R ∙ m).annihilator` of an element `m` of `M`", "`p` is an associated prime of `M` in
Mathlib's sense, the radical of such an annihilator", and "`p` is minimal among the primes
containing such an annihilator" are equivalent.

The implications `Ann(m) = p → p = Ann(m).radical → p ∈ Ann(m).minimalPrimes` are formal. The
content is the descent from a minimal prime to a colon ideal, and it is the source's argument:
writing `p = (g₁, …, gₙ)`, one replaces `x` by a scalar multiple `c • x` which every generator `gᵢ`
already carries into `N`, while keeping `p` minimal over `N : c • x`, so that `p ≤ N : c • x ≤ p`.
One generator is dealt with at a time by `exists_smul_mem_of_mem_minimalPrimes`: minimality of `p`
over `N : x` provides `y ∉ p` and `n` with `y gⁿ • x ∈ N` (this is
`exists_notMem_mul_pow_mem_of_mem_minimalPrimes`), and then the exponent `n` is brought down to `1`
by `exists_smul_mem_of_pow_smul_mem`: given `gⁿ⁺¹ • x ∈ N`, either `N : g • x ≤ p`, and one
recurses on `g • x` with the exponent `n`, or some `y ∉ p` has `y g • x ∈ N`, and `g` carries
`y • x` into `N` outright. Every step replaces `x` by a scalar multiple, and minimality of `p` over
the colon ideal survives that replacement: `mem_minimalPrimes_colon_smul` when the new colon ideal
is again inside `p`, and `mem_minimalPrimes_colon_smul_of_notMem`, where the containment is
automatic, when the scalar is outside `p`. Since a scalar multiple only enlarges the colon ideal
(`colon_le_colon_smul`), generators cleared earlier stay cleared.

## Main results

* `Stacks.AssociatedPrimes.WeakComparison.solution`: the statement of Stacks Tag 058A.

## Implementation notes

The descent is carried out for the colon ideal `N : x = Submodule.colon N {x}` of an arbitrary
submodule `N ≤ M`, not just for the annihilator `Ann(x) = ⊥ : x` of the statement (the two are
identified by `Submodule.bot_colon'`): at that generality it is
`Submodule.exists_eq_colon_of_mem_minimalPrimes` with `IsNoetherianRing R` weakened to `p.FG`, and
the two are the same proof. `M ⧸ N` would reduce the general case to `N = ⊥`, but only for
`AddCommGroup M`, whereas the argument itself needs nothing beyond `AddCommMonoid M`.

The source runs the descent in the local ring `R_𝔭`, where an element of `M_𝔭` has annihilator
inside `𝔭R_𝔭` as soon as it is nonzero, and measures progress by the decrease of `∑ eᵢ` for the
minimal exponents `eᵢ` with `gᵢ^{eᵢ} • m = 0`. Over `R` the condition `N : x ≤ p` has to be carried
explicitly, and it is exactly what the second case above restores; the extra scalar `y ∉ p` it
introduces is the localization, used one element at a time. No minimal exponent is needed then:
the recursion is a plain induction on any exponent `n` with `gⁿ • x ∈ N`, and the generators are
handled by induction on a finite generating set of `p`.

The sharpened form of minimality used here, `y * x ^ n ∈ I` for some `y ∉ p` rather than the
`y ∉ I` of `Ideal.exists_mul_mem_of_mem_minimalPrimes`, is proved from
`Ideal.exists_le_prime_disjoint` applied to the submonoid `p.primeCompl ⊔ Submonoid.powers x`; it
is the statement that `p R_𝔭` is the radical of `I R_𝔭`, written without localizing. Mathlib's
`Ideal.iUnion_minimalPrimes` says as much, but only over a `CommRing`, its proof going through
`Localization.AtPrime`.

## References

* [Stacks Project, Tag 058A](https://stacks.math.columbia.edu/tag/058A)
-/

namespace Stacks.AssociatedPrimes.WeakComparison

open Submodule

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {p I J : Ideal R} {N : Submodule R M} {x : M}

/-- Minimality over an ideal is inherited by an intermediate ideal: if `p` is minimal among the
primes containing `I` and `I ≤ J ≤ p`, then `p` is minimal among the primes containing `J`. -/
private theorem mem_minimalPrimes_of_le_of_le (hp : p ∈ I.minimalPrimes) (hIJ : I ≤ J)
    (hJp : J ≤ p) : p ∈ J.minimalPrimes :=
  ⟨⟨hp.1.1, hJp⟩, fun _ hq hqp => hp.2 ⟨hq.1, hIJ.trans hq.2⟩ hqp⟩

/-- Sharpening of `Ideal.exists_mul_mem_of_mem_minimalPrimes`: if `p` is minimal among the primes
containing `I` and `z ∈ p`, then `z` becomes nilpotent in `I` after multiplication by a single
element *outside `p`*, i.e. `y * z ^ n ∈ I` for some `y ∉ p` and some `n`. Equivalently, the
radical of `I R_p` is `p R_p`. -/
private theorem exists_notMem_mul_pow_mem_of_mem_minimalPrimes (hp : p ∈ I.minimalPrimes)
    {z : R} (hz : z ∈ p) : ∃ y ∉ p, ∃ n : ℕ, y * z ^ n ∈ I := by
  have hp' : p.IsPrime := hp.1.1
  have hnd : ¬ Disjoint (I : Set R) (p.primeCompl ⊔ Submonoid.powers z : Submonoid R) := by
    intro hd
    obtain ⟨q, hq, hIq, hqd⟩ := Ideal.exists_le_prime_disjoint I _ hd
    have hqp : q ≤ p := fun w hw =>
      not_not.mp fun hwp => Set.disjoint_left.mp hqd hw (Submonoid.mem_sup_left hwp)
    exact Set.disjoint_left.mp hqd (hp.2 ⟨hq, hIq⟩ hqp hz)
      (Submonoid.mem_sup_right (Submonoid.mem_powers z))
  obtain ⟨w, hwI, hwS⟩ := Set.not_disjoint_iff.mp hnd
  obtain ⟨y, hy, -, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hwS
  exact ⟨y, hy, n, hwI⟩

/-- Multiplying an element by a scalar can only enlarge its colon ideal. -/
private theorem colon_le_colon_smul (N : Submodule R M) (c : R) (x : M) :
    N.colon {x} ≤ N.colon {c • x} := fun r hr => by
  rw [mem_colon_singleton] at hr ⊢
  rw [smul_comm]
  exact N.smul_mem c hr

/-- Minimality of `p` over a colon ideal survives passing from `x` to a scalar multiple `c • x`, as
soon as the enlarged colon ideal is still contained in `p`. -/
private theorem mem_minimalPrimes_colon_smul (hx : p ∈ (N.colon {x}).minimalPrimes) {c : R}
    (hc : N.colon {c • x} ≤ p) : p ∈ (N.colon {c • x}).minimalPrimes :=
  mem_minimalPrimes_of_le_of_le hx (colon_le_colon_smul N c x) hc

/-- For a scalar `y ∉ p` the containment `N : y • x ≤ p` is automatic, by primality: minimality of
`p` over a colon ideal survives multiplying the element by any scalar outside `p`. This is the one
place the localization at `p` is used, one element at a time. -/
private theorem mem_minimalPrimes_colon_smul_of_notMem (hx : p ∈ (N.colon {x}).minimalPrimes)
    {y : R} (hy : y ∉ p) : p ∈ (N.colon {y • x}).minimalPrimes :=
  mem_minimalPrimes_colon_smul hx fun r hr => by
    rw [mem_colon_singleton, smul_smul] at hr
    exact (hx.1.1.mem_or_mem (hx.1.2 (mem_colon_singleton.mpr hr))).resolve_right hy

/-- Exponent reduction: if `p` is minimal over the colon ideal `N : x` and some power of `g`
carries `x` into `N`, then `g` itself carries a scalar multiple `c • x` into `N`, with `p` still
minimal over `N : c • x`. -/
private theorem exists_smul_mem_of_pow_smul_mem {g : R} (n : ℕ) (x : M)
    (hx : p ∈ (N.colon {x}).minimalPrimes) (h : g ^ n • x ∈ N) :
    ∃ c : R, p ∈ (N.colon {c • x}).minimalPrimes ∧ g • (c • x) ∈ N := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, one_smul] at h
    simp [show N.colon {x} = ⊤ by simpa using h, Ideal.minimalPrimes_top] at hx
  | succ n ih =>
    by_cases hgx : N.colon {g • x} ≤ p
    · obtain ⟨c, hc, hgc⟩ := ih (g • x) (mem_minimalPrimes_colon_smul hx hgx)
        (by rw [smul_smul, ← pow_succ]; exact h)
      exact ⟨c * g, by rwa [mul_smul], by rwa [mul_smul]⟩
    · obtain ⟨y, hy, hyp⟩ := SetLike.not_le_iff_exists.mp hgx
      refine ⟨y, mem_minimalPrimes_colon_smul_of_notMem hx hyp, ?_⟩
      rw [smul_comm]
      exact mem_colon_singleton.mp hy

/-- One generator at a time: if `p` is minimal over `N : x` and `g ∈ p`, then `g` carries some
scalar multiple `c • x` into `N`, with `p` still minimal over `N : c • x`. -/
private theorem exists_smul_mem_of_mem_minimalPrimes (hx : p ∈ (N.colon {x}).minimalPrimes)
    {g : R} (hg : g ∈ p) :
    ∃ c : R, p ∈ (N.colon {c • x}).minimalPrimes ∧ g • (c • x) ∈ N := by
  obtain ⟨y, hy, n, hyn⟩ := exists_notMem_mul_pow_mem_of_mem_minimalPrimes hx hg
  obtain ⟨c, hc, hgc⟩ := exists_smul_mem_of_pow_smul_mem n (y • x)
    (mem_minimalPrimes_colon_smul_of_notMem hx hy)
    (by rw [smul_smul, mul_comm]; exact mem_colon_singleton.mp hyn)
  exact ⟨c * y, by rwa [mul_smul], by rwa [mul_smul]⟩

/-- Finitely many generators at a time: if `p` is minimal over `N : x` and `s` is a finite subset
of `p`, then every element of `s` carries some scalar multiple `c • x` into `N`, with `p` still
minimal over `N : c • x`. -/
private theorem exists_forall_smul_mem_of_mem_minimalPrimes {s : Finset R} (hs : ∀ g ∈ s, g ∈ p)
    (x : M) (hx : p ∈ (N.colon {x}).minimalPrimes) :
    ∃ c : R, p ∈ (N.colon {c • x}).minimalPrimes ∧ ∀ g ∈ s, g • (c • x) ∈ N := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => exact ⟨1, by rwa [one_smul], by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, hc₁, hs₁⟩ := ih (fun g hg => hs g (Finset.mem_insert_of_mem hg)) x hx
    obtain ⟨c₂, hc₂, ha⟩ := exists_smul_mem_of_mem_minimalPrimes hc₁
      (hs a (Finset.mem_insert_self a s))
    refine ⟨c₂ * c₁, by rwa [mul_smul], fun g hg => ?_⟩
    rw [mul_smul]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact ha
    · rw [smul_comm]
      exact N.smul_mem c₂ (hs₁ g hg)

/-- The content of Stacks 058A, for the colon ideal of an arbitrary submodule: a finitely generated
prime which is minimal among the primes containing `N : x` *is* a colon ideal `N : x'`. This is
`Submodule.exists_eq_colon_of_mem_minimalPrimes` with `IsNoetherianRing R` weakened to `p.FG`. -/
private theorem exists_eq_colon_of_fg_of_mem_minimalPrimes (hp : p.FG)
    (hx : p ∈ (N.colon {x}).minimalPrimes) : ∃ x' : M, p = N.colon {x'} := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨c, hc, hs'⟩ := exists_forall_smul_mem_of_mem_minimalPrimes
    (fun g hg => hs ▸ Ideal.subset_span hg) x hx
  refine ⟨c • x, le_antisymm ?_ hc.1.2⟩
  rw [← hs, Ideal.span_le]
  exact fun g hg => mem_colon_singleton.mpr (hs' g hg)

/-- For a finitely generated ideal `p` of `R` and an `R`-module `M`, the following are equivalent:
`p` is prime and is the annihilator of an element of `M`; `p` is an associated prime of `M`; and
`p` is minimal among the primes containing the annihilator of an element of `M`. -/
public theorem solution {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {p : Ideal R} (hp : p.FG) :
    List.TFAE [(p.IsPrime ∧ ∃ m : M, p = (R ∙ m).annihilator),
      IsAssociatedPrime p M,
      ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes] := by
  simp only [← Submodule.bot_colon' (R := R)]
  tfae_have 1 → 2 := by
    rintro ⟨hp', m, rfl⟩
    exact ⟨hp', m, hp'.radical.symm⟩
  tfae_have 2 → 3 := by
    rintro ⟨hp', m, hm⟩
    exact ⟨m, by rw [← Ideal.radical_minimalPrimes, ← hm,
      Ideal.minimalPrimes_eq_subsingleton_self]; rfl⟩
  tfae_have 3 → 1 := fun ⟨m, hm⟩ => ⟨hm.1.1, exists_eq_colon_of_fg_of_mem_minimalPrimes hp hm⟩
  tfae_finish

end Stacks.AssociatedPrimes.WeakComparison

/-!
# Associated and weakly associated primes agree at a finitely generated prime

Let `R` be a ring and let `M` be an `R`-module. A prime `p` of `R` is *associated* to `M` when it
is the annihilator `Ann(m) = {f | f • m = 0}` of an element `m ∈ M`, and *weakly associated* to `M`
when it is minimal among the primes containing `Ann(m)` for some `m ∈ M`; the set of the former is
`Ass(M)`, of the latter `WeakAss(M)`, and `Ass(M) ⊆ WeakAss(M)` always.

This file records the converse inclusion at a finitely generated prime: if `p` is finitely
generated and `p ∈ WeakAss(M)`, then `p = Ann(m)` for some `m ∈ M`. Neither `R` nor `M` is assumed
Noetherian or finite; finite generation of the single ideal `p` is all that is used. Since every
ideal of a Noetherian ring is finitely generated, `Ass(M) = WeakAss(M)` for every module over a
Noetherian ring.

## Main results

* `isAssociatedPrime_tfae_of_fg`: for a finitely generated ideal `p` of `R` and an `R`-module `M`,
  the three conditions "`p` is prime and is the annihilator of an element of `M`", "`p` is an
  associated prime of `M` in Mathlib's sense, i.e. the radical of the annihilator of an element",
  and "`p` is minimal over the annihilator of an element of `M`" are equivalent.
* `associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator`: over a Noetherian ring,
  `Ass(M) = WeakAss(M)`.

## Implementation notes

`Ann(m)` is `(R ∙ m).annihilator`, the annihilator of the cyclic submodule generated by `m`
(`Submodule.mem_annihilator_span_singleton : f ∈ (R ∙ m).annihilator ↔ f • m = 0`); it is the
ideal `Submodule.colon ⊥ {m}` in which Mathlib phrases `IsAssociatedPrime`, the two being equal by
`Submodule.mem_colon_singleton`. Membership of `WeakAss(M)` is
`∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes`, minimality among the primes containing an ideal
being `Ideal.minimalPrimes`; this is the spelling used for Tags 0548, 05C4, 05CB and 0CUB, the
notion having no name in Mathlib.

The source states one equivalence, `p ∈ Ass(M) ↔ p ∈ WeakAss(M)`. Mathlib's `associatedPrimes`
is defined with a radical — `IsAssociatedPrime p M` is `p.IsPrime ∧ ∃ m, p = (Ann m).radical`, a
deliberately nonstandard convention which is *not* the source's `Ass(M)` for a general ring —
and it is squeezed between the two sides. So the equivalence is stated as a `TFAE` of three
conditions, with Mathlib's condition in the middle: this loses nothing (the source's iff is
`(isAssociatedPrime_tfae_of_fg hp).out 0 2`) and adds the identification with Mathlib's
`associatedPrimes`, in whose vocabulary Tags 02CE, 05BV and 05DZ are stated.

The first result generalizes `Submodule.exists_eq_colon_of_mem_minimalPrimes`, which draws the same
conclusion from `IsNoetherianRing R`, to a hypothesis on `p` alone; its submodule form, with
`N.colon {x}` in place of an annihilator, is this statement for the module `M ⧸ N`. Over a
Noetherian ring that lemma of Mathlib is available, so the second result is obtained from it and
the elementary inclusion `Ass(M) ⊆ WeakAss(M)`; the content of the tag is the first result, where
only the ideal `p` is finitely generated.

Faithfulness. (1) The one hypothesis is live and the conclusion uses it: for a valuation ring `R`
with value group `ℚ` and valuation `v`, maximal ideal `m` and `I = {x | 1 ≤ v x}`, the module
`M = R ⧸ I` has `Ann(1) = I` with `m` the only prime containing `I`, so `m ∈ WeakAss(M)`, while
`Ann(x) = {r | 1 ≤ v r + v x}` is never `m`, so `Ass(M) = ∅`; the third condition therefore does
not imply the first for a prime that is not finitely generated. No hypothesis is placed on `M`, and
none is used. (2) The scalars and base are the source's: `p` is an ideal of `R`, `M` is an
`R`-module and every annihilator is an ideal of `R`; the source's proof passes to `R_p` and `M_p`,
but no localization appears in the statement, which is about `R` itself. (3) The source names no
canonical map here, and the two operations it does name are pinned to Mathlib's canonical ones,
`Submodule.annihilator (R ∙ m)` for `Ann(m)` and `Ideal.minimalPrimes` for minimality over it;
each condition asserts an equality or a membership of ideals, not the mere existence of some
comparison. (4) The instantiation is not degenerate: for `R = ℤ`, `M = ℤ ⧸ 2ℤ` and `p = (2)` the
ideal `p` is finitely generated and all three conditions hold, witnessed by `m = 1`; and over
`R = ℤ` the second result says `Ass(M) = WeakAss(M)` for every abelian group `M`, both sides being
nonempty as soon as `M ≠ 0`.

## References

* [Stacks Project, Tag 058A](https://stacks.math.columbia.edu/tag/058A)
-/

@[expose] public section

/-- **Stacks 058A.** Let `R` be a ring, `M` an `R`-module and `p` a finitely generated ideal of
`R`. Then `p ∈ Ass(M)`, i.e. `p` is prime and is the annihilator of an element of `M`, iff `p` is
an associated prime of `M` in Mathlib's sense (the radical of the annihilator of an element), iff
`p ∈ WeakAss(M)`, i.e. `p` is minimal among the primes containing the annihilator of an element of
`M`. -/
@[stacks 058A]
public theorem isAssociatedPrime_tfae_of_fg {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {p : Ideal R} (hp : p.FG) :
    List.TFAE [(p.IsPrime ∧ ∃ m : M, p = (R ∙ m).annihilator),
      IsAssociatedPrime p M,
      ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes] :=
    by exact Stacks.AssociatedPrimes.WeakComparison.solution hp

/-- **Stacks 058A**, the Noetherian case. Let `R` be a Noetherian ring and `M` an `R`-module. Then
`Ass(M) = WeakAss(M)`: a prime of `R` is the radical of the annihilator of an element of `M` if and
only if it is minimal among the primes containing the annihilator of an element of `M`. -/
@[stacks 058A]
public theorem associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator {R : Type*}
    [CommSemiring R] [IsNoetherianRing R] {M : Type*} [AddCommMonoid M] [Module R M] :
    associatedPrimes R M =
      {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} := by
  have hann : ∀ m : M, (R ∙ m).annihilator = Submodule.colon ⊥ {m} := fun m =>
    (Submodule.bot_colon' (R := R) (S := {m})).symm
  ext p
  constructor
  · rintro ⟨hp, m, hm⟩
    refine ⟨m, ?_⟩
    rw [hann m]
    refine ⟨⟨hp, hm ▸ Ideal.le_radical⟩, fun q hq _ => ?_⟩
    rw [hm]
    exact hq.1.radical_le_iff.mpr hq.2
  · rintro ⟨m, hm⟩
    rw [hann m] at hm
    obtain ⟨m', hm'⟩ := Submodule.exists_eq_colon_of_mem_minimalPrimes hm
    have hp : p.IsPrime := hm.1.1
    exact ⟨hp, m', by rw [← hm']; exact hp.radical.symm⟩

end

/-!
# A minimal prime of the support is weakly associated

Proof of `Module.exists_mem_minimalPrimes_annihilator_span_singleton_of_minimal_mem_support`
(Stacks 05C4): for a ring `R` and an `R`-module `M`, a prime `𝔭` which is minimal among the
elements of `Supp(M)` is weakly associated to `M`, i.e. `𝔭` is minimal over the annihilator of
some element of `M`.

Membership `𝔭 ∈ Supp(M)` says that `Ann(R ∙ m) ≤ 𝔭` for some `m : M`, so a minimal element of
`Supp(M)` comes with such a witness `m`, and the content of the lemma is that *every* witness
already exhibits `𝔭` as a minimal prime over `Ann(R ∙ m)`: a prime `𝔮 ≤ 𝔭` containing
`Ann(R ∙ m)` lies in `Supp(M)` for the same witness `m`, so minimality of `𝔭` in `Supp(M)` forces
`𝔭 ≤ 𝔮`. That is `mem_minimalPrimes_annihilator_of_minimal_mem_support`, and the statement is it
applied to the witness the hypothesis itself produces.

## Main results

* `Stacks.AssociatedPrimes.WeakGenericPoint.solution`: the statement of Stacks Tag 05C4.

## Implementation notes

The source localizes at `𝔭`: there `Supp(M_𝔭) = {𝔭R_𝔭}`, so `M_𝔭 ≠ 0` has a weakly associated
prime (Lemma 0588), that prime lies in `Supp(M_𝔭)` (Lemma 0589) and hence equals `𝔭R_𝔭`, which
descends to `𝔭 ∈ WeakAss(M)` (Lemma 0566). Those three inputs serve only to transport across the
localization the equivalence between `𝔭 ∈ Supp(M)` and `Ann(R ∙ m) ≤ 𝔭` for some `m : M`, and
that equivalence is available unlocalized as `Module.mem_support_iff_exists_annihilator`. The
localization is therefore not avoided but reused, that equivalence being itself proved by
localizing.

## References

* [Stacks Project, Tag 05C4](https://stacks.math.columbia.edu/tag/05C4)
-/

namespace Stacks.AssociatedPrimes.WeakGenericPoint

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {p : PrimeSpectrum R} {m : M}

/-- At a prime `𝔭` minimal among the elements of `Supp(M)`, *every* element `m : M` witnessing
`𝔭 ∈ Supp(M)` witnesses that `𝔭` is weakly associated to `M`: `𝔭` is minimal over `Ann(R ∙ m)`,
because a prime `𝔮 ≤ 𝔭` containing `Ann(R ∙ m)` lies in `Supp(M)` with the same witness. -/
private theorem mem_minimalPrimes_annihilator_of_minimal_mem_support
    (hp : Minimal (· ∈ Module.support R M) p) (hm : (R ∙ m).annihilator ≤ p.asIdeal) :
    p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes :=
  ⟨⟨p.isPrime, hm⟩, fun q hq hqp => hp.le_of_le (y := ⟨q, hq.1⟩)
    (Module.mem_support_iff_exists_annihilator.mpr ⟨m, hq.2⟩) hqp⟩

/-- A prime `p` minimal among the elements of `Module.support R M` is minimal over the annihilator
of some element of `M`. -/
public theorem solution (hp : Minimal (· ∈ Module.support R M) p) :
    ∃ m : M, p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes :=
  have ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp.prop
  ⟨m, mem_minimalPrimes_annihilator_of_minimal_mem_support hp hm⟩

end Stacks.AssociatedPrimes.WeakGenericPoint

/-!
# A minimal prime of the support of a module is weakly associated to it

Let `R` be a ring and let `M` be an `R`-module. The support `Supp(M)` of `M` is the set of primes
`𝔭` of `R` at which `M` does not localize to zero, and a prime `𝔭` is *weakly associated* to `M`
when it is minimal among the primes containing the annihilator of some element of `M`. The two
sets are related by `WeakAss(M) ⊆ Supp(M)`, and this file records the converse at the bottom of
the support: a prime that is minimal among the elements of `Supp(M)` is weakly associated to `M`.

Neither `R` nor `M` is assumed Noetherian or finite; over a Noetherian ring weakly associated
primes coincide with associated primes, so this specializes to the statement that the minimal
elements of the support of a module over a Noetherian ring are associated primes.

## Main results

* `Module.exists_mem_minimalPrimes_annihilator_span_singleton_of_minimal_mem_support`: a prime
  minimal among the elements of `Supp(M)` is minimal over the annihilator of an element of `M`,
  i.e. lies in `WeakAss(M)`.

## Implementation notes

`Supp(M)` is Mathlib's `Module.support R M`, a set of points of `PrimeSpectrum R`, which is the
abstract form of the source's `Supp(M)`; membership is
`Nontrivial (LocalizedModule 𝔭.asIdeal.primeCompl M)` and is equivalent to
`∃ m, (R ∙ m).annihilator ≤ 𝔭` (`Module.mem_support_iff_exists_annihilator`).
Minimality among its elements is `Minimal (· ∈ Module.support R M) 𝔭` for the order on
`PrimeSpectrum R`, which unfolds to `𝔭 ∈ Supp(M)` together with `∀ 𝔮 ∈ Supp(M), 𝔮 ≤ 𝔭 → 𝔭 ≤ 𝔮`.

`WeakAss(M)` has no name in Mathlib, so it is spelled out as for Tags 058A and 0548: `𝔭` is
weakly associated to `M` exactly when `𝔭.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes` for some
`m : M`, the annihilator of an element being that of the submodule it generates and minimality
over it being `Ideal.minimalPrimes`. The conclusion is stated in the existential form rather than
as an inclusion of sets so that a caller may use the witness `m`; the set-level inclusion
`{𝔭 | Minimal (· ∈ Supp(M)) 𝔭} ⊆ WeakAss(M)` of the source is this statement quantified over
`𝔭`.

Faithfulness. (1) The single hypothesis is used whole: `𝔭 ∈ Supp(M)` gives `M_𝔭 ≠ 0` and hence a
weakly associated prime of `M_𝔭`, while minimality forces that prime to be `𝔭R_𝔭` itself; drop
either half and the conclusion fails: for `R = M = ℤ` the prime `(2)` lies in `Supp(ℤ)` but is not
weakly associated to `ℤ`, whose only weakly associated prime is `(0)`, so membership alone is too
weak; and for `M = 0` every prime satisfies the minimality clause vacuously while `WeakAss(0) = ∅`,
so minimality alone is too weak. (2) Base and scalars are the source's: `M` is an `R`-module, the
primes are primes of `R` and the annihilators are ideals of `R`, and no `R_𝔭`-module structure
enters the statement even though the source's proof localizes. (3) The source names no canonical
map here; both operations it does name are pinned to Mathlib's canonical ones, `Module.support R M`
for `Supp(M)` and `Submodule.annihilator (R ∙ m)` for the annihilator of `m`. (4) The hypothesis is
satisfiable and the conclusion has content: for `R = M = ℤ` one has `Supp(ℤ) = Spec(ℤ)` with least
element `(0)`, and `(0)` is indeed minimal over `(ℤ ∙ 1).annihilator = 0`, witnessed by `m = 1`.

## References

* [Stacks Project, Tag 05C4](https://stacks.math.columbia.edu/tag/05C4)

## Tags

weakly associated prime, support, annihilator, minimal prime, localization
-/

@[expose] public section

/-- **Stacks 05C4.** Let `R` be a ring and `M` an `R`-module. Any prime `𝔭` which is minimal among
the elements of the support of `M` is weakly associated to `M`, i.e. `𝔭` is minimal over the
annihilator of some element of `M`. -/
@[stacks 05C4]
public theorem Module.exists_mem_minimalPrimes_annihilator_span_singleton_of_minimal_mem_support
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}
    (hp : Minimal (· ∈ Module.support R M) p) :
    ∃ m : M, p.asIdeal ∈ (R ∙ m).annihilator.minimalPrimes :=
    by apply Stacks.AssociatedPrimes.WeakGenericPoint.solution ; assumption

end

/-!
# Weakly associated primes and an exact sequence

Let `R` be a commutative semiring, let `0 → M → M' → M''` be an exact sequence of `R`-modules, and
write `WeakAss(N)` for the set of primes of `R` that are minimal among the primes containing the
annihilator `Ann(n) = (R ∙ n).annihilator` of an element `n` of an `R`-module `N`. This file proves
`Module.weaklyAssociatedPrimes_subset_union_of_exact` (Stacks 0548):
`WeakAss(M') ⊆ WeakAss(M) ∪ WeakAss(M'')`.

Fix `m : M'` and a prime `p` minimal over `Ann(m)`, and note `Ann(m) ≤ Ann(g m)`. There are two
cases.

* If `Ann(g m) ≤ p` then `p` is minimal over `Ann(g m)` too, since an ideal squeezed between
  `Ann(m)` and `p` inherits `p` as a minimal prime: a prime `q ≤ p` containing the squeezed ideal
  already contains `Ann(m)`. So `g m` witnesses `p ∈ WeakAss(M'')`.
* Otherwise choose `r ∈ Ann(g m)` with `r ∉ p`. Then `g (r • m) = 0`, so exactness produces
  `a : M` with `f a = r • m`, and injectivity of `f` gives `Ann(a) = Ann(r • m)`. Multiplying by a
  scalar outside `p` does not disturb minimality of `p`: `Ann(m) ≤ Ann(r • m)` always, and
  `Ann(r • m) ≤ p` because `s r ∈ Ann(m) ≤ p` and `r ∉ p` force `s ∈ p`, so the same squeeze
  applies. Thus `a` witnesses `p ∈ WeakAss(M)`.

## Main results

* `Stacks.AssociatedPrimes.WeakExactness.solution`: the statement of Stacks Tag 0548, second
  inclusion.

## Implementation notes

The source localizes at `p` and argues with the characterization of Lemma 0566: the radical of the
annihilator of `m ∈ M'_p` is `p R_p`, and either the image of `m` in `M''_p` is zero, so that `m`
comes from `M_p`, or its annihilator has the same radical. The squeeze above is that argument with
the localization removed. Membership of `p` in `Ann(n).minimalPrimes` is what "the radical of the
annihilator becomes the maximal ideal after localizing at `p`" says about `R` itself, and the
dichotomy "image zero, or same radical" becomes the dichotomy on whether `Ann(g m) ≤ p`; the second
branch replaces "`m` comes from `M_p`" by its content over `R`, namely that `r • m` comes from `M`
for a single `r ∉ p`. Nothing is lost: the statement never mentions a localization, and dropping it
is what lets the proof run over a commutative semiring with modules that are only additive monoids,
where the source's short exact sequence of localizations is unavailable.

Four general facts are used that Mathlib does not have; each is a `private` lemma here, named for
the Mathlib declaration it should become. The mathematics of the lemma is
`mem_minimalPrimes_annihilator_smul_of_notMem`: minimality of a prime over the annihilator of an
element is unchanged by multiplying that element by a scalar outside the prime.

* `mem_minimalPrimes_of_le_of_le`: `Ideal.mem_minimalPrimes_of_le_of_le`, the squeeze. It is
  `Minimal.mono` for `Ideal.IsMinimalPrime`, whose two predicates have to be named explicitly:
  `Ideal.IsMinimalPrime` is a `def`, so it does not unify with `Minimal ?P ?p` while `?P` is still
  a metavariable.
* `annihilator_span_singleton_le_map` and `annihilator_span_singleton_map_of_injective`:
  `Submodule.annihilator_span_singleton_le_map` and
  `Submodule.annihilator_span_singleton_map_of_injective`, that `Ann(m) ≤ Ann(f m)` for a linear
  `f`, with equality for injective `f`. The first is used for `g` and, through `LinearMap.lsmul`,
  for multiplication by `r`; the second transports the conclusion along `f`.
* `annihilator_span_singleton_smul_le`: `Submodule.annihilator_span_singleton_smul_le`, the
  primality step, that a prime containing `Ann(m)` but not `r` contains `Ann(r • m)`.

## References

* [Stacks Project, Tag 0548](https://stacks.math.columbia.edu/tag/0548)
-/

@[expose] public section

namespace Stacks.AssociatedPrimes.WeakExactness

section Helpers

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The annihilator of an element is contained in the annihilator of its image. -/
private theorem annihilator_span_singleton_le_map (f : M →ₗ[R] N) (m : M) :
    (R ∙ m).annihilator ≤ (R ∙ f m).annihilator := by
  simp only [SetLike.le_def, Submodule.mem_annihilator_span_singleton, ← map_smul]
  exact fun r hr => by rw [hr, map_zero]

/-- An injective linear map preserves the annihilator of an element. -/
private theorem annihilator_span_singleton_map_of_injective {f : M →ₗ[R] N}
    (hf : Function.Injective f) (m : M) : (R ∙ f m).annihilator = (R ∙ m).annihilator := by
  ext r
  simp only [Submodule.mem_annihilator_span_singleton, ← map_smul, LinearMap.map_eq_zero_iff f hf]

/-- A prime containing the annihilator of `m` but not containing `r` contains the annihilator of
`r • m`. -/
private theorem annihilator_span_singleton_smul_le {p : Ideal R} (hp : p.IsPrime) {m : M}
    (hm : (R ∙ m).annihilator ≤ p) {r : R} (hr : r ∉ p) : (R ∙ r • m).annihilator ≤ p := by
  intro s hs
  rw [Submodule.mem_annihilator_span_singleton, smul_smul] at hs
  have hsr : s * r ∈ p := hm ((Submodule.mem_annihilator_span_singleton m (s * r)).mpr hs)
  exact (hp.mem_or_mem hsr).resolve_right hr

/-- Multiplying an element by a scalar outside `p` does not disturb minimality of `p` over its
annihilator: if `p` is minimal over `Ann(m)` and `r ∉ p`, then `p` is minimal over `Ann(r • m)`. -/
private theorem mem_minimalPrimes_annihilator_smul_of_notMem {p : Ideal R} {m : M}
    (hm : p ∈ (R ∙ m).annihilator.minimalPrimes) {r : R} (hr : r ∉ p) :
    p ∈ (R ∙ r • m).annihilator.minimalPrimes :=
  Stacks.AssociatedPrimes.WeakComparison.mem_minimalPrimes_of_le_of_le hm
    (annihilator_span_singleton_le_map (LinearMap.lsmul R M r) m)
    (annihilator_span_singleton_smul_le hm.1.1 hm.1.2 hr)

end Helpers

/-- For an injective `f : M →ₗ[R] M'` and `g : M' →ₗ[R] M''` exact at `M'`, every prime minimal
over the annihilator of an element of `M'` is minimal over the annihilator of an element of `M`
or of an element of `M''`. -/
public theorem solution
    {R : Type*} [CommSemiring R] {M M' M'' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    [AddCommMonoid M''] [Module R M''] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    {p : Ideal R | ∃ m : M', p ∈ (R ∙ m).annihilator.minimalPrimes} ⊆
      {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} ∪
        {p : Ideal R | ∃ m : M'', p ∈ (R ∙ m).annihilator.minimalPrimes} := by
  rintro p ⟨m, hm⟩
  by_cases h : (R ∙ g m).annihilator ≤ p
  · exact Or.inr ⟨g m, Stacks.AssociatedPrimes.WeakComparison.mem_minimalPrimes_of_le_of_le hm
      (annihilator_span_singleton_le_map g m) h⟩
  · obtain ⟨r, hr, hrp⟩ : ∃ r ∈ (R ∙ g m).annihilator, r ∉ p := by
      simpa [SetLike.le_def] using h
    rw [Submodule.mem_annihilator_span_singleton, ← map_smul] at hr
    obtain ⟨a, ha⟩ := (hfg (r • m)).mp hr
    refine Or.inl ⟨a, ?_⟩
    rw [← annihilator_span_singleton_map_of_injective hf a, ha]
    exact mem_minimalPrimes_annihilator_smul_of_notMem hm hrp

end Stacks.AssociatedPrimes.WeakExactness

end

/-!
# Weakly associated primes and exact sequences

Let `R` be a ring and `N` an `R`-module. A prime `p` of `R` is *weakly associated* to `N` when `p`
is minimal among the primes containing the annihilator of some element of `N`, and `WeakAss(N)`
denotes the set of these primes.

Weakly associated primes behave in an exact sequence `0 → M → M' → M''` the way associated primes
do: an injection `M ↪ M'` preserves the annihilator of an element, so `WeakAss(M) ⊆ WeakAss(M')`,
and an element of `M'` either has its annihilator seen already in `M''` or, after multiplying by
one element outside `p`, comes from `M`, so `WeakAss(M') ⊆ WeakAss(M) ∪ WeakAss(M'')`. Neither `R`
nor the modules are assumed Noetherian or finite, which is what weakly associated primes buy over
associated ones.

## Main results

* `Module.weaklyAssociatedPrimes_subset_of_injective`: an injective `f : M →ₗ[R] M'` gives
  `WeakAss(M) ⊆ WeakAss(M')`.
* `Module.weaklyAssociatedPrimes_subset_union_of_exact`: for an exact sequence
  `0 → M → M' → M''` of `R`-modules, `WeakAss(M') ⊆ WeakAss(M) ∪ WeakAss(M'')`.

## Implementation notes

`WeakAss(N)` is spelled out inline, as the set of primes `p` with
`p ∈ (R ∙ m).annihilator.minimalPrimes` for some `m : N`: the annihilator of an element is the
annihilator of the cyclic submodule it generates, and minimality among the primes containing an
ideal is `Ideal.minimalPrimes`. This is the spelling used by
`Module.injective_pi_localization_weaklyAssociatedPrimes` (Tag 05CB) and keeps the two files
interchangeable; the notion has no name in Mathlib.

The two inclusions are separate declarations rather than one conjunction, each under exactly the
hypotheses it uses: the first needs only injectivity of `f`, so stating it alongside the second
would burden it with a map `g` and an exactness hypothesis no caller of it has, and at this
generality — `CommSemiring R` and `AddCommMonoid` modules — a caller with only an injection cannot
manufacture them. This is also how Mathlib states the associated-primes siblings
`associatedPrimes.subset_of_injective` and `associatedPrimes.subset_union_of_exact`, from which the
names and the binders here are taken. Separating them also isolates the content: the first
inclusion is the observation that an injection preserves the annihilator of an element, three lines
from `Submodule.mem_annihilator_span_singleton`, while the mathematics of the lemma is entirely in
the second.

The exact sequence is written `0 → M → M' → M''`, with the middle module `M'`; the source writes
`0 → M' → M → M'' → 0`, so the source's `M', M, M''` are the `M, M', M''` here. Surjectivity of
`M' → M''` is not assumed: exactness of `0 → M → M' → M''` alone gives both inclusions, and
dropping it is the same generalization Mathlib's associated-primes siblings make. For the same
reason the hypotheses are `CommSemiring R` and `AddCommMonoid` modules rather than a commutative
ring and abelian groups; the source argues after localizing at `p`, but the two inclusions are
statements about annihilators of single elements and need no subtraction.

Faithfulness. (1) Every hypothesis is live. Both inclusions fail without injectivity of `f`,
already for the surjection `f : ℤ ↠ ℤ/2` over `R = ℤ`: there `WeakAss(ℤ) = {(0)}` is not contained
in `WeakAss(ℤ/2) = {(2)}`, and taking `g = 0` with `M'' = 0` (so that `f` and `g` are exact)
`WeakAss(ℤ/2) = {(2)}` is not contained in `WeakAss(ℤ) ∪ WeakAss(0) = {(0)}`. Exactness is used
only by the second, which fails for `g = 0` on a module with a torsion element. (2) The scalars are
the source's: `R` is the base of all three modules, the maps are `R`-linear, and the primes are
primes of `R`, no localization of `R` entering the statement. (3) The two inclusions are inclusions
of the sets themselves, not the existence of some injection or covering, so the canonical maps `f`
and `g` of the sequence are the ones the conclusion is about. (4) The instantiation is not
degenerate: for `R = ℤ` and `0 → ℤ/2 → ℤ/6 → ℤ/3 → 0` (that is, `3ℤ/6ℤ ⊆ ℤ/6ℤ` with quotient
`ℤ/3`), the three sets are `{(2)}`, `{(2), (3)}` and `{(3)}`, so the first inclusion is strict and
the second needs both terms of the union.

## References

* [Stacks Project, Tag 0548](https://stacks.math.columbia.edu/tag/0548)

## Tags

weakly associated prime, exact sequence, annihilator, minimal prime
-/

@[expose] public section

/-- **Stacks 0548**, first inclusion. Let `R` be a ring and let `f : M →ₗ[R] M'` be an injective
map of `R`-modules. Then `WeakAss(M) ⊆ WeakAss(M')`, where `WeakAss(N)` is the set of primes of `R`
minimal over the annihilator of an element of `N`. -/
@[stacks 0548]
public theorem Module.weaklyAssociatedPrimes_subset_of_injective
    {R : Type*} [CommSemiring R] {M M' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    {f : M →ₗ[R] M'} (hf : Function.Injective f) :
    {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} ⊆
      {p : Ideal R | ∃ m : M', p ∈ (R ∙ m).annihilator.minimalPrimes} := by
  rintro p ⟨m, hm⟩
  refine ⟨f m, ?_⟩
  rwa [Stacks.AssociatedPrimes.WeakExactness.annihilator_span_singleton_map_of_injective hf]

/-- **Stacks 0548**, second inclusion. Let `R` be a ring and let `0 → M → M' → M''` be an exact
sequence of `R`-modules, i.e. `f : M →ₗ[R] M'` is injective with image the kernel of
`g : M' →ₗ[R] M''`. Then `WeakAss(M') ⊆ WeakAss(M) ∪ WeakAss(M'')`, where `WeakAss(N)` is the set
of primes of `R` minimal over the annihilator of an element of `N`. -/
@[stacks 0548]
public theorem Module.weaklyAssociatedPrimes_subset_union_of_exact
    {R : Type*} [CommSemiring R] {M M' M'' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    [AddCommMonoid M''] [Module R M''] {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    {p : Ideal R | ∃ m : M', p ∈ (R ∙ m).annihilator.minimalPrimes} ⊆
      {p : Ideal R | ∃ m : M, p ∈ (R ∙ m).annihilator.minimalPrimes} ∪
        {p : Ideal R | ∃ m : M'', p ∈ (R ∙ m).annihilator.minimalPrimes} :=
    by exact Stacks.AssociatedPrimes.WeakExactness.solution (g := g) (f := f) hf hfg

end
