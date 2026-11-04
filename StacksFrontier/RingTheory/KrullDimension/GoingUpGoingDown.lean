module

public import StacksFrontier.RingTheory.Ideal.GoingUpGoingDown.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Going up or going down plus surjectivity forces a dimension inequality

Let `φ : R → S` be a map of commutative rings with unit. A prime `q` of `S` *lies over* a
prime `p` of `R` when `φ⁻¹(q) = p`, i.e. `p` is the contraction of `q` along `φ`, and the
induced map `Spec(S) → Spec(R)` sends `q ↦ φ⁻¹(q)`.

## Main results

If `φ` satisfies either going up or going down, and the induced map `Spec(S) → Spec(R)`
is surjective, then `dim(R) ≤ dim(S)`.

The disjunction is inclusive — one of the two hypotheses suffices — so it is recorded as
two statements, `ringKrullDim_le_of_goingUp` and `ringKrullDim_le_of_goingDown`. Krull
dimension is `ringKrullDim`, valued in the extended natural numbers `WithBot ℕ∞`, whose
ordering handles the degenerate zero-ring case `⊥` uniformly.

Surjectivity of `Spec(S) → Spec(R)` is expressed through
`PrimeSpectrum.comap φ : PrimeSpectrum S → PrimeSpectrum R`: it says precisely that every
prime `p` of `R` has a prime `q` of `S` with `φ⁻¹(q) = p`, that is, lying over `p`.

## Proof outline

Assume going up and take a chain of primes `p₀ ⊊ p₁ ⊊ ⋯ ⊊ p_e` in `R`. Surjectivity
gives a prime `q₀` of `S` lying over `p₀`, and going up extends this inductively to
`q₀ ⊆ q₁ ⊆ ⋯ ⊆ q_e` with `q_i` lying over `p_i`. Since the `p_i` increase strictly and
`q_i` contracts to `p_i`, the `q_i` increase strictly too, so `q₀ ⊊ ⋯ ⊊ q_e` is a chain
of length `e` in `S`. Hence `dim(S) ≥ e` for every chain length `e` realized in `R`,
giving `dim(S) ≥ dim(R)`. Going down is analogous, building the chain downward from a
prime lying over `p_e`.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

open Order

/-- **Reduction helper.** To prove `krullDim α ≤ krullDim β` it suffices to show that
every chain (`LTSeries`) in `α` can be matched by a chain in `β` of at least the same
length. This is exactly the supremum-over-chains characterization of `krullDim`
(`Order.krullDim α = ⨆ p : LTSeries α, ↑p.length`): the left supremum is bounded by the
right one termwise. -/
theorem krullDim_le_of_chain_lift {α β : Type*} [Preorder α] [Preorder β]
    (H : ∀ l : LTSeries α, ∃ m : LTSeries β, l.length ≤ m.length) :
    krullDim α ≤ krullDim β := by
  rw [Order.krullDim, Order.krullDim]
  refine iSup_le fun l => ?_
  obtain ⟨m, hm⟩ := H l
  exact le_iSup_of_le m (by exact_mod_cast hm)

/-- Contracting along `φ` detects strictness: if `Q ≤ Q'` have different contractions,
then `Q < Q'`. -/
private theorem lt_of_le_of_comap_ne (φ : R →+* S) {Q Q' : PrimeSpectrum S} (h : Q ≤ Q')
    (h' : PrimeSpectrum.comap φ Q ≠ PrimeSpectrum.comap φ Q') : Q < Q' :=
  lt_of_le_of_ne h fun e => h' (congrArg _ e)

/-- **Chain-lifting lemma, going-up version.**
Under going up and surjectivity of `Spec(S) → Spec(R)`, every chain of primes in `R`
lifts to a chain in `S` of the same length.

Let `l` be a chain `p₀ < p₁ < ⋯ < p_e` in `Spec(R)` with `e = l.length`. The lifted chain
`m` in `Spec(S)` is built index by index, maintaining `comap φ (m i) = l i`.

At the base, surjectivity of `PrimeSpectrum.comap φ` produces a prime lying over `l 0`.
At the inductive step, given a prime `q` of `S` lying over `l i`, the chain supplies
`(l i).asIdeal ≤ (l (i+1)).asIdeal` with both ideals prime, so going up yields a prime
`q'` of `S` with `q ≤ q'` lying over `(l (i+1)).asIdeal`.

The extension is strict: `l` increases strictly, so the contractions `l i` and `l (i+1)`
differ, and monotonicity of `comap φ` then rules out `q = q'`. Hence the construction is
strictly monotone on `Fin (e+1)` and packages into an `LTSeries` of length
`e = l.length`. -/
theorem chain_lift_goingUp (φ : R →+* S) (hup : GoingUp_00oh φ)
    (hsurj : Function.Surjective (PrimeSpectrum.comap φ))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ m : LTSeries (PrimeSpectrum S), l.length ≤ m.length := by
  classical
  set e := l.length with he
  -- motive: an LTSeries prefix of length i whose last element lies over l i
  let motive : Fin (e + 1) → Prop := fun i =>
    ∃ m : LTSeries (PrimeSpectrum S), m.length = (i : ℕ) ∧ PrimeSpectrum.comap φ m.last = l i
  have base : motive 0 := by
    obtain ⟨q, hq⟩ := hsurj (l 0)
    exact ⟨RelSeries.singleton _ q, by simp, by simpa using hq⟩
  have step : ∀ i : Fin e, motive i.castSucc → motive i.succ := by
    rintro i ⟨m, hmlen, hmlast⟩
    have hlt : l i.castSucc < l i.succ := l.step i
    obtain ⟨q', hq'prime, hq'le, hq'lies⟩ := hup (l i.castSucc).asIdeal (l i.succ).asIdeal
      (l i.castSucc).isPrime (l i.succ).isPrime
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) m.last.asIdeal m.last.isPrime
      (by rw [LiesOver_00oh, ← PrimeSpectrum.comap_asIdeal, hmlast])
    have hQcomap : PrimeSpectrum.comap φ ⟨q', hq'prime⟩ = l i.succ :=
      PrimeSpectrum.ext hq'lies
    refine ⟨m.snoc ⟨q', hq'prime⟩ (lt_of_le_of_comap_ne φ
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hq'le) ?_), ?_, ?_⟩
    · rw [hmlast, hQcomap]; exact hlt.ne
    · simp [hmlen]
    · rw [RelSeries.last_snoc]; exact hQcomap
  obtain ⟨m, hm, -⟩ := Fin.induction (motive := motive) base step (Fin.last e)
  exact ⟨m, hm.ge⟩

/-- **Chain-lifting lemma, going-down version.**
Under going down and surjectivity of `Spec(S) → Spec(R)`, every chain of primes in `R`
lifts to a chain in `S` of the same length.

Dual to `chain_lift_goingUp`: for a chain `p₀ < p₁ < ⋯ < p_e` in `Spec(R)` with
`e = l.length`, the lifted chain is built from the top downward. Surjectivity supplies a
prime over `p_e`, and given a prime over `p_{i+1}`, going down yields a prime of `S`
below it lying over `p_i`.

Strictness is as in the going-up case: consecutive contractions `l i` and `l (i+1)`
differ, so monotonicity of `comap φ` forces the inclusion to be strict. The result
packages into an `LTSeries` of length `e`. -/
theorem chain_lift_goingDown (φ : R →+* S) (hdown : GoingDown_00oh φ)
    (hsurj : Function.Surjective (PrimeSpectrum.comap φ))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ m : LTSeries (PrimeSpectrum S), l.length ≤ m.length := by
  classical
  set e := l.length with he
  -- motive: an LTSeries suffix of length e - i whose head lies over l i
  let motive : Fin (e + 1) → Prop := fun i =>
    ∃ m : LTSeries (PrimeSpectrum S), m.length = e - (i : ℕ) ∧ PrimeSpectrum.comap φ m.head = l i
  have base : motive (Fin.last e) := by
    obtain ⟨q, hq⟩ := hsurj (l (Fin.last e))
    exact ⟨RelSeries.singleton _ q, by simp, by simpa using hq⟩
  have step : ∀ i : Fin e, motive i.succ → motive i.castSucc := by
    rintro i ⟨m, hmlen, hmhead⟩
    have hlt : l i.castSucc < l i.succ := l.step i
    obtain ⟨q', hq'prime, hq'le, hq'lies⟩ := hdown (l i.castSucc).asIdeal (l i.succ).asIdeal
      (l i.castSucc).isPrime (l i.succ).isPrime
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) m.head.asIdeal m.head.isPrime
      (by rw [LiesOver_00oh, ← PrimeSpectrum.comap_asIdeal, hmhead])
    have hQcomap : PrimeSpectrum.comap φ ⟨q', hq'prime⟩ = l i.castSucc :=
      PrimeSpectrum.ext hq'lies
    refine ⟨m.cons ⟨q', hq'prime⟩ (lt_of_le_of_comap_ne φ
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hq'le) ?_), ?_, ?_⟩
    · rw [hmhead, hQcomap]; exact hlt.ne
    · simp only [RelSeries.cons_length, hmlen]
      have : (i.castSucc : ℕ) + 1 = (i.succ : ℕ) := by simp
      omega
    · rw [RelSeries.head_cons]; exact hQcomap
  obtain ⟨m, hm, -⟩ := Fin.reverseInduction (motive := motive) base step 0
  exact ⟨m, by simpa using hm.ge⟩

/-- **Going-up version.**
If `φ : R → S` satisfies going up and the induced map `Spec(S) → Spec(R)` is
surjective, then `dim(R) ≤ dim(S)`.

This follows from `chain_lift_goingUp` through `krullDim_le_of_chain_lift`, since
`ringKrullDim R` is `krullDim (PrimeSpectrum R)` by definition. -/
@[stacks 00OH, ega "IV 5.4.1" "(ii), special case"]
theorem ringKrullDim_le_of_goingUp (φ : R →+* S) (hup : GoingUp_00oh φ)
    (hsurj : Function.Surjective (PrimeSpectrum.comap φ)) :
    ringKrullDim R ≤ ringKrullDim S :=
  krullDim_le_of_chain_lift (chain_lift_goingUp φ hup hsurj)

/-- **Going-down version.**
If `φ : R → S` satisfies going down and the induced map `Spec(S) → Spec(R)` is
surjective, then `dim(R) ≤ dim(S)`.

This follows from `chain_lift_goingDown` through `krullDim_le_of_chain_lift`. -/
@[stacks 00OH, ega "IV 5.4.1" "(ii), special case"]
theorem ringKrullDim_le_of_goingDown (φ : R →+* S) (hdown : GoingDown_00oh φ)
    (hsurj : Function.Surjective (PrimeSpectrum.comap φ)) :
    ringKrullDim R ≤ ringKrullDim S :=
  krullDim_le_of_chain_lift (chain_lift_goingDown φ hdown hsurj)

-- ===== merged from Sec112/Tag00OI =====

/-!
# Homomorphisms and dimension: going up and maximal ideals

Let `φ : R → S` be a ring homomorphism of commutative rings.

A prime ideal `q ⊆ S` *lies over* a prime ideal `p ⊆ R` if the inverse image
(contraction) of `q` under `φ` equals `p`, i.e. `φ⁻¹(q) = p`. For any prime ideal
`q ⊆ S` its contraction `φ⁻¹(q)` is automatically a prime ideal of `R`; see
`Ideal.comap_isPrime`.

The ring map `φ` satisfies *going up* if, given prime ideals `p ⊆ p'` in `R` and a
prime ideal `q` in `S` lying over `p`, there exists a prime ideal `q'` of `S` with
`q ⊆ q'` which lies over `p'`.

## Main definitions

* `LiesOver`: a prime ideal of `S` lies over a prime ideal of `R` under `φ`.
* `GoingUp`: the going up property of a ring map.

## Main results

* `comap_isMaximal_of_goingUp`: if `φ` satisfies going up and `q ⊆ S` is a maximal
  ideal, then its inverse image `φ⁻¹(q) ⊆ R` is a maximal ideal of `R`.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Stacks Tag 00OI.** If `φ : R → S` satisfies going up and `q ⊆ S` is a maximal
ideal, then its contraction `φ⁻¹(q)` is a maximal ideal of `R`. -/
@[stacks 00OI]
theorem comap_isMaximal_of_goingUp (φ : R →+* S) (hφ : GoingUp φ)
    (q : Ideal S) (hq : q.IsMaximal) :
    (Ideal.comap φ q).IsMaximal := by
  -- get a maximal ideal `p'` containing the proper ideal `φ⁻¹(q)`, and apply going up
  obtain ⟨p', hp'max, hpp'⟩ := Ideal.exists_le_maximal _ (Ideal.comap_isPrime φ q).ne_top
  obtain ⟨q', hq'prime, hqq', hq'lo⟩ :=
    hφ _ p' (Ideal.comap_isPrime φ q) hp'max.isPrime hpp' q hq.isPrime rfl
  -- q is maximal, q ⊆ q', q' prime hence proper, so q' = q and p' = comap φ q
  rwa [← hq'lo, ← hq.eq_of_le hq'prime.ne_top hqq'] at hp'max

-- ===== merged from Sec112/Tag00OJ =====

/-!
# Homomorphisms and dimension: integral ring maps

Let `R` and `S` be commutative rings and let `f : R → S` be a ring homomorphism such
that `S` is integral over `R`, that is, every `s ∈ S` is a root of a monic polynomial
with coefficients in `f(R)` (in Mathlib, `RingHom.IsIntegral f`). Then

1. `dim(R) ≥ dim(S)`, equivalently `ringKrullDim S ≤ ringKrullDim R`;
2. every closed point of `Spec(S)` maps to a closed point of `Spec(R)` under the
   induced map `Spec(f) = PrimeSpectrum.comap f`.

Here `dim(A)` is the Krull dimension `ringKrullDim A`, the supremum over chains of
prime ideals `𝔭₀ ⊊ ⋯ ⊊ 𝔭ₙ` of their length `n`, valued in `WithBot ℕ∞` and equal to
`-∞` only for the zero ring. The spectrum `Spec(A) = PrimeSpectrum A` is the set of
prime ideals of `A` with the Zariski topology, and a ring map `f : R → S` induces the
continuous map `PrimeSpectrum.comap f : Spec(S) → Spec(R)` sending `𝔮` to `f⁻¹(𝔮)`. A
point `x ∈ Spec(A)` is closed when `{x}` is closed, equivalently when `x.asIdeal` is a
maximal ideal of `A`.

The inequality is oriented so that `dim(R) ≥ dim(S)` reads as
`ringKrullDim S ≤ ringKrullDim R` for Mathlib's `≤` on `WithBot ℕ∞`; it holds because
contraction along `f` sends strict chains of primes in `S` to strict chains in `R`. No
injectivity, surjectivity or finiteness hypothesis on `f` is needed beyond
integrality.
-/

@[expose] public section

/-- **Stacks Tag 00OJ.** If `f : R → S` is a ring map making `S` integral over `R`,
then `ringKrullDim S ≤ ringKrullDim R` and every closed point of `Spec(S)` contracts
to a closed point of `Spec(R)`. -/
@[stacks 00OJ,
  ega "0 16.1.5" "dim(B) ≤ dim(A)",
  ega "IV 4.1.2" "(ii), special case",
  ega "IV 5.4.2" "Affine case",
  ega "IV 5.4.3" "dim(B) ≤ dim(A)",
  ega "IV 5.5.1" "special case",
  ega "IV 5.5.2" "special case",
  ega "IV 5.6.6" "special case"]
theorem integral_dim_up
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
    ∀ q : PrimeSpectrum S, IsClosed ({q} : Set (PrimeSpectrum S)) →
      IsClosed ({PrimeSpectrum.comap f q} : Set (PrimeSpectrum R)) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have halg : algebraMap R S = f := rfl
  constructor
  · -- (a) dimension inequality via strict monotonicity of the contraction map
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f) ?_
    intro p q hpq
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, ← halg]
    have := p.isPrime
    exact Ideal.IsIntegral.comap_lt_comap hpq
  · -- (b) closed points map to closed points (maximal contracts to maximal)
    intro q hq
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hq ⊢
    rw [PrimeSpectrum.comap_asIdeal, ← halg]
    have := hq
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal
