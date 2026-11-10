module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import StacksFrontier.FieldTheory.KummerExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Lemma 15.117.13 of the Stacks project (tag 09F2).

Throughout, `p` is a prime number and `A` is a commutative ring (with `1`).

## Main Definitions

* (Primitive `p`-th root of unity) An element `ζ ∈ A` is a *primitive `p`-th root of
  unity* if it arises as the image of the standard generator under a ring homomorphism
  `ℤ[ζ] = ℤ[x]/(x^(p-1) + ... + x + 1) → A`, where `ℤ[ζ]` is the ring of integers of the
  `p`-th cyclotomic field `ℚ(ζ)`. In particular such a `ζ` satisfies
  `ζ^(p-1) + ... + ζ + 1 = 0`, and hence `ζ^p = 1`.

* (The element `w`) `w = 1 - ζ ∈ A`, and `(w) ⊆ A` is the ideal it generates.

* (The polynomial `P`) Consider the expression
    `((1 + w z)^p - 1) / w^p = ∑_{i=1}^{p} (p choose i) w^(i-p) z^i`,
  formed a priori in `(ℤ[ζ][w⁻¹])[z]` (or, after base change, in `(A[w⁻¹])[z]`).
  Part of the assertion (Statement 1) is that all of its coefficients in fact lie in `A`;
  the resulting honest polynomial is `P(z) ∈ A[z]`, with coefficients
    `c_p = 1`,  `c_i = (p choose i) w^(i-p)`  for `1 ≤ i ≤ p-1`.

## Main Statements

Let `p` be prime, `A` a commutative ring containing a primitive `p`-th root of unity `ζ`,
and `w = 1 - ζ`. The following hold for ONE common polynomial `P ∈ A[z]`.

* (Statement 1: integrality and shape of `P`) Every coefficient of `((1+wz)^p - 1)/w^p`
  lies in `A`, i.e. `w^(p-i)` divides `(p choose i)` in `A` with `c_i` as quotient, so that
  `P(z)` is a genuine element of `A[z]`; moreover
    `P(z) = z^p - z + ∑_{0 < i < p} a_i z^i`,   with `a_i ∈ (w)`.
  Here `-z` is split off explicitly, so the total coefficient of `z^1` is `-1 + a_1`,
  and the assertion `a_i ∈ (w)` for `0 < i < p` includes `a_1 ∈ (w)`. (It is NOT claimed
  that `c_1 = -1`; one only has `c_1 ≡ -1 (mod (w))`.)

* (Statement 2: functional equation) In `A[z_1, z_2]`,
    `P(z_1 + z_2 + w z_1 z_2) = P(z_1) + P(z_2) + w^p P(z_1) P(z_2)`.
-/

open Polynomial

/-- The coefficients of `(1 + wX)^n` over a commutative ring: the `i`-th one is
`w^i * (n choose i)` for `i ≤ n`. -/
theorem aux_coeff_one_add_wX_pow {R : Type*} [CommRing R] (w : R) (n i : ℕ) (hi : i ≤ n) :
    ((1 + Polynomial.C w * Polynomial.X) ^ n).coeff i = w ^ i * (n.choose i : R) := by
  have hexp : ((1 : R[X]) + Polynomial.C w * Polynomial.X) ^ n
      = ∑ k ∈ Finset.range (n + 1),
          Polynomial.C (w ^ k * (n.choose k : R)) * Polynomial.X ^ k := by
    rw [add_comm (1 : R[X]) (Polynomial.C w * Polynomial.X), add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_pow, one_pow, mul_one, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast,
      Polynomial.C_mul]
    ring
  rw [hexp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 1)) i fun k => w ^ k * (n.choose k : R)]
  simp [hi]

/-
## Encoding notes

* "A contains a primitive `p`-th root of unity `ζ`" is encoded faithfully as the data of a
  ring homomorphism `f : ℤ[ζ_p] → A`, where `ℤ[ζ_p] = CyclotomicRing p ℤ ℚ` is the ring of
  integers of the `p`-th cyclotomic field; `ζ` is the image under `f` of the standard
  generator `zetaGen` (a primitive `p`-th root of unity in `ℤ[ζ_p]`). This is exactly the
  set-up of Definition 1, and it makes the defining cyclotomic relation
  `∑_{i<p} ζ^i = 0` (hence `ζ^p = 1`) available in `A` by transport along `f`
  (see `zetaA_geom_sum_eq_zero` below).

* The expression `((1 + wz)^p - 1)/w^p` is formed a priori over `A[w⁻¹]`, and Statement 1 is
  the assertion that it lies in `A[z]`. That assertion is recorded over `A` itself, by the
  predicate `intProp P`:
    `w^p · P = (1 + wX)^p - 1` in `A[X]`,   `P = ∑_{0 < i ≤ p} c_i z^i`,
    `w^{p-i} · c_i = (p choose i)`  for `0 < i ≤ p`,
  the last clause being the equation `c_i = (p choose i) w^{i-p}` with the division
  discharged. In a general ring `w` may be a zero divisor, so these equations need not pin
  `c_i` down uniquely — but they are exactly what "`(p choose i) w^{i-p}` is an element of
  `A`" says, and they are proved here for the base change along `f` of the universal
  coefficients over `D = ℤ[ζ_p]`, where `w` is a nonzerodivisor and the quotient is
  unambiguous. This is the source's own reduction to the case `A = ℤ[ζ]`.

* The corresponding statement in the localization, `w^p · (P over A[w⁻¹]) = (1 + wX)^p - 1`
  (predicate `quotChar P`), is recorded as well, but it must not be mistaken for Statement 1:
  it constrains only the image of `P` in `(A[w⁻¹])[X]`, and when `w` is nilpotent `A[w⁻¹]` is
  the zero ring, so that every `P` — including `P = 0` — satisfies it. See
  `quotChar_of_isNilpotent`, and `natCast_eq_zero_of_intProp` for the contrast with
  `intProp`.

* All four assertions (`intProp`, `quotChar`, the shape decomposition `shapeProp`, and the
  functional equation `funcEq`) are bundled into a SINGLE existential, so that one and the
  same polynomial `P ∈ A[X]` witnesses all of them simultaneously. This is the canonical
  object of Definition 3.
-/

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime]
  (f : CyclotomicRing p ℤ ℚ →+* A)

-- Main Definition(s)

/-- The standard generator `ζ` of `ℤ[ζ_p] = CyclotomicRing p ℤ ℚ`, a primitive `p`-th root
of unity in that ring. -/
noncomputable def zetaGen : CyclotomicRing p ℤ ℚ :=
  IsCyclotomicExtension.zeta p ℤ (CyclotomicRing p ℤ ℚ)

/-- A primitive `p`-th root of unity in `A`: the image of the standard generator under the
ring homomorphism `f : ℤ[ζ_p] → A` witnessing that `A` contains such a root. -/
noncomputable def zetaA : A := f zetaGen

/-- The element `w = 1 - ζ ∈ A`. -/
noncomputable def wElt : A := 1 - zetaA f

/-- The standard generator `zetaGen` is a primitive `p`-th root of unity. -/
private theorem isPrimitiveRoot_zetaGen : IsPrimitiveRoot (zetaGen (p := p)) p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℤ _

/-- Correctness of the definition of `zetaA`: the image `ζ` of the standard generator
satisfies the defining cyclotomic relation `ζ^(p-1) + ... + ζ + 1 = 0`, i.e.
`∑_{i < p} ζ^i = 0`. (This characterizes `ζ` as a primitive `p`-th root of unity in the
sense of Definition 1.) -/
theorem zetaA_geom_sum_eq_zero :
    ∑ i ∈ Finset.range p, (zetaA f) ^ i = 0 := by
  have h0 : ∑ i ∈ Finset.range p, (zetaGen (p := p)) ^ i = 0 :=
    isPrimitiveRoot_zetaGen.geom_sum_eq_zero hp.out.one_lt
  have := congrArg f h0
  simpa [zetaA, map_sum, map_pow] using this

/-- **Quotient characterization of `P` after inverting `w`.**
The image of `P : A[X]` under the localization map `A[X] → (A[w⁻¹])[X]` is the genuine
quotient `((1 + w z)^p - 1) / w^p`, expressed without division as
`w^p · (P over A[w⁻¹]) = (1 + w X)^p - 1`. Since `w` is a unit in `A[w⁻¹]`, the factor
`w^p` is cancellable, so this determines the image of `P` in `(A[w⁻¹])[X]` uniquely.

This is *not* by itself the integrality assertion of Statement 1: it says nothing about `P`
over `A`, and it is outright vacuous when `w` is nilpotent, since then `A[w⁻¹]` is the zero
ring and every `P` satisfies it (`quotChar_of_isNilpotent`). Integrality over `A` is
`intProp` below; `quotChar` is kept because it is the statement in the localization, and it
follows from `intProp` by applying `Polynomial.map`. -/
noncomputable def quotChar (P : A[X]) : Prop :=
  (C (algebraMap A (Localization.Away (wElt f)) (wElt f))) ^ p
      * (P.map (algebraMap A (Localization.Away (wElt f))))
    = (1 + C (algebraMap A (Localization.Away (wElt f)) (wElt f)) * Polynomial.X) ^ p - 1

/-- **Integrality of `P`, stated over `A` itself** (Statement 1, first part).

The source asserts that `((1 + wz)^p - 1)/w^p` *is an element of* `A[z]`: the coefficients
`(p choose i) · w^{i-p}` of the quotient, formed a priori only after inverting `w`, are
genuine elements of `A`. Written without division, for `P = ∑ c_i z^i`:

* `w^p · P = (1 + wX)^p - 1` in `A[X]` (the quotient is exact over `A`, not merely over
  `A[w⁻¹]`);
* `P` has degree at most `p` and no constant term, i.e. `P = ∑_{0 < i ≤ p} c_i z^i`;
* `w^{p-i} · c_i = (p choose i)` for `0 < i ≤ p`, which is exactly the equation
  `c_i = (p choose i)/w^{p-i} = (p choose i) w^{i-p}` with the division discharged. (Taking
  `i = p` gives `c_p = 1`, so `P` is monic of degree `p`.)

Unlike `quotChar`, this has content for every `A`: e.g. it already forces `(p : A) = 0`
whenever `w^{p-1} = 0` (`natCast_eq_zero_of_intProp`). -/
noncomputable def intProp (P : A[X]) : Prop :=
  (Polynomial.C (wElt f)) ^ p * P = (1 + Polynomial.C (wElt f) * Polynomial.X) ^ p - 1 ∧
    P.natDegree ≤ p ∧ P.coeff 0 = 0 ∧
    ∀ i, 0 < i → i ≤ p → (wElt f) ^ (p - i) * P.coeff i = (p.choose i : A)

/-- **Shape decomposition of `P`** (Statement 1, second part).
`P(z) = z^p - z + ∑_{0 < i < p} a_i z^i` with each `a_i ∈ (w)`. -/
noncomputable def shapeProp (P : A[X]) : Prop :=
  ∃ a : ℕ → A,
    (∀ i, 0 < i → i < p → a i ∈ Ideal.span ({wElt f} : Set A)) ∧
    P = Polynomial.X ^ p - Polynomial.X
          + ∑ i ∈ Finset.Ioo 0 p, C (a i) * Polynomial.X ^ i

/-- **Functional equation of `P`** (Statement 2).
In `A[z_1, z_2] = MvPolynomial (Fin 2) A` (with `z_1 = X 0`, `z_2 = X 1`, and substitution
into `P` via `Polynomial.aeval`):
`P(z_1 + z_2 + w z_1 z_2) = P(z_1) + P(z_2) + w^p P(z_1) P(z_2)`. -/
noncomputable def funcEq (P : A[X]) : Prop :=
  let R := MvPolynomial (Fin 2) A
  let z1 : R := MvPolynomial.X 0
  let z2 : R := MvPolynomial.X 1
  (Polynomial.aeval (z1 + z2 + (algebraMap A R (wElt f)) * z1 * z2) P)
    = (Polynomial.aeval z1 P) + (Polynomial.aeval z2 P)
        + (algebraMap A R ((wElt f) ^ p)) * (Polynomial.aeval z1 P) * (Polynomial.aeval z2 P)

-- Construction of the polynomial P

/-- `u f k = ∑_{j<k} ζ^j` where `ζ = zetaA f`. Note `u f 0 = 0` and
`w * (u f k) = 1 - ζ^k`. -/
noncomputable def uElt (k : ℕ) : A := ∑ j ∈ Finset.range k, (zetaA f) ^ j

/-- The candidate polynomial `P = ∏_{k<p} (X + C (u f k))`. -/
noncomputable def Pcand : A[X] :=
  ∏ k ∈ Finset.range p, (Polynomial.X + Polynomial.C (uElt f k))

/-- `w * (u f k) = 1 - ζ^k`. -/
theorem wElt_mul_uElt (k : ℕ) :
    (wElt f) * (uElt f k) = 1 - (zetaA f) ^ k := by
  unfold wElt uElt
  rw [Finset.mul_sum]
  have : ∀ j ∈ Finset.range k, (1 - zetaA f) * (zetaA f) ^ j
      = (zetaA f) ^ j - (zetaA f) ^ (j + 1) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub' (fun j => (zetaA f) ^ j)]
  simp

/-- Product identity over `A`: `∏_{k<p} (X - C (ζ^k)) = X^p - 1`. Transported from the
universal cyclotomic ring `D = ℤ[ζ_p]` where `zetaGen` is a primitive `p`-th root of unity
in a domain. -/
theorem prod_X_sub_C_zetaA_pow :
    ∏ k ∈ Finset.range p, (Polynomial.X - Polynomial.C ((zetaA f) ^ k))
      = Polynomial.X ^ p - 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hgen : IsPrimitiveRoot (zetaGen (p := p)) p := isPrimitiveRoot_zetaGen
  -- the identity over the domain D
  have hD : ∏ k ∈ Finset.range p,
      (Polynomial.X - Polynomial.C ((zetaGen (p := p)) ^ k))
      = Polynomial.X ^ p - 1 := by
    rw [X_pow_sub_one_eq_prod hp0 hgen]
    refine Finset.prod_bij (fun k _ => (zetaGen (p := p)) ^ k) ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_nthRootsFinset hp0]
      rw [← pow_mul, mul_comm, pow_mul, hgen.pow_eq_one, one_pow]
    · intro a₁ ha₁ a₂ ha₂ heq
      exact hgen.pow_inj (Finset.mem_range.1 ha₁) (Finset.mem_range.1 ha₂) heq
    · intro b hb
      rw [mem_nthRootsFinset hp0] at hb
      obtain ⟨i, hi, hib⟩ := hgen.eq_pow_of_pow_eq_one hb
      exact ⟨i, Finset.mem_range.2 hi, hib⟩
    · intro a ha
      rfl
  -- transport via Polynomial.map f
  have := congrArg (Polynomial.map f) hD
  rw [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] at this
  rw [← this]
  apply Finset.prod_congr rfl
  intro k _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [zetaA, ← map_pow]

/-- Backbone identity: `w^p · P = (1 + w X)^p - 1` in `A[X]`. -/
theorem wpow_mul_Pcand :
    (Polynomial.C (wElt f)) ^ p * (Pcand f)
      = (1 + Polynomial.C (wElt f) * Polynomial.X) ^ p - 1 := by
  unfold Pcand
  have hconst : (Polynomial.C (wElt f)) ^ p
      = ∏ _k ∈ Finset.range p, Polynomial.C (wElt f) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hconst, ← Finset.prod_mul_distrib]
  have hfac : ∀ k ∈ Finset.range p,
      Polynomial.C (wElt f) * (Polynomial.X + Polynomial.C (uElt f k))
        = (1 + Polynomial.C (wElt f) * Polynomial.X) - Polynomial.C ((zetaA f) ^ k) := by
    intro k _
    have h1 : Polynomial.C (wElt f * uElt f k) = Polynomial.C (1 - (zetaA f) ^ k) := by
      rw [wElt_mul_uElt]
    rw [mul_add, ← Polynomial.C_mul] at *
    rw [h1]
    rw [Polynomial.C_sub, Polynomial.C_1]
    ring
  rw [Finset.prod_congr rfl hfac]
  -- now ∏ ((1+wX) - C(ζ^k)) = (1+wX)^p - 1, obtained by composing
  -- prod_X_sub_C_zetaA_pow with X ↦ 1+wX
  have hcomp := congrArg (fun q : A[X] => q.comp (1 + Polynomial.C (wElt f) * Polynomial.X))
    (prod_X_sub_C_zetaA_pow f)
  simp only [Polynomial.prod_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.one_comp, Polynomial.pow_comp] at hcomp
  exact hcomp

/-- `quotChar` holds for `Pcand`. -/
theorem quotChar_Pcand : quotChar f (Pcand f) := by
  unfold quotChar
  have h := congrArg (Polynomial.map (algebraMap A (Localization.Away (wElt f))))
    (wpow_mul_Pcand f)
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] at h
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X] at h
  exact h

/-- **The localization predicate `quotChar` is vacuous when `w` is nilpotent.**

If `w ^ n = 0` in `A`, then in `A[w⁻¹] = Localization.Away w` the element `w` is at once a
unit and nilpotent, so `0 = 1` there and `A[w⁻¹]` is the zero ring. Consequently *every*
`P : A[X]` satisfies `quotChar f P`; in particular `P = 0` does, and the predicate carries no
information about `P` whatsoever. Such `(A, f)` are not pathological edge cases excluded by
the hypotheses: `w` is nilpotent for instance whenever `f` kills `w`, i.e. for every `f`
factoring through `ℤ[ζ_p]/(1 - ζ)`, which by the source's own proof is the (maximal, hence
proper) ideal `(p, w) = (w)`, with quotient the field `𝔽_p`.

This is why Statement 1 is recorded over `A` by `intProp`, which is an honest constraint in
this situation (`natCast_eq_zero_of_intProp`). -/
theorem quotChar_of_isNilpotent (hw : IsNilpotent (wElt f)) (P : A[X]) : quotChar f P := by
  obtain ⟨n, hn⟩ := hw
  have hunit : IsUnit (algebraMap A (Localization.Away (wElt f)) (wElt f)) :=
    IsLocalization.map_units (M := Submonoid.powers (wElt f)) (Localization.Away (wElt f))
      ⟨wElt f, Submonoid.mem_powers _⟩
  have hzero : IsUnit (0 : Localization.Away (wElt f)) := by
    have h := hunit.pow n
    rwa [← map_pow, hn, map_zero] at h
  have : Subsingleton (Localization.Away (wElt f)) :=
    subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
  unfold quotChar
  exact Polynomial.ext fun k => Subsingleton.elim _ _

/-- Contrast with `quotChar_of_isNilpotent`: `intProp` has content exactly where `quotChar`
has none. If `w ^ (p - 1) = 0` — e.g. if `w = 0` — then `intProp f P` forces `(p : A) = 0`,
because its `i = 1` clause reads `w^{p-1} · c_1 = p`. -/
theorem natCast_eq_zero_of_intProp (P : A[X]) (h : intProp f P)
    (hw : (wElt f) ^ (p - 1) = 0) : (p : A) = 0 := by
  have h1 := h.2.2.2 1 one_pos hp.out.one_lt.le
  rw [hw, zero_mul, Nat.choose_one_right] at h1
  exact h1.symm

/-- `intProp` always has content: its `i = p` clause reads `w^0 · c_p = (p choose p) = 1`, so
any `P` satisfying it is monic of degree `p`. In particular `intProp f 0` fails over every
nontrivial `A`, while `quotChar f 0` holds as soon as `w` is nilpotent. -/
theorem coeff_eq_one_of_intProp (P : A[X]) (h : intProp f P) : P.coeff p = 1 := by
  have h1 := h.2.2.2 p hp.out.pos le_rfl
  rwa [Nat.sub_self, pow_zero, one_mul, Nat.choose_self, Nat.cast_one] at h1

/-! ### A concrete degenerate `(A, f)`

For `p = 2` the universal primitive root of unity is `ζ = -1`, so `w = 1 - ζ = 2` in *every*
`A`; and since `ℤ[ζ_2] = ℤ` there is a ring homomorphism `ℤ[ζ_2] → ZMod 4`. In the nontrivial
ring `ZMod 4` the element `w = 2` is nilpotent, so `quotChar` is satisfied there by every
`P` — including `P = 0`, which `intProp` excludes. This is the witness showing that the
localization form of Statement 1 is not merely weaker but empty on part of the hypothesis
class. -/

/-- `ℤ[ζ_2] = ℤ`: the `ℤ`-subalgebra of `ℚ(ζ_2)` generated by the square roots of `1`, which
is the definition of `CyclotomicRing 2 ℤ ℚ`, is `⊥`. -/
theorem adjoin_sq_eq_one_eq_bot :
    Algebra.adjoin ℤ {b : CyclotomicField 2 ℚ | b ^ 2 = 1} = ⊥ := by
  refine le_antisymm (Algebra.adjoin_le ?_) bot_le
  intro b hb
  have hb2 : b * b = 1 := by
    have hb' : b ^ 2 = 1 := hb
    rwa [pow_two] at hb'
  rcases mul_self_eq_one_iff.mp hb2 with h1 | h1
  · rw [SetLike.mem_coe, h1]; exact one_mem _
  · rw [SetLike.mem_coe, h1]; exact neg_mem (one_mem _)

/-- `ℤ[ζ_2] ≃ ℤ`. -/
noncomputable def cyclotomicRingTwoEquivInt : CyclotomicRing 2 ℤ ℚ ≃ₐ[ℤ] ℤ :=
  have : NumberField (CyclotomicField 2 ℚ) :=
    IsCyclotomicExtension.numberField {2} ℚ (CyclotomicField 2 ℚ)
  (Subalgebra.equivOfEq _ _ adjoin_sq_eq_one_eq_bot).trans
    (Algebra.botEquivOfInjective (RingHom.injective_int (algebraMap ℤ (CyclotomicField 2 ℚ))))

/-- A ring homomorphism `ℤ[ζ_2] → ZMod 4`, i.e. an instance of the hypotheses of the lemma
with `p = 2` and `A = ZMod 4`. -/
noncomputable def toZMod4 : CyclotomicRing 2 ℤ ℚ →+* ZMod 4 :=
  (Int.castRingHom (ZMod 4)).comp cyclotomicRingTwoEquivInt.toRingEquiv.toRingHom

/-- For `p = 2` the universal root of unity is `ζ = -1`, so `w = 1 - ζ = 2` in every `A`. -/
theorem wElt_eq_two {B : Type*} [CommRing B] (g : CyclotomicRing 2 ℤ ℚ →+* B) :
    wElt g = 2 := by
  have hneg : (zetaGen (p := 2)) = -1 := isPrimitiveRoot_zetaGen.eq_neg_one_of_two_right
  unfold wElt zetaA
  rw [hneg, map_neg, map_one]
  ring

/-- **The degenerate witness.** With `p = 2`, `A = ZMod 4` and `f = toZMod4`, we have `w = 2`,
which is nilpotent, so `quotChar` holds for EVERY `P : (ZMod 4)[X]`. -/
theorem quotChar_toZMod4 (P : (ZMod 4)[X]) : quotChar toZMod4 P := by
  refine quotChar_of_isNilpotent toZMod4 ?_ P
  rw [wElt_eq_two]
  exact ⟨2, by decide⟩

/-- ... whereas `intProp` is not satisfied by `P = 0` there: the old predicate cannot see the
difference between the intended `z^2 + z` and `0`, the new one can. -/
theorem not_intProp_toZMod4_zero : ¬ intProp toZMod4 (0 : (ZMod 4)[X]) := by
  intro h
  have h1 := coeff_eq_one_of_intProp toZMod4 0 h
  rw [Polynomial.coeff_zero] at h1
  exact absurd h1 (by decide)

/-- The key "evaluated backbone" identity in any `A`-algebra `R`, here used with
`R = MvPolynomial (Fin 2) A`. For any `g`,
`(algebraMap A R w)^p * aeval g P = (1 + algebraMap A R w * g)^p - 1`. -/
theorem star_eval (g : MvPolynomial (Fin 2) A) :
    (algebraMap A (MvPolynomial (Fin 2) A) (wElt f)) ^ p
        * (Polynomial.aeval g) (Pcand f)
      = (1 + (algebraMap A (MvPolynomial (Fin 2) A) (wElt f)) * g) ^ p - 1 := by
  have h := congrArg (Polynomial.aeval g) (wpow_mul_Pcand f)
  rw [map_mul, map_pow, map_sub, map_pow, map_add, map_mul, map_one] at h
  simpa [Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.algebraMap_eq] using h

/-- Over the universal ring `D = ℤ[ζ_p]` the element `w = 1 - ζ` is nonzero: `ζ` is a
primitive `p`-th root of unity there, so `ζ ≠ 1`. As `D` is a domain, `w` is therefore a
nonzerodivisor, which is what makes the quotient `((1 + wz)^p - 1)/w^p` unambiguous over `D`
and lets the integrality statement be transported to any `A`. -/
theorem wElt_id_ne_zero : wElt (RingHom.id (CyclotomicRing p ℤ ℚ)) ≠ 0 := by
  have hzne : (zetaGen (p := p)) ≠ 1 := isPrimitiveRoot_zetaGen.ne_one hp.out.one_lt
  unfold wElt zetaA
  simp only [RingHom.id_apply]
  intro h
  exact hzne (sub_eq_zero.1 h).symm

/-- `funcEq` holds for `Pcand` over the universal domain `D = ℤ[ζ_p]`. -/
theorem funcEq_Pcand_id :
    funcEq (RingHom.id (CyclotomicRing p ℤ ℚ)) (Pcand (RingHom.id (CyclotomicRing p ℤ ℚ))) := by
  set D := CyclotomicRing p ℤ ℚ
  set fid : D →+* D := RingHom.id D
  unfold funcEq
  set R := MvPolynomial (Fin 2) D with hR
  set z1 : R := MvPolynomial.X 0
  set z2 : R := MvPolynomial.X 1
  set W : R := algebraMap D R (wElt fid) with hW
  set Z : R := z1 + z2 + W * z1 * z2 with hZ
  set Pz1 := (Polynomial.aeval z1) (Pcand fid) with hPz1
  set Pz2 := (Polynomial.aeval z2) (Pcand fid) with hPz2
  set Pz := (Polynomial.aeval Z) (Pcand fid) with hPz
  -- W^p is nonzero
  have hwne : wElt fid ≠ 0 := wElt_id_ne_zero
  have hWne : W ^ p ≠ 0 := by
    rw [hW, ← map_pow, MvPolynomial.algebraMap_eq, Ne, MvPolynomial.C_eq_zero]
    exact pow_ne_zero p hwne
  -- the three star identities
  have hsZ := star_eval fid Z
  have hsz1 := star_eval fid z1
  have hsz2 := star_eval fid z2
  rw [← hW] at hsZ hsz1 hsz2
  rw [← hPz] at hsZ
  rw [← hPz1] at hsz1
  rw [← hPz2] at hsz2
  -- factorization 1 + W Z = (1+Wz1)(1+Wz2)
  have hfact : 1 + W * Z = (1 + W * z1) * (1 + W * z2) := by
    rw [hZ]; ring
  rw [hfact] at hsZ
  -- W^p * goal-LHS = W^p * goal-RHS
  have key : W ^ p * Pz = W ^ p * (Pz1 + Pz2 + (algebraMap D R ((wElt fid) ^ p)) * Pz1 * Pz2) := by
    rw [hsZ]
    have hwp : algebraMap D R ((wElt fid) ^ p) = W ^ p := by
      rw [hW, map_pow]
    rw [hwp]
    -- expand RHS using hsz1, hsz2
    have e1 : W ^ p * Pz1 = (1 + W * z1) ^ p - 1 := hsz1
    have e2 : W ^ p * Pz2 = (1 + W * z2) ^ p - 1 := hsz2
    have : W ^ p * (Pz1 + Pz2 + W ^ p * Pz1 * Pz2)
        = (W ^ p * Pz1) + (W ^ p * Pz2) + (W ^ p * Pz1) * (W ^ p * Pz2) := by ring
    rw [this, e1, e2]
    rw [mul_pow]
    ring
  exact mul_left_cancel₀ hWne key

/-- `f (wElt fid) = wElt f`, i.e. `f` carries the universal `w` to the `w` over `A`. -/
theorem map_wElt_id :
    f (wElt (RingHom.id (CyclotomicRing p ℤ ℚ))) = wElt f := by
  unfold wElt zetaA
  simp

/-- `Pcand f` is the image of the universal `Pcand` under `Polynomial.map f`. -/
theorem Pcand_map :
    Pcand f = (Pcand (RingHom.id (CyclotomicRing p ℤ ℚ))).map f := by
  unfold Pcand
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  congr 2
  unfold uElt zetaA
  simp [map_sum, map_pow]

omit hp in
/-- Transport of `aeval` under `MvPolynomial.map f`: for `Q : D[X]` and
`g' : MvPolynomial (Fin 2) D`,
`(MvPolynomial.map f) (aeval g' Q) = aeval ((MvPolynomial.map f) g') (Q.map f)`. -/
theorem map_aeval_comm (Q : (CyclotomicRing p ℤ ℚ)[X])
    (g' : MvPolynomial (Fin 2) (CyclotomicRing p ℤ ℚ)) :
    (MvPolynomial.map f) ((Polynomial.aeval g') Q)
      = (Polynomial.aeval ((MvPolynomial.map f) g')) (Q.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def]
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext d
  simp [MvPolynomial.algebraMap_eq]

/-- **Functional equation holds for `Pcand f`** (Statement 2).
Obtained by transporting the universal-domain identity `funcEq_Pcand_id` along
`MvPolynomial.map f`. There is no new mathematical content: `MvPolynomial.map f` is a ring
hom that commutes with `aeval` (via `map_aeval_comm`), sends `X i ↦ X i`, carries
`algebraMap D R (wElt id)` to `algebraMap A R' (wElt f)` (via `map_wElt_id`), and carries
`Pcand id` to `Pcand f` (via `Pcand_map`); so the equation transports verbatim. -/
theorem funcEq_Pcand : funcEq f (Pcand f) := by
  have hid := funcEq_Pcand_id (p := p)
  unfold funcEq at hid ⊢
  set Mf := MvPolynomial.map (σ := Fin 2) f with hMf
  have himg := congrArg Mf hid
  -- naturality of algebraMap under Mf
  have hnat : ∀ x : CyclotomicRing p ℤ ℚ,
      Mf (algebraMap (CyclotomicRing p ℤ ℚ) (MvPolynomial (Fin 2) (CyclotomicRing p ℤ ℚ)) x)
        = algebraMap A (MvPolynomial (Fin 2) A) (f x) := by
    intro x
    rw [hMf, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  simp only [hMf, map_add, map_mul, map_pow, map_aeval_comm, MvPolynomial.map_X] at himg
  rw [← hMf, hnat, map_wElt_id, ← map_pow] at himg
  rw [Pcand_map]
  exact himg

/-- Helper: over `ZMod p`, `∏_{a} (X + C a) = X^p - X`. -/
theorem prod_zmod_X_add_C_eq (p : ℕ) [Fact p.Prime] :
    ∏ a : ZMod p, (Polynomial.X + Polynomial.C a) = (Polynomial.X ^ p - Polynomial.X : (ZMod
        p)[X]) := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hcard1 : 1 < Fintype.card (ZMod p) := by
    simpa [hcard] using (Fact.out : p.Prime).one_lt
  have hmonic : (Polynomial.X ^ Fintype.card (ZMod p) - Polynomial.X : (ZMod p)[X]).Monic := by
    have h : (Polynomial.X : (ZMod p)[X]).degree
        < (Polynomial.X ^ Fintype.card (ZMod p) : (ZMod p)[X]).degree := by
      rw [degree_X, degree_X_pow]
      exact_mod_cast hcard1
    exact (monic_X_pow _).sub_of_left h
  have hsplits : (Polynomial.X ^ Fintype.card (ZMod p) - Polynomial.X : (ZMod p)[X]).Splits := by
    rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
        FiniteField.X_pow_card_sub_X_natDegree_eq _ hcard1]
    rfl
  have heq := hsplits.eq_prod_roots_of_monic hmonic
  rw [FiniteField.roots_X_pow_card_sub_X, hcard] at heq
  rw [heq, ← Finset.prod_eq_multiset_prod,
      ← Equiv.prod_comp (Equiv.neg (ZMod p)) (fun a => Polynomial.X - Polynomial.C a)]
  simp

/-- Helper: over any commutative ring `R` with `(p : R) = 0` (`p` prime),
`∏_{k<p} (X + C k) = X^p - X`. -/
theorem prod_range_X_add_C_eq (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp0 : (p : R) = 0) :
    ∏ k ∈ Finset.range p, (Polynomial.X + Polynomial.C (k : R))
      = Polynomial.X ^ p - Polynomial.X := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have : CharP R c := hc
  have hcp : c ∣ p := (CharP.cast_eq_zero_iff R c p).mp hp0
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd c hcp with hc1 | hcp'
  · have : CharP R 1 := hc1 ▸ hc
    have : Subsingleton R := CharP.CharOne.subsingleton
    apply Subsingleton.elim
  · subst hcp'
    let ψ : ZMod c →+* R := ZMod.castHom (dvd_refl c) R
    have hmap := congrArg (Polynomial.map ψ) (prod_zmod_X_add_C_eq c)
    rw [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at hmap
    have hbij : ∏ k ∈ Finset.range c, (Polynomial.X + Polynomial.C (k : R))
        = ∏ i : ZMod c, (Polynomial.X + Polynomial.C (ψ i)) := by
      have : NeZero c := ⟨(Fact.out : c.Prime).ne_zero⟩
      refine Finset.prod_nbij' (fun k => ((k : ℕ) : ZMod c)) (fun i => ZMod.val i)
        (fun a _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
      · intro i _; rw [Finset.mem_range]; exact ZMod.val_lt i
      · intro k hk; rw [Finset.mem_range] at hk; exact ZMod.val_natCast_of_lt hk
      · intro i _; exact ZMod.natCast_zmod_val i
      · intro k hk; rw [Finset.mem_range] at hk; simp [map_natCast]
    rw [hbij, ← hmap]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

/-- `Pcand f` has degree at most `p`: it is a product of `p` linear factors. -/
theorem Pcand_natDegree_le : (Pcand f).natDegree ≤ p := by
  unfold Pcand
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hle : ∀ k ∈ Finset.range p,
      (Polynomial.X + Polynomial.C (uElt f k)).natDegree ≤ 1 := by
    intro k _
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le Polynomial.natDegree_X_le ?_)
    simp
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) hle) ?_
  simp

/-- `Pcand f` has no constant term: its `k = 0` factor is `X + C (uElt f 0) = X`. -/
theorem Pcand_coeff_zero : (Pcand f).coeff 0 = 0 := by
  unfold Pcand
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hp.out.pos)
  have : uElt f 0 = 0 := by unfold uElt; simp
  simp [this]

/-- A polynomial of natural degree `p > 1` with leading coefficient `1` and constant
coefficient `0` is `X^p - X` plus its middle terms, with the linear coefficient shifted by `1`. -/
theorem eq_X_pow_sub_X_add_sum_Ioo {P : A[X]} (hp1 : 1 < p) (hdeg : P.natDegree = p)
    (hc0 : P.coeff 0 = 0) (hcoeffp : P.coeff p = 1) :
    P = Polynomial.X ^ p - Polynomial.X + ∑ i ∈ Finset.Ioo 0 p,
      C (if i = 1 then P.coeff 1 + 1 else P.coeff i) * Polynomial.X ^ i := by
  ext n
  have hgt : p < n → P.coeff n = 0 := fun h => coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X, finsetSum_coeff, coeff_C_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_Ioo]
  split_ifs <;> subst_vars <;> grind

/-- **Shape decomposition holds for `Pcand f`** (Statement 1, second part).

`Pcand f = X^p - X + ∑_{0 < i < p} a_i X^i` with each `a_i ∈ (w)`.

## Informal proof

Write `c_i := (Pcand f).coeff i` and `w := wElt f`.

**Step A (degree, monicity, constant term).** `Pcand f = ∏_{k<p} (X + C (uElt f k))` is a
product of `p` monic linear factors, hence monic of degree `p`; so `c_p = 1` and `c_i = 0`
for `i > p`. The `k = 0` factor is `X + C (uElt f 0) = X + C 0 = X` (since
`uElt f 0 = ∑_{j<0} ζ^j = 0`), so `X ∣ Pcand f`, giving `c_0 = (Pcand f).coeff 0 = 0`.

**Step B (the divisibility of the middle coefficients).** From the backbone identity
`wpow_mul_Pcand`: `C(w)^p · Pcand f = (1 + C(w)·X)^p - 1`. Expanding the binomial,
`(1 + C(w)·X)^p - 1 = ∑_{i=1}^{p} C((p choose i) · w^i) · X^i`. Comparing coefficients of
`X^i` on both sides gives, for every `i`,
  `w^p · c_i = (p choose i) · w^i`.                                      (★)
(For `i = p`: `w^p · c_p = w^p`, consistent with `c_p = 1`. For `i = 0`: `0 = 0`.)

Now work over the universal domain `D = ℤ[ζ_p]` (a Dedekind domain in which `w_D ≠ 0`).
There, `p = u · w_D^{p-1}` for a unit `u ∈ D^×` — the standard fact that
`p = ∏_{k=1}^{p-1}(1 - ζ^k)` with each `1 - ζ^k` an associate of `w_D = 1 - ζ`. Hence in `D`
(where we may cancel the nonzero `w_D^p`), identity (★) becomes
  `c_i^D = (p choose i) · w_D^{i-p} = (p choose i)/p · u · w_D^{i-1}`.
Since `p` is prime and `0 < i < p`, `p ∣ (p choose i)`, so `(p choose i)/p ∈ ℤ ⊆ D` and
  `c_i^D = ((p choose i)/p) · u · w_D^{i-1}`.
Therefore:
  * for `2 ≤ i ≤ p-1`: `c_i^D ∈ (w_D)` because `w_D^{i-1}` has `i-1 ≥ 1`;
  * for `i = 1`: `c_1^D = u`, a unit, and one checks `u ≡ -1 (mod w_D)`, equivalently
    `c_1^D + 1 ∈ (w_D)`. (Reduce mod the prime `(w_D)`: `D/(w_D) ≅ 𝔽_p`, in which
    `c_1^D = p · w_D^{1-p}` reduces — via (★) at `i=1`, `w_D^p c_1^D = p w_D` — to the class
    of `-1`; concretely `∑_{k<p} ζ^k = 0` forces `ζ ≡ 1`, so each `uElt 0..` telescopes and
    the linear coefficient `c_1^D = ∏_{k=1}^{p-1} uElt k` reduces to `(p-1)! ≡ -1` by
    Wilson's theorem mod `p`.)

**Step C (transport to `A`).** Set `a i := f (c_i^D)` for `2 ≤ i ≤ p-1`,
`a 1 := f (c_1^D) + 1`, and `a i := 0` otherwise. By `Pcand_map`,
`Pcand f = (Pcand id).map f`, so `c_i = f (c_i^D)` (`Polynomial.coeff_map`). The ring hom `f`
maps `(w_D)` into `(w)` (image of a span; `map_wElt_id`), so `a i ∈ (w)` for `0 < i < p`.

**Step D (reconstruction).** With these `a i`, prove
`Pcand f = X^p - X + ∑_{i ∈ Ioo 0 p} C (a i) X^i` by `Polynomial.ext`/coefficient matching:
  * coeff `p`: LHS `c_p = 1`; RHS `1 - 0 + 0 = 1` (the `Ioo 0 p` sum omits `i = p`).
  * coeff `0`: LHS `c_0 = 0`; RHS `0 - 0 + 0 = 0`.
  * coeff `1`: LHS `c_1`; RHS `0 - 1 + a 1 = -1 + (c_1 + 1) = c_1`.
  * coeff `i`, `2 ≤ i ≤ p-1`: LHS `c_i`; RHS `0 - 0 + a i = c_i`.
  * coeff `i > p`: both `0`.

This is the substantive step. The cleanest formal route
mirrors `funcEq`/`prod_X_sub_C_zetaA_pow`: prove the coefficient divisibilities over `D`
first, then transport along `f`. -/
theorem shapeProp_Pcand : shapeProp f (Pcand f) := by
  have hp1 : 1 < p := hp.out.one_lt
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact ⟨fun _ => 0, fun i _ _ => Submodule.zero_mem _, Subsingleton.elim _ _⟩
  have : Nontrivial A := hnt
  have hmonic : (Pcand f).Monic := by
    unfold Pcand
    exact monic_prod_of_monic _ _ fun k _ => monic_X_add_C (uElt f k)
  have hdeg : (Pcand f).natDegree = p := by
    unfold Pcand
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_add_C (uElt f k)),
      Finset.sum_congr rfl (fun k _ => natDegree_X_add_C (uElt f k))]
    simp
  set I : Ideal A := Ideal.span ({wElt f} : Set A) with hI
  set q : A →+* A ⧸ I := Ideal.Quotient.mk I with hq
  have hwI : q (wElt f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
  have hzeta1 : q (zetaA f) = 1 := by
    have : q (1 - zetaA f) = 0 := by rw [← wElt]; exact hwI
    rw [map_sub, map_one] at this
    linear_combination -this
  have huk : ∀ k, q (uElt f k) = (k : A ⧸ I) := fun k => by simp [uElt, hzeta1]
  have hp0R : (p : A ⧸ I) = 0 := by simpa [hzeta1] using congrArg q (zetaA_geom_sum_eq_zero f)
  have hmapI : (Pcand f).map q = Polynomial.X ^ p - Polynomial.X := by
    unfold Pcand
    simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, huk]
    exact prod_range_X_add_C_eq (A ⧸ I) p hp0R
  have hqcoeff : ∀ n, q ((Pcand f).coeff n)
      = (if n = p then (1 : A ⧸ I) else 0) - (if n = 1 then 1 else 0) := by
    intro n
    rw [← Polynomial.coeff_map, hmapI, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X]
    simp [eq_comm]
  refine ⟨fun i => if i = 1 then (Pcand f).coeff 1 + 1 else (Pcand f).coeff i, ?_,
    eq_X_pow_sub_X_add_sum_Ioo hp1 hdeg (Pcand_coeff_zero f)
      (by simpa [hdeg] using hmonic.coeff_natDegree)⟩
  intro i hi0 hip
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  simp only []
  by_cases h1 : i = 1
  · subst h1
    rw [ite_eq_left rfl, map_add q, map_one q, hqcoeff]
    have hp1 : (1 : ℕ) ≠ p := by omega
    simp [hp1]
  · rw [ite_eq_right h1, hqcoeff]
    have hip' : i ≠ p := by omega
    simp [hip', h1]

/-- Coefficient form of the backbone identity `w^p · P = (1 + wX)^p - 1`: comparing the
coefficients of `z^i` on both sides gives `w^p · c_i = w^i · (p choose i)` for `0 < i ≤ p`. -/
theorem coeff_wpow_mul_Pcand (i : ℕ) (hi0 : 0 < i) (hip : i ≤ p) :
    (wElt f) ^ p * (Pcand f).coeff i = (wElt f) ^ i * (p.choose i : A) := by
  have h : ((Polynomial.C (wElt f)) ^ p * (Pcand f)).coeff i
      = ((1 + Polynomial.C (wElt f) * Polynomial.X) ^ p - 1 : A[X]).coeff i := by
    rw [wpow_mul_Pcand]
  rw [← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    aux_coeff_one_add_wX_pow (wElt f) p i hip, Polynomial.coeff_one,
    ite_eq_right (by omega : ¬ i = 0), sub_zero] at h
  exact h

/-- **Integrality over the universal ring `D = ℤ[ζ_p]`** — the heart of Statement 1.

For `0 < i ≤ p` the `i`-th coefficient `c_i` of `P` satisfies `w^{p-i} · c_i = (p choose i)`,
that is, `c_i` genuinely *is* the quotient `(p choose i) · w^{i-p}`. Over `D` this is exactly
the divisibility `w^{p-i} ∣ (p choose i)` coming from `p = u · w^{p-1}`; formally it follows
from `coeff_wpow_mul_Pcand` by cancelling the nonzerodivisor `w^i` (`D` is a domain and
`w ≠ 0` by `wElt_id_ne_zero`). -/
theorem wpow_sub_mul_coeff_Pcand_id (i : ℕ) (hi0 : 0 < i) (hip : i ≤ p) :
    (wElt (RingHom.id (CyclotomicRing p ℤ ℚ))) ^ (p - i)
        * (Pcand (RingHom.id (CyclotomicRing p ℤ ℚ))).coeff i
      = (p.choose i : CyclotomicRing p ℤ ℚ) := by
  refine mul_left_cancel₀ (pow_ne_zero i wElt_id_ne_zero) ?_
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hip,
    coeff_wpow_mul_Pcand (RingHom.id (CyclotomicRing p ℤ ℚ)) i hi0 hip]

/-- **Integrality over `A`** (Statement 1, first part): `w^{p-i} · c_i = (p choose i)` for
`0 < i ≤ p`. Obtained from the universal statement by base change along `f`, which is the
source's own reduction ("It suffices to prove this when `A = ℤ[ζ]`"). -/
theorem wpow_sub_mul_coeff_Pcand (i : ℕ) (hi0 : 0 < i) (hip : i ≤ p) :
    (wElt f) ^ (p - i) * (Pcand f).coeff i = (p.choose i : A) := by
  have h := congrArg f (wpow_sub_mul_coeff_Pcand_id (p := p) i hi0 hip)
  rw [map_mul, map_pow, map_wElt_id, map_natCast] at h
  rw [Pcand_map f, Polynomial.coeff_map]
  exact h

/-- **`intProp` holds for `Pcand f`**: the quotient `((1 + wz)^p - 1)/w^p` is an honest
element of `A[z]`, with `i`-th coefficient the honest quotient `(p choose i) w^{i-p}`. -/
theorem intProp_Pcand : intProp f (Pcand f) :=
  ⟨wpow_mul_Pcand f, Pcand_natDegree_le f, Pcand_coeff_zero f,
    fun i hi0 hip => wpow_sub_mul_coeff_Pcand f i hi0 hip⟩

-- Main Statement(s)

/-- **Lemma 15.117.13 (Stacks tag 09F2).**
Let `p` be prime, `A` a commutative ring containing a primitive `p`-th root of unity `ζ`
(encoded by `f : ℤ[ζ_p] → A`), and `w = 1 - ζ`. Then there is ONE common polynomial
`P ∈ A[z]` such that:

* (Statement 1, integrality) `P` *is* the quotient `((1 + w z)^p - 1)/w^p` over `A`:
  `w^p · P = (1 + wz)^p - 1` in `A[z]`, `P = ∑_{0 < i ≤ p} c_i z^i`, and
  `w^{p-i} · c_i = (p choose i)` for `0 < i ≤ p` (predicate `intProp`). In particular `P` is
  monic of degree `p`. The corresponding statement in `(A[w⁻¹])[z]` (predicate `quotChar`) is
  recorded too, but it is weaker — vacuous when `w` is nilpotent, see
  `quotChar_of_isNilpotent` — so it is `intProp` that carries the assertion "`P ∈ A[z]`";
* (Statement 1, shape) `P(z) = z^p - z + ∑_{0 < i < p} a_i z^i` with `a_i ∈ (w)`
  (predicate `shapeProp`);
* (Statement 2, functional equation)
  `P(z_1 + z_2 + w z_1 z_2) = P(z_1) + P(z_2) + w^p P(z_1) P(z_2)` in `A[z_1, z_2]`
  (predicate `funcEq`).

Bundling all of them into a single existential guarantees they hold for the same `P`. -/
@[stacks 09F2]
theorem main_statement :
    ∃ P : A[X], intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P :=
  ⟨Pcand f, intProp_Pcand f, quotChar_Pcand f, shapeProp_Pcand f, funcEq_Pcand f⟩
