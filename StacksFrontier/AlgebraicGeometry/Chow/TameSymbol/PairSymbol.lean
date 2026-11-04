module

public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Existence
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Independence

/-!
# Stacks 0EAS: the tame symbol of the formula Stacks 0EAQ, on an arbitrary pair

Let `(A, 𝔪)` be a Noetherian local ring of dimension one. The formula Stacks 0EAQ attaches to a
simultaneous power factorization of a family of elements of `A`, after a finite modification
`A ⊆ B` (Stacks 0EAG), the element

`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}`

of `κ(𝔪)^*`, namely `AlgebraicGeometry.TameSymbolPreparation.symbolValue`. Stacks 0EAR says that
element depends on neither the modification nor the factorizations, so the formula is a function
of the *pair of elements alone*. This file makes that function, `Stacks.Chow.tameSymbolValue`, and
proves Stacks 0EAS for it: the four identities Stacks 0EAL, 0EAM, 0EAN and 0EAP hold for
**arbitrary pairs of nonzerodivisors of `A`**, so the function is a tame symbol on nonzerodivisors
and extends to the map `∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of Stacks 0EAH satisfying Stacks 0EAI,
0EAJ and 0EAK.

## The function

`Stacks.Chow.tameSymbolValue x y` is the value of the formula at a preparation of the two-element
family `![x, y]`, taken by choice among the values the formula takes there
(`Stacks.Chow.IsTameSymbolValue`), and `1` if the pair admits no preparation at all. Both clauses
are forced:

* two preparations of two families sharing a pair of members give one value for that pair,
  `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_apply_eq`. That is Stacks 0EAR
  (`...symbolValue_eq_of_preparations`) read along a reindexing
  (`AlgebraicGeometry.TameSymbolPreparation.reindex`) onto the pair, together with the one case
  Stacks 0EAR does not cover: a pair of **units** is prepared by a parameter that is either a unit,
  where the local length `m_𝔮` is zero, or a nonunit, where both exponents are zero — so every
  factor of the formula is `1`
  (`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_one_of_isUnit`);
* a pair of units therefore has `1` as its only possible value, which is also what Stacks 0EAN
  demands of it, since `length_A(A/bA) = 0` for `b` a unit. So the fallback never contradicts the
  formula, and `Stacks.Chow.tameSymbolValue_eq_one_of_isUnit` holds whether or not the pair is
  prepared.

`Stacks.Chow.tameSymbolValue_eq_symbolValue` is the identification: at *every* preparation of
*every* family, in any universe, the value of the formula on two members of the family is
`tameSymbolValue` of those two members. Nothing is assumed of the preparation.

## The four identities

Stacks 0EAG supplies, for any finite family of nonzerodivisors not all units, a preparation of the
whole family at once (`AlgebraicGeometry.exists_tameSymbolPreparation_of_ringKrullDim_eq_one`), and
`AlgebraicGeometry.TameSymbolPreparation.baseSymbol` is already a term of
`Stacks.Chow.RegularTameSymbol` whose value on the prepared family is the formula
(`...baseSymbol_apply`). So each identity is proved by preparing the finitely many elements it
mentions simultaneously — `a, a', a a', b` for Stacks 0EAL, `b` for Stacks 0EAM, `u, b` for
Stacks 0EAN, `a, b, b - a` for Stacks 0EAP — and reading off the corresponding field of that one
symbol: `Stacks.Chow.exists_regularTameSymbol_apply_eq`. The remaining case, that the elements
involved are all units, is `Stacks.Chow.tameSymbolValue_eq_one_of_isUnit` on each factor; it is not
vacuous, since a one-dimensional Noetherian local ring can have every nonzerodivisor a unit (its
maximal ideal may consist of zerodivisors).

The hypotheses are the source's: `A` Noetherian local with `ringKrullDim A = 1`, and the arguments
nonzerodivisors. No preparation, modification, extension, domain, normality or
associated-prime hypothesis appears in any of them.

## Main definitions

* `Stacks.Chow.IsTameSymbolValue` — being a value of the formula Stacks 0EAQ on a pair.
* `Stacks.Chow.tameSymbolValue` — the formula Stacks 0EAQ as a function of a pair of
  nonzerodivisors.
* `Stacks.Chow.formulaRegularTameSymbol` — that function as a tame symbol on nonzerodivisors.
* `Stacks.Chow.formulaTameSymbol` — the map `Q(A)^* × Q(A)^* → κ(𝔪)^*` it gives.
* `AlgebraicGeometry.TameSymbolPreparation.reindex` — a preparation of a family, read along a
  reindexing of the family.

## Main results

* `Stacks.Chow.tameSymbolValue_eq_symbolValue` — the function is the formula Stacks 0EAQ at every
  preparation.
* `Stacks.Chow.tameSymbolValue_mul_left`, `Stacks.Chow.tameSymbolValue_mul_right` — Stacks 0EAL.
* `Stacks.Chow.tameSymbolValue_self` — Stacks 0EAM.
* `Stacks.Chow.tameSymbolValue_unit_left` — Stacks 0EAN.
* `Stacks.Chow.tameSymbolValue_steinberg` — Stacks 0EAP.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_apply_eq` — one value for one pair,
  across families and modifications.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_one_of_isUnit` — the formula on two units
  of the family is `1`.
* `AlgebraicGeometry.TameSymbolPreparation.not_isAssociatedPrime_maximalIdeal` — a preparation of a
  family with a nonunit member rules `𝔪` out of the associated primes of the modification.

## References

* [Stacks Project, Tag 0EAS](https://stacks.math.columbia.edu/tag/0EAS)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v w

namespace Stacks.Chow

/-- **The factor of the formula Stacks 0EAQ at a pair of units is `1`.** If `π^e` and `π^f` are
units then either `π` is a unit, and the local length `(Ring.ord R π)` is zero, or `π` is not,
and then `e = f = 0`. -/
theorem factorizationValue_eq_one_of_isUnit_pow {R : Type u} [CommRing R] [IsLocalRing R]
    {π : R} (u v : Rˣ) {e f : ℕ} (he : IsUnit (π ^ e)) (hf : IsUnit (π ^ f)) :
    factorizationValue π u v e f = 1 := by
  by_cases hπ : IsUnit π
  · rw [factorizationValue, Ring.ord_of_isUnit hπ]
    simp
  · obtain rfl : e = 0 := by
      by_contra h
      exact hπ ((isUnit_pow_iff h).mp he)
    obtain rfl : f = 0 := by
      by_contra h
      exact hπ ((isUnit_pow_iff h).mp hf)
    simp [factorizationValue]

end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  {r : ℕ} {a : Fin r → A}

/-! ### The formula on two units of the prepared family -/

/-- **A unit member of a prepared family contributes a unit power of the local parameter.** -/
theorem isUnit_parameter_pow (P : TameSymbolPreparation a B) {i : Fin r} (hi : IsUnit (a i))
    (q : Ideal B) [q.IsMaximal] : IsUnit (P.parameter q ^ P.exponent q i) := by
  have h : IsUnit (algebraMap B (Localization.AtPrime q) (algebraMap A B (a i))) :=
    (hi.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q))
  rw [P.factorization q i] at h
  exact isUnit_of_mul_isUnit_right h

/-- **The formula Stacks 0EAQ on two units of the prepared family is `1`.** Every factor is, by
`Stacks.Chow.factorizationValue_eq_one_of_isUnit_pow`. This is the case Stacks 0EAR leaves out —
it assumes the family has a nonunit member — and it is what Stacks 0EAN demands of a pair of
units, since `length_A(A/bA) = 0` for `b` a unit. -/
theorem symbolValue_eq_one_of_isUnit (P : TameSymbolPreparation a B)
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    {i j : Fin r} (hi : IsUnit (a i)) (hj : IsUnit (a j)) : P.symbolValue i j = 1 := by
  refine Finset.prod_eq_one fun q _ => ?_
  rw [factorizationValue_eq_one_of_isUnit_pow _ _ (P.isUnit_parameter_pow hi q.asIdeal)
    (P.isUnit_parameter_pow hj q.asIdeal), map_one]

/-! ### Reindexing a preparation -/

/-- **A preparation of a family, read along a reindexing of the family.** The modification, the
local parameters and the local lengths are untouched; only the units and exponents are permuted,
dropped or repeated along `σ`. -/
def reindex (P : TameSymbolPreparation a B) {s : ℕ} (σ : Fin s → Fin r) {b : Fin s → A}
    (hb : ∀ k, b k = a (σ k)) : TameSymbolPreparation b B where
  finite := P.finite
  algebraMap_injective := P.algebraMap_injective
  quotient_annihilated_by_maximalIdeal_power := P.quotient_annihilated_by_maximalIdeal_power
  parameter := fun q _ => P.parameter q
  parameter_isRegular := fun q _ => P.parameter_isRegular q
  factorUnit := fun q _ k => P.factorUnit q (σ k)
  exponent := fun q _ k => P.exponent q (σ k)
  factorization := fun q _ k => by rw [hb k]; exact P.factorization q (σ k)

/-- The formula Stacks 0EAQ is unchanged by reindexing: it reads the data at the reindexed
positions. -/
theorem symbolValue_reindex [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    (P : TameSymbolPreparation a B) {s : ℕ} (σ : Fin s → Fin r) {b : Fin s → A}
    (hb : ∀ k, b k = a (σ k)) (i j : Fin s) :
    (P.reindex σ hb).symbolValue i j = P.symbolValue (σ i) (σ j) := rfl

/-! ### The maximal ideal is not an associated prime of a modification -/

/-- **A preparation of a family with a nonunit member rules `𝔪` out of the associated primes of
the modification.** The nonunit member lies in `𝔪` and stays a nonzerodivisor in `B`
(`AlgebraicGeometry.TameSymbolPreparation.algebraMap_mem_nonZeroDivisors`), so it kills nothing,
and `𝔪` annihilates no nonzero element. This is the one hypothesis of Stacks 0EAT that a
preparation does not carry as a field. -/
theorem not_isAssociatedPrime_maximalIdeal [IsNoetherianRing A] (P : TameSymbolPreparation a B)
    (hunit : ¬ ∀ i, IsUnit (a i)) : ¬ IsAssociatedPrime (maximalIdeal A) B := by
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hunit
  exact not_isAssociatedPrime_maximalIdeal_of_mem_nonZeroDivisors ((mem_maximalIdeal _).2 hi₀)
    (P.algebraMap_mem_nonZeroDivisors i₀)

/-! ### One value for one pair -/

/-- **The formula Stacks 0EAQ depends on the pair alone.** Two preparations, of two families over
two modifications, agree on a pair of members the two families share.

This is Stacks 0EAR (`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_preparations`)
read along the reindexings of the two families onto the shared pair, with the pair of units — the
case Stacks 0EAR's `hunit` excludes — settled separately by
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_one_of_isUnit`. Nothing is assumed: the
`Fintype` and locality instances are installed from the preparations, as in Stacks 0EAR. -/
theorem symbolValue_eq_of_apply_eq [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {B' : Type w} [CommRing B'] [Algebra A B'] {r' : ℕ} {a' : Fin r' → A}
    (P : TameSymbolPreparation a B) (P' : TameSymbolPreparation a' B')
    (i j : Fin r) (i' j' : Fin r') (hi : a i = a' i') (hj : a j = a' j') :
    letI : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
    letI : Fintype (MaximalSpectrum B') := @Fintype.ofFinite _ P'.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B',
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P'.isLocalHom
    P.symbolValue i j = P'.symbolValue i' j' := by
  let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B,
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
  let : Fintype (MaximalSpectrum B') := @Fintype.ofFinite _ P'.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B',
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P'.isLocalHom
  by_cases hu : IsUnit (a i) ∧ IsUnit (a j)
  · rw [P.symbolValue_eq_one_of_isUnit hu.1 hu.2,
      P'.symbolValue_eq_one_of_isUnit (hi ▸ hu.1) (hj ▸ hu.2)]
  · have hc : ¬ ∀ k, IsUnit (![a i, a j] k) := fun h =>
      hu ⟨by simpa using h 0, by simpa using h 1⟩
    have key := symbolValue_eq_of_preparations hc
      (P.reindex ![i, j] (fun k => by fin_cases k <;> simp))
      (P'.reindex ![i', j'] (fun k => by fin_cases k <;> simp [hi, hj])) 0 1
    rw [symbolValue_reindex, symbolValue_reindex] at key
    simpa using key

end AlgebraicGeometry.TameSymbolPreparation

namespace Stacks.Chow

open AlgebraicGeometry.TameSymbolPreparation

/-! ### The formula as a function of a pair -/

section Value

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **Being a value of the formula Stacks 0EAQ on the pair `(x, y)`.** Some preparation of the
two-element family `![x, y]` — some finite modification `A ⊆ B` of Stacks 0EAG together with
simultaneous power factorizations of `x` and `y` at the maximal ideals of `B` — gives `v`.

By `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_apply_eq` there is at most one such
`v`, and by Stacks 0EAG there is one whenever `A` is one dimensional and `x`, `y` are
nonzerodivisors not both units. The `Fintype` and locality instances the formula needs are the
preparation's own, as in Stacks 0EAR. -/
def IsTameSymbolValue (x y : A) (v : (ResidueField A)ˣ) : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (P : TameSymbolPreparation ![x, y] B),
    letI : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
    P.symbolValue 0 1 = v

open Classical in
/-- **The tame symbol of Stacks 0EAQ, as a function of an arbitrary pair of nonzerodivisors.**
The value of the formula

`∂_A(x, y) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_1 e_2} ū_1^{e_2} ū_2^{-e_1})^{m_𝔮}`

at a preparation of the pair, which Stacks 0EAR makes independent of the preparation
(`Stacks.Chow.tameSymbolValue_eq_symbolValue`), and `1` on a pair that admits no preparation —
which happens only for a pair of units, where `1` is the value of the formula at every preparation
anyway (`Stacks.Chow.tameSymbolValue_eq_one_of_isUnit`). -/
noncomputable def tameSymbolValue (x y : nonZeroDivisors A) : (ResidueField A)ˣ :=
  if h : ∃ v, IsTameSymbolValue (x : A) (y : A) v then h.choose else 1

variable {x y : nonZeroDivisors A}

/-- `Stacks.Chow.tameSymbolValue` is a value of the formula Stacks 0EAQ whenever there is one. -/
theorem isTameSymbolValue_tameSymbolValue
    (h : ∃ v, IsTameSymbolValue (x : A) (y : A) v) :
    IsTameSymbolValue (x : A) (y : A) (tameSymbolValue x y) := by
  rw [tameSymbolValue, dif_pos h]
  exact h.choose_spec

/-- A pair the formula Stacks 0EAQ has no value on gets `1`. -/
theorem tameSymbolValue_eq_one_of_not_exists
    (h : ¬ ∃ v, IsTameSymbolValue (x : A) (y : A) v) : tameSymbolValue x y = 1 := by
  rw [tameSymbolValue, dif_neg h]

/-- **The tame symbol of two units is `1`.** Either the pair has no preparation, and the value is
`1` by fiat, or it has one, and then the formula is `1` there by
`AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_one_of_isUnit`. This needs nothing of `A`
beyond being local: it is the degenerate case of each of Stacks 0EAL, 0EAM, 0EAN and 0EAP. -/
theorem tameSymbolValue_eq_one_of_isUnit (hx : IsUnit (x : A)) (hy : IsUnit (y : A)) :
    tameSymbolValue x y = 1 := by
  by_cases h : ∃ v, IsTameSymbolValue (x : A) (y : A) v
  · obtain ⟨B, _, _, P, hP⟩ := isTameSymbolValue_tameSymbolValue h
    let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
    let : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
    rw [← hP]
    exact P.symbolValue_eq_one_of_isUnit (by simpa using hx) (by simpa using hy)
  · exact tameSymbolValue_eq_one_of_not_exists h

end Value

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **The function `Stacks.Chow.tameSymbolValue` is the formula Stacks 0EAQ, at every
preparation.** For any preparation of any family over any finite modification of `A`, in any
universe, the formula's value on two members of the family is the value of the function on those
two elements.

Nothing is assumed of the preparation. The two cases are the two clauses of the definition: where
the pair has a value, `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_of_apply_eq`
identifies it with this one; where it has none, Stacks 0EAG forces the pair to be a pair of units,
and then both sides are `1`.

This is what makes the four identities below statements about *the tame symbol of Stacks 0EAQ*:
their subject `Stacks.Chow.tameSymbolValue` is here identified with the product formula
`∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e_i e_j} ū_i^{e_j} ū_j^{-e_i})^{m_𝔮}` of Stacks 0EAQ at every
preparation at which that formula is written down. -/
@[stacks 0EAS "that the function of a pair whose properties (4), (5), (6), (7) are proved below \
is the tame symbol of Stacks 0EAQ: it is the product formula of Stacks 0EAQ at every preparation \
of every family, over an arbitrary one-dimensional Noetherian local ring"]
theorem tameSymbolValue_eq_symbolValue (hdim : ringKrullDim A = 1)
    {B : Type v} [CommRing B] [Algebra A B] {r : ℕ} {a : Fin r → A}
    (P : TameSymbolPreparation a B) (i j : Fin r) (x y : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) :
    letI : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
    letI : ∀ q : MaximalSpectrum B,
      IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
    tameSymbolValue x y = P.symbolValue i j := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using hdim.le)
  let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B,
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
  by_cases h : ∃ v, IsTameSymbolValue (x : A) (y : A) v
  · obtain ⟨B₀, _, _, P₀, hP₀⟩ := isTameSymbolValue_tameSymbolValue h
    rw [← hP₀]
    exact symbolValue_eq_of_apply_eq P₀ P 0 1 i j (by simpa using hx) (by simpa using hy)
  · have hunits : IsUnit (x : A) ∧ IsUnit (y : A) := by
      by_contra hc
      obtain ⟨B₀, _, _, ⟨P₀⟩⟩ := exists_tameSymbolPreparation_of_ringKrullDim_eq_one
        (le_refl 2) ![(x : A), (y : A)]
        (fun k => by
          fin_cases k <;> simpa using isRegular_iff_mem_nonZeroDivisors.mpr (by simp))
        (fun hk => hc ⟨by simpa using hk 0, by simpa using hk 1⟩) hdim
      exact h ⟨_, ⟨B₀, inferInstance, inferInstance, P₀, rfl⟩⟩
    rw [tameSymbolValue_eq_one_of_isUnit hunits.1 hunits.2]
    exact (P.symbolValue_eq_one_of_isUnit (hx ▸ hunits.1) (hy ▸ hunits.2)).symm

/-- **A tame symbol on `A` taking the value `Stacks.Chow.tameSymbolValue` on a prepared family.**
For a finite family of nonzerodivisors of `A`, not all units, Stacks 0EAG prepares the whole
family at once and `AlgebraicGeometry.TameSymbolPreparation.baseSymbol` is the tame symbol on `A`
that Stacks 0EAT assembles from the symbols on the localizations of the modification; its value on
members of the family is the formula Stacks 0EAQ, hence `Stacks.Chow.tameSymbolValue`.

This is how each of Stacks 0EAL, 0EAM, 0EAN and 0EAP is proved for arbitrary arguments: prepare
the finitely many elements the identity mentions simultaneously, and read off the corresponding
field of this one symbol. -/
theorem exists_regularTameSymbol_apply_eq (hdim : ringKrullDim A = 1) {r : ℕ} (hr : 2 ≤ r)
    {a : Fin r → A} (ha : ∀ i, a i ∈ nonZeroDivisors A) (hunit : ¬ ∀ i, IsUnit (a i)) :
    ∃ symb : RegularTameSymbol A, ∀ (i j : Fin r) (x y : nonZeroDivisors A),
      (x : A) = a i → (y : A) = a j → symb x y = tameSymbolValue x y := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using hdim.le)
  obtain ⟨B, _, _, ⟨P⟩⟩ := exists_tameSymbolPreparation_of_ringKrullDim_eq_one hr a
    (fun i => isRegular_iff_mem_nonZeroDivisors.mpr (ha i)) hunit hdim
  let := P.finite
  let : Fintype (MaximalSpectrum B) := @Fintype.ofFinite _ P.finite_maximalSpectrum
  let : ∀ q : MaximalSpectrum B,
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := P.isLocalHom
  let : ∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal) := fun q =>
    isNoetherianRing_localization_of_moduleFinite (A := A) q
  let : ∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := fun q =>
    krullDimLE_one_localization_of_moduleFinite (A := A) q
  refine ⟨P.baseSymbol hunit (P.not_isAssociatedPrime_maximalIdeal hunit),
    fun i j x y hx hy => ?_⟩
  rw [P.baseSymbol_apply hunit (P.not_isAssociatedPrime_maximalIdeal hunit) i j x y hx hy]
  exact (tameSymbolValue_eq_symbolValue hdim P i j x y hx hy).symm

/-! ### Stacks 0EAL, 0EAM, 0EAN and 0EAP for an arbitrary pair -/

/-- A family of nonzerodivisors has a function on pairs that agrees with `tameSymbolValue` on its
members and satisfies the multiplicativity and Steinberg identities: a tame symbol if the family
has a nonunit, and the constant `1` if all members are units. -/
private theorem exists_pairFunction_apply_eq (hdim : ringKrullDim A = 1) {r : ℕ} (hr : 2 ≤ r)
    {a : Fin r → A} (ha : ∀ i, a i ∈ nonZeroDivisors A) :
    ∃ f : nonZeroDivisors A → nonZeroDivisors A → (ResidueField A)ˣ,
      (∀ (i j : Fin r) (x y : nonZeroDivisors A),
        (x : A) = a i → (y : A) = a j → f x y = tameSymbolValue x y) ∧
      (∀ x x' y, f (x * x') y = f x y * f x' y) ∧ (∀ x y y', f x (y * y') = f x y * f x y') ∧
      ∀ (x y z : nonZeroDivisors A), (z : A) = y - x → f x z * f y y = f y z * f x y := by
  by_cases hunit : ∀ i, IsUnit (a i)
  · exact ⟨fun _ _ => 1, fun i j x y hx hy =>
      (tameSymbolValue_eq_one_of_isUnit (hx ▸ hunit i) (hy ▸ hunit j)).symm,
      by simp, by simp, by simp⟩
  · obtain ⟨symb, hsymb⟩ := exists_regularTameSymbol_apply_eq hdim hr ha hunit
    exact ⟨symb, hsymb, symb.map_mul_left, symb.map_mul_right, symb.steinberg⟩

/-- **Stacks 0EAL in the first argument, for the tame symbol of Stacks 0EAQ on arbitrary pairs of
nonzerodivisors.** `∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)`.

The four elements `a`, `a'`, `a a'` and `b` are prepared simultaneously
(`Stacks.Chow.exists_regularTameSymbol_apply_eq`) unless all four are units, and then the identity
is the first argument of `Stacks.Chow.RegularTameSymbol.map_mul_left` of that one symbol. If all
four are units each side is `1`. -/
@[stacks 0EAS "property (4) in the first argument, for the tame symbol of Stacks 0EAQ as a \
function of an arbitrary pair of nonzerodivisors"]
theorem tameSymbolValue_mul_left (hdim : ringKrullDim A = 1) (x x' y : nonZeroDivisors A) :
    tameSymbolValue (x * x') y = tameSymbolValue x y * tameSymbolValue x' y := by
  obtain ⟨f, hf, hmul, -⟩ := exists_pairFunction_apply_eq hdim (r := 4) (by norm_num)
    (a := ![(x : A), (x' : A), (x : A) * (x' : A), (y : A)])
    (fun i => by fin_cases i <;> simp [mul_mem])
  rw [← hf 2 3 (x * x') y (by simp) (by simp), ← hf 0 3 x y (by simp) (by simp),
    ← hf 1 3 x' y (by simp) (by simp)]
  exact hmul x x' y

/-- **Stacks 0EAL in the second argument, for the tame symbol of Stacks 0EAQ on arbitrary pairs of
nonzerodivisors.** `∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')`. -/
@[stacks 0EAS "property (4) in the second argument, for the tame symbol of Stacks 0EAQ as a \
function of an arbitrary pair of nonzerodivisors"]
theorem tameSymbolValue_mul_right (hdim : ringKrullDim A = 1) (x y y' : nonZeroDivisors A) :
    tameSymbolValue x (y * y') = tameSymbolValue x y * tameSymbolValue x y' := by
  obtain ⟨f, hf, -, hmul, -⟩ := exists_pairFunction_apply_eq hdim (r := 4) (by norm_num)
    (a := ![(x : A), (y : A), (y' : A), (y : A) * (y' : A)])
    (fun i => by fin_cases i <;> simp [mul_mem])
  rw [← hf 0 3 x (y * y') (by simp) (by simp), ← hf 0 1 x y (by simp) (by simp),
    ← hf 0 2 x y' (by simp) (by simp)]
  exact hmul x y y'

/-- **Stacks 0EAM for the tame symbol of Stacks 0EAQ on arbitrary pairs of nonzerodivisors.**
`∂_A(b, b) = (-1)^m` with `m = length_A(A/bA)`. For `b` a unit both sides are `1`, since
`length_A(A/bA) = 0`. -/
@[stacks 0EAS "property (5), for the tame symbol of Stacks 0EAQ as a function of an arbitrary \
pair of nonzerodivisors"]
theorem tameSymbolValue_self (hdim : ringKrullDim A = 1) (y : nonZeroDivisors A) :
    tameSymbolValue y y = (-1) ^ (Ring.ord A (y : A)).toNat := by
  by_cases hy : IsUnit (y : A)
  · rw [tameSymbolValue_eq_one_of_isUnit hy hy, Ring.ord_of_isUnit hy]
    simp
  · obtain ⟨symb, hsymb⟩ := exists_regularTameSymbol_apply_eq hdim (r := 2) (le_refl 2)
      (a := ![(y : A), (y : A)]) (fun i => by fin_cases i <;> simp)
      (fun h => hy (by simpa using h 0))
    rw [← hsymb 0 0 y y (by simp) (by simp)]
    exact symb.self y

/-- **Stacks 0EAN for the tame symbol of Stacks 0EAQ on arbitrary pairs of nonzerodivisors.**
`∂_A(u, b) = ū^m` with `m = length_A(A/bA)`, for `u` a unit of `A`. For `b` a unit both sides are
`1`. -/
@[stacks 0EAS "property (6), for the tame symbol of Stacks 0EAQ as a function of an arbitrary \
pair of nonzerodivisors"]
theorem tameSymbolValue_unit_left (hdim : ringKrullDim A = 1) (x y : nonZeroDivisors A) (u : Aˣ)
    (hu : (x : A) = u) :
    tameSymbolValue x y = Units.map (residue A).toMonoidHom u ^ (Ring.ord A (y : A)).toNat := by
  by_cases hy : IsUnit (y : A)
  · rw [tameSymbolValue_eq_one_of_isUnit (hu ▸ u.isUnit) hy, Ring.ord_of_isUnit hy]
    simp
  · obtain ⟨symb, hsymb⟩ := exists_regularTameSymbol_apply_eq hdim (r := 2) (le_refl 2)
      (a := ![(x : A), (y : A)]) (fun i => by fin_cases i <;> simp)
      (fun h => hy (by simpa using h 1))
    rw [← hsymb 0 1 x y (by simp) (by simp)]
    exact symb.unit_left x y u hu

/-- **Stacks 0EAP for the tame symbol of Stacks 0EAQ on arbitrary pairs of nonzerodivisors.**
`∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)` for `a`, `b` and `b - a` nonzerodivisors. If
all three are units each of the four values is `1`. -/
@[stacks 0EAS "property (7), for the tame symbol of Stacks 0EAQ as a function of an arbitrary \
pair of nonzerodivisors"]
theorem tameSymbolValue_steinberg (hdim : ringKrullDim A = 1) (x y z : nonZeroDivisors A)
    (hz : (z : A) = (y : A) - (x : A)) :
    tameSymbolValue x z * tameSymbolValue y y = tameSymbolValue y z * tameSymbolValue x y := by
  obtain ⟨f, hf, -, -, hst⟩ := exists_pairFunction_apply_eq hdim (r := 3) (by norm_num)
    (a := ![(x : A), (y : A), (z : A)]) (fun i => by fin_cases i <;> simp)
  rw [← hf 0 2 x z (by simp) (by simp), ← hf 1 1 y y (by simp) (by simp),
    ← hf 1 2 y z (by simp) (by simp), ← hf 0 1 x y (by simp) (by simp)]
  exact hst x y z hz

/-! ### The tame symbol of Stacks 0EAH that the formula gives -/

/-- **The tame symbol of Stacks 0EAQ on nonzerodivisors of an arbitrary one-dimensional Noetherian
local ring.** `Stacks.Chow.tameSymbolValue` with its four identities Stacks 0EAL, 0EAM, 0EAN and
0EAP, which is the datum Stacks 0EAH asks for on nonzerodivisors. -/
noncomputable def formulaRegularTameSymbol (hdim : ringKrullDim A = 1) : RegularTameSymbol A where
  toFun := tameSymbolValue
  map_mul_left := tameSymbolValue_mul_left hdim
  map_mul_right := tameSymbolValue_mul_right hdim
  self := tameSymbolValue_self hdim
  unit_left := tameSymbolValue_unit_left hdim
  steinberg := tameSymbolValue_steinberg hdim

/-- `Stacks.Chow.formulaRegularTameSymbol` takes the value `Stacks.Chow.tameSymbolValue x y` on a
pair `(x, y)` of nonzerodivisors. -/
@[simp]
theorem formulaRegularTameSymbol_apply (hdim : ringKrullDim A = 1) (x y : nonZeroDivisors A) :
    formulaRegularTameSymbol hdim x y = tameSymbolValue x y := rfl

/-- **Stacks 0EAS, the map the formula Stacks 0EAQ gives on the total ring of fractions.** The
tame symbol

`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*`

of Stacks 0EAH, satisfying Stacks 0EAI, 0EAJ and 0EAK, for an arbitrary one-dimensional Noetherian
local ring: the formula Stacks 0EAQ satisfies Stacks 0EAL, 0EAM, 0EAN and 0EAP on arbitrary pairs
of nonzerodivisors, so `Stacks.Chow.RegularTameSymbol.extend` extends it. On nonzerodivisors it is
the formula itself, by `Stacks.Chow.formulaTameSymbol_regularFractionUnit`. -/
@[stacks 0EAS "that the tame symbol of Stacks 0EAQ, as a function of an arbitrary pair of \
nonzerodivisors, hence gives a map on Q(A)^* satisfying (1), (2), (3)"]
noncomputable def formulaTameSymbol (hdim : ringKrullDim A = 1) (Q : Type v) [CommRing Q]
    [Algebra A Q] [IsFractionRing A Q] : TameSymbol A Q :=
  haveI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using hdim.le)
  (formulaRegularTameSymbol hdim).extend Q

/-- The map of `Stacks.Chow.formulaTameSymbol` restricts on nonzerodivisors of `A` to the formula
Stacks 0EAQ. -/
theorem formulaTameSymbol_regularFractionUnit (hdim : ringKrullDim A = 1) (Q : Type v)
    [CommRing Q] [Algebra A Q] [IsFractionRing A Q] (x y : nonZeroDivisors A) :
    formulaTameSymbol hdim Q (regularFractionUnit x) (regularFractionUnit y) =
      tameSymbolValue x y := by
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using hdim.le)
  exact (formulaRegularTameSymbol hdim).extend_regularFractionUnit Q x y

end Main

end Stacks.Chow

end
