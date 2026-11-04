module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.WellDefinedRefinement

/-!
# The product formula of Stacks 0EAQ satisfies the four conditions of Stacks 0EAH

Let `(A, 𝔪)` be a one-dimensional Noetherian local ring. Stacks 0EAQ defines the tame symbol of
two nonzerodivisors of `A` by choosing a finite extension `A ⊆ B` in which they become unit
multiples of powers of one parameter at every maximal ideal of `B` (Stacks 0EAG) and setting

`∂_A(a₁, a₂) = ∏_𝔮 Norm_{κ(𝔮)/κ(𝔪)}((-1)^{e₁e₂} ū₁^{e₂} ū₂^{-e₁})^{m_𝔮}`,

which is `AlgebraicGeometry.TameSymbolPreparation.symbolValue`. Stacks 0EAS asserts that this
expression satisfies the four conditions Stacks 0EAL, 0EAM, 0EAN and 0EAP, and hence gives a map
`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` satisfying Stacks 0EAI, 0EAJ and 0EAK.

This file proves these assertions at a preparation, for members of the prepared family, with `A`
not assumed to be a domain and `B` not assumed normal. The product formula is identified with the
value of a tame symbol on `A`:

* each localization `B_𝔮` of a preparation is a one-dimensional Noetherian local ring, since the
  local parameter is a nonzerodivisor in its maximal ideal, and therefore carries the tame symbol
  `Stacks.Chow.regularTameSymbolOfKrullDimOne` of Stacks 0EAH; this is
  `AlgebraicGeometry.TameSymbolPreparation.localSymbol`;
* the norm pushforward of Stacks 0EAT assembles that family into a tame symbol on `A`,
  `AlgebraicGeometry.TameSymbolPreparation.baseSymbol`, which satisfies Stacks 0EAL, 0EAM, 0EAN
  and 0EAP;
* on the prepared family its value is the product formula
  (`AlgebraicGeometry.TameSymbolPreparation.baseSymbol_apply`), since a tame symbol on a local ring
  is forced by Stacks 0EAL, 0EAM and 0EAN to take the value of the formula on a simultaneous power
  factorization.

The extension of Stacks 0EAH (`Stacks.Chow.RegularTameSymbol.extend`) then turns the tame symbol on
nonzerodivisors into a map on `Q(A)^*`. Throughout, `hass : ¬ IsAssociatedPrime 𝔪 B` is the
hypothesis of Stacks 0EAT.

## Main definitions

* `AlgebraicGeometry.TameSymbolPreparation.localSymbol` — the tame symbol of Stacks 0EAH at each
  maximal ideal of the extension of a preparation.
* `AlgebraicGeometry.TameSymbolPreparation.baseSymbol` — the tame symbol on `A` that a preparation
  gives, on nonzerodivisors.
* `AlgebraicGeometry.TameSymbolPreparation.fractionTameSymbol` — the same on `Q(A)^*`.

## Main results

* `AlgebraicGeometry.TameSymbolPreparation.baseSymbol_apply` — on the prepared family the tame
  symbol on `A` is the product formula of Stacks 0EAQ.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_mul_left`,
  `AlgebraicGeometry.TameSymbolPreparation.symbolValue_mul_right` — Stacks 0EAL for the formula.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_self` — Stacks 0EAM for the formula.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_unit_left` — Stacks 0EAN for the formula.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_steinberg` — Stacks 0EAP for the formula.
* `AlgebraicGeometry.TameSymbolPreparation.fractionTameSymbol_regularFractionUnit` — the map on
  `Q(A)^*` restricts to the product formula on the prepared family.
* `AlgebraicGeometry.TameSymbolPreparation.symbolValue_eq_symbolValue_of_refinement` — the product
  formula takes the same value over `B` and over a finite refinement `C` of `B`.
* `Stacks.Chow.ringKrullDim_eq_one_of_mem_maximalIdeal` — a local ring of Krull dimension at most
  one with a nonzerodivisor in its maximal ideal has Krull dimension one.

## References

* [Stacks Project, Tag 0EAS](https://stacks.math.columbia.edu/tag/0EAS)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAR](https://stacks.math.columbia.edu/tag/0EAR)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v w

namespace Stacks.Chow

/-- **A local ring of Krull dimension at most one with a nonzerodivisor in its maximal ideal has
Krull dimension exactly one.** -/
theorem ringKrullDim_eq_one_of_mem_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] {π : R} (hreg : π ∈ nonZeroDivisors R) (hmem : π ∈ maximalIdeal R) :
    ringKrullDim R = 1 := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Stacks.Length.height_maximalIdeal_eq_one hreg hmem]
  rfl

end Stacks.Chow

namespace AlgebraicGeometry.TameSymbolPreparation

open Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B] [Fintype (MaximalSpectrum B)]
  [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
  [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
  [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
  {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (hunit : ¬ ∀ i, IsUnit (a i))

/-- **The tame symbol of Stacks 0EAH at a maximal ideal of the extension of a preparation.** The
localization `B_𝔮` has Krull dimension exactly one, its maximal ideal containing the local
parameter of the preparation, a nonzerodivisor; this is
`Stacks.Chow.regularTameSymbolOfKrullDimOne` of `B_𝔮`. -/
noncomputable def localSymbol (q : MaximalSpectrum B) :
    RegularTameSymbol (Localization.AtPrime q.asIdeal) :=
  regularTameSymbolOfKrullDimOne (ringKrullDim_eq_one_of_mem_maximalIdeal
    (isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q.asIdeal))
    (P.parameter_mem_maximal hunit q.asIdeal))

variable (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)

/-- **The tame symbol on `A` that a preparation gives, on pairs of nonzerodivisors.** It is the
norm pushforward of Stacks 0EAT of the tame symbols
`AlgebraicGeometry.TameSymbolPreparation.localSymbol` of the localizations `B_𝔮`. -/
noncomputable def baseSymbol : RegularTameSymbol A :=
  normPushforward hass (P.localSymbol hunit) P.algebraMap_injective
    P.quotient_annihilated_by_maximalIdeal_power

/-- **On the prepared family the tame symbol of
`AlgebraicGeometry.TameSymbolPreparation.baseSymbol` is the product formula of Stacks 0EAQ**, that
is, `AlgebraicGeometry.TameSymbolPreparation.symbolValue`. -/
theorem baseSymbol_apply (i j : Fin r) (x y : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) :
    P.baseSymbol hunit hass x y = P.symbolValue i j :=
  normPushforward_apply_eq_symbolValue hass (P.localSymbol hunit) P.algebraMap_injective
    P.quotient_annihilated_by_maximalIdeal_power P i j x y hx hy

include hunit hass

/-- **Stacks 0EAL for the product formula of Stacks 0EAQ, in the first argument.**
`∂_A(a a', b) = ∂_A(a, b) ∂_A(a', b)` whenever the prepared family contains `a`, `a'`, their
product and `b`. -/
theorem symbolValue_mul_left (i i' k j : Fin r) (x x' y : nonZeroDivisors A)
    (hx : (x : A) = a i) (hx' : (x' : A) = a i') (hy : (y : A) = a j)
    (hk : a k = a i * a i') :
    P.symbolValue k j = P.symbolValue i j * P.symbolValue i' j := by
  rw [← P.baseSymbol_apply hunit hass k j (x * x') y
      (by rw [Submonoid.coe_mul, hx, hx']; exact hk.symm) hy,
    ← P.baseSymbol_apply hunit hass i j x y hx hy,
    ← P.baseSymbol_apply hunit hass i' j x' y hx' hy]
  exact (P.baseSymbol hunit hass).map_mul_left x x' y

/-- **Stacks 0EAL for the product formula of Stacks 0EAQ, in the second argument.**
`∂_A(a, b b') = ∂_A(a, b) ∂_A(a, b')` whenever the prepared family contains `a`, `b`, `b'` and the
product of the last two. -/
theorem symbolValue_mul_right (i j j' k : Fin r) (x y y' : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) (hy' : (y' : A) = a j')
    (hk : a k = a j * a j') :
    P.symbolValue i k = P.symbolValue i j * P.symbolValue i j' := by
  rw [← P.baseSymbol_apply hunit hass i k x (y * y') hx
      (by rw [Submonoid.coe_mul, hy, hy']; exact hk.symm),
    ← P.baseSymbol_apply hunit hass i j x y hx hy,
    ← P.baseSymbol_apply hunit hass i j' x y' hx hy']
  exact (P.baseSymbol hunit hass).map_mul_right x y y'

/-- **Stacks 0EAM for the product formula of Stacks 0EAQ.** `∂_A(b, b) = (-1)^m` with
`m = length_A(A/bA)`. -/
theorem symbolValue_self (i : Fin r) (x : nonZeroDivisors A) (hx : (x : A) = a i) :
    P.symbolValue i i = (-1) ^ (Ring.ord A (a i)).toNat := by
  rw [← P.baseSymbol_apply hunit hass i i x x hx hx, (P.baseSymbol hunit hass).self x, hx]

/-- **Stacks 0EAN for the product formula of Stacks 0EAQ.** `∂_A(u, b) = ū^m` with
`m = length_A(A/bA)`, for `u` a unit of `A`. -/
theorem symbolValue_unit_left (i j : Fin r) (x y : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) (u : Aˣ) (hu : a i = u) :
    P.symbolValue i j =
      Units.map (residue A).toMonoidHom u ^ (Ring.ord A (a j)).toNat := by
  rw [← P.baseSymbol_apply hunit hass i j x y hx hy,
    (P.baseSymbol hunit hass).unit_left x y u (hx.trans hu), hy]

/-- **Stacks 0EAP for the product formula of Stacks 0EAQ.**
`∂_A(a, b - a) ∂_A(b, b) = ∂_A(b, b - a) ∂_A(a, b)` whenever the prepared family contains `a`, `b`
and `b - a`. -/
theorem symbolValue_steinberg (i j k : Fin r) (x y z : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) (hz : (z : A) = a k)
    (hk : a k = a j - a i) :
    P.symbolValue i k * P.symbolValue j j = P.symbolValue j k * P.symbolValue i j := by
  rw [← P.baseSymbol_apply hunit hass i k x z hx hz,
    ← P.baseSymbol_apply hunit hass j j y y hy hy,
    ← P.baseSymbol_apply hunit hass j k y z hy hz,
    ← P.baseSymbol_apply hunit hass i j x y hx hy]
  exact (P.baseSymbol hunit hass).steinberg x y z (by rw [hz, hk, hy, hx])

/-- **Stacks 0EAS, the map the product formula gives.** The tame symbol
`∂_A : Q(A)^* × Q(A)^* → κ(𝔪)^*` of Stacks 0EAH, satisfying Stacks 0EAI, 0EAJ and 0EAK, obtained
by extending `AlgebraicGeometry.TameSymbolPreparation.baseSymbol` to the units of the total ring of
fractions. -/
noncomputable def fractionTameSymbol (Q : Type*) [CommRing Q] [Algebra A Q]
    [IsFractionRing A Q] : Stacks.Chow.TameSymbol A Q :=
  (P.baseSymbol hunit hass).extend Q

/-- On the prepared family the map of
`AlgebraicGeometry.TameSymbolPreparation.fractionTameSymbol` is the product formula of
Stacks 0EAQ. -/
theorem fractionTameSymbol_regularFractionUnit (Q : Type*) [CommRing Q] [Algebra A Q]
    [IsFractionRing A Q] (i j : Fin r) (x y : nonZeroDivisors A)
    (hx : (x : A) = a i) (hy : (y : A) = a j) :
    P.fractionTameSymbol hunit hass Q (regularFractionUnit x) (regularFractionUnit y) =
      P.symbolValue i j :=
  ((P.baseSymbol hunit hass).extend_regularFractionUnit Q x y).trans
    (P.baseSymbol_apply hunit hass i j x y hx hy)

omit [Module.Finite A B] in
/-- **Independence of the product formula from the extension, against a refinement.** Two
preparations of the same family, one over `A ⊆ B` and one over a finite refinement `A ⊆ C` of it
satisfying the hypotheses of Stacks 0EAT at the maximal ideals of `B`, give the same value of the
product formula of Stacks 0EAQ. -/
theorem symbolValue_eq_symbolValue_of_refinement
    {C : Type w} [CommRing C] [Algebra A C] [Module.Finite A C] [Fintype (MaximalSpectrum C)]
    [∀ s : MaximalSpectrum C, IsLocalHom (algebraMap A (Localization.AtPrime s.asIdeal))]
    [∀ s : MaximalSpectrum C, IsNoetherianRing (Localization.AtPrime s.asIdeal)]
    [∀ s : MaximalSpectrum C, Ring.KrullDimLE 1 (Localization.AtPrime s.asIdeal)]
    [Algebra B C] [IsScalarTower A B C] [Module.Finite B C]
    [∀ q : MaximalSpectrum B,
      Fintype (MaximalSpectrum
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime (v.asIdeal.under C))]
    [∀ (q : MaximalSpectrum B)
        (v : MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))),
      Localization.AtPrime.IsLiesOverAlgebra q.asIdeal (v.asIdeal.under C)]
    (hC : ¬ IsAssociatedPrime (maximalIdeal A) C)
    (hfibre : ∀ q : MaximalSpectrum B,
      ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime q.asIdeal))
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl)))
    (hinjFibre : ∀ q : MaximalSpectrum B,
      Function.Injective (algebraMap (Localization.AtPrime q.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (hquotFibre : ∀ q : MaximalSpectrum B,
      ∃ n : ℕ, maximalIdeal (Localization.AtPrime q.asIdeal) ^ n •
        (⊤ : Submodule (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime q.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid C q.asIdeal.primeCompl))))
    (PC : TameSymbolPreparation a C) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    P.symbolValue i j = PC.symbolValue i j :=
  (symbolValue_eq_normPushforward hass hC hfibre (PC.localSymbol hunit)
        PC.algebraMap_injective PC.quotient_annihilated_by_maximalIdeal_power
        hinjFibre hquotFibre P i j x y hx hy).trans
    (PC.baseSymbol_apply hunit hC i j x y hx hy)

end AlgebraicGeometry.TameSymbolPreparation

end
