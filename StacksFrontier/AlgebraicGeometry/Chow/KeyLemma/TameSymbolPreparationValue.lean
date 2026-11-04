module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FiniteExtension

/-!
# The tame symbol on the output of a tame-symbol preparation

The finite modification of Stacks 0EAG takes finitely many nonzerodivisors of a one-dimensional
Noetherian local ring `A` to a finite extension `A ⊆ B` in which, at every maximal ideal `q` of
`B`, they become unit multiples of powers of one common parameter — with the unit parts units of
the localization `B_q`. That is `AlgebraicGeometry.TameSymbolPreparation`.

This file evaluates the tame symbol on that output. Two statements:

* on each localization `B_q`, the symbol of two members of the prepared family is given by the
  formula of Stacks 0EAL/0EAM/0EAN on a simultaneous power factorization. The unit parts of a
  preparation are units of `B_q`, which is precisely the ring carrying that symbol, so this is a
  direct application of `Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization` and needs no
  bridging;
* on the base `A`, the symbol obtained from those by the norm pushforward of Stacks 0EAT is the
  product over the maximal ideals of `B` of the norms of those values.

The second is the step the proof of Stacks 0EAW performs to pass from a prepared finite extension
back to the ring it started from. What it does **not** supply is the identity the source then
uses, that the order of vanishing of the symbol on the base is the sum of the orders of vanishing
of the symbols on the extension; that is Algebra 02MJ, formalized as
`Stacks.Ring.ord_norm_eq_sum_inertiaDeg_mul_ord`, applied to the residue-field extensions rather
than to the rings, and it is not assembled here.

## Main results

* `Stacks.Chow.tameSymbol_apply_eq_of_tameSymbolPreparation` — the tame symbol on a localization
  of a preparation, evaluated on the preparation's own factorization data.
* `Stacks.Chow.normPushforward_apply_eq_of_tameSymbolPreparation` — the norm pushforward of those
  symbols to the base, evaluated on the same data.

## Implementation notes

`AlgebraicGeometry.TameSymbolPreparation` indexes its data by an ideal of `B` with an `IsMaximal`
instance, while `Stacks.Chow.normPushforward` indexes by `MaximalSpectrum B`; the second statement
crosses that by writing `q.asIdeal` and letting the `MaximalSpectrum` instance supply maximality.

A preparation supplies three of the four non-instance hypotheses of
`Stacks.Chow.normPushforward` — `hinj` is its `algebraMap_injective`, `hquot` is its
`quotient_annihilated_by_maximalIdeal_power` in the same spelling, and `Module.Finite` is its
`finite` — and the two instance families are its `finite_maximalSpectrum` and `isLocalHom`. The
one hypothesis it does **not** supply is
`hass : ¬ IsAssociatedPrime (IsLocalRing.maximalIdeal A) B`, so that is carried here as a
hypothesis, as are the Noetherian and dimension instances on the localizations; they are stated as
binders in the same style as
`AlgebraicGeometry.TameSymbolPreparation.finiteDimensional_residueField`, which likewise takes an
instance its own `isLocalHom` supplies.

## References

* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAT](https://stacks.math.columbia.edu/tag/0EAT)
* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

universe u v

namespace Stacks.Chow

/-- **The tame symbol on a localization of a tame-symbol preparation.** At a maximal ideal `q` of
the finite extension produced by Stacks 0EAG, two members of the prepared family are unit multiples
of powers of the common parameter, with unit parts units of `B_q`; so the symbol of the two is

`∂_{B_q}(a i, a j) = ((-1) ^ (e_i e_j) ū_i ^ (e_j) v̄_j ^ (-e_i)) ^ m`,
`m = length_{B_q}(B_q / π_q B_q)`,

by Stacks 0EAL, 0EAM and 0EAN. The unit parts of a preparation are units of the very ring carrying
the symbol, so this is `Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization` applied directly;
no passage between units of the base and units of a localization is involved. -/
@[stacks 0EAQ "the factor at a single maximal ideal"]
theorem tameSymbol_apply_eq_of_tameSymbolPreparation
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B)
    (q : Ideal B) [q.IsMaximal]
    [IsNoetherianRing (Localization.AtPrime q)] [Ring.KrullDimLE 1 (Localization.AtPrime q)]
    (symb : RegularTameSymbol (Localization.AtPrime q))
    (i j : Fin r) (x y : nonZeroDivisors (Localization.AtPrime q))
    (hx : (x : Localization.AtPrime q) = algebraMap A (Localization.AtPrime q) (a i))
    (hy : (y : Localization.AtPrime q) = algebraMap A (Localization.AtPrime q) (a j)) :
    symb x y =
      ((-1) ^ (P.exponent q i * P.exponent q j) *
          Units.map (residue (Localization.AtPrime q)).toMonoidHom (P.factorUnit q i) ^
            P.exponent q j *
          (Units.map (residue (Localization.AtPrime q)).toMonoidHom
            (P.factorUnit q j))⁻¹ ^ P.exponent q i) ^
        (Ring.ord (Localization.AtPrime q) (P.parameter q)).toNat := by
  refine symb.apply_eq_of_factorization
    ⟨P.parameter q, isRegular_iff_mem_nonZeroDivisors.mp (P.parameter_isRegular q)⟩
    x y (P.factorUnit q i) (P.factorUnit q j) (P.exponent q i) (P.exponent q j)
    (hx.trans ?_) (hy.trans ?_) <;>
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q), P.factorization]

/-- **The tame symbol pushed back from a tame-symbol preparation to its base, evaluated on the
preparation's data.** The norm pushforward of Stacks 0EAT assembles the symbols on the
localizations of a finite extension into a symbol on the base; on the output of Stacks 0EAG each of
those symbols is the formula of
`Stacks.Chow.tameSymbol_apply_eq_of_tameSymbolPreparation`, so the symbol on the base is the
product of the norms of those formulas.

This is the passage the proof of Stacks 0EAW makes from the prepared finite extension back to the
ring it began with. The order-of-vanishing form of it, which is what that proof actually uses,
needs Algebra 02MJ at the residue fields and is not proved here. -/
@[stacks 0EAQ "the product over the maximal ideals"]
theorem normPushforward_apply_eq_of_tameSymbolPreparation
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {B : Type v} [CommRing B] [Algebra A B] [Module.Finite A B]
    [Fintype (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ q : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [∀ q : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal)]
    (hass : ¬ IsAssociatedPrime (maximalIdeal A) B)
    (symb : ∀ q : MaximalSpectrum B, RegularTameSymbol (Localization.AtPrime q.asIdeal))
    (hinj : Function.Injective (algebraMap A B))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    {r : ℕ} {a : Fin r → A} (P : TameSymbolPreparation a B) (i j : Fin r)
    (x y : nonZeroDivisors A) (hx : (x : A) = a i) (hy : (y : A) = a j) :
    normPushforward hass symb hinj hquot x y =
      ∏ q : MaximalSpectrum B,
        Units.map (Algebra.norm (ResidueField A) :
            ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
          (((-1) ^ (P.exponent q.asIdeal i * P.exponent q.asIdeal j) *
              Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom
                (P.factorUnit q.asIdeal i) ^ P.exponent q.asIdeal j *
              (Units.map (residue (Localization.AtPrime q.asIdeal)).toMonoidHom
                (P.factorUnit q.asIdeal j))⁻¹ ^ P.exponent q.asIdeal i) ^
            (Ring.ord (Localization.AtPrime q.asIdeal) (P.parameter q.asIdeal)).toNat) := by
  rw [normPushforward_apply]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  exact tameSymbol_apply_eq_of_tameSymbolPreparation P q.asIdeal (symb q) i j _ _
    (by rw [toExtensionNonZeroDivisor_val, hx]) (by rw [toExtensionNonZeroDivisor_val, hy])

end Stacks.Chow

end
