module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.FormulaComparison

/-!
# Reciprocity for the tame symbol of the formula Stacks 0EAQ

Stacks 0EAW: for a two-dimensional Noetherian local ring `A` and nonzerodivisors `a, b` of `A`,

`∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = 0`,

where `∂_{A_𝔮}` is the tame symbol of Section 0EAH on the one-dimensional Noetherian local ring
`A_𝔮`, defined by the recipe Stacks 0EAQ (`Stacks.Chow.tameSymbolValue`, packaged with its four
identities as `Stacks.Chow.formulaRegularTameSymbol`).

The proof combines two results. `Stacks.Chow.finsum_tameSymbolOrderAt_canonical_eq_zero` is the
same vanishing for the periodic determinant `d_{A_𝔮}(a, b)` of Stacks 02PZ, and
`Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue` identifies that determinant with the formula
Stacks 0EAQ on every one-dimensional Noetherian local ring. So the two sums agree term by term.

## Main results

* `Stacks.Chow.finsum_tameSymbolOrderAt_formula_eq_zero` — **Stacks 0EAW** for the tame symbol
  of Stacks 0EAQ.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

universe u

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsLocalRing A] in
/-- At a height-one prime, the summand of Stacks 0EAW formed with the tame symbol of the formula
Stacks 0EAQ equals the summand formed with the periodic determinant of Stacks 02PZ, by
`Stacks.Chow.regularModuleSymbol_eq_tameSymbolValue` on `A_𝔮`. -/
theorem tameSymbolOrderAt_formula_eq_canonical (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (x y : nonZeroDivisors A) :
    tameSymbolOrderAt hdim p
        (formulaRegularTameSymbol (ringKrullDim_localization_heightOnePrime p)) x y =
      tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) x y := by
  simp only [tameSymbolOrderAt, canonicalHeightOneSymbol, formulaRegularTameSymbol_apply,
    regularTameSymbolOfKrullDimOne_apply, regularModuleSymbol_eq_tameSymbolValue]

/-- **Stacks Project, Tag 0EAW.** Let `(A, 𝔪)` be a two-dimensional Noetherian local ring and let
`a, b ∈ A` be nonzerodivisors. Then

`∑ ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = 0`,

the sum being over the height-one primes `𝔮` of `A`, where `∂_{A_𝔮}` is the tame symbol of the
one-dimensional Noetherian local ring `A_𝔮` given by the formula Stacks 0EAQ
(`Stacks.Chow.formulaRegularTameSymbol`, whose value is `Stacks.Chow.tameSymbolValue`). Only
finitely many primes contribute, by `Stacks.Chow.finite_tameSymbolOrderAt_support`. -/
@[stacks 0EAW]
theorem finsum_tameSymbolOrderAt_formula_eq_zero (hdim : ringKrullDim A = 2)
    (x y : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A,
      tameSymbolOrderAt hdim p
        (formulaRegularTameSymbol (ringKrullDim_localization_heightOnePrime p)) x y = 0 :=
  (finsum_congr fun p => tameSymbolOrderAt_formula_eq_canonical hdim p x y).trans
    (finsum_tameSymbolOrderAt_canonical_eq_zero hdim x y)

end Stacks.Chow

end
