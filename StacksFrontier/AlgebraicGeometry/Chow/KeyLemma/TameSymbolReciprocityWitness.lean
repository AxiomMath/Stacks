module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.NormalSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocity

/-!
# Witnesses for the reciprocity sum of tame-symbol orders

The cases of the reciprocity relation Stacks 0EAW proved in
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocity` are statements about a
two-dimensional Noetherian ring together with a tame symbol on the localization at each of its
height-one primes. The symbol is carried as data, so each of them is only as strong as the
supply of such data; this file discharges every hypothesis of them at one concrete ring.

The ring is the polynomial ring `k[X₀, X₁]` over a field, which is a Noetherian normal domain of
Krull dimension exactly two with height-one primes, and the symbols are the canonical ones of
`Stacks.Chow.normalHeightOneSymbol`. Over that ring the reciprocity sum is shown to vanish for
`a = X₀ ^ e`, `b = X₀ ^ f` with no hypothesis left over, and to vanish whenever one of the two
arguments is a unit.

## Main results

* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_pow_mvPolynomial` — the reciprocity relation
  Stacks 0EAW for two powers of a variable of `k[X₀, X₁]`, with every hypothesis discharged.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_isUnit_left_mvPolynomial` — the reciprocity
  relation for a unit first argument over the same ring.

## Implementation notes

The two arguments of the symbol are elements of the submonoid `nonZeroDivisors`, so the powers
of a variable are presented through `Stacks.Chow.mvPolynomialX`, the variable packaged as a
nonzerodivisor; in a domain a nonzero element is a nonzerodivisor.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
-/

@[expose] public section

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k]

/-- A variable of `k[X₀, X₁]` as a nonzerodivisor: the polynomial ring over a field is a domain
and a variable is nonzero. -/
noncomputable def mvPolynomialX (i : Fin 2) :
    nonZeroDivisors (MvPolynomial (Fin 2) k) :=
  ⟨_root_.MvPolynomial.X i,
    mem_nonZeroDivisors_of_ne_zero (_root_.MvPolynomial.X_ne_zero i)⟩

/-- **The vanishing sum of Stacks 0EAW for two powers of a variable, with every hypothesis
discharged.** Over the polynomial ring in two variables over a field, with the canonical tame
symbol at each height-one prime, the orders of `∂(X₀ ^ e, X₀ ^ f)` sum to zero. This is the
globally prepared case of the relation at a concrete two-dimensional Noetherian ring: `X₀ ^ e`
and `X₀ ^ f` are unit multiples of powers of the nonzerodivisor `X₀`. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_pow_mvPolynomial (e f : ℕ) :
    ∑ᶠ p : HeightOnePrime (MvPolynomial (Fin 2) k),
        tameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p (normalHeightOneSymbol p)
          (mvPolynomialX k 0 ^ e) (mvPolynomialX k 0 ^ f) = 0 :=
  tameSymbolOrderAt_finsum_eq_zero_of_global_factorization
    (MvPolynomial.ringKrullDim_fin_two k) normalHeightOneSymbol
    (mvPolynomialX k 0 ^ e) (mvPolynomialX k 0 ^ f) (mvPolynomialX k 0) 1 1 e f
    (by simp) (by simp)

/-- **The vanishing sum of Stacks 0EAW for a unit first argument**, over the polynomial ring in
two variables over a field with its canonical tame symbols. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_isUnit_left_mvPolynomial
    (a b : nonZeroDivisors (MvPolynomial (Fin 2) k)) (ha : IsUnit (a : MvPolynomial (Fin 2) k)) :
    ∑ᶠ p : HeightOnePrime (MvPolynomial (Fin 2) k),
        tameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p (normalHeightOneSymbol p)
          a b = 0 :=
  tameSymbolOrderAt_finsum_eq_zero_of_isUnit_left
    (MvPolynomial.ringKrullDim_fin_two k) normalHeightOneSymbol a b ha

end Stacks.Chow

end
