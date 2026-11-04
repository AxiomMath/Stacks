module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocity

/-!
# The reciprocity sum in the prepared case, with unit parts in the localizations

Let `A` be a two-dimensional Noetherian ring and `a, b` nonzerodivisors of `A`. The proof of the
reciprocity relation Stacks 0EAW reduces, after a finite modification, to the case where at every
height-one prime `𝔮` there are a nonzerodivisor `π_𝔮` of `A_𝔮`, units `u_𝔮, v_𝔮` of `A_𝔮` and
exponents `e_𝔮, f_𝔮` with

`a = u_𝔮 π_𝔮 ^ e_𝔮`,  `b = v_𝔮 π_𝔮 ^ f_𝔮`   in `A_𝔮`.

That is the *prepared case*: the unit parts are units of the localization `A_𝔮`, not of `A`, which
is what the finite modification of Stacks 0EAG supplies. This file is about that case.

The value of each summand is already available: `Stacks.Chow.tameSymbolOrderAt_eq_of_factorization`
evaluates it as

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = m_𝔮 (f_𝔮 ord_{A/𝔮}(ū_𝔮) - e_𝔮 ord_{A/𝔮}(v̄_𝔮))`,
`m_𝔮 = length_{A_𝔮}(A_𝔮 / π_𝔮 A_𝔮)`,

and its unit parts are already units of `A_𝔮`. What this file adds is the consequence for the
*sum*: the reciprocity sum of Stacks 0EAW equals the sum of those explicit order defects, so in
the prepared case the relation is **equivalent** to the vanishing of a sum in which the tame
symbol no longer appears. That is `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_iff_finsum_order`,
and it is an `iff`, hence a reformulation of the relation rather than a weakening of it.

The orders `ord_{A/𝔮}(ū_𝔮)` of the unit parts do **not** vanish in this case — that is exactly why
the source computes the summand through the multiplicities `e_A(M_𝔮, a, b)` of two-periodic
complexes, and why `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_isUnit`, which asks the
unit parts to come from `A`, does not apply. Each individual summand vanishes only under the
sharper condition `f_𝔮 ord_{A/𝔮}(ū_𝔮) = e_𝔮 ord_{A/𝔮}(v̄_𝔮)`, which is
`Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_order`; that condition is strictly weaker
than asking the unit parts to be units of `A`, and
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolCancellation` exhibits prepared data at a
concrete ring for which it fails while the sum still vanishes, by cancellation.

As in `Stacks.Chow.finite_tameSymbolOrderAt_support`, none of this needs `A` to be local.

## Main results

* `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_order` — the summand of Stacks 0EAW
  vanishes at a prepared prime whose two unit parts have proportional orders of vanishing. This
  generalizes `Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_isUnit`, which is the case
  where both orders are zero because the unit parts come from `A`.
* `Stacks.Chow.exists_factorization_order_of_notMem` — at a height-one prime avoiding both
  arguments the prepared data always exists and its termwise condition is automatic, so asking
  for prepared data at every height-one prime is no stronger than asking for it at the finitely
  many primes that contribute.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_finsum_order` — **the reciprocity sum in the prepared
  case**: it equals the explicit sum of the order defects of the unit parts, with no tame symbol
  left in the statement.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_iff_finsum_order` — consequently the relation of
  Stacks 0EAW is equivalent, in the prepared case, to the vanishing of that explicit sum.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_finsum_order` — the resulting interface: a proof
  that the explicit sum vanishes gives the reciprocity relation. This is the prepared-case
  companion of `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_multiplicity`.
* `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_factorization_order` — the relation when every
  summand vanishes on its own, which is the only case in which no cancellation is involved.

## Implementation notes

The prepared data is carried as a family of functions indexed by the height-one primes, matching
the way `Stacks.Chow.finite_tameSymbolOrderAt_support` carries the symbols, rather than as a
structure: no new object is introduced, so the statements here are directly comparable with the
existing ones.

The order defect is written out at each occurrence rather than named, because naming it would
introduce a definition whose only purpose is to abbreviate one expression appearing in four
statements of one file.

## References

* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section Prepared

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The summand of Stacks 0EAW vanishes at a prepared prime whose unit parts have proportional
orders of vanishing.** If in `A_𝔮` we have `a = u π ^ e` and `b = v π ^ f` with `π` a
nonzerodivisor of `A_𝔮` and `u`, `v` units of `A_𝔮`, then

`ord_{A/𝔮}(∂_{A_𝔮}(a, b)) = m (f ord_{A/𝔮}(ū) - e ord_{A/𝔮}(v̄))`,

so the summand vanishes as soon as `f ord_{A/𝔮}(ū) = e ord_{A/𝔮}(v̄)`.

This is the sharp termwise condition.
`Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_isUnit` is the special case where the unit
parts come from `A`, so that both orders are zero; here they may be any units of the localization,
as the finite modification of Stacks 0EAG produces. -/
theorem tameSymbolOrderAt_eq_zero_of_factorization_order (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A) (π : nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : (Localization.AtPrime p.1.asIdeal)ˣ) (e f : ℕ)
    (ha : (toLocalizationNonZeroDivisor p.1.asIdeal a :
        Localization.AtPrime p.1.asIdeal) =
      u * (π : Localization.AtPrime p.1.asIdeal) ^ e)
    (hb : (toLocalizationNonZeroDivisor p.1.asIdeal b :
        Localization.AtPrime p.1.asIdeal) =
      v * (π : Localization.AtPrime p.1.asIdeal) ^ f)
    (horder : (f : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom u) =
        (e : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom v)) :
    tameSymbolOrderAt hdim p symb a b = 0 := by
  rw [tameSymbolOrderAt_eq_of_factorization hdim p symb a b π u v e f ha hb, horder,
    sub_self, mul_zero]

/-- **At a height-one prime avoiding both arguments the prepared data exists and its termwise
condition holds.** Take the parameter to be `1`, the unit parts the two arguments themselves and
both exponents `0`.

This is what makes the hypotheses of the statements below, which ask for prepared data at *every*
height-one prime, no stronger than the source's, which asks for it only at the finitely many
primes containing one of the two arguments: at every other prime the data can always be chosen,
and there the termwise condition of
`Stacks.Chow.tameSymbolOrderAt_eq_zero_of_factorization_order` is automatic. -/
theorem exists_factorization_order_of_notMem (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (a b : nonZeroDivisors A)
    (ha : (a : A) ∉ p.1.asIdeal) (hb : (b : A) ∉ p.1.asIdeal) :
    ∃ (π : nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
      (u v : (Localization.AtPrime p.1.asIdeal)ˣ) (e f : ℕ),
      (toLocalizationNonZeroDivisor p.1.asIdeal a :
          Localization.AtPrime p.1.asIdeal) =
        u * (π : Localization.AtPrime p.1.asIdeal) ^ e ∧
      (toLocalizationNonZeroDivisor p.1.asIdeal b :
          Localization.AtPrime p.1.asIdeal) =
        v * (π : Localization.AtPrime p.1.asIdeal) ^ f ∧
      (f : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom u) =
        (e : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom v) := by
  refine ⟨1, (isUnit_toLocalizationNonZeroDivisor p.1.asIdeal a ha).unit,
    (isUnit_toLocalizationNonZeroDivisor p.1.asIdeal b hb).unit, 0, 0, ?_, ?_, ?_⟩
  · rw [pow_zero, mul_one, IsUnit.unit_spec]
  · rw [pow_zero, mul_one, IsUnit.unit_spec]
  · rw [Nat.cast_zero, zero_mul, zero_mul]

/-- **The reciprocity sum of Stacks 0EAW in the prepared case.** If at every height-one prime the
two nonzerodivisors admit a simultaneous power factorization whose unit parts are units of the
localization, then the reciprocity sum is the explicit sum

`∑_𝔮 m_𝔮 (f_𝔮 ord_{A/𝔮}(ū_𝔮) - e_𝔮 ord_{A/𝔮}(v̄_𝔮))`,  `m_𝔮 = length_{A_𝔮}(A_𝔮 / π_𝔮 A_𝔮)`,

in which the tame symbol no longer appears. This is the case the proof of Stacks 0EAW reaches
after the finite modification of Stacks 0EAG, and the sum it has to show vanishes. -/
theorem tameSymbolOrderAt_finsum_eq_finsum_order (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A)
    (π : ∀ p : HeightOnePrime A, nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : ∀ p : HeightOnePrime A, (Localization.AtPrime p.1.asIdeal)ˣ)
    (e f : HeightOnePrime A → ℕ)
    (ha : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal a : Localization.AtPrime p.1.asIdeal) =
        u p * (π p : Localization.AtPrime p.1.asIdeal) ^ e p)
    (hb : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal b : Localization.AtPrime p.1.asIdeal) =
        v p * (π p : Localization.AtPrime p.1.asIdeal) ^ f p) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b =
      ∑ᶠ p : HeightOnePrime A,
        ((Ring.ord (Localization.AtPrime p.1.asIdeal)
            (π p : Localization.AtPrime p.1.asIdeal)).toNat *
          ((f p : ℤ) * heightOneOrd hdim p
              (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (u p)) -
            (e p : ℤ) * heightOneOrd hdim p
              (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (v p)))) :=
  finsum_congr fun p =>
    tameSymbolOrderAt_eq_of_factorization hdim p (symb p) a b (π p) (u p) (v p) (e p) (f p)
      (ha p) (hb p)

/-- **In the prepared case Stacks 0EAW is equivalent to the vanishing of an explicit sum of orders
of vanishing.** Both directions, so this is a reformulation of the relation and not a weaker
statement: the content left over after the finite modification of Stacks 0EAG is exactly that the
order defects of the unit parts cancel. -/
theorem tameSymbolOrderAt_finsum_eq_zero_iff_finsum_order (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A)
    (π : ∀ p : HeightOnePrime A, nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : ∀ p : HeightOnePrime A, (Localization.AtPrime p.1.asIdeal)ˣ)
    (e f : HeightOnePrime A → ℕ)
    (ha : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal a : Localization.AtPrime p.1.asIdeal) =
        u p * (π p : Localization.AtPrime p.1.asIdeal) ^ e p)
    (hb : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal b : Localization.AtPrime p.1.asIdeal) =
        v p * (π p : Localization.AtPrime p.1.asIdeal) ^ f p) :
    (∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0) ↔
      ∑ᶠ p : HeightOnePrime A,
        ((Ring.ord (Localization.AtPrime p.1.asIdeal)
            (π p : Localization.AtPrime p.1.asIdeal)).toNat *
          ((f p : ℤ) * heightOneOrd hdim p
              (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (u p)) -
            (e p : ℤ) * heightOneOrd hdim p
              (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (v p)))) = 0 := by
  rw [tameSymbolOrderAt_finsum_eq_finsum_order hdim symb a b π u v e f ha hb]

/-- **The prepared-case interface for Stacks 0EAW.** A proof that the explicit order defects of the
unit parts sum to zero gives the reciprocity relation. This is the companion of
`Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_multiplicity`: the multiplicity identity of the
source is one way to supply this sum, and it is the way the source chooses. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_finsum_order (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A)
    (π : ∀ p : HeightOnePrime A, nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : ∀ p : HeightOnePrime A, (Localization.AtPrime p.1.asIdeal)ˣ)
    (e f : HeightOnePrime A → ℕ)
    (ha : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal a : Localization.AtPrime p.1.asIdeal) =
        u p * (π p : Localization.AtPrime p.1.asIdeal) ^ e p)
    (hb : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal b : Localization.AtPrime p.1.asIdeal) =
        v p * (π p : Localization.AtPrime p.1.asIdeal) ^ f p)
    (hsum : ∑ᶠ p : HeightOnePrime A,
      ((Ring.ord (Localization.AtPrime p.1.asIdeal)
          (π p : Localization.AtPrime p.1.asIdeal)).toNat *
        ((f p : ℤ) * heightOneOrd hdim p
            (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (u p)) -
          (e p : ℤ) * heightOneOrd hdim p
            (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (v p)))) = 0) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 :=
  (tameSymbolOrderAt_finsum_eq_zero_iff_finsum_order hdim symb a b π u v e f ha hb).mpr hsum

/-- **Stacks 0EAW in the prepared case when no cancellation is involved.** If at every height-one
prime the orders of vanishing of the two unit parts are proportional to the two exponents, then
every summand vanishes on its own and the reciprocity sum is zero.

This is the widest case in which the relation follows from the properties of the tame symbol
alone. It contains `Stacks.Chow.tameSymbolOrderAt_finsum_eq_zero_of_global_factorization`, where
the unit parts come from `A` and both orders are zero. Outside it the summands do not vanish
individually and the sum is zero only by cancellation. -/
theorem tameSymbolOrderAt_finsum_eq_zero_of_factorization_order (hdim : ringKrullDim A = 2)
    (symb : ∀ p : HeightOnePrime A, RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    (a b : nonZeroDivisors A)
    (π : ∀ p : HeightOnePrime A, nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (u v : ∀ p : HeightOnePrime A, (Localization.AtPrime p.1.asIdeal)ˣ)
    (e f : HeightOnePrime A → ℕ)
    (ha : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal a : Localization.AtPrime p.1.asIdeal) =
        u p * (π p : Localization.AtPrime p.1.asIdeal) ^ e p)
    (hb : ∀ p : HeightOnePrime A,
      (toLocalizationNonZeroDivisor p.1.asIdeal b : Localization.AtPrime p.1.asIdeal) =
        v p * (π p : Localization.AtPrime p.1.asIdeal) ^ f p)
    (horder : ∀ p : HeightOnePrime A,
      (f p : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (u p)) =
        (e p : ℤ) * heightOneOrd hdim p
          (Units.map (residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom (v p))) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (symb p) a b = 0 := by
  rw [finsum_congr fun p => tameSymbolOrderAt_eq_zero_of_factorization_order hdim p (symb p)
    a b (π p) (u p) (v p) (e p) (f p) (ha p) (hb p) (horder p), finsum_zero]

end Prepared

end Stacks.Chow

end
