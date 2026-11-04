module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Stalk
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafStalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A germ of a meromorphic function on an integral scheme is a fraction

The multipliers `g` of [Stacks, Tag 0BD7] are meromorphic functions on the base, and the
uniqueness sentence of the penultimate paragraph of that proof compares two of them through the
local ring: `g` is well defined "up to multiplication by an element of `𝒪_{Y, y}^*`". The
descent of such a unit, `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_stalkMap`, takes two
elements of `𝒪_{Y, y}` and not two germs of `𝒦_Y`, so a germ of `𝒦_Y` has to be presented as
`p / d` with `p, d ∈ 𝒪_{Y, y}` and `d` a nonzerodivisor before that descent can be applied.

This file is that presentation. On an integral scheme the stalk of `𝒦_Y` at `y` is the fraction
field of `𝒪_{Y, y}`, so the presentation exists, two germs may be given a common denominator,
and a relation between numerators is the same thing as a relation between the germs.

## Main definitions

* `AlgebraicGeometry.toTotalQuotientStalk`: the ring map `𝒪_{Y, y} ⟶ (𝒦_Y)_y`.

## Main results

* `AlgebraicGeometry.isFractionRing_stalk_totalQuotientSheaf`: on an integral scheme the stalk of
  `𝒦_Y` is the fraction field of the local ring. This is
  `AlgebraicGeometry.stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated` with both of
  its hypotheses discharged from integrality, which until now was done inline.
* `AlgebraicGeometry.toTotalQuotientStalk_injective` and
  `AlgebraicGeometry.isUnit_toTotalQuotientStalk`: that map is injective, and a nonzero germ of
  `𝒪_Y` becomes invertible, so a denominator may be divided out.
* `AlgebraicGeometry.exists_mul_toTotalQuotientStalk_eq`: a germ of `𝒦_Y` is `p / d`.
* `AlgebraicGeometry.exists_mul_toTotalQuotientStalk_eq₂`: two germs with one common `d`.
* `AlgebraicGeometry.eq_mul_of_numerator_eq_mul`: with a common denominator, a relation
  `p = v q` between the numerators gives the relation `a = v b` between the germs — the form in
  which the conclusion of the unit descent is carried back to the multipliers.

## Implementation notes

`AlgebraicGeometry.toTotalQuotientStalk` is not a new map: it is
`(TopCat.Presheaf.stalkFunctor CommRingCat y).map Y.toTotalQuotientSheaf.hom`, which this
library writes out at every use, ascribed at the type `↑(Y.presheaf.stalk y) →+*
↑(Y.totalQuotientSheaf.presheaf.stalk y)`. The ascription is what the statements below need:
the codomain of the inline spelling is `(stalkFunctor CommRingCat y).obj
Y.totalQuotientSheaf.obj`, and multiplying a germ of `𝒦_Y` by an element of *that* type leaves
`HMul` unsolved even though the two types are definitionally equal.

The denominator is returned as `d ≠ 0` rather than as membership of `nonZeroDivisors`: on an
integral scheme the local ring is a domain, so the two are interchangeable, and the consumers
of this file divide by `d` rather than cancel it.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (Y : Scheme.{u}) (y : Y)

/-- The ring map `𝒪_{Y, y} ⟶ (𝒦_Y)_y` on stalks induced by `𝒪_Y ⟶ 𝒦_Y`. -/
noncomputable def toTotalQuotientStalk :
    ↑(Y.presheaf.stalk y) →+* ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat y).map Y.toTotalQuotientSheaf.hom).hom

variable [IsIntegral Y]

/-- **The stalk of `𝒦_Y` at a point of an integral scheme is the fraction field of the local
ring there.** Every weakly associated point of an integral scheme is a generic point and every
open has finitely many irreducible components, which are the two hypotheses of
`AlgebraicGeometry.stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated`. -/
theorem isFractionRing_stalk_totalQuotientSheaf :
    letI : Algebra ↑(Y.presheaf.stalk y) ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
      (toTotalQuotientStalk Y y).toAlgebra
    IsFractionRing ↑(Y.presheaf.stalk y) ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
  stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated Y
    (le_of_eq (weaklyAssociatedPointsOfScheme_eq_genericPoints Y))
    (fun U _ => Stacks.Divisors.finite_irreducibleComponents_opens Y U) y

/-- **A regular germ is determined by the meromorphic function it is.** On an integral scheme
`𝒪_{Y, y} ⟶ (𝒦_Y)_y` is the inclusion of a domain in its fraction field. -/
@[ega "IV 20.1.4" "special case"]
theorem toTotalQuotientStalk_injective : Function.Injective (toTotalQuotientStalk Y y) := by
  let : Algebra ↑(Y.presheaf.stalk y) ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
    (toTotalQuotientStalk Y y).toAlgebra
  have := isFractionRing_stalk_totalQuotientSheaf Y y
  exact IsFractionRing.injective ↑(Y.presheaf.stalk y)
    ↑(Y.totalQuotientSheaf.presheaf.stalk y)

/-- **A nonzero germ of `𝒪_Y` is invertible as a meromorphic function**, which is what lets a
denominator be divided out rather than only cancelled. -/
theorem isUnit_toTotalQuotientStalk {d : ↑(Y.presheaf.stalk y)} (hd : d ≠ 0) :
    IsUnit (toTotalQuotientStalk Y y d) := by
  let : Algebra ↑(Y.presheaf.stalk y) ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
    (toTotalQuotientStalk Y y).toAlgebra
  have := isFractionRing_stalk_totalQuotientSheaf Y y
  exact IsLocalization.map_units ↑(Y.totalQuotientSheaf.presheaf.stalk y)
    (⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ : nonZeroDivisors ↑(Y.presheaf.stalk y))

/-- **A germ of a meromorphic function is `p / d`.** For `Y` integral, every element of the
stalk of `𝒦_Y` at `y` satisfies `a d = p` with `p, d ∈ 𝒪_{Y, y}` and `d ≠ 0`. -/
theorem exists_mul_toTotalQuotientStalk_eq (a : ↑(Y.totalQuotientSheaf.presheaf.stalk y)) :
    ∃ p d : ↑(Y.presheaf.stalk y), d ≠ 0 ∧
      a * toTotalQuotientStalk Y y d = toTotalQuotientStalk Y y p := by
  let : Algebra ↑(Y.presheaf.stalk y) ↑(Y.totalQuotientSheaf.presheaf.stalk y) :=
    (toTotalQuotientStalk Y y).toAlgebra
  have := isFractionRing_stalk_totalQuotientSheaf Y y
  obtain ⟨⟨p, d, hd⟩, hpd⟩ := IsLocalization.surj
    (nonZeroDivisors ↑(Y.presheaf.stalk y)) a
  exact ⟨p, d, nonZeroDivisors.ne_zero hd, hpd⟩

/-- **Two germs of meromorphic functions share a denominator.** The product of the two separate
denominators serves for both, which is what makes a *relation* between two multipliers readable
on their numerators. -/
theorem exists_mul_toTotalQuotientStalk_eq₂ (a b : ↑(Y.totalQuotientSheaf.presheaf.stalk y)) :
    ∃ p q d : ↑(Y.presheaf.stalk y), d ≠ 0 ∧
      a * toTotalQuotientStalk Y y d = toTotalQuotientStalk Y y p ∧
        b * toTotalQuotientStalk Y y d = toTotalQuotientStalk Y y q := by
  obtain ⟨p, d, hd, hpd⟩ := exists_mul_toTotalQuotientStalk_eq Y y a
  obtain ⟨q, e, he, hqe⟩ := exists_mul_toTotalQuotientStalk_eq Y y b
  refine ⟨p * e, q * d, d * e, mul_ne_zero hd he, ?_, ?_⟩
  · rw [map_mul, ← mul_assoc, hpd, map_mul]
  · rw [map_mul, mul_comm (toTotalQuotientStalk Y y d) (toTotalQuotientStalk Y y e),
      ← mul_assoc, hqe, map_mul]

/-- **A relation between the numerators is a relation between the germs.** If `a` and `b` are
written over a common denominator `d ≠ 0` with numerators `p` and `q`, and `p = v q`, then
`a = v b` in the stalk of `𝒦_Y`. The local ring of an integral scheme is a domain, so `d` stays
nonzero in the fraction field and cancels. -/
theorem eq_mul_of_numerator_eq_mul {a b : ↑(Y.totalQuotientSheaf.presheaf.stalk y)}
    {p q d v : ↑(Y.presheaf.stalk y)} (hd : d ≠ 0)
    (ha : a * toTotalQuotientStalk Y y d = toTotalQuotientStalk Y y p)
    (hb : b * toTotalQuotientStalk Y y d = toTotalQuotientStalk Y y q)
    (hpq : p = v * q) :
    a = toTotalQuotientStalk Y y v * b := by
  refine (isUnit_toTotalQuotientStalk Y y hd).mul_left_inj.1 ?_
  rw [ha, hpq, map_mul, mul_assoc, hb]

end AlgebraicGeometry

end
