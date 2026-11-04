module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Arithmetic of the order of vanishing of a nonzero fraction

For a Noetherian domain of dimension at most one, the order of vanishing of a nonzero element
of its fraction field is an integer, obtained from `Ring.ordFrac` by stripping the adjoined
zero and passing from the multiplicative to the additive notation. The order is additive for
products, negates on inverses, subtracts on quotients, and vanishes on signs.

## Main results

* `Module.FiniteLength.toAdd_unzero_ordFrac_mul`,
  `Module.FiniteLength.toAdd_unzero_ordFrac_inv` and
  `Module.FiniteLength.toAdd_unzero_ordFrac_div` are the three arithmetic identities.
* `Module.FiniteLength.toAdd_unzero_ordFrac_mul_div_mul` combines them into the alternating sum
  of four orders.
* `Module.FiniteLength.toAdd_unzero_ordFrac_neg_one_pow` says a power of `-1` has order zero.

## Implementation notes

The order is written in the form `Multiplicative.toAdd (WithZero.unzero h)`, with the proof `h`
that the value of `Ring.ordFrac` is nonzero obtained from the element being a unit. Since that
proof is irrelevant, these identities rewrite against any other proof of the same fact.

## References

* [Stacks Project, Tag 02MC](https://stacks.math.columbia.edu/tag/02MC)
-/

@[expose] public section

namespace Module.FiniteLength

universe u v

variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D]
  {K : Type v} [Field K] [Algebra D K] [IsFractionRing D K]

/-- A square root of one in the integers written multiplicatively is zero additively. -/
private theorem toAdd_eq_zero_of_mul_self_eq_one {u : Multiplicative ℤ} (h : u * u = 1) :
    Multiplicative.toAdd u = 0 := by
  have h' : Multiplicative.toAdd u + Multiplicative.toAdd u = 0 :=
    congrArg Multiplicative.toAdd h
  omega

/-- If a nonzero value equals a coerced element, its `unzero` has the same additive value. -/
private theorem toAdd_unzero_congr {x : WithZero (Multiplicative ℤ)} {y : Multiplicative ℤ}
    (hx : x ≠ 0) (h : x = y) : Multiplicative.toAdd (WithZero.unzero hx) = Multiplicative.toAdd y :=
  congrArg Multiplicative.toAdd (WithZero.coe_inj.mp (by simpa using h))

/-- The order of a product of two nonzero fractions is the sum of their orders. -/
public theorem toAdd_unzero_ordFrac_mul (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D (f * g))
        (((mul_ne_zero hf hg).isUnit.map (Ring.ordFrac D)).ne_zero)) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D f)
          ((hf.isUnit.map (Ring.ordFrac D)).ne_zero)) +
        Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D g)
          ((hg.isUnit.map (Ring.ordFrac D)).ne_zero)) := by
  rw [← toAdd_mul]
  exact toAdd_unzero_congr _ (by simp)

/-- The order of the inverse of a nonzero fraction is the negative of its order. -/
public theorem toAdd_unzero_ordFrac_inv (f : K) (hf : f ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D f⁻¹)
        (((inv_ne_zero hf).isUnit.map (Ring.ordFrac D)).ne_zero)) =
      -Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D f)
        ((hf.isUnit.map (Ring.ordFrac D)).ne_zero)) := by
  rw [← toAdd_inv]
  exact toAdd_unzero_congr _ (by simp)

/-- The order of a quotient of two nonzero fractions is the difference of their orders. -/
public theorem toAdd_unzero_ordFrac_div (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D (f / g))
        (((div_ne_zero hf hg).isUnit.map (Ring.ordFrac D)).ne_zero)) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D f)
          ((hf.isUnit.map (Ring.ordFrac D)).ne_zero)) -
        Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D g)
          ((hg.isUnit.map (Ring.ordFrac D)).ne_zero)) := by
  rw [← toAdd_div]
  exact toAdd_unzero_congr _ (by simp [div_eq_mul_inv])

/-- The alternating combination of the orders of four nonzero fractions is the order of the
fraction `c * a / (d * b)`. -/
public theorem toAdd_unzero_ordFrac_mul_div_mul (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D a)
          ((ha.isUnit.map (Ring.ordFrac D)).ne_zero)) -
        Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D b)
          ((hb.isUnit.map (Ring.ordFrac D)).ne_zero)) +
        Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D c)
          ((hc.isUnit.map (Ring.ordFrac D)).ne_zero)) -
        Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D d)
          ((hd.isUnit.map (Ring.ordFrac D)).ne_zero)) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D (c * a / (d * b)))
        (((div_ne_zero (mul_ne_zero hc ha) (mul_ne_zero hd hb)).isUnit.map
          (Ring.ordFrac D)).ne_zero)) := by
  rw [toAdd_unzero_ordFrac_div (c * a) (d * b) (mul_ne_zero hc ha) (mul_ne_zero hd hb),
    toAdd_unzero_ordFrac_mul c a hc ha, toAdd_unzero_ordFrac_mul d b hd hb]
  ring

/-- A power of `-1` has order zero. -/
public theorem toAdd_unzero_ordFrac_neg_one_pow (k : ℕ) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D ((-1 : K) ^ k))
      (((pow_ne_zero k (show (-1 : K) ≠ 0 from neg_ne_zero.mpr one_ne_zero)).isUnit.map
        (Ring.ordFrac D)).ne_zero)) = 0 := by
  refine toAdd_eq_zero_of_mul_self_eq_one (WithZero.coe_inj.mp ?_)
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_one, ← map_mul,
    show ((-1 : K) ^ k) * ((-1 : K) ^ k) = 1 from by rw [← mul_pow]; norm_num, map_one]

end Module.FiniteLength
