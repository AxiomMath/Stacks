module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# The order of vanishing along a prime divisor of an algebraic space

Let `X` be an algebraic space and let `Z ⊆ X` be a prime divisor with generic point `ξ`. The
henselian local ring `𝒪^h_{X, ξ}` need not be a domain, so the order of vanishing along `Z` is
read off the *total* ring of fractions `Q(𝒪^h_{X, ξ})`, the localization of `𝒪^h_{X, ξ}` at its
nonzerodivisors: a unit of `Q(𝒪^h_{X, ξ})` is a fraction `a / b` of nonzerodivisors, and its
order of vanishing is `length(𝒪^h_{X, ξ} / a 𝒪^h_{X, ξ}) - length(𝒪^h_{X, ξ} / b 𝒪^h_{X, ξ})`,
an integer because the two lengths are finite when `𝒪^h_{X, ξ}` is Noetherian of dimension at
most one.

The first half of the file carries out that construction for an arbitrary Noetherian ring of
Krull dimension at most one, where it is the extension of `Ring.ordMonoidWithZeroHom` along the
localization map at the nonzerodivisors; the second half evaluates it at the henselian local
ring of a decent algebraic space at the generic point of a prime divisor.

## Main definitions

* `Ring.ordTotalFrac` is the order of vanishing on a total ring of fractions, as a homomorphism
  of monoids with zero into `WithZero (Multiplicative ℤ)`, and `Ring.ordTotalFracInt` is its
  integer value at a unit.
* `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing` is `𝒪^h_{X, ξ}` for `ξ` the
  generic point of a prime divisor, and
  `AlgebraicGeometry.Space.PrimeDivisor.genericTotalFractionRing` is `Q(𝒪^h_{X, ξ})`.
* `AlgebraicGeometry.Space.PrimeDivisor.ord` is the order of vanishing along a prime divisor of
  a unit of the total ring of fractions of the henselian local ring at its generic point.

## Main results

* `Ring.ordTotalFracInt_mul` and `AlgebraicGeometry.Space.PrimeDivisor.ord_mul`: the order of
  vanishing is additive in the function, so it is a homomorphism from the group of units into
  `ℤ`.
* `Ring.ordTotalFracInt_mk'` and `AlgebraicGeometry.Space.PrimeDivisor.ord_mk'`: the value at a
  fraction of nonzerodivisors is the difference of the two lengths.
* `Ring.ordTotalFracInt_algebraMap` and
  `AlgebraicGeometry.Space.PrimeDivisor.ord_algebraMap`: the value at a nonzerodivisor of the
  ring itself is the length of the quotient by the ideal it generates.
* `Ring.ordTotalFracInt_congr` and `AlgebraicGeometry.Space.PrimeDivisor.ord_congr`: the value
  depends neither on the proof that the function is a unit nor on the representative of the
  function.

## Implementation notes

`Ring.ordFrac` of the ambient library is the same extension of `Ring.ordMonoidWithZeroHom`, but
it is stated for a *field* of fractions and so is unavailable for a ring with zerodivisors,
which is exactly the case at hand: the henselian local ring at the generic point of a prime
divisor of an integral algebraic space is reduced but need not be a domain. Nothing else in the
construction uses the domain hypothesis — `Ring.ord_mul` is additive for any nonzerodivisor and
`Ring.ord` is finite on nonzerodivisors of a Noetherian ring of dimension at most one — so
`Ring.ordTotalFrac` is that same lift taken over an arbitrary total ring of fractions.

`Ring.ordTotalFracInt` is valued in `ℤ` rather than in `WithZero (Multiplicative ℤ)`, which is
what makes it a coefficient of a Weil divisor; a unit of the total ring of fractions has
invertible, hence nonzero, image, and `WithZero.unzero` strips the adjoined zero. Its unit
hypothesis is a proposition, so the value does not depend on the proof supplied.

The Noetherian, nontriviality and dimension hypotheses on the henselian local ring are carried
as instance arguments of `AlgebraicGeometry.Space.PrimeDivisor.ord`. They hold for a prime
divisor of a locally Noetherian integral algebraic space, where `𝒪^h_{X, ξ}` is a reduced
one-dimensional Noetherian local ring; that identification is not proved here, and neither is
the injection of the function field `R(X)` into `Q(𝒪^h_{X, ξ})` along which the order of
vanishing is evaluated at a rational function.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

/-! ### The order of vanishing on a total ring of fractions -/

namespace Ring

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Nontrivial R]
variable {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- The order of vanishing on a total ring of fractions `K` of a Noetherian ring `R` of Krull
dimension at most one: the extension of `Ring.ordMonoidWithZeroHom` along the localization map
at the nonzerodivisors of `R`. -/
noncomputable def ordTotalFrac : K →*₀ WithZero (Multiplicative ℤ) :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors R) K).lift₀ (ordMonoidWithZeroHom R)
    (ordMonoidWithZeroHom_isUnit R)

/-- On an element of `R` the order of vanishing of the total ring of fractions is the order of
vanishing of `R`. -/
theorem ordTotalFrac_algebraMap (x : R) :
    ordTotalFrac R (algebraMap R K x) = ordMonoidWithZeroHom R x :=
  Submonoid.LocalizationMap.lift_eq ..

/-- The integer-valued order of vanishing of a unit `x` of a total ring of fractions `K` of a
Noetherian ring `R` of Krull dimension at most one. -/
noncomputable def ordTotalFracInt (x : K) (hx : IsUnit x) : ℤ :=
  Multiplicative.toAdd (WithZero.unzero (hx.map (ordTotalFrac R (K := K))).ne_zero)

/-- The integer-valued order of vanishing of a unit is the `WithZero`-valued one, coerced. -/
private theorem coe_ofAdd_ordTotalFracInt (x : K) (hx : IsUnit x) :
    ((Multiplicative.ofAdd (ordTotalFracInt R x hx) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) = ordTotalFrac R x := by
  simp [ordTotalFracInt]

/-- The order of vanishing of a product of units is the sum of the orders of vanishing. -/
theorem ordTotalFracInt_mul (x y : K) (hx : IsUnit x) (hy : IsUnit y) :
    ordTotalFracInt R (x * y) (hx.mul hy) =
      ordTotalFracInt R x hx + ordTotalFracInt R y hy := by
  refine Multiplicative.ofAdd.injective (WithZero.coe_injective ?_)
  rw [ofAdd_add, WithZero.coe_mul, coe_ofAdd_ordTotalFracInt, coe_ofAdd_ordTotalFracInt,
    coe_ofAdd_ordTotalFracInt, map_mul]

/-- On a nonzerodivisor `r` of `R` the order of vanishing is the length of `R ⧸ (r)`, which is
finite under the standing hypotheses. -/
theorem ordTotalFracInt_algebraMap (r : R) (hr : r ∈ nonZeroDivisors R) :
    ordTotalFracInt R (algebraMap R K r) (IsLocalization.map_units K ⟨r, hr⟩) =
      ((Ring.ord R r).toNat : ℤ) := by
  refine Multiplicative.ofAdd.injective (WithZero.coe_injective ?_)
  rw [coe_ofAdd_ordTotalFracInt, ordTotalFrac_algebraMap]
  exact ordMonoidWithZeroHom_eq_coe R hr (ENat.natCast_toNat (ord_ne_top hr)).symm

/-- The order of vanishing of a unit does not depend on the proof that it is a unit, nor on the
representative of the element. -/
theorem ordTotalFracInt_congr {x y : K} (hx : IsUnit x) (hy : IsUnit y) (h : x = y) :
    ordTotalFracInt R x hx = ordTotalFracInt R y hy := by
  subst h
  rfl

/-- The order of vanishing of a fraction `a / b` of nonzerodivisors is the difference of the
lengths of `R ⧸ (a)` and `R ⧸ (b)`. -/
theorem ordTotalFracInt_mk' (a b : nonZeroDivisors R)
    (hu : IsUnit (IsLocalization.mk' K (a : R) b)) :
    ordTotalFracInt R (IsLocalization.mk' K (a : R) b) hu =
      ((Ring.ord R (a : R)).toNat : ℤ) - ((Ring.ord R (b : R)).toNat : ℤ) := by
  have hb : IsUnit (algebraMap R K (b : R)) := IsLocalization.map_units K b
  have ha : IsUnit (algebraMap R K (a : R)) := IsLocalization.map_units K a
  have hspec : IsLocalization.mk' K (a : R) b * algebraMap R K (b : R) =
      algebraMap R K (a : R) := IsLocalization.mk'_spec K (a : R) b
  have key := (ordTotalFracInt_congr R (hu.mul hb) ha hspec).symm.trans
    (ordTotalFracInt_mul R _ _ hu hb)
  rw [ordTotalFracInt_algebraMap R (a : R) a.2] at key
  rw [ordTotalFracInt_algebraMap R (b : R) b.2] at key
  omega

end Ring

/-! ### The order of vanishing along a prime divisor -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- The henselian local ring of a decent algebraic space at the generic point of a prime
divisor. -/
noncomputable abbrev PrimeDivisor.genericHenselianLocalRing : CommRingCat.{u + 1} :=
  henselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec

/-- The total ring of fractions of the henselian local ring at the generic point of a prime
divisor: its localization at the nonzerodivisors. -/
noncomputable abbrev PrimeDivisor.genericTotalFractionRing : Type (u + 1) :=
  FractionRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)

variable [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)]

/-- The order of vanishing along a prime divisor `Z` of a unit `f` of the total ring of
fractions of the henselian local ring at the generic point of `Z`. -/
noncomputable def PrimeDivisor.ord (f : Z.genericTotalFractionRing B S hS hX hdec)
    (hf : IsUnit f) : ℤ :=
  Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec) f hf

/-- The order of vanishing along a prime divisor depends neither on the proof that the function
is a unit nor on the representative of the function. -/
theorem PrimeDivisor.ord_congr {f g : Z.genericTotalFractionRing B S hS hX hdec}
    (hf : IsUnit f) (hg : IsUnit g) (h : f = g) :
    Z.ord B S hS hX hdec f hf = Z.ord B S hS hX hdec g hg :=
  Ring.ordTotalFracInt_congr _ hf hg h

/-- The order of vanishing along a prime divisor is additive in the function. -/
theorem PrimeDivisor.ord_mul (f g : Z.genericTotalFractionRing B S hS hX hdec)
    (hf : IsUnit f) (hg : IsUnit g) :
    Z.ord B S hS hX hdec (f * g) (hf.mul hg) =
      Z.ord B S hS hX hdec f hf + Z.ord B S hS hX hdec g hg :=
  Ring.ordTotalFracInt_mul _ f g hf hg

/-- The order of vanishing along a prime divisor of a nonzerodivisor of the henselian local ring
at its generic point is the length of the quotient by the ideal that element generates. -/
theorem PrimeDivisor.ord_algebraMap
    (r : ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (hr : r ∈ nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :
    Z.ord B S hS hX hdec
        (algebraMap _ (Z.genericTotalFractionRing B S hS hX hdec) r)
        (IsLocalization.map_units _ ⟨r, hr⟩) =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec) r).toNat : ℤ) :=
  Ring.ordTotalFracInt_algebraMap _ r hr

/-- The order of vanishing along a prime divisor of a fraction `a / b` of nonzerodivisors of the
henselian local ring at its generic point is the difference of the lengths of the quotients by
the ideals `(a)` and `(b)`.

This is the defining formula of the order of vanishing, computed on the total ring of fractions
of the henselian local ring. -/
@[stacks 0ENL "the difference-of-lengths formula, on a unit of the total ring of fractions of the
  henselian local ring at the generic point"]
theorem PrimeDivisor.ord_mk'
    (a b : nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (hu : IsUnit (IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
      (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b)) :
    Z.ord B S hS hX hdec (IsLocalization.mk' (Z.genericTotalFractionRing B S hS hX hdec)
        (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec)) b) hu =
      ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (a : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) -
        ((Ring.ord ↥(Z.genericHenselianLocalRing B S hS hX hdec)
          (b : ↥(Z.genericHenselianLocalRing B S hS hX hdec))).toNat : ℤ) :=
  Ring.ordTotalFracInt_mk' _ a b hu

end AlgebraicGeometry.Space

end
