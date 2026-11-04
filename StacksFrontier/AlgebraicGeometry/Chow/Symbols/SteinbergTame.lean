module

public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Steinberg
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.RingTheory.LocalRing.PrepareTwoNonZeroDivisors

/-!
# The Steinberg relation for the tame symbol

Let `A` be a Noetherian local domain of dimension one with fraction field `K`. The tame symbol
`d_A` of Tag 02Q1 is a bimultiplicative pairing on `Kˣ` with values in the units of the residue
field of `A`. For `x ∈ K` other than `0` and `1` it satisfies the Steinberg relation

`d_A(x, 1 - x) = 1`.

## Main results

* `AlgebraicGeometry.tameSymbol_one_sub` is the relation, with the two arguments presented as
  units of `K` identified by `(y : K) = 1 - (x : K)`.
* `AlgebraicGeometry.tameSymbol_one_sub_mk0` is the same relation written for an element of `K`
  that is neither `0` nor `1`.

## Implementation notes

The two fractions are given as units of `K` together with an equality in `K` identifying the
second with one minus the first. This records the hypothesis `x ∉ {0, 1}` of the source: `x` is a
unit exactly when it is nonzero, and `1 - x` is a unit exactly when `x ≠ 1`. The second form
converts this presentation for a bare element of `K` with the two exclusions as hypotheses.

The derivation follows the source. Writing `x = a / b` with `a` and `b` nonzero elements of `A`
gives `1 - x = (b - a) / b`, and the hypothesis that `1 - x` is a unit forces `b - a ≠ 0`.
Bimultiplicativity expands the symbol of the two quotients into the four symbols of `a` and `b`
against `b - a` and `b`, which the preparatory relation of Tag 02Q8 collapses. The auxiliary
multiplicativity lemmas are proved for an arbitrary term of `AlgebraicGeometry.TameSymbol`, since
they use nothing but the two multiplicativity fields.

Tag 02Q8 is proved in this development for every Noetherian local ring, using the preparation of
two nonzerodivisors of Tag 02Q7, which
`Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors` proves.

## References

* [Stacks Project, Tag 02Q9](https://stacks.math.columbia.edu/tag/02Q9)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

universe u v

namespace TameSymbol

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {hdim : ringKrullDim A = 1} (T : TameSymbol (K := K) hdim)

/-- The tame symbol is trivial when its second argument is `1`. -/
@[simp]
theorem one_right (x : Kˣ) : T x 1 = 1 := by
  apply mul_left_cancel (a := T x 1)
  simpa using (T.map_mul_right x 1 1).symm

/-- The tame symbol is trivial when its first argument is `1`. -/
@[simp]
theorem one_left (y : Kˣ) : T 1 y = 1 := by
  apply mul_left_cancel (a := T 1 y)
  simpa using (T.map_mul_left 1 1 y).symm

/-- The tame symbol inverts an inverse in its first argument. -/
theorem inv_left (x y : Kˣ) : T x⁻¹ y = (T x y)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.2
  rw [← T.map_mul_left, inv_mul_cancel, one_left]

/-- The tame symbol inverts an inverse in its second argument. -/
theorem inv_right (x y : Kˣ) : T x y⁻¹ = (T x y)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.2
  rw [← T.map_mul_right, inv_mul_cancel, one_right]

/-- Bimultiplicativity expands the tame symbol of two quotients. -/
theorem div_div (a b c d : Kˣ) :
    T (a / b) (c / d) = T a c * (T a d)⁻¹ * (T b c)⁻¹ * T b d := by
  rw [div_eq_mul_inv, T.map_mul_left, inv_left,
    div_eq_mul_inv, T.map_mul_right, T.map_mul_right,
    inv_right, inv_right, mul_inv_rev, inv_inv]
  simp [mul_comm, mul_assoc]

end TameSymbol

/-- **Stacks Project, Tag 02Q9.** Let `A` be a Noetherian local domain of dimension one with
fraction field `K`. For `x` a unit of `K` and `y` the unit `1 - x` of `K`, the tame symbol of
Tag 02Q1 satisfies `d_A(x, 1 - x) = 1` in the units of the residue field of `A`.

Asking that both `x` and `1 - x` be units of `K` is the hypothesis `x ∉ {0, 1}` of the source. -/
@[stacks 02Q9 "two units of the fraction field identified by `(y : K) = 1 - (x : K)`"]
theorem tameSymbol_one_sub {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] (hdim : ringKrullDim A = 1)
    (x y : Kˣ) (hy : (y : K) = 1 - (x : K)) :
    tameSymbol (K := K) hdim x y = 1 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (x : K)
  have ha : a ≠ 0 := by
    intro h
    exact x.ne_zero (by simpa [h] using hab.symm)
  let ar : RegularElements A := ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩
  let br : RegularElements A := ⟨b, hb⟩
  have hyfrac : (y : K) = algebraMap A K (b - a) / algebraMap A K b := by
    rw [hy, ← hab, map_sub]
    field_simp [IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb]
  have hba : b - a ≠ 0 := by
    intro h
    apply y.ne_zero
    rw [hyfrac, h, map_zero, zero_div]
  let car : RegularElements A := ⟨b - a, mem_nonZeroDivisors_iff_ne_zero.mpr hba⟩
  let ua := (IsLocalization.map_units K ar).unit
  let ub := (IsLocalization.map_units K br).unit
  let uc := (IsLocalization.map_units K car).unit
  have hx : x = ua / ub := by apply Units.ext; simpa [ua, ub] using hab.symm
  have hy' : y = uc / ub := by apply Units.ext; simpa [uc, ub, car, br] using hyfrac
  let T := tameSymbol (K := K) hdim
  change T x y = 1
  rw [hx, hy', T.div_div ua ub uc ub]
  have har : IsRegular a := isRegular_iff_mem_nonZeroDivisors.mpr ar.property
  have hbr : IsRegular b := isRegular_iff_mem_nonZeroDivisors.mpr br.property
  have hcar : IsRegular (b - a) := isRegular_iff_mem_nonZeroDivisors.mpr car.property
  have hprepare := moduleSymbol_steinberg_prepare
    (A := A) (M := A) a b
    har.isSMulRegular hbr.isSMulRegular hcar.isSMulRegular
    ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)
  have hsymbol : T ua uc * T ub ub = T ub uc * T ua ub := by
    rw [T.eq_moduleSymbol a (b - a) har hcar,
      T.eq_moduleSymbol b b hbr hbr,
      T.eq_moduleSymbol b (b - a) hbr hcar,
      T.eq_moduleSymbol a b har hbr]
    exact hprepare
  calc
    T ua uc * (T ua ub)⁻¹ * (T ub uc)⁻¹ * T ub ub =
        (T ua uc * T ub ub) * (T ub uc * T ua ub)⁻¹ := by
          rw [mul_inv]
          ac_rfl
    _ = 1 := by rw [hsymbol]; simp

/-- **Stacks Project, Tag 02Q9.** Let `A` be a Noetherian local domain of dimension one with
fraction field `K`. For `x ∈ K` other than `0` and `1`, the tame symbol of Tag 02Q1 satisfies
`d_A(x, 1 - x) = 1` in the units of the residue field of `A`. -/
@[stacks 02Q9 "an element of the fraction field other than `0` and `1`"]
theorem tameSymbol_one_sub_mk0 {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] {K : Type v} [Field K]
    [Algebra A K] [IsFractionRing A K] (hdim : ringKrullDim A = 1)
    (x : K) (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) :
    tameSymbol (K := K) hdim (Units.mk0 x hx₀)
      (Units.mk0 (1 - x) (sub_ne_zero_of_ne hx₁.symm)) = 1 :=
  tameSymbol_one_sub hdim _ _ rfl

end AlgebraicGeometry
