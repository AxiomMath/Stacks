module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.DualNumber
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicCharts

/-!
# Pole orders at the zero section of a plane Weierstrass cubic

Let `W` be a Weierstrass equation over a commutative ring `R`, with no condition on its
discriminant. Near the zero section `(0 : 1 : 0)` the plane cubic is the chart `D₊(y)` with
equation `Z w = X³`, `w = 1 + a₁X + a₃Z - a₂X² - a₄XZ - a₆Z²`, where `X = x / y` and `Z = z / y`.
Along the zero section `X` is a formal parameter: there is a formal arc
`R[X, Z]/(F(X, 1, Z)) → R⟦X⟧` with `X ↦ X` and `Z ↦ X³ / w`. Since `x = X / Z` and `y = 1 / Z`,
the affine coordinate ring `R[x, y]/(f)` maps to the Laurent series `R((X))` with `x ↦ w / X²` and
`y ↦ w / X³`, and its monomials `xⁱ` and `xⁱ y` acquire poles of the distinct orders `2i` and
`2i + 3` with leading coefficient `1`. This file proves that the elements with a pole of order at
most `3` are the combinations `r + s x + t y`, and those with a pole of order at most `2` the
combinations `r + s x`, with `t` and `s` read off from the leading coefficient. It also sets up the
first-order thickenings of the zero section, with which the tangent of a morphism at the zero
section is computed.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.formalW`: the root `w ≡ 1 mod X` in `R⟦X⟧`
  of a monic cubic, obtained from Hensel's lemma; `formalZ W = X³ / w`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.arcHom`: the formal arc
  `R[X, Z]/(F(X, 1, Z)) → R⟦X⟧`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.laurentHom` the punctured formal arc
  `R[x, y]/(f) → R((X))`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.PoleBound`: a Laurent series has a pole of
  order at most `n`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.weightFiltration`: the span of the
  monomials of weight at most `k`, where `x` has weight `2` and `y` weight `3`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.tangentHom`: the first-order thickening of
  the zero section with tangent `p`, a homomorphism to the dual numbers.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.SpecMap_laurentHom_chartZ`: the punctured
  formal arc is the formal arc read through the chart `D₊(z)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.mem_weightFiltration_of_poleBound`: an
  element of weight at most `k + 1` with a pole of order at most `k` has weight at most `k`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_eq_of_poleBound_three`,
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_eq_of_laurentHom_eq_three` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_eq_of_laurentHom_eq_two`: **the
  pole-order bounds**, `L₃ = R + R x + R y` and `L₂ = R + R x`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.eq_tangentHom`: every `R`-linear
  first-order thickening of the zero section is a `tangentHom W p`.

## Implementation notes

The root `w` comes from `HenselianRing` for `R⟦X⟧` at `(X)`, which Mathlib derives from
`X`-adic completeness. Its cubic `T³ - (1 + a₁X - a₂X²)T² - (a₃ - a₄X)X³T + a₆X⁶` is monic, unlike
the equation `Z w(X, Z) = X³` it replaces: it is the equation satisfied by `w(X, X³/T)` at `T = w`.

Pole orders are stated without any order function on `R((X))`, which over a general ring is not
multiplicative: a pole of order at most `n` is a factorization `X⁻ⁿ G` with `G` a power series,
and the leading-coefficient argument is `constantCoeff_eq_zero_of_poleBound`, which only uses that
`R⟦X⟧ → R((X))` is injective.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, Chapter IV]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### The formal expansion of the zero section -/

/-- The monic cubic `T³ - (1 + a₁X - a₂X²)T² - (a₃ - a₄X)X³T + a₆X⁶` over `R⟦X⟧`. Its root
`w ≡ 1 mod X` is the function `1 + a₁X + a₃Z - a₂X² - a₄XZ - a₆Z²` along the formal branch
`Z = X³ / w` of the chart `D₊(y)` through the zero section. -/
def formalPolynomial : Polynomial (PowerSeries R) :=
  Polynomial.X ^ 3 + (-Polynomial.C (1 + PowerSeries.C W.a₁ * PowerSeries.X -
      PowerSeries.C W.a₂ * PowerSeries.X ^ 2) * Polynomial.X ^ 2 -
    Polynomial.C ((PowerSeries.C W.a₃ - PowerSeries.C W.a₄ * PowerSeries.X) * PowerSeries.X ^ 3) *
      Polynomial.X + Polynomial.C (PowerSeries.C W.a₆ * PowerSeries.X ^ 6))

/-- The cubic `formalPolynomial W` is monic. -/
theorem monic_formalPolynomial : (formalPolynomial W).Monic :=
  Polynomial.monic_X_pow_add
    ((Polynomial.degree_le_of_natDegree_le (n := 2) (by compute_degree)).trans_lt
      (by exact_mod_cast Nat.lt_succ_self 2))

/-- The cubic `formalPolynomial W` has a root `w` in `R⟦X⟧` with `w ≡ 1 mod X`. -/
theorem exists_formalPolynomial_isRoot :
    ∃ w : PowerSeries R, (formalPolynomial W).IsRoot w ∧
      w - 1 ∈ Ideal.span {(PowerSeries.X : PowerSeries R)} := by
  refine HenselianRing.is_henselian _ (monic_formalPolynomial W) 1 ?_ ?_
  · refine Ideal.mem_span_singleton.mpr ⟨-PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X -
      (PowerSeries.C W.a₃ - PowerSeries.C W.a₄ * PowerSeries.X) * PowerSeries.X ^ 2 +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 5, ?_⟩
    simp only [formalPolynomial, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · have hX : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries R)}) PowerSeries.X = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have : (formalPolynomial W).derivative.eval 1 = 1 + PowerSeries.X *
        (-2 * PowerSeries.C W.a₁ + 2 * PowerSeries.C W.a₂ * PowerSeries.X -
          (PowerSeries.C W.a₃ - PowerSeries.C W.a₄ * PowerSeries.X) * PowerSeries.X ^ 2) := by
      simp only [formalPolynomial, Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_neg, Polynomial.derivative_mul, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
        Polynomial.eval_zero]
      push_cast
      ring
    rw [this, map_add, map_mul, hX, zero_mul, add_zero, map_one]
    exact isUnit_one

/-- The root `w ≡ 1 mod X` of `formalPolynomial W` in `R⟦X⟧`. -/
def formalW : PowerSeries R := (exists_formalPolynomial_isRoot W).choose

/-- The power series `w = formalW W` satisfies
`w³ - (1 + a₁X - a₂X²)w² - (a₃ - a₄X)X³w + a₆X⁶ = 0`. -/
theorem formalW_equation :
    formalW W ^ 3 - (1 + PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₂ *
        PowerSeries.X ^ 2) * formalW W ^ 2 -
      (PowerSeries.C W.a₃ - PowerSeries.C W.a₄ * PowerSeries.X) * PowerSeries.X ^ 3 * formalW W +
      PowerSeries.C W.a₆ * PowerSeries.X ^ 6 = 0 := by
  have h : (formalPolynomial W).IsRoot (formalW W) :=
    (exists_formalPolynomial_isRoot W).choose_spec.1
  simp only [Polynomial.IsRoot, formalPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at h
  linear_combination h

/-- The constant coefficient of `formalW W` is `1`. -/
theorem constantCoeff_formalW : PowerSeries.constantCoeff (formalW W) = 1 := by
  have h : formalW W - 1 ∈ Ideal.span {(PowerSeries.X : PowerSeries R)} :=
    (exists_formalPolynomial_isRoot W).choose_spec.2
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
  exact h

/-- The power series `formalW W` is a unit of `R⟦X⟧`. -/
theorem isUnit_formalW : IsUnit (formalW W) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_formalW]
  exact isUnit_one

/-- The inverse of `formalW W`. -/
def formalWInv : PowerSeries R := ↑(isUnit_formalW W).unit⁻¹

/-- `formalWInv W` is a left inverse of `formalW W`. -/
theorem formalWInv_mul : formalWInv W * formalW W = 1 :=
  (isUnit_formalW W).val_inv_mul

/-- The formal branch `Z = X³ / w` of the chart `D₊(y)` through the zero section. -/
def formalZ : PowerSeries R := PowerSeries.X ^ 3 * formalWInv W

/-- **The formal arc at the zero section.** The homomorphism from the coordinate ring of the chart
`D₊(y)` to `R⟦X⟧` with `X ↦ X` and `Z ↦ X³ / w`: the completion of the plane cubic along the
zero section, with `X = x / y` as formal parameter. -/
def arcHom : ChartYRing W →+* PowerSeries R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom PowerSeries.C (formalZ W)) PowerSeries.X <| by
    have hw := formalW_equation W
    have hv := formalWInv_mul W
    have key : Polynomial.eval₂ (Polynomial.eval₂RingHom PowerSeries.C (formalZ W)) PowerSeries.X
        (chartYPolynomial W) * formalW W ^ 3 = 0 := by
      simp only [chartYPolynomial, formalZ, Polynomial.eval₂_add, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.coe_eval₂RingHom]
      set v := formalWInv W
      set w := formalW W
      set X := (PowerSeries.X : PowerSeries R)
      linear_combination X ^ 3 * hw + (PowerSeries.C W.a₂ * X ^ 5 * w ^ 2 +
        PowerSeries.C W.a₄ * X ^ 7 * w * (v * w + 1) - PowerSeries.C W.a₁ * X ^ 4 * w ^ 2 -
        X ^ 3 * w ^ 2 - PowerSeries.C W.a₃ * X ^ 6 * w * (v * w + 1) +
        PowerSeries.C W.a₆ * X ^ 9 * ((v * w) ^ 2 + v * w + 1)) * hv
    exact ((isUnit_formalW W).pow 3).mul_left_eq_zero.mp key

/-- The formal arc sends `X` to `X`. -/
@[simp] theorem arcHom_chartYX : arcHom W (chartYX W) = PowerSeries.X := by
  simp [arcHom, chartYX]

/-- The formal arc sends `Z` to `formalZ W = X³ / w`. -/
@[simp] theorem arcHom_chartYZ : arcHom W (chartYZ W) = formalZ W := by
  simp [arcHom, chartYZ]

/-- The formal arc sends a scalar `a : R` to the constant power series `a`. -/
@[simp] theorem arcHom_algebraMap (a : R) : arcHom W (algebraMap R _ a) = PowerSeries.C a := by
  simp [arcHom, algebraMap_chartYRing]

/-- The constant coefficient of `formalWInv W` is `1`. -/
theorem constantCoeff_formalWInv : PowerSeries.constantCoeff (formalWInv W) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (formalWInv_mul W)
  rwa [map_mul, constantCoeff_formalW, mul_one, map_one] at h

/-- Ring homomorphisms out of `ChartYRing W` which agree on scalars, `X` and `Z` are equal. -/
private theorem chartYRing_ringHom_ext {S : Type*} [Semiring S] {f g : ChartYRing W →+* S}
    (hR : ∀ a : R, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hZ : f (chartYZ W) = g (chartYZ W)) (hX : f (chartYX W) = g (chartYX W)) : f = g := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a => ?_) hZ) hX
  simpa only [RingHom.comp_apply, algebraMap_chartYRing] using hR a

/-- The formal arc followed by the constant coefficient is evaluation at the origin of the chart
`D₊(y)`. -/
theorem constantCoeff_arcHom : (PowerSeries.constantCoeff).comp (arcHom W) = chartYEvalZero W := by
  refine chartYRing_ringHom_ext W (fun a => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, arcHom_algebraMap, PowerSeries.constantCoeff_C,
      chartYEvalZero_algebraMap]
  · simp [arcHom_chartYZ, chartYEvalZero_chartYZ, formalZ]
  · simp [arcHom_chartYX, chartYEvalZero_chartYX]

/-! ### The punctured formal arc -/

/-- The power series `R⟦X⟧ → R((X))` into Laurent series. -/
abbrev ofPS : PowerSeries R →+* LaurentSeries R := HahnSeries.ofPowerSeries ℤ R

/-- The inverse `w / X³` of `Z = X³ / w` in `R((X))`. -/
def laurentInv : LaurentSeries R := HahnSeries.single (-3) 1 * ofPS (formalW W)

/-- The power series `Xⁿ` is the Laurent monomial of degree `n`. -/
theorem ofPS_X_pow (n : ℕ) : ofPS (PowerSeries.X ^ n : PowerSeries R) =
    HahnSeries.single (n : ℤ) 1 := by
  rw [ofPS, HahnSeries.ofPowerSeries_X_pow]

/-- `Xᵃ * Xᵇ = Xᵃ⁺ᵇ` in `R((X))`. -/
theorem single_mul_single_one (a b : ℤ) :
    (HahnSeries.single a 1 * HahnSeries.single b 1 : LaurentSeries R) =
      HahnSeries.single (a + b) 1 := by
  rw [HahnSeries.single_mul_single, mul_one]

/-- The image of `Z` in `R((X))` under the formal arc is inverse to `laurentInv W`. -/
theorem ofPS_arcHom_chartYZ_mul_laurentInv :
    ((ofPS).comp (arcHom W)) (chartYZ W) * laurentInv W = 1 := by
  rw [RingHom.comp_apply, arcHom_chartYZ, formalZ, laurentInv, map_mul, ofPS_X_pow]
  calc HahnSeries.single ((3 : ℕ) : ℤ) 1 * ofPS (formalWInv W) *
        (HahnSeries.single (-3) 1 * ofPS (formalW W))
      = (HahnSeries.single ((3 : ℕ) : ℤ) 1 * HahnSeries.single (-3) 1) *
          ofPS (formalWInv W * formalW W) := by rw [map_mul]; ring
    _ = 1 := by
      rw [single_mul_single_one, formalWInv_mul]
      simp

/-- **The punctured formal arc.** The homomorphism `R[x, y]/(f) → R((X))` with
`x ↦ X / Z = w / X²` and `y ↦ 1 / Z = w / X³`: the affine coordinate ring of the plane cubic,
expanded at the zero section in the formal parameter `X = x / y`. -/
def laurentHom : W.toAffine.CoordinateRing →+* LaurentSeries R :=
  chartZOfChartY W ((ofPS).comp (arcHom W)) (laurentInv W) (ofPS_arcHom_chartYZ_mul_laurentInv W)

/-- The punctured formal arc sends `x` to `w / X²`. -/
theorem laurentHom_x : laurentHom W (AdjoinRoot.of _ Polynomial.X) =
    HahnSeries.single (-2) 1 * ofPS (formalW W) := by
  rw [laurentHom, chartZOfChartY_x, RingHom.comp_apply, arcHom_chartYX, laurentInv,
    ← mul_assoc, ← pow_one (PowerSeries.X : PowerSeries R), ofPS_X_pow, single_mul_single_one]
  norm_num

/-- The punctured formal arc sends `y` to `w / X³`. -/
theorem laurentHom_y : laurentHom W (AdjoinRoot.root _) =
    HahnSeries.single (-3) 1 * ofPS (formalW W) := by
  rw [laurentHom, chartZOfChartY_y, laurentInv]

/-- The punctured formal arc sends a scalar `a : R` to the constant Laurent series `a`. -/
theorem laurentHom_algebraMap (a : R) :
    laurentHom W (algebraMap R _ a) = HahnSeries.C a := by
  rw [laurentHom, chartZOfChartY_algebraMap, RingHom.comp_apply, arcHom_algebraMap,
    HahnSeries.ofPowerSeries_C]

/-- The punctured formal arc is the formal arc, read through the chart `D₊(z)`. -/
theorem SpecMap_laurentHom_chartZ :
    Spec.map (CommRingCat.ofHom (laurentHom W)) ≫ chartZ W =
      Spec.map (CommRingCat.ofHom (ofPS (R := R))) ≫
        Spec.map (CommRingCat.ofHom (arcHom W)) ≫ chartY W := by
  rw [laurentHom, SpecMap_chartZOfChartY_chartZ, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-! ### Pole bounds -/

section PoleBound

/-- Shifting the pole order: `X⁻ⁿ G = X⁻⁽ⁿ⁺ᵈ⁾ (Xᵈ G)`. -/
private theorem single_mul_ofPS_eq_X_pow_mul (n d : ℕ) (G : PowerSeries R) :
    HahnSeries.single (-(n : ℤ)) 1 * ofPS G =
      HahnSeries.single (-((n + d : ℕ) : ℤ)) 1 * ofPS (PowerSeries.X ^ d * G) := by
  rw [map_mul, ofPS_X_pow, ← mul_assoc, single_mul_single_one]
  congr 3
  push_cast
  ring

/-- A Laurent series has a pole of order at most `n` at `X = 0`: it is `X⁻ⁿ` times a power
series. -/
def PoleBound (n : ℕ) (f : LaurentSeries R) : Prop :=
  ∃ G : PowerSeries R, f = HahnSeries.single (-(n : ℤ)) 1 * ofPS G

/-- Pole orders are subadditive under multiplication. -/
theorem PoleBound.mul {n m : ℕ} {f g : LaurentSeries R} (hf : PoleBound n f)
    (hg : PoleBound m g) : PoleBound (n + m) (f * g) := by
  obtain ⟨G, rfl⟩ := hf
  obtain ⟨H, rfl⟩ := hg
  refine ⟨G * H, ?_⟩
  calc _ = (HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-(m : ℤ)) 1) *
        (ofPS G * ofPS H) := by ring
    _ = _ := by
      rw [single_mul_single_one, map_mul]
      congr 3
      push_cast
      ring

/-- A pole of order at most `n` is a pole of order at most `m` for every `m ≥ n`. -/
theorem PoleBound.mono {n m : ℕ} {f : LaurentSeries R} (hf : PoleBound n f) (h : n ≤ m) :
    PoleBound m f := by
  obtain ⟨G, rfl⟩ := hf
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨PowerSeries.X ^ d * G, single_mul_ofPS_eq_X_pow_mul n d G⟩

/-- A sum of Laurent series with poles of order at most `n` has a pole of order at most `n`. -/
theorem PoleBound.add {n : ℕ} {f g : LaurentSeries R} (hf : PoleBound n f) (hg : PoleBound n g) :
    PoleBound n (f + g) := by
  obtain ⟨G, rfl⟩ := hf
  obtain ⟨H, rfl⟩ := hg
  exact ⟨G + H, by rw [map_add]; ring⟩

/-- A difference of Laurent series with poles of order at most `n` has a pole of order at most
`n`. -/
theorem PoleBound.sub {n : ℕ} {f g : LaurentSeries R} (hf : PoleBound n f) (hg : PoleBound n g) :
    PoleBound n (f - g) := by
  obtain ⟨G, rfl⟩ := hf
  obtain ⟨H, rfl⟩ := hg
  exact ⟨G - H, by rw [map_sub]; ring⟩

/-- The Laurent series `0` has a pole of order at most `n` for every `n`. -/
theorem PoleBound.zero (n : ℕ) : PoleBound n (0 : LaurentSeries R) := ⟨0, by simp⟩

/-- A constant multiple of a Laurent series with a pole of order at most `n` has a pole of order
at most `n`. -/
theorem PoleBound.C_mul {n : ℕ} {f : LaurentSeries R} (hf : PoleBound n f) (c : R) :
    PoleBound n (HahnSeries.C c * f) := by
  obtain ⟨G, rfl⟩ := hf
  refine ⟨PowerSeries.C c * G, ?_⟩
  rw [map_mul, ofPS, HahnSeries.ofPowerSeries_C]
  ring

/-- The Laurent series `1` has no pole. -/
theorem PoleBound.one : PoleBound 0 (1 : LaurentSeries R) := ⟨1, by simp⟩

/-- If `f` has a pole of order at most `k`, then `f ^ i` has a pole of order at most `k i`. -/
theorem PoleBound.pow {k : ℕ} {f : LaurentSeries R} (hf : PoleBound k f) (i : ℕ) :
    PoleBound (k * i) (f ^ i) := by
  induction i with
  | zero => simpa using PoleBound.one
  | succ i ih => rw [pow_succ, mul_add, mul_one]; exact ih.mul hf

/-- A polynomial of degree at most `d` in a Laurent series with a pole of order at most `k` has a
pole of order at most `k d`. -/
theorem PoleBound.eval₂ {k : ℕ} {f : LaurentSeries R} (hf : PoleBound k f) (p : Polynomial R)
    {d : ℕ} (hd : p.natDegree ≤ d) : PoleBound (k * d) (p.eval₂ HahnSeries.C f) := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  refine Finset.sum_induction _ (PoleBound (k * d)) (fun _ _ => PoleBound.add)
    (PoleBound.zero _) fun i hi => ?_
  exact ((hf.pow i).mono
    (Nat.mul_le_mul_left k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).C_mul _

/-- The factor `X⁻ⁿ` of a Laurent series is determined by it. -/
theorem eq_of_single_mul_ofPS_eq {n : ℤ} {G H : PowerSeries R}
    (h : HahnSeries.single n 1 * ofPS G = HahnSeries.single n 1 * ofPS H) : G = H := by
  have key (K : PowerSeries R) :
      HahnSeries.single (-n) 1 * (HahnSeries.single n 1 * ofPS K) = ofPS K := by
    rw [← mul_assoc, single_mul_single_one, neg_add_cancel, HahnSeries.single_zero_one, one_mul]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := R)
  rw [← key G, h, key H]

/-- **The leading coefficient of a pole of exact order.** If `X ^ (-(n + 1)) * G` has a pole of
order at most `n`, then the constant coefficient of `G` vanishes. -/
theorem constantCoeff_eq_zero_of_poleBound {n : ℕ} {G : PowerSeries R}
    (h : PoleBound n (HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 * ofPS G)) :
    PowerSeries.constantCoeff G = 0 := by
  obtain ⟨H, hH⟩ := h
  have : HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 * ofPS G =
      HahnSeries.single (-((n + 1 : ℕ) : ℤ)) 1 * ofPS (PowerSeries.X * H) := by
    simpa only [hH, pow_one] using single_mul_ofPS_eq_X_pow_mul n 1 H
  rw [eq_of_single_mul_ofPS_eq this, map_mul, PowerSeries.constantCoeff_X, zero_mul]

end PoleBound

/-! ### The weight filtration of the affine coordinate ring -/

/-- The affine coordinate `x` in `R[x, y]/(f)`. -/
abbrev affX : W.toAffine.CoordinateRing := AdjoinRoot.of _ Polynomial.X

/-- The affine coordinate `y` in `R[x, y]/(f)`. -/
abbrev affY : W.toAffine.CoordinateRing := AdjoinRoot.root _

/-- The monomial of weight `k` in `R[x, y]/(f)`, where `x` has weight `2` and `y` weight `3`:
`xⁱ` for `k = 2i` and `xⁱy` for `k = 2i + 3`; there is none of weight `1`, and `weightMono W 1`
is `0`. -/
def weightMono : ℕ → W.toAffine.CoordinateRing
  | 0 => 1
  | 1 => 0
  | 2 => affX W
  | 3 => affY W
  | k + 4 => affX W * weightMono (k + 2)

/-- The monomial of weight `2i` is `xⁱ`. -/
theorem weightMono_two_mul (i : ℕ) : weightMono W (2 * i) = affX W ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rcases i with - | i
    · simp [weightMono]
    · rw [show 2 * (i + 1 + 1) = 2 * i + 4 by ring, weightMono,
        show 2 * i + 2 = 2 * (i + 1) by ring, ih, pow_succ' (affX W) (i + 1)]

/-- The monomial of weight `2i + 3` is `xⁱ y`. -/
theorem weightMono_two_mul_add_three (i : ℕ) : weightMono W (2 * i + 3) = affX W ^ i * affY W := by
  induction i with
  | zero => simp [weightMono]
  | succ i ih =>
    rw [show 2 * (i + 1) + 3 = (2 * i + 1) + 4 by ring, weightMono,
      show 2 * i + 1 + 2 = 2 * i + 3 by ring, ih, pow_succ', mul_assoc]

/-- The span of the monomials of weight at most `k`. -/
def weightFiltration : ℕ → Submodule R W.toAffine.CoordinateRing
  | 0 => R ∙ 1
  | k + 1 => weightFiltration k ⊔ R ∙ weightMono W (k + 1)

/-- The weight filtration is increasing. -/
theorem weightFiltration_mono {k l : ℕ} (h : k ≤ l) :
    weightFiltration W k ≤ weightFiltration W l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans le_sup_left

/-- The monomial of weight `k` has weight at most `k`. -/
theorem weightMono_mem_weightFiltration (k : ℕ) : weightMono W k ∈ weightFiltration W k := by
  rcases k with - | k
  · exact Submodule.mem_span_singleton_self _
  · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- For `a : R`, the element `a xⁱ` has weight at most `2i`. -/
theorem algebraMap_mul_pow_affX_mem (a : R) (i : ℕ) :
    algebraMap R _ a * affX W ^ i ∈ weightFiltration W (2 * i) := by
  rw [← weightMono_two_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (weightMono_mem_weightFiltration W _)

/-- For `a : R`, the element `a xⁱ y` has weight at most `2i + 3`. -/
theorem algebraMap_mul_pow_affX_mul_affY_mem (a : R) (i : ℕ) :
    algebraMap R _ a * (affX W ^ i * affY W) ∈ weightFiltration W (2 * i + 3) := by
  rw [← weightMono_two_mul_add_three, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (weightMono_mem_weightFiltration W _)

/-- A polynomial `a ∈ R[x]` acting on `1` in `R[x, y]/(f)` is its evaluation at `x`. -/
theorem smul_one_eq_eval₂ (a : Polynomial R) :
    a • (1 : W.toAffine.CoordinateRing) = a.eval₂ (algebraMap R _) (affX W) := by
  rw [Algebra.smul_def, mul_one]
  conv_lhs => rw [← Polynomial.eval₂_C_X (p := a)]
  rw [Polynomial.hom_eval₂]
  congr 1

/-- A polynomial in `x` of degree at most `d` has weight at most `2d`. -/
theorem eval₂_mem_weightFiltration (a : Polynomial R) {d : ℕ} (hd : a.natDegree ≤ d) :
    a.eval₂ (algebraMap R _) (affX W) ∈ weightFiltration W (2 * d) := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  refine Submodule.sum_mem _ fun i hi => ?_
  exact weightFiltration_mono W (by have := Finset.mem_range.mp hi; omega)
    (algebraMap_mul_pow_affX_mem W _ i)

/-- A polynomial in `x` of degree at most `d`, times `y`, has weight at most `2d + 3`. -/
theorem eval₂_mul_affY_mem_weightFiltration (a : Polynomial R) {d : ℕ} (hd : a.natDegree ≤ d) :
    a.eval₂ (algebraMap R _) (affX W) * affY W ∈ weightFiltration W (2 * d + 3) := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd), Finset.sum_mul]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [mul_assoc]
  exact weightFiltration_mono W (by have := Finset.mem_range.mp hi; omega)
    (algebraMap_mul_pow_affX_mul_affY_mem W _ i)

/-- Every element of `R[x, y]/(f)` has finite weight. -/
theorem exists_mem_weightFiltration (p : W.toAffine.CoordinateRing) :
    ∃ k, p ∈ weightFiltration W k := by
  obtain ⟨a, b, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq p
  refine ⟨2 * (a.natDegree + b.natDegree) + 3, add_mem ?_ ?_⟩
  · rw [smul_one_eq_eval₂]
    exact weightFiltration_mono W (by omega) (eval₂_mem_weightFiltration W a le_rfl)
  · show b • affY W ∈ _
    rw [← smul_one_mul, smul_one_eq_eval₂]
    exact weightFiltration_mono W (by omega) (eval₂_mul_affY_mem_weightFiltration W b le_rfl)

/-! ### Pole orders of the monomials -/

/-- The punctured formal arc is `R`-linear. -/
theorem laurentHom_smul (c : R) (a : W.toAffine.CoordinateRing) :
    laurentHom W (c • a) = HahnSeries.C c * laurentHom W a := by
  rw [Algebra.smul_def, map_mul, laurentHom_algebraMap]

/-- The punctured formal arc sends `xⁱ` to `wⁱ / X²ⁱ`. -/
theorem laurentHom_affX_pow (i : ℕ) : laurentHom W (affX W ^ i) =
    HahnSeries.single (-((2 * i : ℕ) : ℤ)) 1 * ofPS (formalW W ^ i) := by
  rw [map_pow, laurentHom_x, mul_pow, HahnSeries.single_pow, one_pow, map_pow]
  congr 3
  push_cast
  ring

/-- The punctured formal arc sends `xⁱ y` to `wⁱ⁺¹ / X²ⁱ⁺³`. -/
theorem laurentHom_affX_pow_mul_affY (i : ℕ) : laurentHom W (affX W ^ i * affY W) =
    HahnSeries.single (-((2 * i + 3 : ℕ) : ℤ)) 1 * ofPS (formalW W ^ (i + 1)) := by
  rw [map_mul, laurentHom_affX_pow, laurentHom_y, pow_succ, map_mul]
  calc _ = (HahnSeries.single (-((2 * i : ℕ) : ℤ)) 1 * HahnSeries.single (-3) 1) *
        (ofPS (formalW W ^ i) * ofPS (formalW W)) := by ring
    _ = _ := by
      rw [single_mul_single_one]
      congr 3
      push_cast
      ring

/-- Every monomial of weight `k ≠ 1` has a pole of order exactly `k`, with leading
coefficient `1`. -/
theorem laurentHom_weightMono {k : ℕ} (hk : k ≠ 1) : ∃ G : PowerSeries R,
    laurentHom W (weightMono W k) = HahnSeries.single (-(k : ℤ)) 1 * ofPS G ∧
      PowerSeries.constantCoeff G = 1 := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 3 := by
    rcases Nat.even_or_odd k with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, Or.inl (by omega)⟩
    · exact ⟨i - 1, Or.inr (by omega)⟩
  · refine ⟨formalW W ^ i, ?_, by rw [map_pow, constantCoeff_formalW, one_pow]⟩
    rw [weightMono_two_mul, laurentHom_affX_pow]
  · refine ⟨formalW W ^ (i + 1), ?_, by rw [map_pow, constantCoeff_formalW, one_pow]⟩
    rw [weightMono_two_mul_add_three, laurentHom_affX_pow_mul_affY]

/-- The monomial of weight `k` has a pole of order at most `k` at the zero section. -/
theorem poleBound_laurentHom_weightMono (k : ℕ) : PoleBound k (laurentHom W (weightMono W k)) := by
  by_cases hk : k = 1
  · subst hk
    exact ⟨0, by simp [weightMono]⟩
  · obtain ⟨G, hG, -⟩ := laurentHom_weightMono W hk
    exact ⟨G, hG⟩

/-- An element of weight at most `k` has a pole of order at most `k` at the zero section. -/
theorem poleBound_of_mem_weightFiltration {k : ℕ} {a : W.toAffine.CoordinateRing}
    (ha : a ∈ weightFiltration W k) : PoleBound k (laurentHom W a) := by
  induction k generalizing a with
  | zero =>
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [laurentHom_smul, map_one, mul_one]
    exact ⟨PowerSeries.C c, by simp [ofPS, HahnSeries.ofPowerSeries_C]⟩
  | succ k ih =>
    obtain ⟨a', ha', b, hb, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, laurentHom_smul]
    exact ((ih ha').mono (Nat.le_succ k)).add ((poleBound_laurentHom_weightMono W _).C_mul c)

/-- **The leading term of the weight filtration.** An element of weight at most `k + 1` whose
pole order at the zero section is at most `k` has weight at most `k`, as soon as `k ≥ 1`. -/
theorem mem_weightFiltration_of_poleBound {k : ℕ} (hk : 1 ≤ k) {a : W.toAffine.CoordinateRing}
    (ha : a ∈ weightFiltration W (k + 1)) (hp : PoleBound k (laurentHom W a)) :
    a ∈ weightFiltration W k := by
  obtain ⟨a', ha', b, hb, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨G, hG, hG1⟩ := laurentHom_weightMono W (k := k + 1) (by omega)
  have h : PoleBound k (HahnSeries.single (-((k + 1 : ℕ) : ℤ)) 1 * ofPS (PowerSeries.C c * G)) := by
    have := hp.sub (poleBound_of_mem_weightFiltration W ha')
    rw [map_add, add_sub_cancel_left, laurentHom_smul, hG] at this
    convert this using 1
    rw [map_mul, ofPS, HahnSeries.ofPowerSeries_C]
    ring
  have hc := constantCoeff_eq_zero_of_poleBound h
  rw [map_mul, hG1, mul_one, PowerSeries.constantCoeff_C] at hc
  rw [hc, zero_smul, add_zero]
  exact ha'

/-- An element of finite weight with a pole of order at most `3` at the zero section has weight
at most `3`. -/
theorem mem_weightFiltration_three_of_poleBound {k : ℕ} {a : W.toAffine.CoordinateRing}
    (ha : a ∈ weightFiltration W k) (hp : PoleBound 3 (laurentHom W a)) :
    a ∈ weightFiltration W 3 := by
  induction k with
  | zero => exact weightFiltration_mono W (by omega) ha
  | succ k ih =>
    by_cases hk : k + 1 ≤ 3
    · exact weightFiltration_mono W hk ha
    · exact ih (mem_weightFiltration_of_poleBound W (by omega) ha (hp.mono (by omega)))

/-- An element of weight at most `3` is a combination `r + s x + t y`. -/
theorem exists_eq_of_mem_weightFiltration_three {a : W.toAffine.CoordinateRing}
    (ha : a ∈ weightFiltration W 3) : ∃ r s t : R,
      a = algebraMap R _ r + algebraMap R _ s * affX W + algebraMap R _ t * affY W := by
  obtain ⟨a₂, ha₂, b₃, hb₃, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨a₁, ha₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp ha₂
  obtain ⟨a₀, ha₀, b₁, hb₁, rfl⟩ := Submodule.mem_sup.mp ha₁
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha₀
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb₁
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hb₂
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb₃
  refine ⟨r, s, t, ?_⟩
  simp only [weightMono, add_zero, Algebra.smul_def, mul_one, mul_zero]

/-- **The pole-order bound.** An element of `R[x, y]/(f)` with a pole of order at most `3` at the
zero section is a combination `r + s x + t y`. -/
theorem exists_eq_of_poleBound_three {a : W.toAffine.CoordinateRing}
    (hp : PoleBound 3 (laurentHom W a)) : ∃ r s t : R,
      a = algebraMap R _ r + algebraMap R _ s * affX W + algebraMap R _ t * affY W := by
  obtain ⟨k, hk⟩ := exists_mem_weightFiltration W a
  exact exists_eq_of_mem_weightFiltration_three W (mem_weightFiltration_three_of_poleBound W hk hp)

/-- The punctured formal arc sends `r + s x + t y` to `X⁻³ (r X³ + s X w + t w)`. -/
theorem laurentHom_add_mul_add_mul (r s t : R) :
    laurentHom W (algebraMap R _ r + algebraMap R _ s * affX W + algebraMap R _ t * affY W) =
      HahnSeries.single (-3) 1 * ofPS (PowerSeries.C r * PowerSeries.X ^ 3 +
        PowerSeries.C s * PowerSeries.X * formalW W + PowerSeries.C t * formalW W) := by
  rw [map_add, map_add, map_mul, map_mul, laurentHom_algebraMap, laurentHom_algebraMap,
    laurentHom_algebraMap, laurentHom_x, laurentHom_y, map_add, map_add, map_mul, map_mul,
    map_mul, map_mul, ofPS_X_pow, ← pow_one (PowerSeries.X : PowerSeries R), ofPS_X_pow]
  simp only [ofPS, HahnSeries.ofPowerSeries_C]
  calc _ = HahnSeries.C r * 1 + HahnSeries.C s * HahnSeries.single (-2) 1 *
        HahnSeries.ofPowerSeries ℤ R (formalW W) +
      HahnSeries.C t * HahnSeries.single (-3) 1 * HahnSeries.ofPowerSeries ℤ R (formalW W) := by
        ring
    _ = _ := by
      rw [← HahnSeries.single_zero_one, show (0 : ℤ) = -3 + ((3 : ℕ) : ℤ) by norm_num,
        show (-2 : ℤ) = -3 + ((1 : ℕ) : ℤ) by norm_num, ← single_mul_single_one,
        ← single_mul_single_one]
      ring

/-- An element with expansion `X⁻³ G` is `r + s x + t y`, where `G = r X³ + s X w + t w`. -/
private theorem exists_eq_and_eq_of_laurentHom_eq_three {a : W.toAffine.CoordinateRing}
    {G : PowerSeries R} (h : laurentHom W a = HahnSeries.single (-((3 : ℕ) : ℤ)) 1 * ofPS G) :
    ∃ r s t : R, a = algebraMap R _ r + algebraMap R _ s * affX W + algebraMap R _ t * affY W ∧
      G = PowerSeries.C r * PowerSeries.X ^ 3 + PowerSeries.C s * PowerSeries.X * formalW W +
        PowerSeries.C t * formalW W := by
  obtain ⟨r, s, t, rfl⟩ := exists_eq_of_poleBound_three W ⟨G, h⟩
  rw [laurentHom_add_mul_add_mul] at h
  have h' : _ = HahnSeries.single (-3) 1 * ofPS G := h.trans (by norm_num)
  exact ⟨r, s, t, rfl, (eq_of_single_mul_ofPS_eq h').symm⟩

/-- **Elements with a pole of order at most `3`.** If the expansion of `a` at the zero section is
`X⁻³ G`, then `a = r + s x + t y` with `t` the constant coefficient of `G`. -/
theorem exists_eq_of_laurentHom_eq_three {a : W.toAffine.CoordinateRing} {G : PowerSeries R}
    (h : laurentHom W a = HahnSeries.single (-((3 : ℕ) : ℤ)) 1 * ofPS G) : ∃ r s : R,
      a = algebraMap R _ r + algebraMap R _ s * affX W +
        algebraMap R _ (PowerSeries.constantCoeff G) * affY W := by
  obtain ⟨r, s, t, rfl, rfl⟩ := exists_eq_and_eq_of_laurentHom_eq_three W h
  exact ⟨r, s, by simp [constantCoeff_formalW]⟩

/-- **Elements with a pole of order at most `2`.** If the expansion of `a` at the zero section is
`X⁻² G`, then `a = r + s x` with `s` the constant coefficient of `G`. -/
theorem exists_eq_of_laurentHom_eq_two {a : W.toAffine.CoordinateRing} {G : PowerSeries R}
    (h : laurentHom W a = HahnSeries.single (-((2 : ℕ) : ℤ)) 1 * ofPS G) : ∃ r : R,
      a = algebraMap R _ r + algebraMap R _ (PowerSeries.constantCoeff G) * affX W := by
  have h3 : laurentHom W a = HahnSeries.single (-((3 : ℕ) : ℤ)) 1 *
      ofPS (PowerSeries.X * G) := by
    simpa only [pow_one] using h.trans (single_mul_ofPS_eq_X_pow_mul 2 1 G)
  obtain ⟨r, s, t, rfl, hG⟩ := exists_eq_and_eq_of_laurentHom_eq_three W h3
  have ht : t = 0 := by
    simpa [constantCoeff_formalW] using (congrArg PowerSeries.constantCoeff hG).symm
  subst ht
  have hG' := PowerSeries.X_mul_cancel (hG.trans (by simp; ring) :
    PowerSeries.X * G = PowerSeries.X * (PowerSeries.C r * PowerSeries.X ^ 2 +
      PowerSeries.C s * formalW W))
  exact ⟨r, by simp [hG', constantCoeff_formalW]⟩

/-! ### First-order thickenings of the zero section -/

/-- The first-order thickening of the zero section with tangent `p`: the homomorphism from the
coordinate ring of the chart `D₊(y)` to the dual numbers `R[ε]` with `X ↦ p ε` and `Z ↦ 0`. -/
def tangentHom (p : R) : ChartYRing W →+* DualNumber R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap R (DualNumber R)) 0)
    (TrivSqZeroExt.inr p) <| by
    simp only [chartYPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom]
    simp [pow_succ]

/-- The thickening with tangent `p` sends `X` to `p ε`. -/
@[simp] theorem tangentHom_chartYX (p : R) : tangentHom W p (chartYX W) = TrivSqZeroExt.inr p := by
  simp [tangentHom, chartYX]

/-- The thickening with tangent `p` sends `Z` to `0`. -/
@[simp] theorem tangentHom_chartYZ (p : R) : tangentHom W p (chartYZ W) = 0 := by
  simp [tangentHom, chartYZ]

/-- The thickening with tangent `p` sends a scalar `a : R` to `a`. -/
@[simp] theorem tangentHom_algebraMap (p a : R) :
    tangentHom W p (algebraMap R _ a) = algebraMap R _ a := by
  simp [tangentHom, algebraMap_chartYRing]

/-- **The first-order thickenings of the zero section.** A homomorphism from the coordinate ring
of the chart `D₊(y)` to the dual numbers which is `R`-linear and restricts to evaluation at the
origin is `tangentHom W p` for `p` the `ε`-coefficient of the image of `X`. -/
theorem eq_tangentHom (θ : ChartYRing W →+* DualNumber R)
    (hR : ∀ a, θ (algebraMap R _ a) = algebraMap R _ a)
    (h0 : ∀ b, (θ b).fst = chartYEvalZero W b) :
    θ = tangentHom W (θ (chartYX W)).snd := by
  have hX : θ (chartYX W) = TrivSqZeroExt.inr (θ (chartYX W)).snd :=
    TrivSqZeroExt.ext (by rw [h0, chartYEvalZero_chartYX, TrivSqZeroExt.fst_inr]) rfl
  have hZ' : θ (chartYZ W) = TrivSqZeroExt.inr (θ (chartYZ W)).snd :=
    TrivSqZeroExt.ext (by rw [h0, chartYEvalZero_chartYZ, TrivSqZeroExt.fst_inr]) rfl
  have hZ : θ (chartYZ W) = 0 := by
    have h := congrArg θ (chartY_equation W)
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, hR] at h
    rw [hX, hZ'] at h
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, TrivSqZeroExt.inr_mul_inr, mul_zero,
      zero_mul, add_zero, sub_zero] at h
    rw [hZ']
    exact h
  refine chartYRing_ringHom_ext W (fun a => ?_) ?_ ?_
  · simp only [hR, tangentHom_algebraMap]
  · rw [hZ, tangentHom_chartYZ]
  · rw [tangentHom_chartYX, hX, TrivSqZeroExt.snd_inr]

/-- The tangent of a first-order thickening is determined by the thickening. -/
theorem tangentHom_injective : Function.Injective (tangentHom W) := fun p q h => by
  have := congrArg (fun θ : ChartYRing W →+* DualNumber R => (θ (chartYX W)).snd) h
  simpa using this

/-- The rescaling `ε ↦ p ε` of the dual numbers. -/
def rescaleDual (p : R) : DualNumber R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (p • LinearMap.id)

/-- The thickening with tangent `p`, reduced modulo `ε`, is evaluation at the origin of the chart
`D₊(y)`. -/
theorem fst_tangentHom (p : R) (b : ChartYRing W) :
    (tangentHom W p b).fst = chartYEvalZero W b := by
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (tangentHom W p) = chartYEvalZero W := by
    refine chartYRing_ringHom_ext W (fun a => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, tangentHom_algebraMap, chartYEvalZero_algebraMap]
      simp
    · simp [chartYEvalZero_chartYZ]
    · simp [chartYEvalZero_chartYX]
  exact congr($this b)

/-- Rescaling `ε ↦ p ε` takes the thickening with tangent `q` to the one with tangent `p q`. -/
theorem rescaleDual_comp_tangentHom (p q : R) :
    (rescaleDual p).toRingHom.comp (tangentHom W q) = tangentHom W (p * q) := by
  rw [eq_tangentHom W ((rescaleDual p).toRingHom.comp (tangentHom W q))]
  · simp [rescaleDual, TrivSqZeroExt.snd_map, mul_comm]
  · intro a
    simp
  · intro b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rescaleDual,
      TrivSqZeroExt.fst_map, fst_tangentHom]

/-- The truncation `R⟦X⟧ → R[ε]`, `X ↦ ε`. -/
def powerSeriesToDual : PowerSeries R →+* DualNumber R where
  toFun f :=
    TrivSqZeroExt.inl (PowerSeries.constantCoeff f) + TrivSqZeroExt.inr (PowerSeries.coeff 1 f)
  map_one' := by simp [PowerSeries.coeff_one]
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  map_zero' := by simp
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The truncation of `f` to first order has the constant coefficient of `f` as its real part. -/
@[simp] theorem fst_powerSeriesToDual (f : PowerSeries R) :
    (powerSeriesToDual f).fst = PowerSeries.constantCoeff f := by
  simp [powerSeriesToDual]

/-- The truncation of `f` to first order has the coefficient of `X` in `f` as its
`ε`-coefficient. -/
@[simp] theorem snd_powerSeriesToDual (f : PowerSeries R) :
    (powerSeriesToDual f).snd = PowerSeries.coeff 1 f := by
  simp [powerSeriesToDual]

/-- The formal arc, truncated to first order, is the thickening with tangent `1`. -/
theorem powerSeriesToDual_comp_arcHom : powerSeriesToDual.comp (arcHom W) = tangentHom W 1 := by
  rw [eq_tangentHom W (powerSeriesToDual.comp (arcHom W))]
  · simp
  · intro a
    rw [RingHom.comp_apply, arcHom_algebraMap]
    exact TrivSqZeroExt.ext (by simp [TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [TrivSqZeroExt.algebraMap_eq_inl])
  · intro b
    rw [RingHom.comp_apply, fst_powerSeriesToDual, ← RingHom.comp_apply, constantCoeff_arcHom]

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass
