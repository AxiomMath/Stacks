module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatCurve
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.TorusRing

/-!
# The torus chart of the cubic surface and of the Fermat cubic

On the cubic surface `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` of Stacks 0D5E, the open
subset `D₊(T₀ T₁ T₂)` where no homogeneous coordinate vanishes is the two-dimensional torus
`Spec k[x, y][1 / (x y)]`, with `x = T₁ / T₀` and `y = T₂ / T₀`: dividing the equation by `T₀ ^ 3`
gives `1 + x ^ 3 + y ^ 3 - t x y = 0`, and since `x y` is a unit there this determines
`t = (1 + x ^ 3 + y ^ 3) / (x y)`. On the central fibre, the Fermat cubic
`T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 = 0`, the same open subset is the closed curve
`1 + x ^ 3 + y ^ 3 = 0` of the torus.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.surfaceTorusOpen`: the open `D₊(T₀ T₁ T₂)` of the
  cubic surface.
* `Stacks.Examples.CurveFamilyNotScheme.fermatTorusOpen`: the open `D₊(T₀ T₁ T₂)` of the
  Fermat cubic curve.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.exists_iso_surfaceTorusOpen`: `D₊(T₀ T₁ T₂)` of the
  cubic surface is the torus `Spec k[x, y][1 / (x y)]`, over the affine line through
  `t ↦ (1 + x ^ 3 + y ^ 3) / (x y)`.
* `Stacks.Examples.CurveFamilyNotScheme.nonempty_iso_fermatTorusOpen`: `D₊(T₀ T₁ T₂)` of the
  Fermat cubic is `Spec k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3)`.

## Implementation notes

Both computations are instances of one statement about a graded quotient
`R[T₀, T₁, T₂] ⧸ I`. The degree-zero localization at `T₀ T₁ T₂` contains the fractions
`x = T₁² T₂ / (T₀ T₁ T₂)`, `y = T₁ T₂² / (T₀ T₁ T₂)` and `w = T₀³ / (T₀ T₁ T₂)`, with `w x y = 1`,
and a homogeneous `P` of degree `3 n` gives `P / (T₀ T₁ T₂) ^ n = P(1, x, y) wⁿ`
(`Stacks.Examples.CurveFamilyNotScheme.eval₂_torusChart`). Hence a ring homomorphism out of the
degree-zero localization which has a section sending the coordinates to `x`, `y` and the inverse
of `x y` to `w` is bijective (`Stacks.Examples.CurveFamilyNotScheme.torusChartLift_bijective`).

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
  Stacks.AlgebraicGeometry.ProjPolyChart Stacks.RingTheory.HomogeneousQuotient

universe u v

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The degree-zero localization at `T₀ T₁ T₂` of a graded quotient -/

section General

variable {R : Type u} [CommRing R] (I : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))

/-- The class of the monomial `T₀ T₁ T₂` in the graded quotient `R[T₀, T₁, T₂] ⧸ I`. -/
abbrev torusMonomial : MvPolynomial (Fin 3) R ⧸ I.toIdeal :=
  Ideal.Quotient.mk I.toIdeal (X 0 * X 1 * X 2)

/-- The class of a homogeneous polynomial of degree `n` has degree `n` in the quotient. -/
theorem mk_mem_quotientGrading_of_isHomogeneous {P : MvPolynomial (Fin 3) R} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    Ideal.Quotient.mk I.toIdeal P ∈ quotientGrading (homogeneousSubmodule (Fin 3) R) I n :=
  quotientGrading_mk_mem _ I ((mem_homogeneousSubmodule _ _).2 hP)

/-- The monomial `T₀ T₁ T₂` has degree three. -/
theorem torusMonomial_mem :
    torusMonomial I ∈ quotientGrading (homogeneousSubmodule (Fin 3) R) I 3 :=
  mk_mem_quotientGrading_of_isHomogeneous I
    (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _))

/-- The degree-zero localization of `R[T₀, T₁, T₂] ⧸ I` at `T₀ T₁ T₂`. -/
abbrev TorusChartAway : Type u :=
  Away (quotientGrading (homogeneousSubmodule (Fin 3) R) I) (torusMonomial I)

/-- A monomial of degree three, as an element of degree `1 • 3`. -/
theorem mk_mem_one_smul_three {P : MvPolynomial (Fin 3) R} (hP : P.IsHomogeneous 3) :
    Ideal.Quotient.mk I.toIdeal P ∈ quotientGrading (homogeneousSubmodule (Fin 3) R) I (1 • 3) :=
  mk_mem_quotientGrading_of_isHomogeneous I (by rwa [smul_eq_mul, one_mul])

/-- The affine coordinate `x = T₁ / T₀`, written `T₁² T₂ / (T₀ T₁ T₂)`. -/
def torusChartX : TorusChartAway I :=
  Away.mk _ (torusMonomial_mem I) 1 (Ideal.Quotient.mk I.toIdeal (X 1 ^ 2 * X 2))
    (mk_mem_one_smul_three I ((isHomogeneous_X_pow _ 2).mul (isHomogeneous_X _ _)))

/-- The affine coordinate `y = T₂ / T₀`, written `T₁ T₂² / (T₀ T₁ T₂)`. -/
def torusChartY : TorusChartAway I :=
  Away.mk _ (torusMonomial_mem I) 1 (Ideal.Quotient.mk I.toIdeal (X 1 * X 2 ^ 2))
    (mk_mem_one_smul_three I ((isHomogeneous_X _ _).mul (isHomogeneous_X_pow _ 2)))

/-- The inverse `T₀² / (T₁ T₂)` of `x y`, written `T₀³ / (T₀ T₁ T₂)`. -/
def torusChartW : TorusChartAway I :=
  Away.mk _ (torusMonomial_mem I) 1 (Ideal.Quotient.mk I.toIdeal (X 0 ^ 3))
    (mk_mem_one_smul_three I (isHomogeneous_X_pow _ 3))

/-- The constants `R → (R[T₀, T₁, T₂] ⧸ I)₀ → (R[T₀, T₁, T₂] ⧸ I)_{(T₀T₁T₂)}`. -/
def torusChartConst : R →+* TorusChartAway I :=
  (fromZeroRingHom _ _).comp ((GradedRing.projZeroRingHom'
    (quotientGrading (homogeneousSubmodule (Fin 3) R) I)).comp
      (algebraMap R (MvPolynomial (Fin 3) R ⧸ I.toIdeal)))

/-- In the localization at `T₀ T₁ T₂`, the fraction `a / (T₀ T₁ T₂) ^ n` is `a` times the `n`-th
power of the inverse of `T₀ T₁ T₂`. -/
theorem localization_mk_torusMonomial (a : MvPolynomial (Fin 3) R ⧸ I.toIdeal) (n : ℕ)
    (h : torusMonomial I ^ n ∈ Submonoid.powers (torusMonomial I)) :
    (Localization.mk a ⟨torusMonomial I ^ n, h⟩ : Localization.Away (torusMonomial I)) =
      algebraMap _ _ a * IsLocalization.Away.invSelf (torusMonomial I) ^ n := by
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * _ * algebraMap _ _ (torusMonomial I ^ n)
  rw [map_pow, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The constant `r` of the chart is the class of `C r`. -/
theorem val_torusChartConst (r : R) : (torusChartConst I r).val =
    algebraMap _ (Localization.Away (torusMonomial I)) (Ideal.Quotient.mk I.toIdeal (C r)) := by
  have h0 : Ideal.Quotient.mk I.toIdeal (C r) ∈
      quotientGrading (homogeneousSubmodule (Fin 3) R) I 0 :=
    mk_mem_quotientGrading_of_isHomogeneous I (isHomogeneous_C _ r)
  have h1 : ((GradedRing.projZeroRingHom' (quotientGrading (homogeneousSubmodule (Fin 3) R) I))
      (algebraMap R _ r) : MvPolynomial (Fin 3) R ⧸ I.toIdeal) =
        Ideal.Quotient.mk I.toIdeal (C r) := by
    rw [GradedRing.coe_projZeroRingHom'_apply, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq]
    exact DirectSum.decompose_of_mem_same _ h0
  rw [← h1, ← Localization.mk_one_eq_algebraMap]
  rfl

/-- The constant `r` of the chart is the fraction `C r / (T₀ T₁ T₂) ^ 0`. -/
theorem torusChartConst_eq (r : R) :
    torusChartConst I r = Away.mk _ (torusMonomial_mem I) 0 (Ideal.Quotient.mk I.toIdeal (C r))
      (mk_mem_quotientGrading_of_isHomogeneous I
        (by rw [zero_smul]; exact isHomogeneous_C _ r)) := by
  apply HomogeneousLocalization.val_injective
  rw [val_torusChartConst, Away.val_mk, localization_mk_torusMonomial, pow_zero, mul_one]

/-- The image of the class of the variable `Tⱼ` in the localization. -/
abbrev torusVar (j : Fin 3) : Localization.Away (torusMonomial I) :=
  algebraMap _ _ (Ideal.Quotient.mk I.toIdeal (X j))

/-- In the localization, `T₀ T₁ T₂` times its inverse is one. -/
theorem torusVar_mul_invSelf :
    torusVar I 0 * torusVar I 1 * torusVar I 2 * IsLocalization.Away.invSelf (torusMonomial I) =
      1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Localization.Away (torusMonomial I))
    (torusMonomial I)
  simpa only [torusMonomial, map_mul] using h

/-- The value of `x` in the localization. -/
theorem val_torusChartX : (torusChartX I).val =
    torusVar I 1 ^ 2 * torusVar I 2 * IsLocalization.Away.invSelf (torusMonomial I) := by
  rw [torusChartX, Away.val_mk, localization_mk_torusMonomial, pow_one, map_mul, map_pow,
    map_mul, map_pow]

/-- The value of `y` in the localization. -/
theorem val_torusChartY : (torusChartY I).val =
    torusVar I 1 * torusVar I 2 ^ 2 * IsLocalization.Away.invSelf (torusMonomial I) := by
  rw [torusChartY, Away.val_mk, localization_mk_torusMonomial, pow_one, map_mul, map_pow,
    map_mul, map_pow]

/-- The value of `w` in the localization. -/
theorem val_torusChartW : (torusChartW I).val =
    torusVar I 0 ^ 3 * IsLocalization.Away.invSelf (torusMonomial I) := by
  rw [torusChartW, Away.val_mk, localization_mk_torusMonomial, pow_one, map_pow, map_pow]

/-- `w` is the inverse of `x y`. -/
theorem torusChartW_mul_X_mul_Y : torusChartW I * torusChartX I * torusChartY I = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_mul, val_torusChartW, val_torusChartX, val_torusChartY, val_one]
  calc _ = (torusVar I 0 * torusVar I 1 * torusVar I 2 *
        IsLocalization.Away.invSelf (torusMonomial I)) ^ 3 := by ring
    _ = 1 := by rw [torusVar_mul_invSelf, one_pow]

/-- **Dehomogenization at `T₀ T₁ T₂`.** A homogeneous polynomial `P` of degree `3 n`, evaluated at
`(1, x, y)` and multiplied by `wⁿ`, is the fraction `P / (T₀ T₁ T₂) ^ n`. -/
theorem eval₂_torusChart {P : MvPolynomial (Fin 3) R} {n : ℕ} (hP : P.IsHomogeneous (n • 3))
    (hp : Ideal.Quotient.mk I.toIdeal P ∈
      quotientGrading (homogeneousSubmodule (Fin 3) R) I (n • 3)) :
    eval₂ (torusChartConst I) ![1, torusChartX I, torusChartY I] P * torusChartW I ^ n =
      Away.mk _ (torusMonomial_mem I) n (Ideal.Quotient.mk I.toIdeal P) hp := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, localization_mk_torusMonomial, ← HomogeneousLocalization.algebraMap_apply,
    map_mul, map_pow, MvPolynomial.eval₂_comp_left]
  obtain ⟨u, hu_def⟩ : ∃ u : Localization.Away (torusMonomial I),
      u = torusVar I 1 * torusVar I 2 * IsLocalization.Away.invSelf (torusMonomial I) := ⟨_, rfl⟩
  have hu : u * torusVar I 0 = 1 := by
    rw [← torusVar_mul_invSelf I, hu_def]
    ring
  have hv : (⇑(algebraMap (TorusChartAway I) (Localization.Away (torusMonomial I))) ∘
      ![1, torusChartX I, torusChartY I]) = fun j => u * torusVar I j := by
    funext j
    fin_cases j
    · simp [hu]
    · simp only [Function.comp_apply, HomogeneousLocalization.algebraMap_apply]
      simp [val_torusChartX, hu_def]
      ring
    · simp only [Function.comp_apply, HomogeneousLocalization.algebraMap_apply]
      simp [val_torusChartY, hu_def]
      ring
  have hc : (algebraMap (TorusChartAway I) (Localization.Away (torusMonomial I))).comp
      (torusChartConst I) = ((algebraMap _ (Localization.Away (torusMonomial I))).comp
        (Ideal.Quotient.mk I.toIdeal)).comp C :=
    RingHom.ext fun r => val_torusChartConst I r
  have hmk : algebraMap _ (Localization.Away (torusMonomial I)) (Ideal.Quotient.mk I.toIdeal P) =
      eval₂ (((algebraMap _ (Localization.Away (torusMonomial I))).comp
        (Ideal.Quotient.mk I.toIdeal)).comp C) (torusVar I) P := by
    change ((algebraMap _ (Localization.Away (torusMonomial I))).comp
      (Ideal.Quotient.mk I.toIdeal)) P = _
    conv_lhs => rw [← MvPolynomial.eval₂_eta P]
    rw [MvPolynomial.eval₂_comp_left]
    rfl
  rw [hv, hP.eval₂_const_mul, hc, ← hmk, HomogeneousLocalization.algebraMap_apply,
    val_torusChartW]
  calc _ = algebraMap _ (Localization.Away (torusMonomial I)) (Ideal.Quotient.mk I.toIdeal P) *
        ((u * torusVar I 0) ^ 3 * IsLocalization.Away.invSelf (torusMonomial I)) ^ n := by
        rw [smul_eq_mul]
        ring
    _ = _ := by rw [hu, one_pow, one_mul]

variable {B : Type v} [CommRing B] (κ : MvPolynomial (Fin 3) R ⧸ I.toIdeal →+* B) (v : B)
  (hv : κ (torusMonomial I) * v = 1)

/-- The ring homomorphism out of the chart induced by a ring homomorphism `κ` under which
`T₀ T₁ T₂` has the inverse `v`: the fraction `p / (T₀ T₁ T₂) ^ n` goes to `κ p * vⁿ`. -/
def torusChartLift : TorusChartAway I →+* B :=
  (Localization.awayLift κ (torusMonomial I) (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)).comp
    (algebraMap _ (Localization.Away (torusMonomial I)))

/-- `torusChartLift` sends the fraction `p / (T₀ T₁ T₂) ^ n` to `κ p * vⁿ`. -/
theorem torusChartLift_mk (n : ℕ) (p : MvPolynomial (Fin 3) R ⧸ I.toIdeal)
    (hp : p ∈ quotientGrading (homogeneousSubmodule (Fin 3) R) I (n • 3)) :
    torusChartLift I κ v hv (Away.mk _ (torusMonomial_mem I) n p hp) = κ p * v ^ n := by
  rw [torusChartLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  exact Localization.awayLift_mk κ _ p v hv n

/-- `torusChartLift` sends the constant `r` to `κ (C r)`. -/
theorem torusChartLift_const (r : R) :
    torusChartLift I κ v hv (torusChartConst I r) = κ (Ideal.Quotient.mk I.toIdeal (C r)) := by
  rw [torusChartConst_eq, torusChartLift_mk, pow_zero, mul_one]

/-- **The chart identification.** Let `κ` be a ring homomorphism out of `R[T₀, T₁, T₂] ⧸ I` with
`κ T₀ = 1` under which `T₀ T₁ T₂` has the inverse `v`, and `σ` a ring homomorphism into the chart
sending `κ T₁`, `κ T₂` and `v` to `x`, `y` and `w`, and constants to constants. If `σ` is a
section of `torusChartLift`, then `torusChartLift` is bijective. -/
theorem torusChartLift_bijective (h0 : κ (Ideal.Quotient.mk I.toIdeal (X 0)) = 1)
    (σ : B →+* TorusChartAway I)
    (h1 : σ (κ (Ideal.Quotient.mk I.toIdeal (X 1))) = torusChartX I)
    (h2 : σ (κ (Ideal.Quotient.mk I.toIdeal (X 2))) = torusChartY I)
    (hC : ∀ r, σ (κ (Ideal.Quotient.mk I.toIdeal (C r))) = torusChartConst I r)
    (hσv : σ v = torusChartW I) (hsec : ∀ b, torusChartLift I κ v hv (σ b) = b) :
    Function.Bijective (torusChartLift I κ v hv) := by
  refine ⟨Function.LeftInverse.injective (g := σ) fun z => ?_, fun b => ⟨σ b, hsec b⟩⟩
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (torusMonomial_mem I) z
  obtain ⟨P, hP, rfl⟩ := (mem_quotientGrading_iff _ I).mp hp
  rw [torusChartLift_mk, map_mul, map_pow, hσv]
  have hg : (σ.comp κ).comp (Ideal.Quotient.mk I.toIdeal) =
      eval₂Hom (torusChartConst I) ![1, torusChartX I, torusChartY I] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hC]
    · intro j
      fin_cases j <;> simp [h0, h1, h2]
  have h := RingHom.congr_fun hg P
  simp only [RingHom.comp_apply, coe_eval₂Hom] at h
  rw [h]
  exact eval₂_torusChart I ((mem_homogeneousSubmodule _ _).1 hP) hp

end General

/-! ### Ring homomorphisms out of the torus ring -/

section TorusSection

variable {k : Type u} [Field k] {T : Type v} [CommRing T] (c : k →+* T) (x y w : T)
  (hw : w * x * y = 1)

/-- The ring homomorphism `k[x, y][1 / (x y)] → T` sending the coordinates to `x` and `y`, for
`x y` a unit of `T` with inverse `w`. -/
def torusSection : torusRing k →+* T :=
  IsLocalization.Away.lift (X 0 * X 1 : MvPolynomial (Fin 2) k)
    (g := eval₂Hom c ![x, y]) (isUnit_iff_exists_inv'.mpr ⟨w, by simpa [mul_assoc] using hw⟩)

/-- `torusSection` extends evaluation at `(x, y)`. -/
theorem torusSection_algebraMap (p : MvPolynomial (Fin 2) k) :
    torusSection c x y w hw (algebraMap _ _ p) = eval₂Hom c ![x, y] p :=
  IsLocalization.Away.lift_eq _ _ p

/-- `torusSection` sends the inverse of `x y` to `w`. -/
theorem torusSection_invSelf :
    torusSection c x y w hw (IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k)) =
      w := by
  have h := congrArg (torusSection c x y w hw)
    (IsLocalization.Away.mul_invSelf (S := torusRing k) (X 0 * X 1 : MvPolynomial (Fin 2) k))
  rw [map_mul, torusSection_algebraMap, map_one] at h
  simp only [coe_eval₂Hom, eval₂_mul, eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  calc _ = (w * x * y) * torusSection c x y w hw
        (IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k)) := by
        rw [hw, one_mul]
    _ = w := by rw [mul_assoc, mul_assoc, ← mul_assoc x, h, mul_one]

end TorusSection

/-- Two ring homomorphisms out of the torus ring agreeing on constants and coordinates agree. -/
theorem torusRing_ringHom_ext {k : Type u} [Field k] {T : Type v} [CommRing T]
    {g g' : torusRing k →+* T}
    (hC : ∀ a, g (algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (C a)) =
      g' (algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (C a)))
    (hX : ∀ i, g (algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X i)) =
      g' (algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X i))) : g = g' :=
  IsLocalization.ringHom_ext (Submonoid.powers (X 0 * X 1 : MvPolynomial (Fin 2) k))
    (MvPolynomial.ringHom_ext hC hX)

variable (k : Type u) [Field k]

/-- In the torus ring, `x y` times its inverse is one. -/
theorem torus_mul_invSelf :
    algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0) *
      algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1) *
      IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k) = 1 := by
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf _

/-! ### The torus chart of the cubic surface -/

/-- The torus chart `D₊(T₀ T₁ T₂)` of the cubic surface. -/
def surfaceTorusOpen : (cubicSurface k).Opens :=
  Proj.basicOpen (quotientGrading (polyGrading (Polynomial k) 2) (cubicIdeal k))
    (Ideal.Quotient.mk (cubicIdeal k).toIdeal (X 0 * X 1 * X 2))

/-- The torus point `(1 : x : y)` with `t = (1 + x ^ 3 + y ^ 3) / (x y)`, as a homomorphism out of
`k[t][T₀, T₁, T₂]`. -/
def surfaceTorusEval : MvPolynomial (Fin 3) (Polynomial k) →+* torusRing k :=
  eval₂Hom (Polynomial.eval₂RingHom (algebraMap k (torusRing k)) (torusParameter k))
    ![1, algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0),
      algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1)]

/-- The cubic vanishes at the torus point. -/
theorem surfaceTorusEval_cubicEquation : surfaceTorusEval k (cubicEquation k) = 0 := by
  have h := torus_mul_invSelf k
  simp only [surfaceTorusEval, cubicEquation, coe_eval₂Hom, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, torusParameter, torusFermat, map_add, map_one, map_pow]
  linear_combination -(1 + algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0) ^ 3 +
    algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1) ^ 3) * h

/-- The torus point as a homomorphism out of the homogeneous coordinate ring of the surface. -/
def surfaceTorusκ : MvPolynomial (Fin 3) (Polynomial k) ⧸ (cubicIdeal k).toIdeal →+* torusRing k :=
  Ideal.Quotient.lift _ (surfaceTorusEval k) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, surfaceTorusEval_cubicEquation, mul_zero]

/-- `T₀ T₁ T₂` goes to `x y`, which has the inverse `1 / (x y)`. -/
theorem surfaceTorusκ_mul_invSelf :
    surfaceTorusκ k (torusMonomial (cubicIdeal k)) *
      IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k) = 1 := by
  simp only [surfaceTorusκ, torusMonomial, Ideal.Quotient.lift_mk, surfaceTorusEval,
    coe_eval₂Hom, eval₂_mul, eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul]
  exact torus_mul_invSelf k

/-- The homomorphism `(k[t][T₀, T₁, T₂] ⧸ (F))_{(T₀T₁T₂)} → k[x, y][1 / (x y)]`. -/
def surfaceTorusLift : TorusChartAway (cubicIdeal k) →+* torusRing k :=
  torusChartLift (cubicIdeal k) (surfaceTorusκ k) _ (surfaceTorusκ_mul_invSelf k)

/-- The inverse homomorphism `k[x, y][1 / (x y)] → (k[t][T₀, T₁, T₂] ⧸ (F))_{(T₀T₁T₂)}`. -/
def surfaceTorusSection : torusRing k →+* TorusChartAway (cubicIdeal k) :=
  torusSection ((torusChartConst (cubicIdeal k)).comp Polynomial.C) (torusChartX _)
    (torusChartY _) (torusChartW _) (torusChartW_mul_X_mul_Y _)

/-- In the chart, the affine equation `1 + x ^ 3 + y ^ 3 - t x y` vanishes. -/
theorem surfaceChart_equation :
    1 + torusChartX (cubicIdeal k) ^ 3 + torusChartY (cubicIdeal k) ^ 3 -
      torusChartConst (cubicIdeal k) Polynomial.X * torusChartX (cubicIdeal k) *
        torusChartY (cubicIdeal k) = 0 := by
  have hF : (cubicEquation k).IsHomogeneous (1 • 3) := by
    rw [smul_eq_mul, one_mul]
    exact (mem_homogeneousSubmodule _ _).1 (cubicEquation_mem k)
  have h := eval₂_torusChart (cubicIdeal k) hF
    (mk_mem_quotientGrading_of_isHomogeneous _ hF)
  have h0 : Ideal.Quotient.mk (cubicIdeal k).toIdeal (cubicEquation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hz : Away.mk _ (torusMonomial_mem (cubicIdeal k)) 1 _
      (mk_mem_quotientGrading_of_isHomogeneous _ hF) = 0 := by
    apply HomogeneousLocalization.val_injective
    simp [h0, Localization.mk_zero]
  rw [hz] at h
  have hw := torusChartW_mul_X_mul_Y (cubicIdeal k)
  simp only [cubicEquation, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, pow_one] at h
  linear_combination (torusChartX (cubicIdeal k) * torusChartY (cubicIdeal k)) * h +
    (-(1 + torusChartX (cubicIdeal k) ^ 3 + torusChartY (cubicIdeal k) ^ 3 -
      torusChartConst (cubicIdeal k) Polynomial.X * torusChartX (cubicIdeal k) *
        torusChartY (cubicIdeal k))) * hw

/-- The section sends `t = (1 + x ^ 3 + y ^ 3) / (x y)` to the constant `t` of the chart. -/
theorem surfaceTorusSection_parameter :
    surfaceTorusSection k (torusParameter k) = torusChartConst (cubicIdeal k) Polynomial.X := by
  rw [torusParameter, torusFermat, map_mul, surfaceTorusSection, torusSection_invSelf,
    torusSection_algebraMap]
  simp only [coe_eval₂Hom, eval₂_add, eval₂_one, eval₂_pow, eval₂_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  linear_combination torusChartW (cubicIdeal k) * surfaceChart_equation k +
    torusChartConst (cubicIdeal k) Polynomial.X * torusChartW_mul_X_mul_Y (cubicIdeal k)

/-- The section sends a constant `a` of `k` to the constant `a` of the chart. -/
theorem surfaceTorusSection_algebraMap (a : k) :
    surfaceTorusSection k (algebraMap k (torusRing k) a) =
      torusChartConst (cubicIdeal k) (Polynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (torusRing k),
    MvPolynomial.algebraMap_eq, surfaceTorusSection, torusSection_algebraMap]
  simp

/-- The homomorphism of the chart sends the constant `p` of `k[t]` to `p(t)`. -/
theorem surfaceTorusLift_const (p : Polynomial k) :
    surfaceTorusLift k (torusChartConst (cubicIdeal k) p) =
      Polynomial.eval₂RingHom (algebraMap k (torusRing k)) (torusParameter k) p := by
  rw [surfaceTorusLift, torusChartLift_const]
  simp [surfaceTorusκ, surfaceTorusEval]

/-- The homomorphism `(k[t][T₀, T₁, T₂] ⧸ (F))_{(T₀T₁T₂)} → k[x, y][1 / (x y)]` is bijective. -/
theorem surfaceTorusLift_bijective : Function.Bijective (surfaceTorusLift k) := by
  have hsec : (surfaceTorusLift k).comp (surfaceTorusSection k) = RingHom.id _ := by
    refine torusRing_ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, surfaceTorusSection_algebraMap,
        surfaceTorusLift_const]
      simp
    · fin_cases i
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [surfaceTorusSection, torusSection_algebraMap]
        simp only [coe_eval₂Hom, eval₂_X, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [surfaceTorusLift, torusChartX, torusChartLift_mk]
        simp only [surfaceTorusκ, surfaceTorusEval, Ideal.Quotient.lift_mk, coe_eval₂Hom,
          eval₂_mul, eval₂_pow, eval₂_X, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, pow_one, Matrix.cons_val_zero]
        linear_combination algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0) *
          torus_mul_invSelf k
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [surfaceTorusSection, torusSection_algebraMap]
        simp only [coe_eval₂Hom, eval₂_X, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [surfaceTorusLift, torusChartY, torusChartLift_mk]
        simp only [surfaceTorusκ, surfaceTorusEval, Ideal.Quotient.lift_mk, coe_eval₂Hom,
          eval₂_mul, eval₂_pow, eval₂_X, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, pow_one, Matrix.cons_val_zero]
        linear_combination algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1) *
          torus_mul_invSelf k
  refine torusChartLift_bijective (cubicIdeal k) (surfaceTorusκ k) _
    (surfaceTorusκ_mul_invSelf k) ?_ (surfaceTorusSection k) ?_ ?_ (fun r => ?_) ?_
    (fun b => RingHom.congr_fun hsec b)
  · simp [surfaceTorusκ, surfaceTorusEval]
  · simp only [surfaceTorusκ, surfaceTorusEval, Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_X,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [surfaceTorusSection, torusSection_algebraMap]
    simp
  · simp only [surfaceTorusκ, surfaceTorusEval, Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_X,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [surfaceTorusSection, torusSection_algebraMap]
    simp
  · simp only [surfaceTorusκ, surfaceTorusEval, Ideal.Quotient.lift_mk, coe_eval₂Hom, eval₂_C]
    have h : (surfaceTorusSection k).comp
        (Polynomial.eval₂RingHom (algebraMap k (torusRing k)) (torusParameter k)) =
          torusChartConst (cubicIdeal k) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact surfaceTorusSection_algebraMap k a
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        exact surfaceTorusSection_parameter k
    exact RingHom.congr_fun h r
  · exact torusSection_invSelf _ _ _ _ _

/-- **The torus chart of the cubic surface.** The open `D₊(T₀ T₁ T₂)` of the cubic surface is the
torus `Spec k[x, y][1 / (x y)]`, with `x = T₁ / T₀` and `y = T₂ / T₀`, and over the affine line
the coordinate `t` is the function `(1 + x ^ 3 + y ^ 3) / (x y)`. -/
theorem exists_iso_surfaceTorusOpen :
    ∃ e : Spec (CommRingCat.of (torusRing k)) ≅ (surfaceTorusOpen k : Scheme),
      e.hom ≫ (surfaceTorusOpen k).ι ≫ cubicSurfaceToLine k =
        Spec.map (CommRingCat.ofHom
          (Polynomial.eval₂RingHom (algebraMap k (torusRing k)) (torusParameter k))) := by
  refine ⟨Scheme.Spec.mapIso
      (RingEquiv.ofBijective _ (surfaceTorusLift_bijective k)).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec _ _ (torusMonomial_mem (cubicIdeal k)) three_pos).symm, ?_⟩
  change Spec.map (CommRingCat.ofHom (surfaceTorusLift k)) ≫
    (Proj.basicOpenIsoSpec _ _ (torusMonomial_mem (cubicIdeal k)) three_pos).inv ≫
      (Proj.basicOpen _ (torusMonomial (cubicIdeal k))).ι ≫ Proj.toSpecZero _ ≫
        Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' _).comp
          (algebraMap (Polynomial k) _))) = _
  rw [Proj.basicOpenIsoSpec_inv_ι_assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  exact surfaceTorusLift_const k p

/-! ### The torus chart of the Fermat cubic -/

/-- The torus chart `D₊(T₀ T₁ T₂)` of the Fermat cubic curve. -/
def fermatTorusOpen : (fermatCurve k).Opens :=
  Proj.basicOpen (quotientGrading (MvPolynomial.homogeneousSubmodule (Fin 3) k) (fermatIdeal k))
    (Ideal.Quotient.mk (fermatIdeal k).toIdeal (X 0 * X 1 * X 2))

/-- The point `(1 : x : y)` of the curve `1 + x ^ 3 + y ^ 3 = 0` of the torus, as a homomorphism
out of `k[T₀, T₁, T₂]`. -/
def fermatTorusEval : MvPolynomial (Fin 3) k →+* torusRing k ⧸ Ideal.span {torusFermat k} :=
  (Ideal.Quotient.mk _).comp (eval₂Hom (algebraMap k (torusRing k))
    ![1, algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0),
      algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1)])

/-- The Fermat cubic vanishes at that point. -/
theorem fermatTorusEval_fermatCubic : fermatTorusEval k (fermatCubic k) = 0 := by
  have h : eval₂Hom (algebraMap k (torusRing k))
      ![1, algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0),
        algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1)] (fermatCubic k) =
      torusFermat k := by
    simp [fermatCubic, torusFermat]
  rw [fermatTorusEval, RingHom.comp_apply, h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- The point as a homomorphism out of the homogeneous coordinate ring of the Fermat cubic. -/
def fermatTorusκ :
    MvPolynomial (Fin 3) k ⧸ (fermatIdeal k).toIdeal →+* torusRing k ⧸ Ideal.span {torusFermat k} :=
  Ideal.Quotient.lift _ (fermatTorusEval k) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, fermatTorusEval_fermatCubic, mul_zero]

/-- `T₀ T₁ T₂` goes to `x y`, which has the inverse `1 / (x y)`. -/
theorem fermatTorusκ_mul_invSelf :
    fermatTorusκ k (torusMonomial (fermatIdeal k)) *
      Ideal.Quotient.mk _ (IsLocalization.Away.invSelf (X 0 * X 1 : MvPolynomial (Fin 2) k)) =
        1 := by
  simp only [fermatTorusκ, torusMonomial, Ideal.Quotient.lift_mk, fermatTorusEval,
    RingHom.comp_apply, coe_eval₂Hom, eval₂_mul, eval₂_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_mul,
    ← map_mul]
  rw [IsLocalization.Away.mul_invSelf, map_one]

/-- In the chart of the Fermat cubic, the affine equation `1 + x ^ 3 + y ^ 3` vanishes. -/
theorem fermatChart_equation :
    1 + torusChartX (fermatIdeal k) ^ 3 + torusChartY (fermatIdeal k) ^ 3 = 0 := by
  have hF : (fermatCubic k).IsHomogeneous (1 • 3) := by
    rw [smul_eq_mul, one_mul]
    exact fermatCubic_isHomogeneous k
  have h := eval₂_torusChart (fermatIdeal k) hF
    (mk_mem_quotientGrading_of_isHomogeneous _ hF)
  have h0 : Ideal.Quotient.mk (fermatIdeal k).toIdeal (fermatCubic k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hz : Away.mk _ (torusMonomial_mem (fermatIdeal k)) 1 _
      (mk_mem_quotientGrading_of_isHomogeneous _ hF) = 0 := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, h0, Localization.mk_zero, val_zero]
  rw [hz] at h
  have hw := torusChartW_mul_X_mul_Y (fermatIdeal k)
  simp only [fermatCubic, eval₂_add, eval₂_pow, eval₂_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    pow_one] at h
  linear_combination (torusChartX (fermatIdeal k) * torusChartY (fermatIdeal k)) * h +
    (-(1 + torusChartX (fermatIdeal k) ^ 3 + torusChartY (fermatIdeal k) ^ 3)) * hw

/-- The section `k[x, y][1 / (x y)] → (k[T₀, T₁, T₂] ⧸ (F₀))_{(T₀T₁T₂)}` before the quotient. -/
def fermatTorusSection₀ : torusRing k →+* TorusChartAway (fermatIdeal k) :=
  torusSection (torusChartConst (fermatIdeal k)) (torusChartX _) (torusChartY _) (torusChartW _)
    (torusChartW_mul_X_mul_Y _)

/-- The section `k[x, y][1 / (x y)] ⧸ (1 + x ^ 3 + y ^ 3) → (k[T₀, T₁, T₂] ⧸ (F₀))_{(T₀T₁T₂)}`. -/
def fermatTorusSection :
    torusRing k ⧸ Ideal.span {torusFermat k} →+* TorusChartAway (fermatIdeal k) :=
  Ideal.Quotient.lift _ (fermatTorusSection₀ k) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, torusFermat, fermatTorusSection₀, torusSection_algebraMap]
    simp only [coe_eval₂Hom, eval₂_add, eval₂_one, eval₂_pow, eval₂_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [fermatChart_equation, mul_zero]

/-- The homomorphism `(k[T₀, T₁, T₂] ⧸ (F₀))_{(T₀T₁T₂)} → k[x, y][1 / (x y)] ⧸ (1 + x³ + y³)`. -/
def fermatTorusLift : TorusChartAway (fermatIdeal k) →+* torusRing k ⧸ Ideal.span {torusFermat k} :=
  torusChartLift (fermatIdeal k) (fermatTorusκ k) _ (fermatTorusκ_mul_invSelf k)

/-- The homomorphism `fermatTorusLift` is bijective. -/
theorem fermatTorusLift_bijective : Function.Bijective (fermatTorusLift k) := by
  have hsec : ((fermatTorusLift k).comp (fermatTorusSection k)).comp (Ideal.Quotient.mk _) =
      Ideal.Quotient.mk _ := by
    refine torusRing_ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, fermatTorusSection, Ideal.Quotient.lift_mk,
        fermatTorusSection₀, torusSection_algebraMap, coe_eval₂Hom, eval₂_C]
      rw [fermatTorusLift, torusChartLift_const]
      simp only [fermatTorusκ, Ideal.Quotient.lift_mk, fermatTorusEval, RingHom.comp_apply,
        coe_eval₂Hom, eval₂_C]
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (torusRing k),
        MvPolynomial.algebraMap_eq]
    · fin_cases i
      · simp only [RingHom.comp_apply, fermatTorusSection, Ideal.Quotient.lift_mk,
          fermatTorusSection₀, torusSection_algebraMap, coe_eval₂Hom, eval₂_X, Fin.zero_eta,
          Fin.isValue, Matrix.cons_val_zero]
        rw [fermatTorusLift, torusChartX, torusChartLift_mk]
        simp only [fermatTorusκ, fermatTorusEval, Ideal.Quotient.lift_mk, RingHom.comp_apply,
          coe_eval₂Hom, eval₂_mul, eval₂_pow, eval₂_X, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, pow_one, ← map_pow, ← map_mul, Matrix.cons_val_zero]
        congr 1
        simp only [map_mul, map_pow]
        linear_combination algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 0) *
          torus_mul_invSelf k
      · simp only [RingHom.comp_apply, fermatTorusSection, Ideal.Quotient.lift_mk,
          fermatTorusSection₀, torusSection_algebraMap, coe_eval₂Hom, eval₂_X, Fin.mk_one,
          Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [fermatTorusLift, torusChartY, torusChartLift_mk]
        simp only [fermatTorusκ, fermatTorusEval, Ideal.Quotient.lift_mk, RingHom.comp_apply,
          coe_eval₂Hom, eval₂_mul, eval₂_pow, eval₂_X, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, pow_one, ← map_pow, ← map_mul, Matrix.cons_val_zero]
        congr 1
        simp only [map_mul, map_pow]
        linear_combination algebraMap (MvPolynomial (Fin 2) k) (torusRing k) (X 1) *
          torus_mul_invSelf k
  have hsec' : (fermatTorusLift k).comp (fermatTorusSection k) = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext hsec
  refine torusChartLift_bijective (fermatIdeal k) (fermatTorusκ k) _
    (fermatTorusκ_mul_invSelf k) ?_ (fermatTorusSection k) ?_ ?_ (fun r => ?_) ?_
    (fun b => RingHom.congr_fun hsec' b)
  · simp only [fermatTorusκ, Ideal.Quotient.lift_mk, fermatTorusEval, RingHom.comp_apply,
      coe_eval₂Hom, eval₂_X, Matrix.cons_val_zero, map_one]
  · simp only [fermatTorusκ, fermatTorusEval, Ideal.Quotient.lift_mk, RingHom.comp_apply,
      coe_eval₂Hom, eval₂_X, Matrix.cons_val_one, Matrix.cons_val_zero,
      fermatTorusSection,
      fermatTorusSection₀, torusSection_algebraMap]
  · simp only [fermatTorusκ, fermatTorusEval, Ideal.Quotient.lift_mk, RingHom.comp_apply,
      coe_eval₂Hom, eval₂_X, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      fermatTorusSection, fermatTorusSection₀, torusSection_algebraMap]
  · simp only [fermatTorusκ, fermatTorusEval, Ideal.Quotient.lift_mk, RingHom.comp_apply,
      coe_eval₂Hom, eval₂_C, fermatTorusSection]
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k) (torusRing k),
      MvPolynomial.algebraMap_eq, fermatTorusSection₀, torusSection_algebraMap]
    simp
  · rw [fermatTorusSection, Ideal.Quotient.lift_mk, fermatTorusSection₀]
    exact torusSection_invSelf _ _ _ _ _

/-- **The torus chart of the Fermat cubic.** The open `D₊(T₀ T₁ T₂)` of the Fermat cubic curve
is the closed curve `1 + x ^ 3 + y ^ 3 = 0` of the torus `Spec k[x, y][1 / (x y)]`. -/
theorem nonempty_iso_fermatTorusOpen :
    Nonempty (Spec (CommRingCat.of (torusRing k ⧸ Ideal.span {torusFermat k})) ≅
      (fermatTorusOpen k : Scheme)) :=
  ⟨Scheme.Spec.mapIso
      (RingEquiv.ofBijective _ (fermatTorusLift_bijective k)).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec _ _ (torusMonomial_mem (fermatIdeal k)) three_pos).symm⟩

end Stacks.Examples.CurveFamilyNotScheme

end
