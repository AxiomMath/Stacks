module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import StacksFrontier.AlgebraicGeometry.ClosedSubschemeProjQuotient.Saturation
public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChange
public import StacksFrontier.AlgebraicGeometry.Limits.AffineIntoProjective
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing

/-!
# The example of [Stacks, Tag 0CD1]: the curve is nonsingular and the projection exists

`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChange.lean` states the example of
[Stacks, Tag 0CD1] — the plane cubic `F = T₁²T₀ - T₂³ + aT₀³` over a field of characteristic
three in which `a` is not a cube — and computes the two genus values. This file supplies the two
assertions of the example that are about the geometry rather than the algebra: the curve is
**nonsingular**, and the morphism to `𝐏¹_k` that the example projects along **exists** and is
the coordinate projection.

## Main definitions

* `Stacks.Curves.InseparableGenus.coeffDerivation`: a derivation of `R` acting on `R[X]`
  coefficientwise.
* `Stacks.Curves.InseparableGenus.coordProjHom` and `.coordProjGradedHom`: the substitution
  `k[S₀, S₁] → k[T₀, T₁, T₂]`, `Sⱼ ↦ Tⱼ`, as a ring and as a graded ring homomorphism.

## Main results

* `Stacks.Curves.InseparableGenus.isRegular_of_idealOfClosedSubscheme_eq_span`: the plane cubic
  of [Stacks, Tag 0CD1] is a **regular**, that is nonsingular, scheme.
* `Stacks.Curves.InseparableGenus.exists_coordProj_hom`: the **morphism `f : Z ⟶ 𝐏¹_k`** of the
  example exists, and the inverse images of the standard opens identify it as the projection
  `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`.
* `Stacks.Curves.InseparableGenus.isRegular_and_exists_coordProj_and_genus_ne`: **[Stacks, Tag
  0CD1]** in one statement — the curve, its nonsingularity, the projection to `𝐏¹_k`, the purely
  inseparable degree-three extension of function fields, and the two genus values `1` and `0`.

## Implementation notes

**Nonsingularity, chart by chart.** `Stacks.ProjectiveChart.chartQuotientEquiv` presents the
chart `Z ∩ D₊(Tⱼ)` as `k[Y₀, Y₁] ⧸ (F(Tⱼ = 1))`, an affine open of `Z`. Two charts suffice:
every point of the curve satisfies its equation (`planeCubic_mem_asHomogeneousIdeal`, which reads
off that the standard open of `F` pulls back to that of `0` under the presentation of `Z` as
`Proj` of the quotient by its homogeneous ideal), and at such a point `T₀` or `T₁` is invertible,
since otherwise `T₂³ = T₁²T₀ + aT₀³` would vanish too and the point would be irrelevant. So only

```
F(T₀ = 1) = Y₀² - Y₁³ + a   and   F(T₁ = 1) = Y₀ - Y₁³ + aY₀³
```

have to be shown to present regular rings.

**The derivation criterion.** Both are handled by [Stacks, Tag 07PF]
(`isRegularRing_quotient_span_singleton_of_isUnit_derivation`): a hypersurface in a regular ring
is regular as soon as some derivation carries its equation to a unit. On `D₊(T₁)` the partial
derivative in `Y₀` does it, because `∂(Y₀ + aY₀³)/∂Y₀ = 1 + 3aY₀² = 1` in characteristic three.

On `D₊(T₀)` no partial derivative works — `∂/∂Y₀ = 2Y₀` and `∂/∂Y₁ = -3Y₁² = 0`, so the curve is
*not smooth* over `k` along `Y₀ = 0`, which is exactly the point of the example. What works is a
derivation of `k` itself: `a` is not a cube in the imperfect field `k`, so by [Stacks, Tag 07PH]
some `D : Derivation ℤ k k` has `D a ≠ 0`, and the coefficientwise derivation of `k[Y₁][Y₀]` it
induces carries `Y₁³ - a` to the unit `-D a`. That is the shape of [Stacks, Tag 07PG], which is
how the chart is handled here. So nonsingularity of this curve genuinely *is* the failure of `a`
to be a cube, and the curve is regular without being smooth over `k`.

**The projection.** The substitution `Sⱼ ↦ Tⱼ` does not induce a morphism `𝐏²_k ⟶ 𝐏¹_k`: it is
undefined at `(0 : 0 : 1)`. It induces one on the open where some `Tⱼ`, `j ∈ {0, 1}`, is
invertible, which is [Stacks, Tag 01MY] and is this repository's
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` on
`Stacks.AlgebraicGeometry.ProjShared.mapDomain`. The curve lies in that open — the same
computation that gave two charts — so the closed immersion lifts through it and the composite is
`f`. What identifies the composite as *the* projection, rather than some morphism to `𝐏¹_k`, is
`mapHom_preimage_basicOpen`: for homogeneous `G` of positive degree, `f ⁻¹ᵁ D₊(G)` is
`i ⁻¹ᵁ D₊(G(T₀, T₁))`, and those identities determine `f` on points.

**The curve is an input here, and it is satisfiable.** Every statement in this file takes the
curve as data — a scheme `Z`, a closed immersion into `𝐏²_k`, and the hypotheses that it is
nonempty, equidimensional of dimension one, without embedded points, and cut out by `F`. All six
are discharged for `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))` in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurve.lean` and
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeCurveDimension.lean`, where
`Stacks.Curves.InseparableGenus.planeCubicCurve_isRegular_and_genus_ne` is the statement below
with nothing assumed.

**What is not here.** For the curve taken as input here the purely inseparable degree-three
extension of function fields is stated as the extension `k(x) ⊆ k(x)(y)`, `y³ = x² + a`, of
`Stacks.Curves.InseparableGenus.curveFunctionField`, and is *not* identified with the extension
of function fields of `f` — nothing about an arbitrary `Z` would let it be. For the explicitly
constructed curve the identification is complete:
`Stacks.Curves.InseparableGenus.functionFieldEquivCurveFunctionField`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeFunctionField.lean`, computes
`Z.functionField` as `curveFunctionField k a` through the chart `D₊(T₀)`,
`Stacks.Curves.InseparableGenus.isDominant_planeCubicProjection`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeDominant.lean`, makes `f` induce an
extension of function fields at all, and
`Stacks.Curves.InseparableGenus.isPurelyInseparable_and_finrank_projectionFunctionField`, in
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean`, states the
extension for the embedding of `k(x)` that `f` itself gives.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 07PF](https://stacks.math.columbia.edu/tag/07PF)
* [Stacks Project, Tag 07PG](https://stacks.math.columbia.edu/tag/07PG)
* [Stacks Project, Tag 07PH](https://stacks.math.columbia.edu/tag/07PH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)
open Stacks.ProjectiveChart (dehomCoeff dehomCoeff_eq_aeval subschemeChart chartQuotientEquiv
  isAffineOpen_subschemeChart)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain mem_mapDomain_iff)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom mapHom_preimage_basicOpen)

universe u

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### A derivation of the coefficients -/

open Polynomial in
/-- Differentiating the coefficients of a polynomial: a derivation of `R` acts on `R[X]`
coefficientwise, killing `X`. -/
def coeffDerivation {R : Type*} [CommRing R] (D : Derivation ℤ R R) :
    Derivation ℤ R[X] R[X] :=
  let E := PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
  Derivation.mk' E.toLinearMap E.leibniz

open Polynomial in
/-- The coefficientwise derivation `coeffDerivation D` sends the constant `C r` to `C (D r)`. -/
@[simp] theorem coeffDerivation_C {R : Type*} [CommRing R] (D : Derivation ℤ R R) (r : R) :
    coeffDerivation D (C r) = C (D r) := by
  ext n
  simp [coeffDerivation]

open Polynomial in
/-- The coefficientwise derivation `coeffDerivation D` kills the variable `X`. -/
@[simp] theorem coeffDerivation_X {R : Type*} [CommRing R] (D : Derivation ℤ R R) :
    coeffDerivation D (X : R[X]) = 0 := by
  ext n
  simp [coeffDerivation, Derivation.mapCoeffs_X]

open Polynomial in
/-- The two-variable polynomial ring as an iterated one-variable polynomial ring. -/
def bivariateEquiv (k : Type u) [CommRing k] : MvPolynomial (Fin 2) k ≃+* k[X][X] :=
  (MvPolynomial.finSuccEquiv k 1).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv)

open Polynomial in
/-- `bivariateEquiv k` sends the constant `r` to the doubly constant polynomial `C (C r)`. -/
@[simp] theorem bivariateEquiv_C (k : Type u) [CommRing k] (r : k) :
    bivariateEquiv k (MvPolynomial.C r) = C (C r) := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_apply, MvPolynomial.uniqueAlgEquiv_apply]

open Polynomial in
/-- `bivariateEquiv k` sends the variable `X 0` to the outer variable `X`. -/
@[simp] theorem bivariateEquiv_X_zero (k : Type u) [CommRing k] :
    bivariateEquiv k (MvPolynomial.X 0) = Polynomial.X := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_apply]

open Polynomial in
/-- `bivariateEquiv k` sends the variable `X 1` to the inner variable, the constant `C X`. -/
@[simp] theorem bivariateEquiv_X_one (k : Type u) [CommRing k] :
    bivariateEquiv k (MvPolynomial.X 1) = C Polynomial.X := by
  show (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv)
    ((MvPolynomial.finSuccEquiv k 1) (MvPolynomial.X (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- A field of exponential characteristic three has characteristic three. -/
private theorem charP_three_of_expChar (k : Type u) [Field k] [ExpChar k 3] : CharP k 3 := by
  cases ‹ExpChar k 3› with
  | prime hp => infer_instance

/-- **An element of an imperfect field of characteristic `p` which is not a `p`-th power is seen
by a derivation.** This is [Stacks, Tag 07PH] at `p = 3` for the ground field of the example. -/
theorem exists_derivation_apply_ne_zero_of_forall_pow_ne {k : Type u} [Field k] [ExpChar k 3]
    (a : k) (ha : ∀ b : k, b ^ 3 ≠ a) : ∃ D : Derivation ℤ k k, D a ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have := charP_three_of_expChar k
  have : IsAdicComplete (IsLocalRing.maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact IsAdicComplete.bot k
  exact exists_derivation_apply_ne_zero_of_not_pow_fractionRing (R := k) (K := k) a
    fun ⟨b, hb⟩ => ha b hb.symm

/-! ### The three affine charts of the cubic are regular -/

/-- **The chart `D₊(T₀)` is regular**: the chart ring is `k[Y₁][Y₀] ⧸ (Y₀² - (Y₁³ - a))`, a
quotient of a polynomial ring by `p(Y₀) - g` for the integral polynomial `p = Y₀²` and
`g = Y₁³ - a`, and the coefficientwise derivation attached to a derivation `D` of `k` with
`D a ≠ 0` carries `g` to the unit `-D a`. This is the chart on which the curve is regular without
being smooth over `k`. -/
theorem isRegularRing_chartZero (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    IsRegularRing (MvPolynomial (Fin 2) k ⧸
      Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 3 + MvPolynomial.C a}) := by
  classical
  obtain ⟨D, hD⟩ := exists_derivation_apply_ne_zero_of_forall_pow_ne a ha
  set g : Polynomial k := Polynomial.X ^ 3 - Polynomial.C a with hg
  have hDg : coeffDerivation D g = -Polynomial.C (D a) := by
    rw [hg, map_sub, coeffDerivation_C, Derivation.leibniz_pow, coeffDerivation_X, smul_zero,
      smul_zero, zero_sub]
  have hreg : IsRegularRing (Polynomial (Polynomial k) ⧸
      Ideal.span {(Polynomial.X ^ 2 : Polynomial ℤ).map (algebraMap ℤ (Polynomial k)) -
        Polynomial.C g}) :=
    isRegularRing_quotient_polynomial_sub_C_of_isUnit_derivation g (coeffDerivation D)
      (hDg ▸ ((Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hD)).neg)) (Polynomial.X ^ 2)
  refine IsRegularRing.of_ringEquiv (R := Polynomial (Polynomial k) ⧸
      Ideal.span {(Polynomial.X ^ 2 : Polynomial ℤ).map (algebraMap ℤ (Polynomial k)) -
        Polynomial.C g})
    (RingEquiv.symm (Ideal.quotientEquiv _ _ (bivariateEquiv k) ?_))
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  rw [Set.singleton_eq_singleton_iff, hg]
  push_cast
  simp only [map_sub, map_add, map_pow, bivariateEquiv_C, bivariateEquiv_X_zero,
    bivariateEquiv_X_one, Polynomial.map_pow, Polynomial.map_X]
  ring

/-- **The chart `D₊(T₁)` is regular**: in characteristic three the derivative of
`Y₀ - Y₁³ + aY₀³` in `Y₀` is `1 + 3aY₀² = 1`, a unit. This chart is even smooth over `k`. -/
theorem isRegularRing_chartOne (k : Type u) [Field k] [ExpChar k 3] (a : k) :
    IsRegularRing (MvPolynomial (Fin 2) k ⧸
      Ideal.span {MvPolynomial.X 0 - MvPolynomial.X 1 ^ 3 +
        MvPolynomial.C a * MvPolynomial.X 0 ^ 3}) := by
  have := charP_three_of_expChar k
  have hthree : (3 : MvPolynomial (Fin 2) k) = 0 := CharP.cast_eq_zero _ 3
  let D := (MvPolynomial.pderiv (R := k) (0 : Fin 2)).restrictScalars ℤ
  let G : MvPolynomial (Fin 2) k := MvPolynomial.X 0 - MvPolynomial.X 1 ^ 3 +
    MvPolynomial.C a * MvPolynomial.X 0 ^ 3
  have hD : D G = 1 := by
    simp [D, G, Derivation.leibniz_pow, Derivation.leibniz, smul_eq_mul,
      MvPolynomial.pderiv_X, hthree]
  exact isRegularRing_quotient_span_singleton_of_isUnit_derivation G D
    (hD ▸ isUnit_one.map (Ideal.Quotient.mk _))

/-! ### The dehomogenizations of the cubic -/

/-- The dehomogenization of the cubic on `D₊(T₀)`: in the coordinates `Y₀ = T₁/T₀` and
`Y₁ = T₂/T₀` the equation is `Y₀² - Y₁³ + a`. -/
theorem dehomCoeff_planeCubic_zero (k : Type u) [CommRing k] (a : k) :
    dehomCoeff k (0 : Fin 3) (planeCubic k a) =
      MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 3 + MvPolynomial.C a := by
  have h1 : finSuccEquiv' (0 : Fin 3) 1 = some 0 := by decide
  have h2 : finSuccEquiv' (0 : Fin 3) 2 = some 1 := by decide
  rw [dehomCoeff_eq_aeval, planeCubic]
  simp [h1, h2]

/-- The dehomogenization of the cubic on `D₊(T₁)`: in the coordinates `Y₀ = T₀/T₁` and
`Y₁ = T₂/T₁` the equation is `Y₀ - Y₁³ + aY₀³`. -/
theorem dehomCoeff_planeCubic_one (k : Type u) [CommRing k] (a : k) :
    dehomCoeff k (1 : Fin 3) (planeCubic k a) =
      MvPolynomial.X 0 - MvPolynomial.X 1 ^ 3 + MvPolynomial.C a * MvPolynomial.X 0 ^ 3 := by
  have h1 : finSuccEquiv' (1 : Fin 3) 0 = some 0 := by decide
  have h2 : finSuccEquiv' (1 : Fin 3) 2 = some 1 := by decide
  rw [dehomCoeff_eq_aeval, planeCubic]
  simp [h1, h2]

/-- Each of the two dehomogenizations of the cubic that the curve is covered by presents a
regular ring. -/
theorem isRegularRing_dehomCoeff_planeCubic (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) {j : Fin 3} (hj : j = 0 ∨ j = 1) :
    IsRegularRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {dehomCoeff k j (planeCubic k a)}) := by
  rcases hj with rfl | rfl
  · rw [dehomCoeff_planeCubic_zero]
    exact isRegularRing_chartZero k a ha
  · rw [dehomCoeff_planeCubic_one]
    exact isRegularRing_chartOne k a

/-! ### Nonsingularity of the curve -/

/-- **A point of the curve satisfies its equation.** The curve is `Proj` of the quotient by its
homogeneous ideal, so the standard open of the equation pulls back to the standard open of `0`,
which is empty. -/
theorem planeCubic_mem_asHomogeneousIdeal {k : Type u} [Field k] (a : k) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) (x : Z) :
    planeCubic k a ∈ (i.base x).asHomogeneousIdeal := by
  set 𝒮 := MvPolynomial.homogeneousSubmodule (Fin 3) k
  set I := Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme 𝒮 i
  have hzero : Stacks.RingTheory.HomogeneousQuotient.quotientMk 𝒮 I (planeCubic k a) = 0 := by
    rw [Stacks.RingTheory.HomogeneousQuotient.quotientMk_apply, Ideal.Quotient.eq_zero_iff_mem]
    show planeCubic k a ∈ idealOfClosedSubscheme 𝒮 i
    rw [hI]
    exact Ideal.mem_span_singleton_self _
  have hpre : i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (planeCubic k a) = ⊥ := by
    rw [← Stacks.ClosedSubschemeProjQuotient.projQuotientIso_hom_comp_ambientHom 𝒮 i,
      Scheme.Hom.comp_preimage,
      Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_preimage_basicOpen 𝒮 _ _ _
        (planeCubic k a) 3
        ((MvPolynomial.mem_homogeneousSubmodule 3 _).2 (planeCubic_isHomogeneous k a))
        (by decide),
      hzero, AlgebraicGeometry.Proj.basicOpen_zero, Scheme.Hom.preimage_bot]
  by_contra hmem
  have hx : x ∈ i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (planeCubic k a) := hmem
  rw [hpre] at hx
  simp at hx

/-- **The curve misses the point `(0 : 0 : 1)`.** At a point of the plane cubic one of the first
two coordinates is invertible: if `T₀` and `T₁` both vanished then `T₂³ = T₁²T₀ + aT₀³` would too,
hence `T₂`, and the point would be the irrelevant ideal. -/
theorem X_zero_notMem_or_X_one_notMem {k : Type u} [Field k] (a : k)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (hF : planeCubic k a ∈ p.asHomogeneousIdeal) :
    MvPolynomial.X (0 : Fin 3) ∉ p.asHomogeneousIdeal ∨
      MvPolynomial.X (1 : Fin 3) ∉ p.asHomogeneousIdeal := by
  rw [← not_and_or]
  rintro ⟨h0, h1⟩
  set J := p.asHomogeneousIdeal.toIdeal
  have h0' : MvPolynomial.X (0 : Fin 3) ∈ J := h0
  have h2 : MvPolynomial.X (2 : Fin 3) ∈ J := by
    refine p.isPrime.mem_of_pow_mem 3 ?_
    convert J.sub_mem
      (J.add_mem (J.mul_mem_left (MvPolynomial.X 1 ^ 2) h0')
        (J.mul_mem_left (MvPolynomial.C a) (J.pow_mem_of_mem h0' 3 (by decide)))) hF using 1
    rw [planeCubic]
    ring
  have hcover := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
    (MvPolynomial.homogeneousSubmodule (Fin 3) k)
    (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) k)
    (fun j => ⟨1, MvPolynomial.isHomogeneous_X k j⟩)
    (AlgebraicGeometry.ProjectiveSpace.adjoin_range_X_homogeneousSubmodule_zero 2 k)
  have hp : p ∈ ⨆ j : Fin 3,
      AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 3) k)
        (MvPolynomial.X j) := by
    rw [hcover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have hj' : MvPolynomial.X j ∉ p.asHomogeneousIdeal := hj
  fin_cases j
  exacts [hj' h0, hj' h1, hj' h2]

/-- **The curve of [Stacks, Tag 0CD1] is nonsingular.** Every point of the plane cubic lies on
`D₊(T₀)` or on `D₊(T₁)`, each of which is an affine open of the curve whose ring of functions is
regular, so the curve is regular — nonsingular — in the sense of [Stacks, Tag 02IS]. This is the
nonsingularity the source asserts; the squarefreeness of `y³ - a` is only its shadow on one
chart. -/
theorem isRegular_of_idealOfClosedSubscheme_eq_span {k : Type u} [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    IsRegular Z := by
  have hF : planeCubic k a ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k (3 • 1) := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (planeCubic_isHomogeneous k a)
  intro x
  obtain ⟨j, hj, hx⟩ : ∃ j : Fin 3, (j = 0 ∨ j = 1) ∧
      MvPolynomial.X j ∉ (i.base x).asHomogeneousIdeal := by
    rcases X_zero_notMem_or_X_one_notMem a (i.base x)
      (planeCubic_mem_asHomogeneousIdeal a i hI x) with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  refine ⟨⟨subschemeChart i j, isAffineOpen_subschemeChart i j⟩, hx, ?_⟩
  have := isRegularRing_dehomCoeff_planeCubic k a ha hj
  exact IsRegularRing.of_ringEquiv (chartQuotientEquiv i j (planeCubic k a) hF hI)

/-! ### The projection to the projective line -/

/-- **The coordinate projection on equations**: the substitution `k[S₀, S₁] → k[T₀, T₁, T₂]`,
`Sⱼ ↦ Tⱼ`, whose induced morphism of projective spectra is the projection
`(T₀ : T₁ : T₂) ↦ (T₀ : T₁)` away from the point `(0 : 0 : 1)`. -/
def coordProjHom (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 3) k :=
  (MvPolynomial.rename (R := k) (fun j : Fin 2 => (⟨j.val, by omega⟩ : Fin 3))).toRingHom

/-- `coordProjHom k` sends the variable `Sⱼ` to the variable `Tⱼ`. -/
@[simp] theorem coordProjHom_X (k : Type u) [CommRing k] (j : Fin 2) :
    coordProjHom k (MvPolynomial.X j) = MvPolynomial.X ⟨j.val, by omega⟩ := by
  simp [coordProjHom]

/-- The coordinate projection as a homomorphism of graded rings: substituting variables for
variables preserves the degree. -/
def coordProjGradedHom (k : Type u) [CommRing k] :
    MvPolynomial.homogeneousSubmodule (Fin 2) k →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin 3) k where
  toRingHom := coordProjHom k
  map_mem := fun hf => MvPolynomial.IsHomogeneous.rename_isHomogeneous hf

/-- **The projection is defined at every point of the curve.** The coordinate projection is
defined away from `(0 : 0 : 1)`, and the curve misses that point. -/
theorem mem_mapDomain_coordProjGradedHom {k : Type u} [Field k] (a : k)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    (hF : planeCubic k a ∈ p.asHomogeneousIdeal) :
    p ∈ mapDomain (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 2,
      coordProjHom k (MvPolynomial.X j) ∉ p.asHomogeneousIdeal := by
    rcases X_zero_notMem_or_X_one_notMem a p hF with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨1,
    TopologicalSpace.Opens.mem_iSup.mpr ⟨by decide,
      TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X k j⟩, hj⟩⟩⟩

/-- **The morphism `f : Z ⟶ 𝐏¹_k` of [Stacks, Tag 0CD1] exists**, and it is the coordinate
projection `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`: the standard open of a homogeneous `G` of positive
degree pulls back along `f` to the standard open of `G(T₀, T₁)` pulled back along the embedding
of the curve in `𝐏²_k`. That identity on the standard opens of all positive-degree homogeneous
elements determines `f` pointwise, so no morphism is assumed: this constructs the `x`-projection
the example projects along.

The construction is [Stacks, Tag 01MY]: the graded homomorphism `Sⱼ ↦ Tⱼ` induces a morphism on
the open `U` of `𝐏²_k` where some `Tⱼ`, `j ∈ {0, 1}`, is invertible, that open is the complement
of `(0 : 0 : 1)`, and the curve lies in it because its equation gives `T₂³ = T₁²T₀ + aT₀³`. -/
theorem exists_coordProj_hom {k : Type u} [Field k] (a : k) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)) [IsClosedImmersion i]
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    ∃ f : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k),
      ∀ (G : MvPolynomial (Fin 2) k) (d : ℕ),
        G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d → 0 < d →
        f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
          i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G) := by
  set U := mapDomain (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjGradedHom k)
  have hrange : Set.range i.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨i.base x, mem_mapDomain_coordProjGradedHom a (i.base x)
      (planeCubic_mem_asHomogeneousIdeal a i hI x)⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift U.ι i hrange ≫ mapHom _ _ (coordProjGradedHom k),
    fun G d hG hd => ?_⟩
  rw [Scheme.Hom.comp_preimage, mapHom_preimage_basicOpen _ _ _ G d hG hd,
    ← Scheme.Hom.comp_preimage, IsOpenImmersion.lift_fac]
  rfl

/-! ### The example of Tag 0CD1 -/

/-- **[Stacks, Tag 0CD1] for a supplied plane cubic, with the abstract function field.** Let `k`
be a field of characteristic three and `a ∈ k` an element which is not a cube — such a pair
exists by `exists_charThree_notCube` — and let `Z ⊆ 𝐏²_k` be the plane curve cut out by
`F = T₁²T₀ - T₂³ + aT₀³`. Then

* `Z` is a curve over `k` and is **nonsingular** (`IsRegular`, [Stacks, Tag 02IS]);
* the coordinate projection `f : Z ⟶ 𝐏¹_k`, `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`, **exists**, and is
  pinned down by its inverse images of the standard opens;
* the extension `k(x) ⊆ k(x)(y)`, `y³ = x² + a`, named `curveFunctionField k a`, is purely
  inseparable of degree three;
* the genus of `Z` is `1` while the genus of `𝐏¹_k` is `0`, so the two differ.

So the genus is **not** preserved by a purely inseparable morphism of nonsingular projective
curves. Both genus values are computed, from [Stacks, Tag 0BYD] and from the vanishing of
`H¹(𝐏¹_k, 𝒪)`; nonsingularity is proved, from the derivation criterion of [Stacks, Tag 07PF];
and the morphism is constructed, by [Stacks, Tag 01MY]. The example in full — properness,
nonsingularity of `𝐏¹_k`, and the extension of function fields that the projection itself
induces — is `Stacks.Curves.InseparableGenus.planeCubicProjection_inseparable_genus_change`. -/
theorem isRegular_and_exists_coordProj_and_genus_ne {k : Type u} [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a)
    {Z : Scheme.{u}} [Nonempty Z]
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W = 1)
    (hI : idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin 3) k) i =
      Ideal.span {planeCubic k a}) :
    IsCurve k (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 2) ∧
      IsRegular Z ∧
      (∃ f : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k),
        ∀ (G : MvPolynomial (Fin 2) k) (d : ℕ),
          G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d → 0 < d →
          f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
              (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
            i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
              (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G)) ∧
      IsPurelyInseparable (RatFunc k) (curveFunctionField k a) ∧
      Module.finrank (RatFunc k) (curveFunctionField k a) = 3 ∧
      genus (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 2) = 1 ∧
      genus (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) = 0 ∧
      genus (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 2) ≠
        genus (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) := by
  obtain ⟨-, hcurve, hone, hline, hne, hins, hrank⟩ :=
    isCurve_and_genus_ne_genus_projectiveLine a ha i hno hdim hI
  exact ⟨hcurve, isRegular_of_idealOfClosedSubscheme_eq_span a ha i hI,
    exists_coordProj_hom a i hI, hins, hrank, hone, hline, hne⟩

end Stacks.Curves.InseparableGenus

end
