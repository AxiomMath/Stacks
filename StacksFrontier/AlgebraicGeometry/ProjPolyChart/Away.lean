module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The standard affine chart of `Proj` of a polynomial ring

Let `R` be a commutative ring and grade `R[T₀, …, Tₙ]` by total degree. For a variable `Tᵢ` the
degree-zero homogeneous localization `R[T]_{(Tᵢ)}` — Mathlib's
`HomogeneousLocalization.Away` — is the coordinate ring of the standard affine chart `D₊(Tᵢ)`
of `Proj R[T]`. This file identifies it with a polynomial ring in `n` variables over `R`, the
variables being the affine coordinates `T_j / T_i` for `j ≠ i`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`: the total-degree grading, named so that
  statements about it carry no local instance in their heads.
* `Stacks.AlgebraicGeometry.ProjPolyChart.chartHom`: the ring homomorphism
  `R[Y_j : j ≠ i] → R[T]_{(Tᵢ)}` sending `Y_j` to `T_j / T_i`.
* `Stacks.AlgebraicGeometry.ProjPolyChart.chartRetract`: the retraction, obtained by setting
  `Tᵢ = 1`.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`: the ring isomorphism
  `R[Y_j : j ≠ i] ≃+* R[T]_{(Tᵢ)}`.

## Implementation notes

Injectivity of `chartHom` is proved by exhibiting a retraction rather than by a direct
computation. The substitution `Tᵢ ↦ 1`, `T_j ↦ Y_j` is a ring homomorphism
`R[T] → R[Y_j : j ≠ i]` that sends `Tᵢ` to a unit, so it extends over the localization
`R[T][1/Tᵢ]`, into which `R[T]_{(Tᵢ)}` embeds by `HomogeneousLocalization.val`. On the fraction
`a / Tᵢ^k` the extension is the substitution applied to `a`, which is
`chartRetract_mk`; that identity is what makes the composite the identity on the generators.

Surjectivity is Mathlib's `HomogeneousLocalization.Away.span_mk_prod_pow_eq_top`: for a graded
ring generated over its degree-zero part by finitely many homogeneous elements, the
degree-zero localization at a homogeneous `f` is spanned, as a module over the degree-zero
part, by the fractions `(∏ vᵉ) / fᵃ`. Here the generators are the variables, all of degree one,
so a spanning fraction is `(∏_k T_k^{a_k}) / Tᵢ^a` with `∑_k a_k = a`; cancelling the `Tᵢ^{a_i}`
in the numerator exhibits it as the image of the monomial `∏_{j ≠ i} Y_j^{a_j}`. The span is
over the degree-zero part rather than over `R`, and the two agree because
`algebraMap R (R[T] 0)` is surjective: a polynomial homogeneous of degree zero is a constant.

The index type of the chart is the subtype `{j // j ≠ i}` rather than `Fin n`: no bijection with
`Fin n` is needed, and the subtype keeps the affine coordinate attached to the variable it comes
from.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))

/-- The grading of `R[T₀, …, Tₙ]` by total degree. -/
public abbrev polyGrading : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Each variable is homogeneous of degree one. -/
public theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ polyGrading R n 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _)

/-- Each variable is homogeneous of degree `1 • 1`, the shape `HomogeneousLocalization.Away.mk`
asks for with denominator exponent one. -/
public theorem X_mem_smul (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ polyGrading R n (1 • 1) := by
  simpa using X_mem_one R n j

/-- A constant is homogeneous of degree `0 • 1`, the shape `HomogeneousLocalization.Away.mk`
asks for with denominator exponent zero. -/
public theorem C_mem_zero (r : R) :
    (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) ∈ polyGrading R n (0 • 1) := by
  simp only [smul_eq_mul]
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)

/-- A polynomial homogeneous of degree zero is a constant: the structure map of the coefficient
ring into the degree-zero part is surjective. -/
public theorem exists_algebraMap_eq (r₀ : polyGrading R n 0) :
    ∃ r : R, algebraMap R (polyGrading R n 0) r = r₀ := by
  obtain ⟨y, hy⟩ := r₀
  have hy' : y ∈ (1 : Submodule R (MvPolynomial (Fin (n + 1)) R)) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]; exact hy
  rw [Submodule.mem_one] at hy'
  obtain ⟨r, hr⟩ := hy'
  exact ⟨r, Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap]; exact hr)⟩

/-- The polynomial ring is generated over its degree-zero part by the variables. -/
public theorem adjoin_range_X_eq_top :
    Algebra.adjoin (polyGrading R n 0) (Set.range (MvPolynomial.X : Fin (n + 1) →
      MvPolynomial (Fin (n + 1)) R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
      have h : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) =
          algebraMap (polyGrading R n 0) (MvPolynomial (Fin (n + 1)) R)
            ⟨MvPolynomial.C r, (MvPolynomial.mem_homogeneousSubmodule _ _).2
              (MvPolynomial.isHomogeneous_C _ _)⟩ := rfl
      rw [h]
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p j hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨j, rfl⟩)

/-- The coefficient ring maps into the chart, as the composite of the identification of the
coefficient ring with the degree-zero part and the structure map of the localization. -/
public def coeffToAway : R →+* Away (polyGrading R n) (MvPolynomial.X i) :=
  (algebraMap (polyGrading R n 0) (Away (polyGrading R n) (MvPolynomial.X i))).comp
    (algebraMap R (polyGrading R n 0))

/-- On the coefficient ring the chart map is the fraction with denominator `Tᵢ^0`. -/
public theorem coeffToAway_eq_mk (r : R) :
    coeffToAway R n i r =
      Away.mk (polyGrading R n) (X_mem_one R n i) 0 (MvPolynomial.C r) (C_mem_zero R n r) := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk]
  have hc : ((algebraMap R (polyGrading R n 0)) r : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C r := by
    rw [SetLike.GradeZero.coe_algebraMap]; simp [MvPolynomial.algebraMap_eq]
  simp only [coeffToAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq]
  rw [show (HomogeneousLocalization.fromZeroRingHom (polyGrading R n)
      (Submonoid.powers (MvPolynomial.X i)) ((algebraMap R (polyGrading R n 0)) r)).val =
      Localization.mk ((algebraMap R (polyGrading R n 0)) r : MvPolynomial (Fin (n + 1)) R) 1
      from rfl, hc]
  congr 1

/-- The affine coordinate `T_j / T_i`. -/
public def chartCoord (j : {j : Fin (n + 1) // j ≠ i}) :
    Away (polyGrading R n) (MvPolynomial.X i) :=
  Away.mk (polyGrading R n) (X_mem_one R n i) 1 (MvPolynomial.X j.1) (X_mem_smul R n j.1)

/-- The comparison `R[Y_j : j ≠ i] → R[T]_{(Tᵢ)}`, sending `Y_j` to the affine coordinate
`T_j / T_i`. -/
public def chartHom :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} R →+* Away (polyGrading R n) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom (coeffToAway R n i) (chartCoord R n i)

/-- The comparison `chartHom` sends a constant `C r` to the image of `r` in the localization. -/
@[simp] public theorem chartHom_C (r : R) :
    chartHom R n i (MvPolynomial.C r) = coeffToAway R n i r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- The comparison `chartHom` sends the variable `Y_j` to the affine coordinate `T_j / T_i`. -/
@[simp] public theorem chartHom_X (j : {j : Fin (n + 1) // j ≠ i}) :
    chartHom R n i (MvPolynomial.X j) = chartCoord R n i j :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The substitution `Tᵢ ↦ 1`, `T_j ↦ Y_j`. -/
public def setOneHom :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial {j : Fin (n + 1) // j ≠ i} R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩)

/-- The substitution `setOneHom` sends `Tᵢ` to `1`. -/
@[simp] public theorem setOneHom_X_self : setOneHom R n i (MvPolynomial.X i) = 1 := by
  simp [setOneHom]

/-- The substitution `setOneHom` sends `T_j` to `Y_j` for `j ≠ i`. -/
@[simp] public theorem setOneHom_X_ne (j : {j : Fin (n + 1) // j ≠ i}) :
    setOneHom R n i (MvPolynomial.X j.1) = MvPolynomial.X j := by
  simp only [setOneHom, MvPolynomial.eval₂Hom_X']
  exact dite_eq_right j.2

/-- The substitution `setOneHom` fixes constants. -/
@[simp] public theorem setOneHom_C (r : R) :
    setOneHom R n i (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- The substitution sends `Tᵢ` to a unit, so it extends over the localization. -/
public theorem isUnit_setOneHom_X : IsUnit (setOneHom R n i (MvPolynomial.X i)) := by
  rw [setOneHom_X_self]; exact isUnit_one

/-- The retraction of the chart comparison: the extension of the substitution `Tᵢ ↦ 1` over the
localization at the powers of `Tᵢ`, restricted along the embedding of the degree-zero
homogeneous localization. -/
public def chartRetract :
    Away (polyGrading R n) (MvPolynomial.X i) →+*
      MvPolynomial {j : Fin (n + 1) // j ≠ i} R :=
  (Localization.awayLift (setOneHom R n i) (MvPolynomial.X i) (isUnit_setOneHom_X R n i)).comp
    (algebraMap (Away (polyGrading R n) (MvPolynomial.X i))
      (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))))

/-- On a fraction the retraction is the substitution applied to the numerator: the denominator
is a power of `Tᵢ`, which the substitution sends to `1`. -/
public theorem chartRetract_mk (k : ℕ) (a : MvPolynomial (Fin (n + 1)) R)
    (ha : a ∈ polyGrading R n (k • 1)) :
    chartRetract R n i (Away.mk (polyGrading R n) (X_mem_one R n i) k a ha) =
      setOneHom R n i a := by
  set θ := Localization.awayLift (setOneHom R n i) (MvPolynomial.X i) (isUnit_setOneHom_X R n i)
  have key : (Away.mk (polyGrading R n) (X_mem_one R n i) k a ha).val *
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.X i ^ k) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) _ a := by
    rw [Away.val_mk, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have h2 := congrArg θ key
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    map_pow, setOneHom_X_self, one_pow, mul_one] at h2
  simpa [chartRetract, HomogeneousLocalization.algebraMap_apply] using h2

/-- The retraction is a retraction. -/
public theorem chartRetract_comp_chartHom :
    (chartRetract R n i).comp (chartHom R n i) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, chartHom_C, coeffToAway_eq_mk, chartRetract_mk, setOneHom_C,
      RingHom.id_apply]
  · rw [RingHom.comp_apply, chartHom_X, chartCoord, chartRetract_mk, setOneHom_X_ne,
      RingHom.id_apply]

/-- The chart comparison is injective. -/
public theorem chartHom_injective : Function.Injective (chartHom R n i) := by
  intro x y h
  have h' := congrArg (chartRetract R n i) h
  simpa only [← RingHom.comp_apply, chartRetract_comp_chartHom, RingHom.id_apply] using h'

/-- A spanning fraction of the chart is the image of a monomial: cancelling the power of `Tᵢ`
that occurs in the numerator turns `(∏_k T_k^{a_k}) / Tᵢ^a` with `∑_k a_k = a` into
`∏_{j ≠ i} (T_j / T_i)^{a_j}`. -/
public theorem chartHom_prod_X (ak : Fin (n + 1) → ℕ) (a : ℕ) (hsum : ∑ k, ak k = a)
    (ha : (∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ ak k) ∈
      polyGrading R n (a • 1)) :
    chartHom R n i (∏ j : {j : Fin (n + 1) // j ≠ i}, MvPolynomial.X j ^ ak j.1) =
      Away.mk (polyGrading R n) (X_mem_one R n i) a
        (∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ ak k) ha := by
  have hprod : (∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ ak k) =
      MvPolynomial.X i ^ ak i *
        ∏ j : {j : Fin (n + 1) // j ≠ i},
          (MvPolynomial.X j.1 : MvPolynomial (Fin (n + 1)) R) ^ ak j.1 := by
    exact Fintype.prod_eq_mul_prod_subtype_ne
      (fun k => (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ ak k) i
  have hsum' : ak i + ∑ j : {j : Fin (n + 1) // j ≠ i}, ak j.1 = a := by
    rw [← hsum]
    exact (Fintype.sum_eq_add_sum_subtype_ne ak i).symm
  rw [map_prod]
  simp only [map_pow, chartHom_X, chartCoord]
  rw [HomogeneousLocalization.ext_iff_val]
  rw [show (∏ j : {j : Fin (n + 1) // j ≠ i},
        Away.mk (polyGrading R n) (X_mem_one R n i) 1 (MvPolynomial.X j.1) (X_mem_smul R n j.1)
          ^ ak j.1).val
      = algebraMap (Away (polyGrading R n) (MvPolynomial.X i))
          (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))
          (∏ j : {j : Fin (n + 1) // j ≠ i},
            Away.mk (polyGrading R n) (X_mem_one R n i) 1 (MvPolynomial.X j.1)
              (X_mem_smul R n j.1) ^ ak j.1) from
      (HomogeneousLocalization.algebraMap_apply _).symm, map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow]
  rw [hprod, ← hsum']
  simp only [pow_one, Finset.prod_pow_eq_pow_sum]
  ring

/-- The chart comparison is surjective. -/
public theorem chartHom_surjective : Function.Surjective (chartHom R n i) := by
  intro z
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
      (𝒜 := polyGrading R n) (X_mem_one R n i) (ι' := Fin (n + 1)) MvPolynomial.X
      (adjoin_range_X_eq_top R n) (fun _ => 1) (fun j => X_mem_one R n j)
  have hz : z ∈ (⊤ : Submodule (polyGrading R n 0)
      (Away (polyGrading R n) (MvPolynomial.X i))) := Submodule.mem_top
  rw [← hspan] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, ak, hai, rfl⟩ := hx
      exact ⟨∏ j : {j : Fin (n + 1) // j ≠ i}, MvPolynomial.X j ^ ak j.1,
        chartHom_prod_X R n i ak b (by simpa using hai) _⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | smul r₀ x hx ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨r, hr⟩ := exists_algebraMap_eq R n r₀
      refine ⟨MvPolynomial.C r * p, ?_⟩
      rw [map_mul, chartHom_C, hp, Algebra.smul_def, ← hr]
      rfl

/-- **The standard affine chart of `Proj` of a polynomial ring.** The degree-zero homogeneous
localization of `R[T₀, …, Tₙ]` at the variable `Tᵢ` is the polynomial ring over `R` on the
affine coordinates `T_j / T_i`, `j ≠ i`. -/
public def chartEquiv :
    MvPolynomial {j : Fin (n + 1) // j ≠ i} R ≃+*
      Away (polyGrading R n) (MvPolynomial.X i) :=
  RingEquiv.ofBijective (chartHom R n i) ⟨chartHom_injective R n i, chartHom_surjective R n i⟩

/-- The chart isomorphism `chartEquiv` acts on elements as the comparison `chartHom`. -/
@[simp] public theorem chartEquiv_apply (p : MvPolynomial {j : Fin (n + 1) // j ≠ i} R) :
    chartEquiv R n i p = chartHom R n i p :=
  rfl

end Stacks.AlgebraicGeometry.ProjPolyChart

end
