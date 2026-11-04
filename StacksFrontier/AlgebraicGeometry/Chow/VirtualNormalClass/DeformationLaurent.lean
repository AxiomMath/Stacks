module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.GlobalParameter
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.BaseIdeal

/-!
# Inverting `t⁻¹` on the deformation space gives the Laurent polynomials

Let `ℐ` be a quasi-coherent ideal sheaf on a scheme `X` and `D = Spec_X(𝒪_X[t⁻¹, ℐt])` its
deformation space. Over an open `W` of `X` the homogeneous sections of the extended Rees algebra
embed into the Laurent polynomials `Γ(X, W)[T, T⁻¹]`
(`Stacks.Deformation.extReesLaurent`), carrying `t⁻¹` to `T⁻¹`. This embedding is the
localization at `t⁻¹`: every Laurent polynomial becomes, after multiplication by a high enough
power of `T⁻¹`, a polynomial in `T⁻¹` with coefficients in `Γ(X, W)`, and those lie in the
nonpositive degrees of the extended Rees algebra, which are `𝒪_X` itself. Geometrically: the
complement of the special fibre `t⁻¹ = 0` of `D` is `X × 𝐆_m`.

## Main results

* `Stacks.Deformation.extReesLaurent_paramTotal`: the Laurent embedding sends `t⁻¹` to `T⁻¹`.
* `Stacks.Deformation.isLocalization_chartLaurent`: on an affine chart, the Laurent embedding is
  the localization at `t⁻¹`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeSpec

universe u

namespace Stacks.Deformation

variable {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.Opens)

/-- The parameter `t⁻¹` among the homogeneous sections over `W`. -/
def paramTotal : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W) :=
  (extReesGradedAlgebra I).toPresheafGradedAlgebra.incl (-1) (paramPiece I W)

/-- A function on `W`, as a homogeneous section of degree zero. -/
def constTotal (a : Γ(X, W)) : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W) :=
  (extReesGradedAlgebra I).toPresheafGradedAlgebra.incl 0
    ((show X.ringCatSheaf.obj.obj (op W) from a) • (extReesOne I).eval (op W))

/-- **`t⁻¹` goes to `T⁻¹`.** -/
theorem extReesLaurent_paramTotal :
    extReesLaurent I W (paramTotal I W) = LaurentPolynomial.T (-1) := by
  refine (extReesLaurent_incl I W (-1) (paramPiece I W)).trans ?_
  rw [extReesAmbient_paramPiece, map_one, one_mul]

/-- A function on `W` goes to the corresponding constant. -/
theorem extReesLaurent_constTotal (a : Γ(X, W)) :
    extReesLaurent I W (constTotal I W a) = LaurentPolynomial.C a := by
  refine (extReesLaurent_incl I W 0 _).trans ?_
  rw [extReesAmbient_smul, extReesAmbient_extReesOne, mul_one, LaurentPolynomial.T_zero, mul_one]
  rfl

/-- After multiplication by a high power of `T⁻¹`, every Laurent polynomial lies in the image of
the Laurent embedding. -/
theorem exists_mul_T_neg_mem (f : LaurentPolynomial Γ(X, W)) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∃ x, extReesLaurent I W x = f * LaurentPolynomial.T (-(M : ℤ)) := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨N₁, h₁⟩ := hp
    obtain ⟨N₂, h₂⟩ := hq
    refine ⟨max N₁ N₂, fun M hM => ?_⟩
    obtain ⟨x₁, hx₁⟩ := h₁ M (le_of_max_le_left hM)
    obtain ⟨x₂, hx₂⟩ := h₂ M (le_of_max_le_right hM)
    exact ⟨x₁ + x₂, by rw [map_add, hx₁, hx₂, add_mul]⟩
  | C_mul_T n a =>
    refine ⟨n.toNat, fun M hM =>
      ⟨constTotal I W a * paramTotal I W ^ (M - n.toNat + (n.toNat - n).toNat), ?_⟩⟩
    rw [map_mul, map_pow, extReesLaurent_constTotal, extReesLaurent_paramTotal,
      LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add]
    congr 2
    omega

/-- The functions on the chart `π⁻¹W` of the deformation space, `W` affine, embedded into the
Laurent polynomials over `Γ(X, W)`. -/
def chartLaurent (W : X.affineOpens) :
    Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1) →+* LaurentPolynomial Γ(X, W.1) :=
  (extReesLaurent I W.1).comp
    (RingEquiv.ofBijective (chartRingHom I W.1) (bijective_chartRingHom I W)).symm.toRingHom

/-- On a homogeneous section `x` over `W`, `chartLaurent` agrees with the Laurent embedding of
`x`. -/
theorem chartLaurent_chartRingHom (W : X.affineOpens)
    (x : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W.1)) :
    chartLaurent I W (chartRingHom I W.1 x) = extReesLaurent I W.1 x := by
  simp only [chartLaurent, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact congrArg _ ((RingEquiv.ofBijective _ (bijective_chartRingHom I W)).symm_apply_apply x)

/-- `t⁻¹` on the chart goes to `T⁻¹`. -/
theorem chartLaurent_paramChartOf (W : X.affineOpens) :
    chartLaurent I W (paramChartOf I W.1) = LaurentPolynomial.T (-1) :=
  (chartLaurent_chartRingHom I W (paramTotal I W.1)).trans (extReesLaurent_paramTotal I W.1)

/-- A power of `t⁻¹` on the chart goes to the corresponding power of `T⁻¹`. -/
private theorem chartLaurent_paramChartOf_pow (W : X.affineOpens) (n : ℕ) :
    chartLaurent I W (paramChartOf I W.1 ^ n) = LaurentPolynomial.T (-(n : ℤ)) := by
  rw [map_pow, chartLaurent_paramChartOf, LaurentPolynomial.T_pow, mul_neg_one]

/-- **The functions on the chart `π⁻¹W` with `t⁻¹` inverted are the Laurent polynomials.** -/
theorem isLocalization_chartLaurent (W : X.affineOpens) :
    letI := (chartLaurent I W).toAlgebra
    IsLocalization.Away (paramChartOf I W.1) (LaurentPolynomial Γ(X, W.1)) := by
  let := (chartLaurent I W).toAlgebra
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨_, ⟨n, rfl⟩⟩ := y
    change IsUnit (chartLaurent I W (paramChartOf I W.1 ^ n))
    rw [chartLaurent_paramChartOf_pow]
    exact LaurentPolynomial.isUnit_T _
  · obtain ⟨N, hN⟩ := exists_mul_T_neg_mem I W.1 z
    obtain ⟨x, hx⟩ := hN N le_rfl
    refine ⟨(chartRingHom I W.1 x, ⟨paramChartOf I W.1 ^ N, ⟨N, rfl⟩⟩), ?_⟩
    change z * chartLaurent I W (paramChartOf I W.1 ^ N) = chartLaurent I W (chartRingHom I W.1 x)
    rw [chartLaurent_chartRingHom, hx, chartLaurent_paramChartOf_pow]
  · refine ⟨1, ?_⟩
    have hinj : Function.Injective (chartLaurent I W) :=
      (extReesLaurent_injective I W.1).comp (RingEquiv.ofBijective (chartRingHom I W.1)
        (bijective_chartRingHom I W)).symm.injective
    rw [hinj h]

/-- The structure map `Γ(X, W) ⟶ Γ(π⁻¹W)` followed by the Laurent embedding is the inclusion of
constants. -/
theorem chartLaurent_app (W : X.affineOpens) (g : Γ(X, W.1)) :
    chartLaurent I W (((deformationSpaceToBase I).app W.1).hom g) = LaurentPolynomial.C g := by
  rw [deformationSpaceToBase_app_eq_chartIncl, ← chartRingHom_incl, chartLaurent_chartRingHom]
  refine (extReesLaurent_incl I W.1 0 _).trans ?_
  rw [LaurentPolynomial.T_zero, mul_one]
  exact congrArg LaurentPolynomial.C (extReesAmbient_extReesOfMem I W 0 g (by simp))

end Stacks.Deformation

end
