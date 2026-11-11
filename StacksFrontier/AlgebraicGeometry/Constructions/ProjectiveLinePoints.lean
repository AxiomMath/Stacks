module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjPointOfRingHom

/-!
# Points of the projective line with values in a ring

Let `R` be a commutative ring. A pair `(x, y)` of elements of `R` determines the evaluation
`ℤ[T₀, T₁] → R`, `T₀ ↦ x`, `T₁ ↦ y`; when one of `x`, `y` is a unit, it gives an `R`-valued point
`[x : y]` of the integral model `ℙ¹_ℤ = Proj ℤ[T₀, T₁]` of the projective line, read on the
standard chart where that coordinate is invertible. We record the two families of points
`[1 : a]` and `[b : 1]`, their naturality in `R`, injectivity of `a ↦ [1 : a]`, and the gluing
relation `[1 : u] = [u⁻¹ : 1]` for a unit `u`.

## Main definitions

* `AlgebraicGeometry.ProjectiveLine.evalCoords`: the evaluation `ℤ[T₀, T₁] → R` at `(x, y)`.
* `AlgebraicGeometry.ProjectiveLine.pointOne`: the point `[1 : a]` of `ℙ¹_ℤ` with values in `R`.
* `AlgebraicGeometry.ProjectiveLine.pointInf`: the point `[b : 1]` of `ℙ¹_ℤ` with values in `R`.

## Main results

* `AlgebraicGeometry.ProjectiveLine.SpecMap_comp_pointOne`,
  `AlgebraicGeometry.ProjectiveLine.SpecMap_comp_pointInf`: the points are natural in `R`.
* `AlgebraicGeometry.ProjectiveLine.pointOne_injective`: `[1 : a] = [1 : a']` only if `a = a'`.
* `AlgebraicGeometry.ProjectiveLine.pointOne_eq_pointInf`: `[1 : u] = [u⁻¹ : 1]` for a unit `u`.
* `AlgebraicGeometry.ProjectiveLine.pointOne_one`: `[1 : 1]` lies on both charts.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- The variables `T₀`, `T₁` are homogeneous of degree one. -/
theorem X_mem_homogeneousSubmodule (i : Fin (1 + 1)) :
    (X i : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ)) ∈
      homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ) 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)

/-- The evaluation `ℤ[T₀, T₁] → R` sending `T₀` to `x` and `T₁` to `y`. -/
def evalCoords (x y : R) : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* R :=
  eval₂Hom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) ![x, y]

/-- The evaluation `evalCoords R x y` sends `T₀` to `x`. -/
@[simp] theorem evalCoords_X_zero (x y : R) : evalCoords R x y (X 0) = x := by
  simp [evalCoords]

/-- The evaluation `evalCoords R x y` sends `T₁` to `y`. -/
@[simp] theorem evalCoords_X_one (x y : R) : evalCoords R x y (X 1) = y := by
  simp [evalCoords]

/-- The evaluation `evalCoords` is natural in the ring of values. -/
theorem comp_evalCoords {R' : Type u} [CommRing R'] (g : R →+* R') (x y : R) :
    g.comp (evalCoords R x y) = evalCoords R' (g x) (g y) := by
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [evalCoords]
  · fin_cases i <;> simp [evalCoords]

/-- A homogeneous polynomial of degree `n` evaluated at `(μ x, μ y)` is `μ ^ n` times its value
at `(x, y)`. -/
theorem evalCoords_mul_mul_of_mem (μ x y : R) {n : ℕ}
    {p : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ)}
    (hp : p ∈ homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ) n) :
    evalCoords R (μ * x) (μ * y) p = μ ^ n * evalCoords R x y p := by
  have hv : (![μ * x, μ * y] : Fin (1 + 1) → R) = fun i => μ * ![x, y] i := by
    funext i
    fin_cases i <;> rfl
  simp only [evalCoords, coe_eval₂Hom]
  rw [hv, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ i ∈ s.support, s i = n := by
    have := (mem_homogeneousSubmodule _ _).1 hp (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The point `[1 : a]` of the integral model `ℙ¹_ℤ` of the projective line, with values in `R`:
its homogeneous coordinates are `T₀ = 1` and `T₁ = a`. -/
def pointOne (a : R) : Spec (.of R) ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Stacks.ProjPoint.point (homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ)) (evalCoords R 1 a)
    (X 0) (X_mem_homogeneousSubmodule 0) one_pos (by rw [evalCoords_X_zero]; exact isUnit_one)

/-- The point `[b : 1]` of the integral model `ℙ¹_ℤ` of the projective line, with values in `R`:
its homogeneous coordinates are `T₀ = b` and `T₁ = 1`. -/
def pointInf (b : R) : Spec (.of R) ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Stacks.ProjPoint.point (homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ)) (evalCoords R b 1)
    (X 1) (X_mem_homogeneousSubmodule 1) one_pos (by rw [evalCoords_X_one]; exact isUnit_one)

/-- The points `[1 : a]` are natural in the ring of values. -/
theorem SpecMap_comp_pointOne {R' : Type u} [CommRing R'] (g : R →+* R') (a : R) :
    Spec.map (CommRingCat.ofHom g) ≫ pointOne R a = pointOne R' (g a) :=
  (Stacks.ProjPoint.SpecMap_comp_point _ g _ _ _ _ _).trans
    (Stacks.ProjPoint.point_congr_ringHom _ (by rw [comp_evalCoords, map_one]) _ _ _ _ _)

/-- The points `[b : 1]` are natural in the ring of values. -/
theorem SpecMap_comp_pointInf {R' : Type u} [CommRing R'] (g : R →+* R') (b : R) :
    Spec.map (CommRingCat.ofHom g) ≫ pointInf R b = pointInf R' (g b) :=
  (Stacks.ProjPoint.SpecMap_comp_point _ g _ _ _ _ _).trans
    (Stacks.ProjPoint.point_congr_ringHom _ (by rw [comp_evalCoords, map_one]) _ _ _ _ _)

variable {R}

/-- The points `[1 : a]` are distinct for distinct `a`. -/
theorem pointOne_injective {a a' : R} (h : pointOne R a = pointOne R a') : a = a' := by
  have h' := congrArg (fun φ => φ (HomogeneousLocalization.Away.mk
      (homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ)) (X_mem_homogeneousSubmodule 0) 1 (X 1)
      (by simpa using X_mem_homogeneousSubmodule 1)))
    (Stacks.ProjPoint.awayEval_eq_of_point_eq _ _ _ _ _ h)
  simp only [Stacks.ProjPoint.awayEval_mk, evalCoords_X_one] at h'
  have hone : ∀ c : R, ∀ hu : IsUnit (evalCoords R 1 c (X 0)), (↑(hu.unit⁻¹ ^ 1) : R) = 1 :=
    fun c hu => (Stacks.ProjPoint.eq_val_inv_pow_of_mul_eq_one hu.unit 1 (by simp)).symm
  rwa [hone, hone, mul_one, mul_one] at h'

/-- **Gluing of the two charts**: for a unit `u`, the points `[1 : u]` and `[u⁻¹ : 1]` agree. -/
theorem pointOne_eq_pointInf (u : Rˣ) : pointOne R (u : R) = pointInf R (↑u⁻¹ : R) := by
  have hu : IsUnit (evalCoords R 1 (u : R) (X 1)) := by
    rw [evalCoords_X_one]
    exact u.isUnit
  have hu' : IsUnit (evalCoords R (↑u⁻¹ * 1) (↑u⁻¹ * ↑u) (X 1)) := by
    rw [evalCoords_X_one, Units.inv_mul]
    exact isUnit_one
  refine (Stacks.ProjPoint.point_indep _ _ _ (X_mem_homogeneousSubmodule 1) one_pos one_pos _
    hu).trans ((Stacks.ProjPoint.point_eq_of_scale _ u⁻¹
      (fun n p hp => evalCoords_mul_mul_of_mem R _ _ _ hp) _ _ one_pos hu hu').trans
    (Stacks.ProjPoint.point_congr_ringHom _ ?_ _ _ _ _ _))
  rw [mul_one, Units.inv_mul]

/-- The point `[1 : 1]` lies on both standard charts. -/
theorem pointOne_one : pointOne R 1 = pointInf R 1 := by
  simpa using pointOne_eq_pointInf (1 : Rˣ)

end AlgebraicGeometry.ProjectiveLine
