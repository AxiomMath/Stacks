module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharPowerSeries
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The local factor `det(1 - φ T)` and the characteristic polynomial

For an endomorphism `φ` of a finite dimensional vector space `V` over a field `K`, the local
factor `det(1 - φ T) ∈ K⟦T⟧` (`Stacks.EtaleCohomology.charPowerSeries φ 1`) is the reverse of the
characteristic polynomial of `φ`. The reverse forgets the zero eigenvalues, but when `φ` is
invertible it has degree `dim V`. So two invertible endomorphisms with the same local factor have
the same characteristic polynomial.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_one_eq_reverse_charpoly`:
  `det(1 - φ T) = reverse(χ_φ)`.
* `Stacks.EtaleCohomology.charpoly_eq_of_charPowerSeries_eq`: invertible endomorphisms with the
  same local factor have the same characteristic polynomial.
-/

@[expose] public noncomputable section

open Module Polynomial

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **`det(1 - φ T)` is the reverse of the characteristic polynomial of `φ`.** -/
theorem charPowerSeries_one_eq_reverse_charpoly (φ : V →ₗ[K] V) :
    charPowerSeries φ 1 = ((LinearMap.charpoly φ).reverse : PowerSeries K) := by
  classical
  let b := Module.finBasis K V
  rw [charPowerSeries_eq_localCharSeries b, ← LinearMap.charpoly_toMatrix φ b,
    Matrix.reverse_charpoly, localCharSeries, localCharMatrix, Matrix.charpolyRev,
    ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply, apply_ite]
  ring

/-- The reverse of the characteristic polynomial of an invertible endomorphism has degree the
dimension. -/
theorem natDegree_reverse_charpoly_of_det_ne_zero (φ : V →ₗ[K] V) (hφ : LinearMap.det φ ≠ 0) :
    (LinearMap.charpoly φ).reverse.natDegree = finrank K V := by
  have h0 : (LinearMap.charpoly φ).coeff 0 ≠ 0 := fun h ↦
    hφ (by rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero])
  rw [Polynomial.reverse_natDegree, LinearMap.charpoly_natDegree,
    natTrailingDegree_eq_zero.2 (Or.inr h0), Nat.sub_zero]

/-- **Invertible endomorphisms with the same local factor `det(1 - φ T)` have the same
characteristic polynomial.** -/
theorem charpoly_eq_of_charPowerSeries_eq (φ : V →ₗ[K] V) (ψ : W →ₗ[K] W)
    (hφ : LinearMap.det φ ≠ 0) (hψ : LinearMap.det ψ ≠ 0)
    (h : charPowerSeries φ 1 = charPowerSeries ψ 1) :
    LinearMap.charpoly φ = LinearMap.charpoly ψ := by
  rw [charPowerSeries_one_eq_reverse_charpoly, charPowerSeries_one_eq_reverse_charpoly] at h
  have hr := Polynomial.coe_inj.1 h
  have hd : (LinearMap.charpoly φ).natDegree = (LinearMap.charpoly ψ).natDegree := by
    rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree,
      ← natDegree_reverse_charpoly_of_det_ne_zero φ hφ,
      ← natDegree_reverse_charpoly_of_det_ne_zero ψ hψ, hr]
  have key (p : K[X]) : p.reverse.reflect p.natDegree = p := by
    rw [Polynomial.reverse, reflect_reflect]
  rw [← key (LinearMap.charpoly φ), ← key (LinearMap.charpoly ψ), hr, hd]

end Stacks.EtaleCohomology
