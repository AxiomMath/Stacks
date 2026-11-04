module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionEulerProduct

/-!
# The local factor of an endomorphism

The local factor `det(1 - φ T ^ d)` of an endomorphism `φ` of a `Λ`-module is the determinant of
`1 - T ^ d • φ` after base change to the power series ring `Λ⟦T⟧`. In any finite basis it is the
local factor of the matrix of `φ`.

## Main definitions

* `Stacks.EtaleCohomology.charPowerSeries`: the local factor `det(1 - φ T ^ d)` of an
  endomorphism.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_eq_localCharSeries`: in a finite basis it is the local
  factor of the matrix of the endomorphism.
* `Stacks.EtaleCohomology.constantCoeff_charPowerSeries` and
  `Stacks.EtaleCohomology.X_pow_dvd_charPowerSeries_sub_one`: for a finite free module the local
  factor has constant coefficient `1` when `d ≠ 0`, and is congruent to `1` modulo `T ^ d`.
-/

@[expose] public noncomputable section

open Module CategoryTheory
open scoped TensorProduct

universe u v w

namespace Stacks.EtaleCohomology

variable {Λ : Type v} [CommRing Λ] {M : Type w} [AddCommGroup M] [Module Λ M]

/-- The local factor `det(1 - φ T ^ d)` of an endomorphism `φ` of a `Λ`-module, as an element of
`Λ⟦T⟧`: the determinant of `1 - T ^ d • φ` after base change to the power series ring. -/
public def charPowerSeries (φ : M →ₗ[Λ] M) (d : ℕ) : PowerSeries Λ :=
  LinearMap.det (1 - (PowerSeries.X ^ d : PowerSeries Λ) • φ.baseChange (PowerSeries Λ))

/-- In a finite basis the local factor of an endomorphism is the local factor of its matrix. -/
public theorem charPowerSeries_eq_localCharSeries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι Λ M) (φ : M →ₗ[Λ] M) (d : ℕ) :
    charPowerSeries φ d = localCharSeries (LinearMap.toMatrix b b φ) d := by
  rw [charPowerSeries, ← LinearMap.det_toMatrix (Algebra.TensorProduct.basis (PowerSeries Λ) b),
    localCharSeries, localCharMatrix]
  congr 1
  have hb := LinearMap.toMatrix_baseChange (PowerSeries Λ) φ b b
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix_apply, LinearMap.sub_apply, map_sub, Finsupp.sub_apply,
    Module.End.one_apply, LinearMap.smul_apply, map_smul, Finsupp.smul_apply,
    ← LinearMap.toMatrix_apply, hb]
  simp [Matrix.one_apply, Basis.repr_self, Finsupp.single_apply, eq_comm, Matrix.map_apply]

/-- The local factor of an endomorphism of a finite free module is congruent to `1` modulo
`T ^ d`. -/
public theorem X_pow_dvd_charPowerSeries_sub_one [Module.Finite Λ M] [Module.Free Λ M]
    (φ : M →ₗ[Λ] M) (d : ℕ) :
    (PowerSeries.X : PowerSeries Λ) ^ d ∣ charPowerSeries φ d - 1 := by
  classical
  rw [charPowerSeries_eq_localCharSeries (Module.Free.chooseBasis Λ M) φ d]
  exact X_pow_dvd_localCharSeries_sub_one _ d

/-- For `d ≠ 0` the local factor of an endomorphism of a finite free module has constant
coefficient `1`. -/
public theorem constantCoeff_charPowerSeries [Module.Finite Λ M] [Module.Free Λ M]
    (φ : M →ₗ[Λ] M) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.constantCoeff (charPowerSeries φ d) = 1 := by
  classical
  rw [charPowerSeries_eq_localCharSeries (Module.Free.chooseBasis Λ M) φ d]
  exact constantCoeff_localCharSeries _ hd

end Stacks.EtaleCohomology

end
