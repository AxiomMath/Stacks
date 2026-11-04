/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional

/-!
# Euler characteristics of tensor powers on a proper curve (Riemann–Roch, Stacks 0AYX)

Let `X` be a proper scheme of dimension at most one over a field `k`. For invertible modules `ℳ`
and `𝒩` the Euler characteristic is additive in the degree: `χ(ℳ ⊗ 𝒩) = χ(ℳ) + χ(𝒩) - χ(𝒪_X)`,
which is the invertible case of Stacks 0AYX
(`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`).
Hence for every integer `m`, `χ(ℒ^{⊗ m}) = m (χ(ℒ) - χ(𝒪_X)) + χ(𝒪_X)`. These are the two
Riemann–Roch computations of the proof of Stacks 0DSQ.

## Main results

* `AlgebraicGeometry.CurveTensorPowerEuler.eulerSum_tensorSheaf`.
* `AlgebraicGeometry.CurveTensorPowerEuler.eulerSum_tensorPowModule`.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CurveTensorPowerEuler

open ProperFlatFibreEulerCharacteristic Stacks.Ample

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- **`χ(ℳ ⊗ 𝒩) = χ(ℳ) + χ(𝒩) - χ(𝒪_X)`** for invertible `ℳ`, `𝒩` on a proper scheme of
dimension at most one over a field (Stacks 0AYX). -/
theorem eulerSum_tensorSheaf (M N : X.Modules) [IsInvertibleModule X M] [IsInvertibleModule X N] :
    eulerSum k f (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).obj M).obj N) =
      eulerSum k f M + eulerSum k f N - eulerSum k f (unitModule X) := by
  have hMN := Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
    X.ringCatSheaf.property M N
  have h := invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim M N
    ‹_› ‹_› hMN
  simp only [invertibleCurveDegree] at h
  unfold eulerSum
  linarith

include hdim in
/-- **`χ(ℒ^{⊗ m}) = m (χ(ℒ) - χ(𝒪_X)) + χ(𝒪_X)`** for an invertible `ℒ` on a proper scheme of
dimension at most one over a field and every integer `m` (Stacks 0AYX). -/
theorem eulerSum_tensorPowModule (L : X.Modules) [IsInvertibleModule X L] (m : ℤ) :
    eulerSum k f (tensorPowModule X L m) =
      m * (eulerSum k f L - eulerSum k f (unitModule X)) + eulerSum k f (unitModule X) := by
  have hstep : ∀ n : ℤ, eulerSum k f (tensorPowModule X L (n + 1)) =
      eulerSum k f (tensorPowModule X L n) + eulerSum k f L - eulerSum k f (unitModule X) := by
    intro n
    rw [← eulerSum_congr k f (tensorPowModuleAddIso X L n 1),
      eulerSum_tensorSheaf k f hdim, eulerSum_congr k f (tensorPowModuleOneIso X L)]
  have h0 : eulerSum k f (tensorPowModule X L 0) = eulerSum k f (unitModule X) :=
    eulerSum_congr k f (tensorPowModuleZeroIso X L)
  induction m using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    rw [hstep, ih]
    ring
  | pred n ih =>
    have := hstep (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring, ih] at this
    linarith

end AlgebraicGeometry.CurveTensorPowerEuler

end
