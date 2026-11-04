module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiPullbackLeg

/-!
# The homogeneous-section map on a chart, for the adjoint transpose

Under the chart identification `𝒪(n)|_{chart} ≅ 𝒪_{Proj Γ(U, 𝒜)}(n)` on an affine open `U` of the
base, the homogeneous-section map `ψ_n : 𝒜_n ⟶ π_*𝒪(n)` of [Stacks, Tag 01NR] is the absolute
section map `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of [Stacks, Tag 01MP]
(`...RelativeProjTwists.TwistData.ψ_chart`). This file states the same description for the
adjoint transpose `...TwistData.psiTransposeNat : π^*𝒜_n ⟶ 𝒪(n)`.

## Main results

* `...RelativeProjTwists.TwistData.psiTransposeNat_chart`: on the chart of an affine open `U` of
  the base and in a natural degree `n`, the absolute global section of `𝒪_{Proj Γ(U, 𝒜)}(n)`
  attached to a section of `𝒜_n` over `U` is carried by the chart identification to the value of
  the transpose on `π⁻¹U` at that section's image under the unit of `π^* ⊣ π_*`.
* `...RelativeProjTwists.TwistData.psiTranspose_chart`: the same for the integer-indexed
  `...TwistData.psiTranspose`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.ProjTwistSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

namespace TwistData

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)

/-- Let `U` be an affine open of the base, `n` a natural number and `a` a section of `𝒜_n` over
`U`. The absolute global section of `𝒪_{Proj Γ(U, 𝒜)}(n)` that `a` defines by [Stacks, Tag 01MP]
is carried by the chart identification of `...RelativeProjTwists.ChartData.mapSection` to the
value of `...RelativeProjTwists.TwistData.psiTransposeNat` on `π⁻¹U` at the image of `a` under the
unit of the adjunction `π^* ⊣ π_*`. -/
public theorem psiTransposeNat_chart (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : A.sectionPieces U n) :
    letI := D.chartData.chart_isOpenImmersion U hU
    D.chartData.mapSection U hU (n : ℤ) ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)
      = (D.chartData.chart_range U hU).symm ▸
          ((D.psiTransposeNat n).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
              (A.piece (n : ℤ))).val.app (op U) a)) := by
  have h := D.ψ_chart U hU n a
  rwa [D.psi_val_app n U a] at h

/-- `psiTransposeNat_chart` for the integer-indexed `...RelativeProjTwists.TwistData.psiTranspose`
in a nonnegative degree. -/
public theorem psiTranspose_chart (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : A.sectionPieces U n) :
    letI := D.chartData.chart_isOpenImmersion U hU
    D.chartData.mapSection U hU ((n : ℕ) : ℤ) ⊤
        (degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)
      = (D.chartData.chart_range U hU).symm ▸
          ((D.psiTranspose ((n : ℕ) : ℤ)).val.app (op ((relativeProj A).toBase ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).unit.app
              (A.piece ((n : ℕ) : ℤ))).val.app (op U) a)) :=
  D.psiTransposeNat_chart U hU n a

end TwistData

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
