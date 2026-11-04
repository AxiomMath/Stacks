module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeChart
import all StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme

/-!
# The graded ideals cutting out a closed subscheme locally of finite presentation

Work in Situation 01NN over a quasi-compact quasi-separated scheme `S`, with `p : Proj_S(𝒜) ⟶ S`
quasi-compact and `i : Z ⟶ Proj_S(𝒜)` a closed subscheme locally of finite presentation.  The
proof of Stacks 0802 produces a degree `d > 0` and a quasi-coherent submodule `ℱ ⊆ 𝒜_d` of finite
type consisting of equations for `Z` and cutting `Z` out on the charts of an affine cover.  This
file records the consequence that the proof of Stacks 085M uses on an étale chart: every
quasi-coherent graded ideal `𝒦` with `ℱ ⊆ 𝒦_d` and contained in the graded ideal of Stacks 0801
cuts out `Z`, that is `Z = Proj_S(𝒜/𝒦)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_ker_eq_ker_projQuotientHom`

## References

* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (D : RelativeProjTwists.TwistData A)

/-- **Every quasi-coherent graded ideal between `ℱ𝒜` and the ideal of Stacks 0801 cuts out a
closed subscheme locally of finite presentation.**  For such a closed subscheme of a
quasi-compact relative Proj over a quasi-compact quasi-separated base there are `d > 0` and a
quasi-coherent finite type `ℱ ⊆ 𝒜_d` contained in the graded ideal of Stacks 0801 such that
`Z = Proj_S(𝒜/𝒦)` for every quasi-coherent graded ideal `𝒦` with `ℱ ⊆ 𝒦_d` contained in that
ideal. -/
theorem exists_finiteType_ker_eq_ker_projQuotientHom {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj A).scheme) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsClosedImmersion i] [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.LocallyOfFinitePresentation i) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          ℱ ≤ (twistKerGradedIdeal A D i).piece (d : ℤ) ∧
            ∀ 𝒦 : QcohGradedIdeal A, ℱ ≤ 𝒦.piece (d : ℤ) →
              (∀ n : ℤ, 𝒦.piece n ≤ (twistKerGradedIdeal A D i).piece n) →
                i.ker = (projQuotientHom A 𝒦).ker := by
  obtain ⟨d, hd, ℱ, hq, hft, heq, hcut⟩ :=
    exists_finiteType_cutsOutOnCharts A (gradedQuotientPresentation_twistKer A D i) hi
  exact ⟨d, hd, ℱ, hq, hft, le_piece_of_isEquationSubmodule A ℱ _ heq,
    fun 𝒦 hle hsub => ker_eq_ker_projQuotientHom_of_cutsOutOnCharts A D i ℱ 𝒦 hle hsub hcut⟩

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
