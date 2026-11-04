module

public import StacksFrontier.AlgebraicGeometry.ChartBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ChartQuotient
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistRestriction
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Chart

/-!
# The chart comparison for the graded ideal of a closed subscheme of a relative Proj

Work in Situation 01NN: a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, twists `D` on
`Proj_S(𝒜)`, and a closed immersion `i : Z ⟶ Proj_S(𝒜)` with `p : Proj_S(𝒜) ⟶ S` quasi-compact.
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal` is the graded ideal
`ℐ_d = ker (𝒜_d ⟶ p_*((i_*𝒪_Z)(d)))` that Stacks Tag 0801 forms.

**This file identifies the local sections of that ideal over an affine open `U` of the base with
the absolute ideal of equations of the closed subscheme `Z ∩ p⁻¹(U)` of the chart
`Proj Γ(U, 𝒜)`.** That identification is the chart comparison the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistRestriction.lean` recorded as the one
remaining statement of Tag 0801.

Both sides are a vanishing condition for twisted sections. On the relative side
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_twistKerGradedIdeal_iff` says that a
homogeneous local section `a` of `𝒜_n` over `U` lies in `ℐ` exactly when the section of `𝒪(n)`
over `p⁻¹(U)` named by `ψ` restricts to zero on `Z`; on the absolute side
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff` says that an
element of `Γ(U, 𝒜)` lies in the ideal of equations exactly when the twisted global section
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of each of its homogeneous components
pulls back to zero. What joins the two is
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart`, which says precisely that the
chart identification carries one section to the other.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_twistKerGradedIdeal_iff_chart`:
  membership in `ℐ` in a nonnegative degree, read on the chart: a homogeneous local section is an
  equation for `Z` exactly when the twisted global section it determines on `Proj Γ(U, 𝒜)` pulls
  back to zero along the base change of `i` to the chart.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionIdeal_eq_idealOfClosedSubscheme`:
  **the chart comparison.** `ℐ(U)` is the ideal of equations of the closed subscheme the chart
  cuts out.

## Implementation notes

The closed subscheme of the chart is
`Stacks.AlgebraicGeometry.ChartBaseChange.chartRestrict ((relativeProj 𝒜).chart U hU) i`, the
restriction of `i` to `p⁻¹(U)` read on `Proj Γ(U, 𝒜)` through the chart. It is a closed immersion
by `Stacks.AlgebraicGeometry.ChartBaseChange.isClosedImmersion_chartRestrict`, so the absolute
ideal of equations is available for it with no hypothesis beyond Tag 0801's own.

The two vanishing conditions are stated at different spellings of the pullback of a section —
`AlgebraicGeometry.Scheme.Modules.pullbackSection` over the open `p⁻¹(U)` on the relative side,
`AlgebraicGeometry.pullbackGlobalSections` on the chart on the absolute side — and
`Stacks.AlgebraicGeometry.ChartBaseChange.pullbackGlobalSections_chartRestrict_eq_zero_iff` is
the comparison of the two. Three further steps are needed, and each is a single rewrite: the
chart identification of the twists is an isomorphism, so it does not affect vanishing
(`Stacks.AlgebraicGeometry.ChartBaseChange.pullbackGlobalSections_hom_eq_zero_iff`); `ψ_chart` is
stated with the transport `(chart_range U hU).symm ▸ _` along the equality of opens
`chart ''ᵁ ⊤ = p⁻¹(U)`, and `pullbackSection_eq_zero_iff_congr` moves a vanishing condition along
such an equality by `subst`; and `ChartData.mapSection` at the open `⊤` is the inverse chart
identification on the nose, because `AlgebraicGeometry.Scheme.Modules.restrictAppIso` at `⊤` is
the identity.

The passage from the degreewise statement to the comparison of ideals is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.coe_decompose_grading`, which says the
homogeneous components computed for the internal grading `𝒜.grading U` are the external
coordinates of the section.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartBaseChange
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

/-! ### Moving a vanishing condition along an equality of opens -/

/-- **Transporting the vanishing of a pulled-back section along an equality of opens.** This is
the shape `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart` is stated at: its
right-hand side is a transport along `chart ''ᵁ ⊤ = p⁻¹(U)`. -/
theorem pullbackSection_eq_zero_iff_congr {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules)
    {W W' : X.Opens} (hW : W = W') {t : F.val.obj (op W)} {t' : F.val.obj (op W')}
    (ht : t = hW.symm ▸ t') :
    Scheme.Modules.pullbackSection i F W (i ⁻¹ᵁ W) le_rfl t = 0 ↔
      Scheme.Modules.pullbackSection i F W' (i ⁻¹ᵁ W') le_rfl t' = 0 := by
  subst hW
  rw [ht]

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) (D : TwistData 𝒜)
  {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)

/-! ### Membership in the graded ideal, read on a chart -/

/-- **Membership in Tag 0801's graded ideal, read on the chart over an affine open of the base.**
A homogeneous local section `a` of `𝒜_n` over `U` is an equation for `Z` exactly when the twisted
global section it determines on the chart `Proj Γ(U, 𝒜)` pulls back to zero along the closed
subscheme the chart cuts out of `Z`.

This is `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mem_twistKerGradedIdeal_iff` with the
relative vanishing condition traded for the absolute one, through the chart identification of the
twists and `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart`. -/
theorem mem_twistKerGradedIdeal_iff_chart [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : 𝒜.sectionPieces U n) :
    letI := D.chartData.chart_isOpenImmersion U hU
    a ∈ ((twistKerGradedIdeal 𝒜 D i).piece (n : ℤ)).toSubmodule.obj (op U) ↔
      pullbackGlobalSections (chartRestrict ((relativeProj 𝒜).chart U hU) i)
          (twistingSheaf (𝒜.grading U) (n : ℤ))
          (degreeSection (𝒜.grading U) n
            ⟨DirectSum.of (𝒜.sectionPieces U) n a, 𝒜.of_mem_grading U a⟩) = 0 := by
  let := D.chartData.chart_isOpenImmersion U hU
  have hiso := (D.chartData.chartIso U hU (n : ℤ)).isIso_hom
  rw [mem_twistKerGradedIdeal_iff 𝒜 D i n U a,
    ← Stacks.AlgebraicGeometry.TwistRigidity.iso_hom_app_inv_app
      (D.chartData.chartIso U hU (n : ℤ)) (op ⊤)
      (degreeSection (𝒜.grading U) n
        ⟨DirectSum.of (𝒜.sectionPieces U) n a, 𝒜.of_mem_grading U a⟩),
    pullbackGlobalSections_hom_eq_zero_iff
      (chartRestrict ((relativeProj 𝒜).chart U hU) i)
      (D.chartData.chartIso U hU (n : ℤ)).hom _,
    pullbackGlobalSections_chartRestrict_eq_zero_iff ((relativeProj 𝒜).chart U hU) i
      (D.algebra.piece (n : ℤ)) _]
  exact (pullbackSection_eq_zero_iff_congr i (D.algebra.piece (n : ℤ))
    (D.chartData.chart_range U hU) (D.ψ_chart U hU n a)).symm

/-! ### The chart comparison -/

/-- The homogeneous components of a section of `Γ(U, 𝒜)` for the internal grading, as the
external coordinates of the section. This is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.coe_decompose_grading` read in the submodule
rather than on the underlying ring. -/
theorem decompose_grading_eq (U : S.Opens) (x : 𝒜.sectionRing U) (n : ℕ) :
    (DirectSum.decompose (𝒜.grading U) x) n =
      ⟨DirectSum.of (𝒜.sectionPieces U) n (x n), 𝒜.of_mem_grading U (x n)⟩ :=
  Subtype.ext (coe_decompose_grading 𝒜 U x n)

/-- **The chart comparison of Tag 0801.** Over an affine open `U` of the base, the homogeneous
ideal `ℐ(U)` of local sections of Tag 0801's graded ideal is the absolute ideal of equations of
the closed subscheme that `Z` cuts out of the chart `Proj Γ(U, 𝒜)`.

Both sides are the condition that every homogeneous component of a section be an equation for
`Z`, so this is `mem_twistKerGradedIdeal_iff_chart` degree by degree. -/
theorem sectionIdeal_eq_idealOfClosedSubscheme [IsClosedImmersion i]
    [QuasiCompact (relativeProj 𝒜).toBase] (U : S.Opens) (hU : IsAffineOpen U) :
    letI := D.chartData.chart_isOpenImmersion U hU
    (sectionIdeal 𝒜 (twistKerGradedIdeal 𝒜 D i) U).toIdeal =
      idealOfClosedSubscheme (𝒜.grading U)
        (chartRestrict ((relativeProj 𝒜).chart U hU) i) := by
  let := D.chartData.chart_isOpenImmersion U hU
  refine Ideal.ext fun x => ?_
  rw [mem_sectionIdeal_iff 𝒜 (twistKerGradedIdeal 𝒜 D i) U x,
    mem_idealOfClosedSubscheme_iff (𝒜.grading U) _ x]
  refine forall_congr' fun n => ?_
  rw [decompose_grading_eq 𝒜 U x n]
  exact mem_twistKerGradedIdeal_iff_chart 𝒜 D i U hU n (x n)

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
