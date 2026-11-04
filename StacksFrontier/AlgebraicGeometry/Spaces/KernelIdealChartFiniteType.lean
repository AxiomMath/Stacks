module

public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealChartFiniteTypeEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation

/-!
# The chart comparison of Stacks 084Q for a closed subspace, proved

For a closed subspace `Z ⊆ X` of an algebraic space over `S` the kernel ideal sheaf of the
inclusion is the defining ideal sheaf of `Z`, so the comparison of finite type of that ideal
sheaf on the small étale site of `X` with finite generation of the chart-level ideal over the
affine opens of a surjective étale scheme chart — the appeal to Properties of Spaces,
Section 66.30 which Stacks 084Q makes, and which
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
carries as the hypothesis `hchart` — is the unconditional equivalence of
`StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealChartFiniteTypeEquivalence.lean`.

This file packages that equivalence into the shape `hchart` is stated in.  The unconditional
form of Stacks 084Q itself is
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ClosedImmersionFinitePresentation.lean`.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_fg_ideal_ker_rep_snd`: the
  hypothesis `hchart` of
  `AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`,
  **proved**, for the inclusion of a closed subspace.

## Implementation notes

The packaging is three steps and no mathematics.  An étale chart in the sense of
`AlgebraicGeometry.Space.SmallEtale` is a morphism `b : yoneda.obj V ⟶ X.1` together with the
property `hbEtale` that `hchart` already quantifies over, so the chart is
`⟨CostructuredArrow.mk b, hbEtale⟩` and its `AlgebraicGeometry.Space.chartScheme` is the scheme
underlying `V` on the nose.  Surjectivity in the sense the descent needs is surjectivity on the
point sets of Stacks 03BU, which `hbSurj` gives by the half
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective` of Stacks 03H5.  And the ideal
sheaf of the inclusion is the defining ideal sheaf of the subspace by
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **The hypothesis `hchart` of Stacks 084Q, proved for the inclusion of a closed subspace.**
On a surjective étale scheme chart `b : V ⟶ X`, finite type of the ideal sheaf
`𝓘_Z = Ker(𝒪_X ⟶ i_*𝒪_Z)` on the small étale site of `X` is finite generation, over every affine
open of `V`, of the ideal cut out by the base-changed closed immersion `Z ×_X V ⟶ V`.

This is `isFiniteTypeOnSite_definingIdealSheaf_iff_fg_ideal_ker_rep_snd_of_isSurjective`
at the chart `⟨CostructuredArrow.mk b, hbEtale⟩`, with surjectivity on points obtained from
`hbSurj` by `AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`. -/
theorem isFiniteTypeOnSite_kernelIdealSheaf_iff_fg_ideal_ker_rep_snd
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ X.1)
    (hbEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    SheafOfModules.IsFiniteTypeOnSite
        (kernelIdealSheaf B S hS (subspaceInclusion B S hS X Z)).toSheafOfModules ↔
      ∀ A : ((BigFppfOver.toScheme B S hS).obj V).affineOpens,
        (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd b)).ker.ideal A).FG := by
  rw [kernelIdealSheaf_eq_definingIdealSheaf B S hS X Z]
  exact isFiniteTypeOnSite_definingIdealSheaf_iff_fg_ideal_ker_rep_snd_of_isSurjective
    B S hS X Z ⟨CostructuredArrow.mk b, hbEtale⟩
    (isSurjective_of_presheafSurjective B S hS b hbSurj)

end AlgebraicGeometry.Space

end
