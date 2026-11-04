module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpectrum

/-!
# The relative spectrum of a bounded algebra

`AlgebraicGeometry.Space.relativeSpectrum` constructs the relative spectrum of Stacks 081W of an
arbitrary quasi-coherent algebra `𝒜` on an algebraic space `X` over an enlargement `B'` of the
big fppf site `B` of `X`. When `𝒜` already has fewer than `B.cutoff` sections over every étale
chart, its relative spectrum exists in `B` itself
(`AlgebraicGeometry.Space.boundedRelativeSpec`), and this file shows that the two agree: read in
`B'` (`AlgebraicGeometry.Space.changeBigSiteAffineOver`), the relative spectrum built in `B` is
isomorphic over `X'` to the one built in `B'`.

The proof compares direct images. Read on the étale charts of `X`, the direct image of the
enlargement of `\underline{Spec}_X(𝒜)` is the direct image of `\underline{Spec}_X(𝒜)`
(`AlgebraicGeometry.Space.changeBigSitePushforwardAlgebraIso`), which is `𝒜`; a sheaf of
`𝒪_{X'}`-algebras is the extension of its restriction to the charts of `X`
(`AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteExtendRestrictIso`), so the direct image is
the extension of `𝒜`, which is the algebra whose relative spectrum
`AlgebraicGeometry.Space.relativeSpectrum` is; and an algebraic space affine over `X'` is
determined by its direct image (Stacks 081V over `B'`).

## Main results

* `AlgebraicGeometry.Space.pushforwardAlgebraChangeBigSiteBoundedRelativeSpecIso`: the direct
  image of the enlargement of the bounded relative spectrum is the algebra of
  `AlgebraicGeometry.Space.relativeSpectrum`.
* `AlgebraicGeometry.Space.nonempty_iso_changeBigSite_boundedRelativeSpec`: the bounded relative
  spectrum, read in the enlarged site, is the relative spectrum.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03FO](https://stacks.math.columbia.edu/tag/03FO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The direct image of the bounded relative spectrum, read in the enlarged site, is the algebra
whose relative spectrum `AlgebraicGeometry.Space.relativeSpectrum` is. -/
def pushforwardAlgebraChangeBigSiteBoundedRelativeSpecIso (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) :
    pushforwardAlgebra (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
        ((changeBigSiteAffineOver B (relativeSpectrumSite A) (isContained_relativeSpectrumSite A)
          S hS X).obj (boundedRelativeSpec B S hS A hA)).obj ≅
      (relativeSpectrumAlgebra A).obj :=
  (AlgebraSheaf.changeBigSiteExtendRestrictIso B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X _).symm ≪≫
    AlgebraSheaf.changeBigSiteExtendIso B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X
      (changeBigSitePushforwardAlgebraIso B (relativeSpectrumSite A)
          (isContained_relativeSpectrumSite A) S hS (boundedRelativeSpec B S hS A hA) ≪≫
        pushforwardAlgebraBoundedRelativeSpecIso B S hS A hA)

/-- **For a bounded algebra the relative spectrum is the bounded relative spectrum, read in the
enlarged site.** When `𝒜` has fewer than `B.cutoff` sections over every étale chart of `X`, the
relative spectrum `AlgebraicGeometry.Space.boundedRelativeSpec` built inside the site `B` of `X`,
carried to the enlarged site by Stacks 03FP (`AlgebraicGeometry.Space.changeBigSiteAffineOver`),
is isomorphic over `X'` to `AlgebraicGeometry.Space.relativeSpectrum 𝒜`. -/
theorem nonempty_iso_changeBigSite_boundedRelativeSpec (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) :
    Nonempty ((changeBigSiteAffineOver B (relativeSpectrumSite A)
      (isContained_relativeSpectrumSite A) S hS X).obj (boundedRelativeSpec B S hS A hA) ≅
        relativeSpectrum A) :=
  nonempty_iso_boundedRelativeSpec (relativeSpectrumSite A) S (contains_relativeSpectrumSite A)
    (relativeSpectrumAlgebra A) (sectionsBelowCutoff_relativeSpectrumAlgebra A) _
    (pushforwardAlgebraChangeBigSiteBoundedRelativeSpecIso A hA)

end AlgebraicGeometry.Space

end
