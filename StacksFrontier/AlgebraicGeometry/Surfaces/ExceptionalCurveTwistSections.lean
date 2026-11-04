module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistMonomialBasis
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# The monomial basis of the sections of a twist on the projective line of an exceptional curve

`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` presents the subscheme
cut out by its ideal sheaf as `AlgebraicGeometry.projectiveLineProj k`, the `Proj` of the graded
polynomial ring `k[T₀, T₁]`, and
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` identifies the restriction of
`𝒪_X(-dE)` to `E`, pulled back there, with the `d`-th twist.  Its global sections are therefore
what the Stacks proof of [Stacks, Tag 0C2K] has to understand, and this file records that for
`d ≥ 0` they are free of rank `d + 1` over `k` on the degree-`d` monomials in the two
coordinates.

This is `Stacks.ProjectiveSpace.Cohomology.projectiveLineTwistSectionsBasis` with its scheme
spelled as `AlgebraicGeometry.projectiveLineProj k`; the two spellings agree because
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1` is the total-degree grading of
`k[T₀, T₁]`.

## Main definitions

* `AlgebraicGeometry.projectiveLineProjTwistSectionsBasis` — **`Γ(𝐏¹_k, 𝒪(d))` is free of rank
  `d + 1`** for `d ≥ 0`, on the monomial basis.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.ProjectiveCohomology Stacks.ProjectiveSpace.Cohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The monomial basis of `H⁰(𝐏¹_k, 𝒪(d))`.**  For `d ≥ 0` the global sections of the `d`-th
twist on the projective line, in the `Proj` presentation used by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`, are free of rank
`d + 1` over `k`, on the basis transported from the degree-`d` monomials `T₀^{d-j} T₁^j` along
the degree-zero row of [Stacks, Tag 01XT].

This is the geometric input the three remaining hypotheses of
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration` rest on. -/
public def projectiveLineProjTwistSectionsBasis (k : Type u) [Field k] (d : ℤ) (hd : 0 ≤ d) :
    Module.Basis (Fin (d.toNat + 1)) k
      ((ModuleCat.restrictScalars.{u} (coeffScalar k 1)).obj
        ((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).obj
          (ProjectiveSpectrum.Proj.twistingSheaf
            (MvPolynomial.homogeneousSubmodule (Fin 2) k) d))) :=
  projectiveLineTwistSectionsBasis k d hd

end AlgebraicGeometry
