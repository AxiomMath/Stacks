module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# A short exact sequence of `𝒪_F`-modules and the base change criterion on affine charts

Stacks 03M1 asserts, among other things, that in a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of modules on an algebraic space, quasi-coherence of two of the three
terms implies quasi-coherence of the third.  This file proves the left implication for the base
change criterion of Stacks 03DX(2) in place of quasi-coherence: if the sections of `T.X₂` and of
`T.X₃` over every affine étale chart are the base change of their sections over any larger
affine étale chart, then the same holds for `T.X₁`.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₁`: the left term of a short
  exact sequence of `𝒪_F`-modules is cartesian on affine charts as soon as the middle and the
  right term are.

## Implementation notes

The statement is at module universe `u`: `CategoryTheory.ShortComplex.ShortExact.fIsKernel`
needs the ambient category to be balanced, and
`CategoryTheory.Balanced (AlgebraicGeometry.Space.Modules.{u, m} B S hS F hF)` is found by
instance search for `m := u` and for `m := u + 1` but not for an independent `m`.  The abelian
structure on the modules of the small étale ringed site comes from sheafification of
`AddCommGrpCat.{m}`-valued presheaves on a site whose objects live in `Type (u + 1)`, which needs
`UnivLE.{u + 1, m}`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The left term of a short exact sequence of `𝒪_F`-modules is cartesian on affine charts as
soon as the other two terms are. -/
theorem isCartesianOnAffineCharts_shortExact_X₁
    (T : CategoryTheory.ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h₂ : IsCartesianOnAffineCharts T.X₂) (h₃ : IsCartesianOnAffineCharts T.X₃) :
    IsCartesianOnAffineCharts T.X₁ :=
  isCartesianOnAffineCharts_of_isLimit T.zero hT.fIsKernel h₂ h₃

end AlgebraicGeometry.Space

end
