module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseConditionsFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibre

/-!
# Free sections along the fibre, at the source's own finite-type hypothesis

`StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibre` proves Stacks 0CVW
reduced to the affine étale chart of the target, at the source's own hypothesis, `F` of finite
type on the small étale site.  This file records it under the name
`AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre_of_isFiniteTypeOnSite`.

## Main results

* `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre_of_isFiniteTypeOnSite`:
  **Stacks 0CVW**.

## References

* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CVW**, at the source's own hypotheses.  Let `f : X ⟶ Y` be a finite type morphism
of algebraic spaces over `S`, let `F` be a finite type quasi-coherent `𝒪_X`-module and let `y`
be a point of `|Y|` at which `F` is flat along the fibre.  Then there is an affine étale
neighbourhood of `y` in `Y` and an affine étale chart of `X` over it, surjective onto the
fibre, over which `F` has free sections along the fibre.

This is `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre`, which takes `F`
of finite type on the small étale site of `X` and derives the finite type of each chart
restriction by `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`. -/
@[stacks 0CVW "the etale neighbourhood, the affine scheme and its free sections are \
delivered, reduced to the affine etale chart of the target.  At the source's own hypotheses: \
`F` of finite type on the small etale site of `X`, from which the finite type of each chart \
restriction follows by isFiniteTypeOnCharts_of_isFiniteTypeOnSite, which is proved"]
alias exists_affineChart_hasFreeSectionsAlongFibre_of_isFiniteTypeOnSite :=
  exists_affineChart_hasFreeSectionsAlongFibre

end AlgebraicGeometry.Space

end
