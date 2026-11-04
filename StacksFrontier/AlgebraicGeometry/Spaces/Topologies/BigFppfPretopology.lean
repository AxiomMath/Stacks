module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SitePretopology

/-!
# The pretopology of a big fppf site of algebraic spaces

The chosen fppf covering families of a big fppf site of algebraic spaces satisfy the site axioms,
so their presieves form a pretopology on the category of algebraic spaces over `S`. Its coverings
are exactly `Cov((Spaces/S)_fppf)`, the chosen fppf coverings, so hypercoverings for this
pretopology are the fppf hypercoverings of Stacks 09X8 read in the site `(Spaces/S)_fppf`; its
Grothendieck topology is the big fppf topology.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.pretopologyBigFppfPretopology`: the pretopology on algebraic
  spaces over `S` whose coverings are the chosen fppf covering families.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.toPrecoverage_pretopology_bigFppfPretopology`: its coverings
  are the presieves of the chosen fppf covering families.
* `AlgebraicGeometry.BigFppfSpaceSite.toGrothendieck_pretopology_bigFppfPretopology`: it generates
  the big fppf topology.

## References

* [Stacks Project, Tag 0DBV](https://stacks.math.columbia.edu/tag/0DBV)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The pretopology of the big fppf site of algebraic spaces over `S`: the coverings of `X` are
the presieves of the chosen fppf covering families of `X`, that is `Cov((Spaces/S)_fppf)`. -/
def pretopologyBigFppfPretopology : Pretopology T.Spaces :=
  IsSite.pretopologyBigFppfPretopology T.isSite

/-- The coverings of the pretopology are the presieves of the chosen fppf covering families. -/
theorem toPrecoverage_pretopology_bigFppfPretopology :
    T.pretopologyBigFppfPretopology.toPrecoverage = T.precoverage :=
  rfl

/-- The pretopology generates the big fppf topology of algebraic spaces. -/
theorem toGrothendieck_pretopology_bigFppfPretopology :
    T.pretopologyBigFppfPretopology.toGrothendieck = T.topology :=
  IsSite.toGrothendieck_pretopology_bigFppfPretopology T.isSite

end AlgebraicGeometry.BigFppfSpaceSite
