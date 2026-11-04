module

public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The schemes of a big fppf site are essentially small

The category of schemes underlying a big fppf site is essentially small, being the schemes below
the site's cardinal cutoff. This is registered here as an instance.

It lives in its own module because both the small-étale-site development and the quasi-coherent
descent development need it and neither imports the other: each reaches this module instead of
carrying its own copy of the instance.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The underlying category of schemes of a big fppf site is essentially small. -/
public instance essentiallySmallSchemes (B : BigFppfSite.{u}) :
    EssentiallySmall.{u} B.Schemes :=
  essentiallySmall_schemeBelow B.cutoff

end AlgebraicGeometry

end
