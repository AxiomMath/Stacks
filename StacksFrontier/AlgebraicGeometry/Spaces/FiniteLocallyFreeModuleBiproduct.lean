module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeBiproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty

/-!
# A biproduct of finite locally free modules on an algebraic space is finite locally free

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  A biproduct
of two finite locally free `𝒪_X`-modules on the small étale site of `X` is finite locally free.

This is the algebraic-space reading of
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biprod`, which is the statement for an
arbitrary sheaf of rings on an arbitrary site.

## Main results

* `AlgebraicGeometry.Space.hasBinaryBiproducts_modules`: `𝒪_X`-modules have binary biproducts.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_biprod`: **a biproduct of two finite
  locally free `𝒪_X`-modules is finite locally free**, Stacks 03DL (2) for a biproduct.

## Implementation notes

The biproduct instance is the point of this file.  Binary biproducts of sheaves of modules are
their binary products, which exist on every site, but `HasBinaryBiproducts` is not registered as
an instance for sheaves of modules — `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biprod` and
`Stacks.SheafOfModules.isFinitePresentation_biprod` therefore take the existence of the biproduct
as an instance hypothesis, and a consumer at the algebraic-space spelling has to seat it before
the biproduct can even be written down.  `AlgebraicGeometry.Space.hasBinaryBiproducts_modules`
seats it once, from `CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts`.

The module universe is the universe of the schemes, which is the universe at which the direct
image, the inverse image and relative ampleness of this tree are stated, and the one at which
the general statement collapses the finite free model of Stacks 03DE (2) onto the module itself.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Modules on the small étale site of an algebraic space have binary biproducts: they are the
binary products, which exist because sheaves of modules on a site have all limits. -/
instance hasBinaryBiproducts_modules (X : AlgebraicSpaces B S hS) :
    HasBinaryBiproducts (Modules.{u, u} B S hS X.1 X.2) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- **Stacks 03DL (2) for a biproduct, on an algebraic space.**  A biproduct of two finite
locally free `𝒪_X`-modules is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_biprod {X : AlgebraicSpaces B S hS}
    (A A' : Modules.{u, u} B S hS X.1 X.2)
    (hA : SheafOfModules.IsFiniteLocallyFreeOnSite A)
    (hA' : SheafOfModules.IsFiniteLocallyFreeOnSite A') :
    SheafOfModules.IsFiniteLocallyFreeOnSite (A ⊞ A') :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_biprod A A' hA hA'

end AlgebraicGeometry.Space

end
