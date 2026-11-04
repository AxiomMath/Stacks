module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.JointSurjectiveBiproductEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty

/-!
# Finite biproducts of modules on an algebraic space

Modules on the small étale site of an algebraic space have biproducts indexed by any finite
type, which is what lets the epimorphism criterion
`Stacks.SheafOfModules.EpiMono.epi_biproductDesc_of_surjective_on_presieve` be written down for
them.

## Main results

* `AlgebraicGeometry.Space.hasFiniteBiproducts_modules`: `𝒪_X`-modules have finite biproducts.

## Implementation notes

Biproducts of sheaves of modules are their products, which exist on every site, but
`CategoryTheory.Limits.HasFiniteBiproducts` is not registered as an instance for sheaves of
modules, so a consumer at the algebraic-space spelling has to seat it before a biproduct over a
finite index type can be written down.  This seats it once, from
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`, exactly as
`AlgebraicGeometry.Space.hasBinaryBiproducts_modules` seats the binary case.

The module universe is the universe of the schemes, which is where the epimorphism criterion
and the finiteness properties of this tree are stated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Modules on the small étale site of an algebraic space have finite biproducts: they are the
finite products, which exist because sheaves of modules on a site have all limits. -/
instance hasFiniteBiproducts_modules (X : AlgebraicSpaces B S hS) :
    HasFiniteBiproducts (Modules.{u, u} B S hS X.1 X.2) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Space

end
