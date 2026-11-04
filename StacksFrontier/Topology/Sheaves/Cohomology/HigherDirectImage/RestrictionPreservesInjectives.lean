module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01E1: restriction to an open subspace preserves injective modules

Let `(X, 𝒪)` be a space with a sheaf of rings and let `j : U → X` be an open subspace.  Stacks
01E1 says that the restriction functor `j^{-1} : Mod(𝒪) ⥤ Mod(𝒪|_U)` carries injective sheaves
of modules to injective sheaves of modules.  This is the right-adjoint half of the
extension-by-zero adjunction of Stacks 00A7 (2), since `j_!` is exact
(`ExtensionByZeroModules.jShriek_preservesMonomorphisms`).

## Main results

* `restMod_preservesInjective`: the restriction of an injective sheaf of modules to an open
  subspace is injective, in the `restMod` vocabulary of Stacks 00A7.

## Implementation notes

The proof is `Stacks.Cohomology.HigherDirectImage.jStar_injective_obj`, stated in the
`ExtensionByZeroModules` vocabulary, where restriction is
`jStar U O = SheafOfModules.pushforward (𝟙 (resRing U O))`, built from the reducible
`TopCat.Presheaf.imF U`, whereas `restMod X U = SheafOfModules.pushforward (phiSh X U)` is built
from the plain definition `jFun X U`. The two restriction functors agree after delta-unfolding
`jFun` and `phiSh`, and term mode identifies them with no reducibility adjustment.

The carrier universe of `X` is pinned to the ring and module universe `u`, because
`SheafOfModules.pullback` exists only through `PresheafOfModules.instIsRightAdjointPushforward`,
which equates the site, ring and module universes.

## References

* [The Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-- The restriction of an injective sheaf of modules to an open subspace is injective. -/
@[stacks 01E1 "restriction_preserves_injectives"]
public theorem restMod_preservesInjective (X : SheafedSpace.{u + 1, u, u} RingCat.{u})
    (U : Opens X.carrier) (I : SheafOfModules.{u} (OXSh X)) [Injective I] :
    Injective ((restMod X U).obj I) :=
  jStar_injective_obj U (OXSh X) I

end Stacks.Cohomology.HigherDirectImage

end
