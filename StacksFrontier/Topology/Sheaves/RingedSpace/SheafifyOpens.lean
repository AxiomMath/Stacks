module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# Sheafification on the open-cover site of a ringed space, for abelian groups

The Grothendieck topology `Opens.grothendieckTopology X.carrier` on the open-cover site of a
ringed space `X` is induced by an essentially small category, so the general machinery of
`Mathlib.CategoryTheory.Sites.Equivalence` provides sheafification of presheaves of abelian
groups on it, and identifies the weak equivalences of such presheaves as the locally bijective
morphisms.

These two facts were kept as `local instance`s, copied verbatim into four different files, so
that they would not enter global instance search (sheafification on an essentially small site
is far too eager a fact to offer everywhere); this file gives them one shared home as
`scoped instance`s. A consumer that wants them brings them into local instance search with
`attribute [local instance]` naming them fully qualified, exactly as it would have named its
own former private copy.

## Main definitions

* `Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat`
* `Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat`
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Topology.RingedSpaceSheafifyOpens

/-- Sheafification of presheaves of abelian groups exists on the open-cover site of a ringed
space, that site being essentially small. -/
scoped instance opensHasSheafifyAddCommGrpCat {X : RingedSpace.{u, u}} :
    HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- On the open-cover site of a ringed space the weak equivalences of presheaves of abelian
groups are the locally bijective morphisms. -/
scoped instance opensWEqualsLocallyBijectiveAddCommGrpCat {X : RingedSpace.{u, u}} :
    (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _

end Stacks.Topology.RingedSpaceSheafifyOpens

end
