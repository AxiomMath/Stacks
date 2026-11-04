module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Sheafification for the Zariski site of opens of a scheme

The site of opens of a scheme is essentially small, so abelian-group-valued presheaves on it
sheafify, and its weak equivalences are the locally bijective maps. Instance search does not find
either fact on its own, because the smallness goes through
`CategoryTheory.EssentiallySmall`; both are one line from
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`.

## Main declarations

* `Stacks.OpensSheafification.hasSheafifyOpens`
* `Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens`

## Implementation notes

The two one-liners were restated as `local instance` in five modules of the tree, under three
names. They are declared here once, and `attribute [local instance]` seats them where they are
needed -- which is how the library already shares such facts (see
`Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian`). They are deliberately NOT global
instances: each is about one site and one target category, and the modules that need them say so
explicitly.

The five modules that restated them have import closures from 207 to 1,404 modules; this one has
the handful of Mathlib files the two proofs use, so each of them gains only this module.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.OpensSheafification

/-- Abelian-group-valued presheaves on the opens of a scheme sheafify. -/
noncomputable local instance hasSheafifyOpens (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of a scheme, the weak equivalences of abelian-group-valued presheaves are the
locally bijective maps. -/
noncomputable local instance wEqualsLocallyBijectiveOpens (X : Scheme.{u}) :
    (Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end Stacks.OpensSheafification

end
