module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Sheafification and abelian structure on the small étale sites

Let `B` be a big étale site containing a scheme `S`.  The small étale site and the small affine
étale site of `S` are categories in `Type (u + 1)` whose morphisms live in `Type u`, so
sheafification of presheaves valued in a `u`-concrete category is not available from the general
theory: the presheaf category only has colimits of size `u + 1`.  It becomes available once the
site is `EssentiallySmall.{u}`, which is
`AlgebraicGeometry.SmallEtale.essentiallySmall`, by
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`.

Those two instances are what the abelian structure on sheaves is built from.  In particular
`SheafOfModules.{u} R` is abelian exactly when `HasSheafify J AddCommGrpCat.{u}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{u}` hold, so sheaves of modules over the structure
sheaf of Stacks 03DU form an abelian category and a morphism between them has a cokernel.  That
is what the clauses of Stacks 0GNB are about.

## Main results

* `AlgebraicGeometry.SmallEtale.hasSheafify` and
  `AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective`: presheaves on the small étale site
  valued in a `u`-concrete category with limits and colimits can be sheafified, and the
  sheafification equivalences are the locally bijective maps.  Likewise on the small affine
  étale site.
* `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf`: abelian-group-valued sheaves on
  the small étale site form a Grothendieck abelian category.

## Implementation notes

`CategoryTheory.sheafIsAbelian` is applied explicitly rather than by instance search, because
the universe variables of `CategoryTheory.HasSheafify` are not determined by the goal
`Abelian (Sheaf J AddCommGrpCat.{u})`, so that instance does not fire on its own.  The abelian
structure on sheaves of *modules* is not restated as an instance: Mathlib's
`SheafOfModules.instAbelian` does fire once the two instances of this file are available, and a
second declaration of it would give instance search two paths to the same
`CategoryTheory.Abelian` structure.  So instance search gives a morphism of sheaves of modules
on the small étale site, or on the small affine étale site, a kernel and a cokernel: the
abelian category `SheafOfModules.{u} (AlgebraicGeometry.SmallEtale.structureSheaf B S hS)` is
the ambient category in which Stacks 0GNB is stated.

Existence of all `u`-colimits in the categories of *sheaves of abelian groups* is not recorded.
It would follow from `CategoryTheory.hasColimitsEssentiallySmallSite`, but that reduces it to
colimits of sheaves on the small model, whose instance search does not terminate within the
default heartbeat budget.  Limits and colimits of sheaves of *modules* are unaffected: they come
from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`, which only need sheafification, and give
sheaves of modules on the small étale site `u`-indexed direct sums and all `u`-limits and
`u`-colimits.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u' u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SmallEtale

section Concrete

variable {A : Type u'} [Category.{u} A] {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Presheaves on the small étale site of `S` valued in a `u`-concrete category with limits and
colimits can be sheafified, because the site is essentially small. -/
public noncomputable instance hasSheafify : HasSheafify (topology B S hS) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On the small étale site of `S`, the morphisms inverted by sheafification are exactly the
locally bijective ones. -/
public instance wEqualsLocallyBijective : (topology B S hS).WEqualsLocallyBijective A :=
  .ofEssentiallySmall.{u} _

end Concrete

/-- Abelian-group-valued sheaves on the small étale site of `S` form an abelian category. -/
public noncomputable instance abelian_sheaf :
    Abelian (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  CategoryTheory.sheafIsAbelian

/-- Abelian-group-valued sheaves on the small étale site of `S` form a Grothendieck abelian
category. -/
public instance isGrothendieckAbelian_sheaf :
    IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

end SmallEtale

namespace SmallAffineEtale

section Concrete

variable {A : Type u'} [Category.{u} A] {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Presheaves on the small affine étale site of `S` valued in a `u`-concrete category with
limits and colimits can be sheafified, because the site is essentially small. -/
public noncomputable instance hasSheafify : HasSheafify (topology B S hS) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On the small affine étale site of `S`, the morphisms inverted by sheafification are exactly
the locally bijective ones. -/
public instance wEqualsLocallyBijective : (topology B S hS).WEqualsLocallyBijective A :=
  .ofEssentiallySmall.{u} _

end Concrete

/-- Abelian-group-valued sheaves on the small affine étale site of `S` form an abelian
category. -/
public noncomputable instance abelian_sheaf :
    Abelian (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  CategoryTheory.sheafIsAbelian

/-- Abelian-group-valued sheaves on the small affine étale site of `S` form a Grothendieck
abelian category. -/
public instance isGrothendieckAbelian_sheaf :
    IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

end SmallAffineEtale

end AlgebraicGeometry

end
