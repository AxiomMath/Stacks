module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# The `𝒪_X`-modules on an algebraic space form a balanced category, in any universe

Let `X` be an algebraic space over a scheme `S` of a big fppf site.  A morphism of `𝒪_X`-modules
which is both a monomorphism and an epimorphism is an isomorphism, for the sections in any
universe containing the universe of the schemes.

`AlgebraicGeometry.Space.balanced_modules` of
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/CoherentSheafCycle.lean` is the same statement for
sections in the universe of the schemes itself; the suffix `_max` here marks the version for an
arbitrary larger universe.

## Main results

* `AlgebraicGeometry.Space.balanced_modules_max`: the category
  `AlgebraicGeometry.Space.Modules.{u, max u m}` of `𝒪_X`-modules is balanced.

## Implementation notes

The content is that the category is abelian, together with
`Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian`.  Mathlib's abelian structure on a
category of sheaves of modules asks for sheafification of `AddCommGrpCat`-valued presheaves on
the site, in the universe of the module sections, and for the local equivalences there to be the
locally bijective morphisms.  `AlgebraicGeometry.Space.ModulesAbelian` supplies both at the
universe `u` of the sections of the structure sheaf; what is needed here is the same two facts
one universe parameter more generally, and they are obtained from
`CategoryTheory.hasSheafify_addCommGrpCat_of_essentiallySmall` and
`CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall`.

Those two reach the module universe `max v z` on a site which is essentially small at `z`, where
`v` is the universe of the *morphisms* of the site.  The small étale site of an algebraic space
has its objects in `Type (u + 1)` but its morphisms in `Type u`, and it is essentially small at
`u` by `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`; enlarging the witnessing
universe by `CategoryTheory.essentiallySmall_lift` therefore gives both facts at every module
universe of the form `max u m`, and no universe inequality about the objects of the site is
involved.

The module universe cannot be freed from `u`, and the obstruction is a single instance rather
than the shape of those two conclusions.  Both facts hold at `AddCommGrpCat.{w}` for exactly the
universe `w` at which the site is essentially small, by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, both of which
take `EssentiallySmall.{w}` and conclude at `w` itself; granting `EssentiallySmall.{m}` of the
small étale site makes the proof below, and `Balanced (Modules.{u, m} B S hS X.1 X.2)` with it,
go through verbatim at a free `m`.  What a free `m` lacks is that instance: `EssentiallySmall.{m}`
entails `LocallySmall.{m}`, the morphisms of the small étale site form a `Type u`, and nothing
makes them `m`-small.  The two lemmas used above state their conclusion at `max v z` because
they enlarge the witnessing universe before appealing to those; that is a consequence of the
bound and not its cause.

## References

* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The `𝒪_X`-modules with sections in any universe containing the universe of the schemes form
a balanced category: they are abelian, the small étale site being essentially small in the
universe of the schemes, which gives it sheafification of presheaves of abelian groups with
sections in that universe and identifies its local equivalences with the locally bijective
morphisms. -/
theorem balanced_modules_max : Balanced (Modules.{u, max u m} B S hS X.1 X.2) := by
  have : EssentiallySmall.{max u m} (SmallEtale B S hS X.1) := essentiallySmall_lift _
  have : HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{max u m} :=
    hasSheafify_addCommGrpCat_of_essentiallySmall (SmallEtale.topology B S hS X.1)
  have : ((smallEtaleRingedSite B S hS X.1 X.2).J).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall (SmallEtale.topology B S hS X.1)
  have : Abelian (Modules.{u, max u m} B S hS X.1 X.2) := SheafOfModules.instAbelian _
  exact Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian

end AlgebraicGeometry.Space

end
