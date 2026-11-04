module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification above the universe of the site

Let `C` be a category carrying a Grothendieck topology `J`, and let `z` be a universe at which
`C` is essentially small.  This file produces, for the category of abelian groups whose carriers
lie in `z` together with the universe of the morphisms of `C`, the two facts that the theory of
sheaves of modules asks of its coefficient site: that abelian presheaves can be sheafified, and
that the morphisms of abelian presheaves which become isomorphisms after sheafification are
exactly the locally bijective ones.  It produces the second of those facts for presheaves of
*sets* in `z` as well.

The point is the universe.  Both facts are available in the library at the universe
`max u v` of the site itself, with `C : Type u` and morphisms in `Type v`; here they are
obtained at a universe which need not contain `u`, so that sheaves of modules on a large site
may have small sections.

## Main results

* `CategoryTheory.essentiallySmall_lift`: essential smallness is preserved by enlarging the
  witnessing universe.
* `CategoryTheory.hasSheafify_addCommGrpCat_of_essentiallySmall` and
  `CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall`: abelian presheaves with
  sections in `max v z` on an essentially small site can be sheafified.
* `CategoryTheory.hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall`: the presheaf of
  sections of such a sheaf of abelian groups is a sheaf of sets.
* `CategoryTheory.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall`: for those
  presheaves the weak equivalences are the locally bijective morphisms.
* `CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_type`: the same for presheaves of
  sets in `z`, which the library has only at the site's own universe `max u v`.

## Implementation notes

There are two routes to sheafification of presheaves valued in a concrete category, and they
reach different universes.

The explicit route is the plus construction, which forms a colimit over the opposite of the
category `J.Cover X` of covering sieves.  That category has objects in `Type (max u v)`, so the
plus construction of a presheaf valued in abelian groups with carriers in `Type w` requires the
forgetful functor to preserve filtered colimits of that size, and hence requires `max u v ≤ w`.
It does then work for every such `w`, with no smallness hypothesis, by
`preservesFilteredColimitsOfSize_of_univLE`.  What it cannot do is reach a universe not
containing `u`.  The same bound is what pins the library's instances
`Presheaf.isLocallyInjective_toSheafify'` and `Presheaf.isLocallySurjective_toSheafify'`, and
through them the generic instance deriving `J.WEqualsLocallyBijective`, to a concrete-category
universe equal to `max u v` on the nose; for the weak equivalences the plus construction does
not even tolerate enlarging `w`, since the pin there is an equality of universes rather than an
inequality.

The route taken here is instead transport along an equivalence of sites.  If `C` is essentially
small at `z` then it is essentially small at `max v z`, and the small model is then a category
whose objects and whose morphisms both lie in `Type (max v z)`.  On that model both facts are
the library's instances at their own universe, and `hasSheafifyEssentiallySmallSite` and
`GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` carry them back to `C`.  The
universe of the site objects never enters, so the result holds at `max v z` whether or not that
universe contains `u`.

The hypothesis is therefore essential smallness and not a universe inequality, and the
conclusion is at `max v z` rather than at `z`: the morphisms of `C` do enter, because
transporting a sheaf condition back from the small model takes limits over categories of
structured arrows of `C`, whose objects involve the morphisms of `C`.

## References

* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
* [Stacks Project, Tag 00ZS](https://stacks.math.columbia.edu/tag/00ZS)
-/

@[expose] public section

universe t z u₁ v₁

namespace CategoryTheory

/-- Essential smallness is preserved by enlarging the witnessing universe: a category
equivalent to a small category with objects and morphisms in `Type z` is equivalent to one with
objects and morphisms in `Type (max z t)`. -/
public theorem essentiallySmall_lift (C : Type u₁) [Category.{v₁} C] [EssentiallySmall.{z} C] :
    EssentiallySmall.{max z t} C :=
  EssentiallySmall.mk' ((equivSmallModel C).trans
    (AsSmall.equiv : SmallModel.{z} C ≌ AsSmall.{t} (SmallModel.{z} C)))

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) [EssentiallySmall.{z} C]

/-- Presheaves of abelian groups with sections in `max v z` on a site which is essentially
small at `z` admit a sheafification which preserves finite limits.  The universe of the
sections need not contain the universe of the objects of the site. -/
@[sga "3 IV 4.3.16" "partial"]
public theorem hasSheafify_addCommGrpCat_of_essentiallySmall :
    HasSheafify J AddCommGrpCat.{max v₁ z} :=
  have : EssentiallySmall.{max v₁ z} C := essentiallySmall_lift C
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max v₁ z, v₁, u₁} J

/-- The sheafification of presheaves of abelian groups with sections in `max v z` on a site
which is essentially small at `z`, as a left adjoint of the inclusion of sheaves. -/
public theorem hasWeakSheafify_addCommGrpCat_of_essentiallySmall :
    HasWeakSheafify J AddCommGrpCat.{max v₁ z} :=
  (hasSheafify_addCommGrpCat_of_essentiallySmall J).isRightAdjoint

/-- On a site which is essentially small at `z`, the presheaf of sections of a sheaf of abelian
groups with sections in `max v z` is a sheaf of sets.  The universe of the sections need not
contain the universe of the objects of the site. -/
public theorem hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall :
    J.HasSheafCompose (forget AddCommGrpCat.{max v₁ z}) :=
  have : EssentiallySmall.{max v₁ z} C := essentiallySmall_lift C
  inferInstance

/-- On a site which is essentially small at `z`, a morphism of presheaves of abelian groups
with sections in `max v z` becomes an isomorphism after sheafification exactly when it is
locally injective and locally surjective.  The universe of the sections need not contain the
universe of the objects of the site. -/
public theorem wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall :
    J.WEqualsLocallyBijective AddCommGrpCat.{max v₁ z} :=
  have : EssentiallySmall.{max v₁ z} C := essentiallySmall_lift C
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

namespace GrothendieckTopology

/-- On a site which is essentially small at `z`, a morphism of presheaves of sets in `z` becomes
an isomorphism after sheafification exactly when it is locally injective and locally surjective. -/
public theorem wEqualsLocallyBijective_type : J.WEqualsLocallyBijective (Type z) :=
  have (X : Cᵒᵖ) : Limits.HasLimitsOfShape
      (StructuredArrow X (equivSmallModel C).inverse.op) (Type z) :=
    Limits.hasLimitsOfShape_of_essentiallySmall.{z} _ _
  WEqualsLocallyBijective.ofEssentiallySmall (A := Type z) J

end GrothendieckTopology

end CategoryTheory

end
