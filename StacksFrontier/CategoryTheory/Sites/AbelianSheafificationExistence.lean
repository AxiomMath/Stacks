module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Existence of sheafification for presheaves of abelian groups

Presheaves of abelian groups with sections in `Type w` on a site admit a left exact
sheafification as soon as the site is essentially small at `w`; no inequality between `w` and the
universes of the objects and morphisms of the site is required.

## Main results

* `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall`:
  abelian presheaves with sections in `w` on a site essentially small at `w` can be sheafified.

## References

* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology

/-- Presheaves of abelian groups with sections in `Type w` on a site which is essentially small
at `w` admit a sheafification, and it is left exact. Neither the universe of the objects of the
site nor that of its morphisms need be contained in `w`. -/
theorem hasSheafify_addCommGrpCat_of_essentiallySmall.{w, v, u} {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{w} C] :
    HasSheafify J AddCommGrpCat.{w} :=
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J) AddCommGrpCat.{w} :=
    inferInstance
  hasSheafifyEssentiallySmallSite.{v, w, u, w + 1, w} J _

end CategoryTheory.GrothendieckTopology

end
