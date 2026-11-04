module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequencePageTwo
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The smallness hypothesis of [Stacks, Tag 01GY], and what it supplies

[Stacks, Tag 01GY] (Hypercoverings, Lemma 25.5.3) begins "Let `𝒞` be a site with fibre
products". In the Stacks Project a *site* is a *small* category:

* Conventions, Section 2.2 (tag `0005`): "A category `𝒞` consists of a **set** of objects and,
  for each pair of objects, a **set** of morphisms between them. In other words, it is what is
  called a 'small' category in other texts. We will use 'big' categories (categories whose
  objects form a proper class) as well, but only those that are listed in Categories, Remark
  4.2.2."
* Sites, Remark 7.6.3 (tag `00VI`): "In order to avoid thinking about things like 'classes of
  classes' and so on, we will **not allow sites to be 'big' categories**, in contrast to what we
  do for categories and 2-categories."

So the source's site is small, and a Lean statement of [Stacks, Tag 01GY] for a site `C : Type u`
with `Category.{v} C` and *no* relation between `u` and `v` asserts strictly more than the source
does. That is not a harmless generalisation: in that regime
`Sheaf J AddCommGrpCat.{v}` is not known to be a Grothendieck abelian category at any universe,
has no known injective objects, and the second-page and abutment identifications of
[Stacks, Tag 01GY] are not available -- see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequencePageTwo.lean`.

This file records the smallness hypothesis and the inputs it supplies.

**What collapses when the site is small.** Čech cohomology of a `w`-indexed semi-representable
object over `X` has coefficients in `AddCommGrpCat.{max u v w}`, while sheaf cohomology -- Mathlib
`CategoryTheory.Sheaf.cohomologyPresheafFunctor`, which is `Ext` out of a sheafified free Yoneda
presheaf -- has coefficients in `AddCommGrpCat.{v}`, `v` being the hom universe of the site. Those
two are different categories in general, and bridging them is what the circular `Ext`-comparison
route of `SpectralSequencePageTwo.lean` was for. For a site which is small in the Stacks sense --
`C : Type v` with `Category.{v} C`, its semi-representable objects indexed by `Type v` -- the two
universes are `max v v v` and `v`, hence the **same** universe, and no bridge is needed at all.

## Main results

* `CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat_max`: **abelian sheaves in the universe
  `max u v w` on any site `C : Type u` with `Category.{v} C` have enough injectives**, with no
  hypothesis beyond sheafification. The coefficient universe already dominates the universes of
  the objects and of the homs of the site, so the `v`-smallness that
  `CategoryTheory.Sheaf.enoughInjectives_of_small` asks for is automatic. This discharges the
  `EnoughInjectives` hypothesis carried by the comparison map and the cohomology comparison of
  [Stacks, Tag 01GY] in
  `StacksFrontier/CategoryTheory/Sites/Hypercovering/DerivedComparisonBoundedBelow.lean`.
* `CategoryTheory.Sheaf.hasExt_of_smallSite`: on a small site, abelian sheaves satisfy
  `HasExt.{v}`, so sheaf cohomology is defined without assuming it. With
  `CategoryTheory.Sheaf.enoughInjectives_of_small` and Mathlib's `HasSheafify` instance for a
  small site, this means **every instance hypothesis of the hypercovering spectral sequence is
  free at the source's own hypotheses**.
* `Stacks.CategoryTheory.Hypercovering.pageTwoSmallSite`, `pageTwoSmallSite_obj`,
  `pageTwoSmallSite_map_hypercovering` and `pageTwoSmallSite_map_hypercovering'`: the second-page
  functor `(K, F) ↦ ȞᵖK(Hᵠ(F))` of [Stacks, Tag 01GY] on a small site, carrying no instance
  hypotheses, together with its value and its action on a morphism of the simplicial
  semi-representable object.

## Implementation notes

**Nothing here carries the tag `01GY`.** Its covering set is three claim-sites -- the comparison
map, the cohomology comparison and the spectral sequence -- and the third is still absent: the
injective-resolution double complex, the second-page isomorphism against `pageTwoSmallSite` and
the functorial abutment are not in the tree. A tag lands only when its whole covering set lands.

`CategoryTheory.hasExt_of_enoughInjectives` is deliberately not an instance in Mathlib, a category
having in general several reasonable `HasExt` universes; it is therefore reproved here in the one
shape a consumer on a small site wants, and left as a plain theorem rather than an instance for
the same reason. It is made a `local instance` only for the span of `pageTwoSmallSite`, whose type
mentions `Ext`.

`pageTwoSmallSite_map_hypercovering` is stated here rather than left to the consumers that need
it. `pageTwoSmallSite` is `pageTwoBifunctor` at the `HasSheafify`, `HasExt` and
`EnoughInjectives` instances resolved in this file, so invoking
`pageTwoBifunctor_map_hypercovering` from another file -- where instance search produces
different instance *terms* for the same classes -- makes the resulting definitional equality of
the two actions on morphisms pass through those terms, and it does not finish checking. Here the
instances agree syntactically and the lemma is the bifunctor lemma applied verbatim.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 0005](https://stacks.math.columbia.edu/tag/0005)
* [Stacks Project, Tag 00VI](https://stacks.math.columbia.edu/tag/00VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe w v u

namespace CategoryTheory.Sheaf

/-- **Abelian sheaves in the universe `max u v w` have enough injectives**, on any site
`C : Type u` with `Category.{v} C`, with no hypothesis beyond the existence of sheafification.

This is `CategoryTheory.Sheaf.enoughInjectives_of_small` at a coefficient universe large enough to
make its smallness hypothesis vacuous: `Small.{max u v w} C` holds for `C : Type u` outright, and
`AddCommGrpCat.{max u v w}` has coproducts indexed by `Type u` and by `Type v` and is Grothendieck
abelian at its own universe. So no relation between `u` and `v` is needed, in contrast to
`Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite`, which is about
coefficients in `AddCommGrpCat.{v}` and does need the site to be `EssentiallySmall.{v}`.

The coefficient universe `max u v w` is the one in which the hypercover cochain complex of a
`w`-indexed semi-representable object lives, so this is the form in which the comparison map and
the cohomology comparison of [Stacks, Tag 01GY] want it; it discharges the `EnoughInjectives`
hypothesis both of them carry. -/
@[sga "3 I 5.2" "special case",
  sga "4 I 7.13" "special case",
  sga "4 V 2.5.2" "special case",
  sga "4½ Arcata 1.6.3"]
theorem enoughInjectives_addCommGrpCat_max {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v w}] :
    EnoughInjectives (Sheaf J AddCommGrpCat.{max u v w}) :=
  enoughInjectives_of_small J AddCommGrpCat.{max u v w}

/-- **On a small site, abelian sheaves are locally `v`-small**: a morphism of sheaves is a family
of components indexed by the objects of the site, and both the objects and the groups of sections
are `v`-small. -/
theorem locallySmall_of_smallSite {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) :
    LocallySmall.{v} (Sheaf J AddCommGrpCat.{v}) :=
  locallySmall_of_small J AddCommGrpCat.{v}

/-- **On a small site, abelian sheaves satisfy `HasExt.{v}`**, so the sheaf cohomology of
[Stacks, Tag 01GY] -- Mathlib's `CategoryTheory.Sheaf.cohomologyPresheafFunctor`, which is an
`Ext` group -- is defined without assuming it.

The ingredients are `CategoryTheory.hasExt_of_enoughInjectives` together with the two facts that a
small site supplies: local `v`-smallness of `Sheaf J AddCommGrpCat.{v}`
(`locallySmall_of_smallSite`) and enough injectives in it
(`CategoryTheory.Sheaf.instIsGrothendieckAbelian`). Not an instance, following Mathlib's policy for
`HasExt`. -/
theorem hasExt_of_smallSite {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) :
    HasExt.{v} (Sheaf J AddCommGrpCat.{v}) :=
  have := locallySmall_of_smallSite J
  hasExt_of_enoughInjectives.{v} (Sheaf J AddCommGrpCat.{v})

end CategoryTheory.Sheaf

namespace Stacks.CategoryTheory.Hypercovering

section SmallSite

variable {C : Type v} [SmallCategory C]

/-- `CategoryTheory.Sheaf.hasExt_of_smallSite` as an instance, for the span of
`pageTwoSmallSite`, whose type mentions `Ext`. Kept local: Mathlib is deliberately selective about
`HasExt` instances, a category having in general several reasonable `HasExt` universes. -/
local instance hasExtSmallSite (J : GrothendieckTopology C) :
    HasExt.{v} (Sheaf J AddCommGrpCat.{v}) :=
  Sheaf.hasExt_of_smallSite J

variable (J : GrothendieckTopology C) (X : C)

/-- **The second page of the hypercovering spectral sequence of [Stacks, Tag 01GY] on a site in
the Stacks sense**: `(K, F) ↦ ȞᵖK(Hᵠ(F))`, contravariantly in the simplicial semi-representable
object `K` over `X` and covariantly in the coefficient sheaf `F`, carrying **no instance
hypotheses at all**.

This is `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor` at the hypotheses of the source: a
small site, and semi-representable objects indexed in the same universe. Its point is the universe
collapse described in the module docstring -- Čech cohomology of a `w`-indexed semi-representable
object has coefficients in `AddCommGrpCat.{max u v w}` and sheaf cohomology in
`AddCommGrpCat.{v}`, and here those are one and the same universe, so the second page is a functor
into `AddCommGrpCat.{v}` and no comparison of `Ext` across universes arises. The three hypotheses
`pageTwoBifunctor` carries -- `HasSheafify`, `HasExt` and (for the resolution) `EnoughInjectives`
-- are all discharged: the first and third by Mathlib's instances for a small site, the second by
`CategoryTheory.Sheaf.hasExt_of_smallSite`. -/
def pageTwoSmallSite (p q : ℕ) :
    (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      AddCommGrpCat.{v} :=
  pageTwoBifunctor.{v, v, v} X J p q

/-- **The value of the second page on a small site is `ȞᵖK(Hᵠ(F))`**, on the nose: the degree-`p`
Čech cohomology of `K` with coefficients in the degree-`q` cohomology presheaf of `F`. -/
lemma pageTwoSmallSite_obj (K : SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))
    (F : Sheaf J AddCommGrpCat.{v}) (p q : ℕ) :
    (pageTwoSmallSite J X p q).obj (op K, F) =
      ((cechCohomologyOverBifunctor.{v, v, v} X p).obj (op K)).obj
        ((Sheaf.cohomologyPresheafFunctor J q).obj F) :=
  pageTwoBifunctor_obj X J K F p q

/-- **On a morphism of simplicial semi-representable objects the second page of a small site is
the canonical pullback map on Čech cohomology**, with the coefficient sheaf fixed.

This is `Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor_map_hypercovering` at the
hypotheses of the source, stated in the file where `pageTwoSmallSite` is defined; see the
implementation notes for why it is not left to the consumers that need it. -/
lemma pageTwoSmallSite_map_hypercovering
    {K L : SimplicialObject (Limits.FormalCoproduct.{v} (Over X))} (f : K ⟶ L)
    (F : Sheaf J AddCommGrpCat.{v}) (p q : ℕ) :
    (pageTwoSmallSite J X p q).map (f.op ×ₘ 𝟙 F) =
      ((cechCohomologyOverBifunctor.{v, v, v} X p).map f.op).app
        ((Sheaf.cohomologyPresheafFunctor J q).obj F) :=
  pageTwoBifunctor_map_hypercovering X J f F p q

/-- `pageTwoSmallSite_map_hypercovering`, for an arbitrary morphism of the opposite category
rather than one of the form `f.op`.  This is the shape a consumer whose simplicial
semi-representable objects are indexed by a subcategory needs, its morphisms not being of the
form `f.op` syntactically. -/
lemma pageTwoSmallSite_map_hypercovering'
    {K L : (SimplicialObject (Limits.FormalCoproduct.{v} (Over X)))ᵒᵖ} (g : K ⟶ L)
    (F : Sheaf J AddCommGrpCat.{v}) (p q : ℕ) :
    (pageTwoSmallSite J X p q).map (g ×ₘ 𝟙 F) =
      ((cechCohomologyOverBifunctor.{v, v, v} X p).map g).app
        ((Sheaf.cohomologyPresheafFunctor J q).obj F) :=
  pageTwoSmallSite_map_hypercovering J X g.unop F p q

end SmallSite

end Stacks.CategoryTheory.Hypercovering

end
