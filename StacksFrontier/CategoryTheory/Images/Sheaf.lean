module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Limits
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.UnderImages
public import StacksFrontier.CategoryTheory.Images.Reflective

/-!
# Images in a category of sheaves

A category of sheaves `CategoryTheory.Sheaf J A` has images as soon as the category of
`A`-valued presheaves does and sheafification exists: `CategoryTheory.sheafToPresheaf` is fully
faithful with left adjoint `CategoryTheory.presheafToSheaf`, so
`Stacks.ReflectiveImages.hasImages_of_reflective` applies once the reflector preserves
monomorphisms -- and under `CategoryTheory.HasSheafify` the reflector preserves all finite
limits, hence monomorphisms.  Unwinding the construction, the image of a morphism of sheaves is
the sheafification of the image presheaf, which is the classical description.

Mathlib has images in a category of sheaves of *sets* only
(`CategoryTheory.instHasImagesSheafType`, built from `CategoryTheory.Subfunctor`), and images in
a functor category into *sets* only.  Neither is available here: the only input beyond
sheafification is images in the presheaf category, which for presheaves of commutative rings is
`Stacks.FunctorImages.hasImages` over `Stacks.CommRingImages.hasImages`.  No abelian-category
route applies, `CommRingCat` not being abelian.

## Main results

* `Stacks.SheafImages.hasImages`: `CategoryTheory.Sheaf J A` has images.
* `Stacks.SheafImages.hasImagesTopCatSheaf`: `TopCat.Sheaf A X` has images. For
  `A = CommRingCat` this is the instance `CategoryTheory.Subobject.semilatticeSup` needs at sheaf
  level.
* `Stacks.SheafImages.hasColimitsOfShapeTopCatSheaf`: colimits of sheaves on a space, restated
  for `TopCat.Sheaf`.
* `Stacks.SheafImages.hasImages_sheaf_commRingCat`: sheaves of commutative rings on a small site
  have images.
* `Stacks.SheafImages.sheafAlgebra_exists_sup`: the subobjects of a sheaf of algebras over a
  sheaf of commutative rings on a space have joins, which is what the directedness half of
  Stacks Tag 05JT asks for.

## Implementation notes

`hasImages` is a genuine instance: all three of its hypotheses are classes, so the chain from
`Stacks.CommRingImages.hasImages` through `Stacks.FunctorImages.hasImages` into a sheaf category
is traversed by instance search alone, and `hasImages_sheaf_commRingCat` is `inferInstance`.

`hasImagesTopCatSheaf` has to be stated separately, and this is not redundancy.  `TopCat.Sheaf`
is a `def` with `deriving Category`, so it carries its own category instance and the head symbol
of `HasImages (TopCat.Sheaf A X)` is not `CategoryTheory.Sheaf`; instance search does not unfold
it.  That is why Mathlib restates limits for `TopCat.Sheaf` in `Mathlib.Topology.Sheaves.Limits`
rather than inheriting them.  The transfer is a `show ... from`, since the two types and the two
category instances are definitionally equal even though they are not syntactically equal.

Images are *not* the only thing missing for the join at sheaf level: with `hasImagesTopCatSheaf` in
place, `CategoryTheory.Limits.HasImages` for `CategoryTheory.Under A` is synthesized, but
`CategoryTheory.Limits.HasBinaryCoproducts (CategoryTheory.Under A)` still is not, because
`Stacks.UnderCoproducts.hasBinaryCoproducts` wants pushouts of sheaves and
`Mathlib.Topology.Sheaves.Limits` restates only *limits* for `TopCat.Sheaf`.  That is the whole
content of `hasColimitsOfShapeTopCatSheaf`, and it is the second of the two premises
`sheafAlgebra_exists_sup` needs.  `Mathlib.Topology.Sheaves.Limits` is imported for the
`CategoryTheory.Limits.HasPullbacks` that `Stacks.UnderImages.hasImages` asks for; without that
import the chain stops one step earlier.

The universe constraints on `hasImages_sheaf_commRingCat` are those of the `HasSheafify` instance
for a concrete category, which builds sheafification by the plus construction: the colimits
involved are indexed by the covering sieves of the site, so the target category needs colimits
of that size.  For a small site `C : Type u` with `Category.{u} C` -- the case of
`TopologicalSpace.Opens X` for `X : TopCat.{u}` -- the right target is `CommRingCat.{u}`.  That
instance lives in `Mathlib.CategoryTheory.Sites.LeftExact`, not in
`Mathlib.CategoryTheory.Sites.ConcreteSheafification`, and importing only the latter leaves
`HasSheafify J CommRingCat` unsynthesizable.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.SheafImages

section Site

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A]

/-- **A category of sheaves has images whenever the presheaf category does and sheafification
exists.**  Sheaves form a reflective subcategory of presheaves, and the reflector preserves
monomorphisms because `CategoryTheory.HasSheafify` makes it preserve finite limits. -/
instance hasImages [HasSheafify J A] [HasImages (Cᵒᵖ ⥤ A)] : HasImages (Sheaf J A) :=
  ReflectiveImages.hasImages_of_reflective (sheafificationAdjunction J A)

end Site

section Space

variable (A : Type u₂) [Category.{v₂} A] (X : TopCat.{u₁})

/-- **A category of sheaves on a topological space has images.**  Restated for `TopCat.Sheaf`,
whose own category instance hides the site from instance search. -/
instance hasImagesTopCatSheaf [HasSheafify (Opens.grothendieckTopology X) A]
    [HasImages ((TopologicalSpace.Opens X)ᵒᵖ ⥤ A)] : HasImages (TopCat.Sheaf A X) :=
  show HasImages (Sheaf (Opens.grothendieckTopology X) A) from inferInstance

/-- Colimits of sheaves on a topological space, restated for `TopCat.Sheaf`.  Mathlib restates
*limits* for `TopCat.Sheaf` in `Mathlib.Topology.Sheaves.Limits` but not colimits, so a pushout
of sheaves is unreachable at this signature without this transfer. -/
instance hasColimitsOfShapeTopCatSheaf (K : Type*) [Category K]
    [HasColimitsOfShape K (Sheaf (Opens.grothendieckTopology X) A)] :
    HasColimitsOfShape K (TopCat.Sheaf A X) :=
  show HasColimitsOfShape K (Sheaf (Opens.grothendieckTopology X) A) from inferInstance

end Space

/-- **Sheaves of commutative rings on a small site have images.**  Recorded to witness that the
instance chain out of `Stacks.CommRingImages.hasImages` is traversed by instance search. -/
theorem hasImages_sheaf_commRingCat {C : Type u₁} [SmallCategory C]
    (J : GrothendieckTopology C) : HasImages (Sheaf J CommRingCat.{u₁}) :=
  inferInstance

/-- **The subobjects of a sheaf of algebras over a sheaf of commutative rings on a topological
space have joins.**  This is the statement the directedness half of Stacks Tag 05JT asks for at
sheaf level; `Stacks.UnderImages.presheafAlgebra_exists_sup` is the same statement one level of
generality down, for presheaves.  The join of two subobjects is the image of the morphism out of
their coproduct, which is their tensor product over the base, so the two ingredients are images
-- supplied by `hasImagesTopCatSheaf` -- and binary coproducts, which are
`Stacks.UnderCoproducts.hasBinaryCoproducts` over the pushouts made reachable by
`hasColimitsOfShapeTopCatSheaf`.

The statement is given in the `∃` form that
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFilteredOrEmpty_of_exists_join` consumes,
rather than as the `SemilatticeSup` instance, so that it is that theorem's hypothesis verbatim. -/
theorem sheafAlgebra_exists_sup {X : TopCat.{u₁}} (A : TopCat.Sheaf CommRingCat.{u₁} X)
    (B : Under A) (S T : Subobject B) : ∃ U : Subobject B, S ≤ U ∧ T ≤ U :=
  ⟨S ⊔ T, le_sup_left, le_sup_right⟩

end Stacks.SheafImages
