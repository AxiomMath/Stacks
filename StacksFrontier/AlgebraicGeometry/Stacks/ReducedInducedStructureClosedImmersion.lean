module

public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction

/-!
# A closed immersion from a reduced stack cuts out the reduced induced structure

Let `𝒳` be an algebraic stack over `S` and let `i : 𝒵 ⟶ 𝒳` be a closed immersion of algebraic
stacks in the sense of **Stacks 04YL** whose source is reduced. This file shows that the
essential image of `i` is the *reduced induced algebraic stack structure* of **Stacks 050C** on
the set of points `i` hits, compares the two renderings of a reduction in Definition 050C — the
structure `AlgebraicGeometry.Stack.StackReduction` (a reduced algebraic stack with a closed
immersion into `𝒳` surjective on points) and the predicate `AlgebraicGeometry.Stack.IsReduction`
on object properties of `𝒳` — and constructs a reduction of every algebraic stack over `S`.

## Main results

* `AlgebraicGeometry.Stack.isReducedStack_fullSubcategory_essImage`: the full subcategory cut out
  by the essential image of an immersion with reduced source is reduced.
* `AlgebraicGeometry.Stack.range_pointsMap_essImageInclusion`: the inclusion of that full
  subcategory hits exactly the points the immersion does.
* `AlgebraicGeometry.Stack.isReducedInducedStackStructure_essImage`: the essential image of a
  closed immersion with reduced source is the reduced induced algebraic stack structure on the
  range of its map on points.
* `AlgebraicGeometry.Stack.StackReduction.ofIsReduction`: a reduction in the object-property
  rendering of Definition 050C gives one in the 1-morphism rendering.
* `AlgebraicGeometry.Stack.StackReduction.isReduction`: a reduction in the 1-morphism rendering
  of Definition 050C gives one in the object-property rendering.
* `AlgebraicGeometry.Stack.stackReduction`: every algebraic stack over `S` has a reduction in the
  1-morphism rendering.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The full subcategory cut out by the essential image of an immersion with reduced source is
reduced.** For an immersion `i : 𝒵 ⟶ 𝒳` with `𝒵` reduced, the full subcategory of `𝒳` cut out
by the essential image of `i`, for any proof that it is an algebraic stack, is reduced. -/
theorem isReducedStack_fullSubcategory_essImage (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsImmersion B S hS i) (hred : IsReducedStack B S hS 𝒵)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    IsReducedStack B S hS
      (fullSubcategoryAlgebraicStack 𝒳
        (CatFiberedInGroupoids.homFunctor i.hom).essImage hP) := by
  obtain ⟨f, hfe, -⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage i hi hP
  exact isReducedStack_of_isEquivalence_stackMorphism f hfe
    (isSurjective_of_isEquivalenceFunctor B S hS f hfe) hred

/-- **The inclusion of the essential image of an immersion hits exactly the points the immersion
hits.** For an immersion `i : 𝒵 ⟶ 𝒳`, the map on points of the inclusion of the full
subcategory cut out by the essential image of `i` has the same range as the map on points of
`i`. -/
theorem range_pointsMap_essImageInclusion (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsImmersion B S hS i)
    (hP : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage)) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳
          (CatFiberedInGroupoids.homFunctor i.hom).essImage hP)) =
      Set.range (AlgebraicStacks.pointsMap B S hS i) := by
  obtain ⟨f, hfe, ⟨α⟩⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage i hi hP
  rw [← AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom, AlgebraicStacks.pointsMap_comp,
    Set.range_comp, (isSurjective_of_isEquivalenceFunctor B S hS f hfe).range_eq, Set.image_univ]

/-- **A closed immersion with reduced source cuts out the reduced induced algebraic stack
structure on the set of points it hits**, in the sense of **Stacks 050C**: for a closed immersion
`i : 𝒵 ⟶ 𝒳` with `𝒵` reduced, the essential image of `i` is the reduced induced algebraic stack
structure on the range of the map on points of `i`. -/
theorem isReducedInducedStackStructure_essImage (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i) (hred : IsReducedStack B S hS 𝒵) :
    IsReducedInducedStackStructure B S hS
      (Set.range (AlgebraicStacks.pointsMap B S hS i))
      (CatFiberedInGroupoids.homFunctor i.hom).essImage :=
  have hiImm : AlgebraicStacks.IsImmersion B S hS i :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS i hi
  ⟨⟨AlgebraicStacks.isClosedSubstack_essImage i hi,
      fun hP => range_pointsMap_essImageInclusion i hiImm hP⟩,
    fun hP => isReducedStack_fullSubcategory_essImage i hiImm hred hP⟩

namespace StackReduction

/-- **A reduction in the tagged sense of Definition 050C, read as a `StackReduction`.** Let `P`
be a property of the objects of `𝒳` which is a reduction in the sense of
`AlgebraicGeometry.Stack.IsReduction` — that is, a reduced closed substack of `𝒳` whose set of
points is all of `|𝒳|`. Then the full subcategory it cuts out, with its canonical inclusion, is a
reduction of `𝒳` in the 1-morphism rendering `AlgebraicGeometry.Stack.StackReduction`. -/
def ofIsReduction {P : ObjectProperty 𝒳.val.val.obj} (h : IsReduction B S hS P) :
    StackReduction B S hS 𝒳 where
  reduction := fullSubcategoryAlgebraicStack 𝒳 P h.1.1.2.choose
  inclusion := fullSubcategoryInclusion 𝒳 P h.1.1.2.choose
  isClosedImmersion := h.1.1.2.choose_spec
  pointsRange := h.1.2 _
  isReducedStack := h.2 _

/-- **A reduction in the 1-morphism rendering of Definition 050C gives one in the object-property
rendering.** The reduction of `𝒳` carried as an `AlgebraicGeometry.Stack.StackReduction` — a
reduced algebraic stack with a closed immersion into `𝒳` surjective on points — cuts out a
reduction of `𝒳` in the tagged sense of `AlgebraicGeometry.Stack.IsReduction`, namely the
essential image of its inclusion. -/
theorem isReduction (R : StackReduction B S hS 𝒳) :
    IsReduction B S hS (CatFiberedInGroupoids.homFunctor R.inclusion.hom).essImage := by
  have h := isReducedInducedStackStructure_essImage R.inclusion R.isClosedImmersion
    R.isReducedStack
  rwa [R.pointsRange] at h

end StackReduction

/-- **Every algebraic stack over `S` has a reduction** (**Stacks 050C**), in the 1-morphism
rendering `AlgebraicGeometry.Stack.StackReduction`: the full subcategory of `𝒳` cut out by a
chosen reduced induced algebraic stack structure on the whole space of points of `𝒳`, with its
inclusion. -/
noncomputable def stackReduction (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    StackReduction B S hS 𝒳 :=
  StackReduction.ofIsReduction
    (exists_isReducedInducedStackStructure 𝒳 Set.univ
      (@isClosed_univ _ (pointTopology B S hS 𝒳.val))).choose_spec

end AlgebraicGeometry.Stack

end
