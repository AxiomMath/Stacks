module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.PointwiseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces.BaseChangeComp

/-!
# Groupoids in algebraic spaces (Stacks 043W)

Let `B` be an algebraic space over a scheme `S` of a big fppf site. Following Stacks 043W, a
*groupoid in algebraic spaces over `B`* consists of algebraic spaces `U` of objects and `R` of
arrows, both over `B`, together with source and target morphisms `R ⟶ U` over `B` and a
composition morphism defined on the algebraic-space fibre product `R ×_{s, U, t} R`, such that
evaluating at every test scheme gives a groupoid. A *morphism* of such groupoids over the same
base is a morphism of the underlying groupoids in presheaves which respects the two structure
morphisms to `B`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces`: **Stacks 043W**, part (1).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom`: **Stacks 043W**, part (2).
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.id` and `…Hom.comp`: the identity morphism and
  the composition of morphisms of groupoids in algebraic spaces over a fixed base, which are the
  identity and the composition of the underlying groupoids in presheaves.
* `AlgebraicGeometry.composableToPullback`: the comparison from the presheaf of composable pairs
  of arrows to the presheaf fibre product, which is what lets the groupoid condition be imposed
  on the *given* algebraic-space composition.
* `AlgebraicGeometry.Space.groupoidPreRelation`: the pre-relation `(t, s)` on the object space
  cut out by the target and source morphisms of a groupoid in algebraic spaces.
* `AlgebraicGeometry.Space.BaseChange`: a groupoid in algebraic spaces over a new base together
  with its canonical projection to the original groupoid, the two structure spaces being the
  chosen fibre products with the new base.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso`: an isomorphism of groupoids in algebraic
  spaces over a fixed base, a morphism each way whose composites are the identity on the object
  and on the arrow space. `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'` and
  `…Iso.mk'` are the constructors which do not ask for the identity law, respectively for the
  backwards morphism.
* `AlgebraicGeometry.Space.baseChangeComposableToOld`: the map from the composable pairs of a
  base-changed groupoid to those of the original, which is what the composition of
  `AlgebraicGeometry.Space.baseChange` is built from.
* `AlgebraicGeometry.Space.baseChangeCompIso`: base changing a groupoid along `B' ⟶ B` and then
  along `B'' ⟶ B'` is base changing it along the composite, as an isomorphism of groupoids in
  algebraic spaces over `B''`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.points_isGroupoid`: **Stacks 043W**, part (1) read
  back off the definition — the source and the target of the quintuple are morphisms over `B`,
  and the `T`-points of the object space form a groupoid category whose arrows are the `T`-points
  of the arrow space with the prescribed endpoints and whose composition is the composition
  morphism of the quintuple.
* `AlgebraicGeometry.Space.groupoidPreRelation_isPreEquivalenceRelation`: **Stacks 043X**, the
  pre-relation of a groupoid in algebraic spaces is a pre-equivalence relation.
* `AlgebraicGeometry.Space.baseChange`: **Stacks 0DTA**, a groupoid in algebraic spaces over `B`
  pulls back along any morphism `B' ⟶ B` of algebraic spaces, and the projections are a morphism
  of groupoids.
* `AlgebraicGeometry.Space.pullbackRightPullbackFstIso_hom_baseChange_map_comp`: the comparison
  of iterated fibre products matches the composition laws of the two base changes. With the
  matching source and target lemmas this is the whole content of
  `AlgebraicGeometry.Space.baseChangeCompIso`.

The underlying groupoid in presheaves, and with it the evaluated groupoid at each test scheme, is
available through `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidInFunctors`.

## A Chapter 78 tag

Stacks 043W is `spaces-groupoids`, **Chapter 78**, which is not in this directory's range of
chapters 81–111. It is formalized here because the Chapter 100–101 results that need it cannot be
stated without it, exactly as for `AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget`
(Stacks 06F8, Chapter 74). A later Chapter 78 development should reuse these names rather than
reshape them.

The definitions are the standard ones: two structures with fixed field names and order, the
helper `composableToPullback`, and a single universe, in the library's namespace. There is no
abbreviation for the presheaf category, since it would name no mathematics; it is inlined.

## Implementation notes

The base is an arbitrary algebraic space over `S`, not a scheme. All structure maps are morphisms
in the category of algebraic spaces over `S` of **Stacks 02X2**, so each is a natural
transformation of presheaves together with algebraicity of its source and target, and the domain
of the composition is the fibre product of that category,
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` (**Stacks 02X2** again), whose algebraicity is
`AlgebraicGeometry.isAlgebraicSpace_pullback`.

`composableToPullback` is the canonical map out of the presheaf of composable pairs
(`Deformation.composableArrows`, **Stacks 06K3**) into the presheaf pullback; it is built with
`CategoryTheory.Limits.pullback.lift` from the two projections. Its role is that the pointwise
groupoid condition is then stated about the composition morphism *of algebraic spaces* that the
structure carries, rather than about a second, independently chosen composition operation on
presheaves.

The pre-relation of **Stacks 043X** is taken in the slice of *presheaves* over the underlying
presheaf of the base, `CategoryTheory.Over B.obj`, which is where
`AlgebraicGeometry.Space.PreRelation` and `AlgebraicGeometry.Space.IsPreEquivalenceRelation`
(**Stacks 043C**) are stated. Algebraic spaces over `B` are a full subcategory of that slice and
by **Stacks 02X2** their fibre product over `B` is the presheaf one, so the product `U ⨯ U` and
the induced relation on the points of each test scheme are literally the same objects as in the
slice of `AlgebraicGeometry.AlgebraicSpaces` over `B`; nothing of the source definition is lost
by taking the larger slice, and the statement applies to more.

Base change along `B' ⟶ B` is built one test object at a time: a section of the base-changed
object or arrow space over a test object is a pair of a section of the new base and a section of
the old space with the same image in `B`, by `AlgebraicGeometry.Space.fiberProductAtEquiv`, since
limits of presheaves are computed pointwise. For a fixed section of the new base the pairs with
that first component are the sections of the old groupoid, so the base change is pointwise a
groupoid — that is `AlgebraicGeometry.Space.FiberBaseChange.pointwise` — and the projections are
a morphism of the underlying groupoids in presheaves. The structure's composition is required on
the *chosen* fibre product rather than on the composable pairs, so the construction transports
the pointwise groupoid along the comparison, which is
`AlgebraicGeometry.Space.transportPointwise`.

The groupoid-in-presheaves vocabulary is **Stacks 06K3** and is already formalized, in
`StacksFrontier/Deformation/Groupoid/Basic.lean`: `Deformation.PointwiseGroupoid`,
`Deformation.composableArrows`, `@[stacks 06K3 "objects"] Deformation.GroupoidInFunctors` and
`@[stacks 06K3 "morphisms"] Deformation.GroupoidInFunctors.Hom`. Nothing of it is re-coined here.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 0DTA](https://stacks.math.columbia.edu/tag/0DTA)
-/
