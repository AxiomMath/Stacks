module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified

/-!
# Unramifiedness of an immersion of algebraic stacks

An immersion of algebraic stacks over `S` (Stacks 04YL, part (3)) is representable by algebraic
spaces and every algebraic space representing one of its base changes along a scheme-valued point
of the target has immersion structural morphism. Unramifiedness of morphisms of algebraic spaces
is Stacks 03ZH, part (1), and an immersion of algebraic spaces is unramified by Stacks 06CQ. This
file carries that implication up to algebraic stacks: an immersion is Deligne–Mumford, and the
relative unramifiedness property of Stacks 03YK that it inherits pointwise makes it pass the
existential étale-smooth diagram test of Stacks 0CIF at unramifiedness.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isImmersion`: **Stacks 06MY** for immersions
  at the Deligne–Mumford condition, that an immersion of algebraic stacks over `S` is
  Deligne–Mumford.
* `AlgebraicGeometry.Stack.AlgebraicStacks.someEtaleSmoothDiagram_unramified_of_isImmersion`: an
  immersion passes the existential étale-smooth diagram test at unramifiedness.

## Implementation notes

`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**) is the Deligne–Mumford condition
together with the *universal* étale-smooth diagram test, and the existential test becomes the
universal one through the converse direction of Stacks 0CIF, which asks for
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget` (**Stacks 0CFZ**) of the property
being tested. That hypothesis at unramifiedness is **Stacks 0CG3**, which this library does not
have — no property of morphisms of algebraic spaces has such a witness here — and neither does
its route, **Stacks 0CG2**: of that tag's three clauses,
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion` proves the two that follow from
the locality hypotheses alone together with the forward half of the third, and the descent half
of the third goes through **Stacks 0CF1**, which is absent. So the two results below are what of
**Stacks 0CIX** is reachable, and neither of them is Stacks 0CIX; that tag is deliberately not
claimed here.

The Deligne–Mumford condition uses only representability, through
`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`,
exactly as `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isMonomorphism` (**Stacks 06MY**)
does; the immersion condition on the represented base changes is not needed for it.

The relative property of Stacks 03YK is not stated as a result of its own because
`AlgebraicGeometry.Stack.HasRelativeProperty` carries the two instance hypotheses on the
property, so the proofs that discharge them have to stand in the same term; they are **Stacks
03ZJ** and **Stacks 042A** along the comparison of precoverages, the pair
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion` discharges for
local finite type.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 06CQ](https://stacks.math.columbia.edu/tag/06CQ)
* [Stacks Project, Tag 06MY](https://stacks.math.columbia.edu/tag/06MY)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06MY, the Deligne–Mumford assertion for immersions.** An immersion of algebraic
stacks over `S` is Deligne–Mumford.

An immersion is representable by algebraic spaces — the first conjunct of Stacks 04YL, part (3) —
and a 1-morphism representable by algebraic spaces is Deligne–Mumford, so the immersion condition
on the represented base changes is not needed. The source reduces the assertion to the
monomorphism case, an immersion being a monomorphism by Stacks 0504; the route taken here reaches
the same conclusion from less. The separatedness assertion of Stacks 06MY for immersions, which
does use the immersion condition, is
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isImmersion`. -/
@[stacks 06MY "immersions are DM"]
theorem isDM_of_isImmersion (j : 𝒵 ⟶ 𝒳) (hj : IsImmersion B S hS j) : Stack.IsDM B S hS j :=
  Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS j hj.1

/-- **An immersion of algebraic stacks over `S` passes the existential étale-smooth diagram test
of Stacks 0CIF at unramifiedness.** There is a diagram of algebraic spaces over the immersion
with smooth right vertical 1-morphism, surjective left vertical 1-morphism and étale comparison
to every 2-fibre product, whose top horizontal morphism of algebraic spaces is unramified.

Every algebraic space representing a base change of the immersion along a scheme-valued point of
the target has immersion structural morphism, so is unramified by Stacks 06CQ; that is the
relative property of Stacks 03YK at unramifiedness, which Stacks 0CIF carries to the existential
diagram test. -/
theorem someEtaleSmoothDiagram_unramified_of_isImmersion
    (j : 𝒵 ⟶ 𝒳) (hj : IsImmersion B S hS j) :
    Stack.HasPropertyOnSomeEtaleSmoothDiagram B S hS
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsUnramified B S hS g.hom) j := by
  let : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsUnramified B S hS g.hom) :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  let : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsUnramified B S hS g.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact Stack.hasPropertyOnSomeEtaleSmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS
    (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsUnramified B S hS g.hom)
    j hj.1
    fun U y hy F hF hrep =>
      Space.isUnramified_of_isImmersion B S hS
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
        (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) (hj.2 U y hy F hF hrep)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
