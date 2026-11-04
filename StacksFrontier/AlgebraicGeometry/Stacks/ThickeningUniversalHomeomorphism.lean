module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack

/-!
# A thickening of algebraic stacks is a relative thickening, a closed immersion and a universal
homeomorphism (Stacks 0CJ7)

Stacks 0CJ7 reads, verbatim:

> Let `i : 𝒳 → 𝒳'` be a morphism of algebraic stacks. The following are equivalent
> 1. `i` is a thickening of algebraic stacks, and
> 2. `i` is representable by algebraic spaces and is a thickening in the sense of Properties of
>    Stacks, Section 100.3.
> Moreover, in this case `i` is a closed immersion and a universal homeomorphism.

The condition of part (2) is `AlgebraicGeometry.Stack.IsRelativeThickening`: representability by
algebraic spaces together with the §04XB relative property at the space-level property of being a
surjective closed immersion, which is what a thickening of algebraic spaces is
(**Stacks 05ZK**). The equivalence is then the translation of the surjectivity clause of
**Stacks 0BPP** part (1) — surjectivity on the points of Stacks 04XG — into the relative property
of **Stacks 03YK**, which is **Stacks 04XI**; the closed-immersion clause is the same condition on
both sides.

The two consequences are of different depths. That `i` is a closed immersion is a clause of the
definition of a thickening in this library, since **Stacks 0BPP** part (1) realises `𝒳` as a
*closed substack* of `𝒳'`. That `i` is a universal homeomorphism is the substance: a base change
of a thickening is a thickening (**Stacks 0BPR**), and a thickening is a homeomorphism on points
because it is bijective on points and closed on points.

## Main results

* `AlgebraicGeometry.Stack.isThickening_iff_isRelativeThickening`: **Stacks 0CJ7**, the
  equivalence of (1) and (2).
* `AlgebraicGeometry.Stack.isClosedImmersion_of_isThickening`: **Stacks 0CJ7**, the
  closed-immersion conclusion.
* `AlgebraicGeometry.Stack.isHomeomorphOnPoints_of_isThickening`: a thickening of algebraic
  stacks is a homeomorphism on the topological spaces of points of Stacks 04XG and 04XL — the
  topological half of the clause of **Stacks 0BPP** part (1) that says the two topological spaces
  are equal.
* `AlgebraicGeometry.Stack.universalHomeomorphism_of_isThickening`: **Stacks 0CJ7**, the
  universal-homeomorphism conclusion.

## Implementation notes

Bijectivity on points of a thickening is
`AlgebraicGeometry.Stack.bijective_pointsMap_of_isThickening`; closedness on points is
`AlgebraicGeometry.Stack.AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion`
(**Stacks 0H20**) applied to the closed-immersion clause. A continuous closed bijection is a
homeomorphism, and continuity of the map on points is Stacks 04XL,
`AlgebraicGeometry.Stack.continuous_pointsMap`.

The universal-homeomorphism conclusion is stated at the model-independent
`AlgebraicGeometry.Stack.UniversalHomeomorphism`, which quantifies over *every* 2-fibre product
square of the cospan, rather than at
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`, which tests only the canonical
square of Stacks 04T2. The canonical-square form is the weaker one and is recorded below as
`AlgebraicGeometry.Stack.AlgebraicStacks.universalHomeomorphism_of_isThickening`; it is a single
application of the model-independent statement.

## References

* [Stacks Project, Tag 0CJ7](https://stacks.math.columbia.edu/tag/0CJ7)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {i : 𝒳 ⟶ 𝒳'}

/-- A 1-morphism of algebraic stacks over `S` is a thickening in the sense of **Stacks 0BPP** part
(1) if and only if it is representable by algebraic spaces and is a thickening in the relative sense
of §04XB, that is a closed immersion all of whose algebraic-space base changes are surjective.

The closed-immersion clause is the same on both sides; the surjectivity clause is surjectivity on
the points of Stacks 04XG on the left and the relative property of Stacks 03YK on the right, and
the two agree by **Stacks 04XI**. -/
@[stacks 0CJ7 "equivalence of (1) and (2)"]
theorem isThickening_iff_isRelativeThickening (i : 𝒳 ⟶ 𝒳') :
    IsThickening i ↔ IsRelativeThickening B S hS i.hom :=
  ⟨isRelativeThickening_of_isThickening B S hS, fun h => ⟨⟨h.1, h.2.1⟩,
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS i h.1).2 (h.2.2 h.1)⟩⟩

/-- A thickening of algebraic stacks over `S` is a closed immersion in the sense of **Stacks 04YL**
part (2).

In this library that is a clause of the definition of a thickening: **Stacks 0BPP** part (1)
realises the source as a *closed substack* of the target, and
`AlgebraicGeometry.Stack.IsThickening` records that closed immersion rather than recovering it
from a looser condition. -/
@[stacks 0CJ7 "closed immersion"]
theorem isClosedImmersion_of_isThickening (hi : IsThickening i) :
    AlgebraicStacks.IsClosedImmersion B S hS i :=
  hi.1

/-- **A thickening of algebraic stacks is a homeomorphism on points.** The map `|𝒳| → |𝒳'|` that
a thickening induces on the topological spaces of points of Stacks 04XG and 04XL is a
homeomorphism.

It is continuous by Stacks 04XL, bijective because a thickening is surjective on points by
definition and injective as a closed immersion
(`AlgebraicGeometry.Stack.bijective_pointsMap_of_isThickening`), and closed because a closed
immersion of algebraic stacks is closed on points (**Stacks 0H20**); a continuous closed
bijection is a homeomorphism.

This is the topological clause of **Stacks 0BPP** part (1), that the two topological spaces are
equal. -/
theorem isHomeomorphOnPoints_of_isThickening (hi : IsThickening i) :
    AlgebraicStacks.IsHomeomorphOnPoints B S hS i := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒳'.val
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨continuous_pointsMap B S hS 𝒳.val 𝒳'.val i.hom.hom,
      AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion B S hS i hi.1,
      bijective_pointsMap_of_isThickening hi⟩

/-- A thickening of algebraic stacks over `S` is a universal homeomorphism in the sense of
**Stacks 0CI7**: every base change of it induces a homeomorphism on the topological spaces of
points of Stacks 04XG and 04XL.

A base change of a thickening is a thickening (**Stacks 0BPR**,
`AlgebraicGeometry.Stack.isThickening_fst_of_isTwoFibreProduct`), and a thickening is a
homeomorphism on points by
`AlgebraicGeometry.Stack.isHomeomorphOnPoints_of_isThickening`. The statement is at the
model-independent `AlgebraicGeometry.Stack.UniversalHomeomorphism`, so it tests every 2-fibre
product square of the cospan and not only the canonical one. -/
@[stacks 0CJ7 "universal homeomorphism"]
theorem universalHomeomorphism_of_isThickening (hi : IsThickening i) :
    UniversalHomeomorphism B S hS i := fun _ _ P hP =>
  isHomeomorphOnPoints_of_isThickening B S hS
    (isThickening_fst_of_isTwoFibreProduct B S hS hi P hP)

namespace AlgebraicStacks

/-- **Stacks 0CJ7, the universal-homeomorphism conclusion at the canonical 2-fibre products.** A
thickening of algebraic stacks over `S` is a universal homeomorphism in the form of
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`, which tests the canonical
squares of Stacks 04T2 only. It is
`AlgebraicGeometry.Stack.universalHomeomorphism_of_isThickening` evaluated at the canonical
square. -/
theorem universalHomeomorphism_of_isThickening (hi : IsThickening i) :
    UniversalHomeomorphism B S hS i := fun 𝒵 g =>
  Stack.universalHomeomorphism_of_isThickening B S hS hi 𝒵 g
    (twoFibreProductSquareAlgebraicStacks B S hS g i)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g i)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
