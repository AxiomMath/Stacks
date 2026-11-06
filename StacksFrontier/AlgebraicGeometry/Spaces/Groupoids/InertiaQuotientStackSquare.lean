module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InertiaGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonSurjectivity
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The inertia square of a quotient stack

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`, let `G/U` be its stabilizer
group algebraic space and let `(G, R', s', t', c')` be its inertia groupoid. This file constructs
the 2-commutative square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

of stacks in groupoids over the big fppf site and proves that it is 2-cartesian. Its lower-left
corner is the quotient stack `[G/R']` of the inertia groupoid, which is equivalent to the inertia
stack `ℐ_{[U/R]}` by `AlgebraicGeometry.Stack.isEquivalence_inertiaQuotientStackCompare`.

## Main definitions

* `AlgebraicGeometry.Stack.inertiaQuotientStackSquare`: the 2-commutative square above.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_inertiaForgetful_source`: the source
  square of `inertiaForgetful` is cartesian.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaQuotientStackSquare`: the square is a
  2-fibre product.
* `AlgebraicGeometry.Stack.inertiaQuotientStackSquare_pt`,
  `AlgebraicGeometry.Stack.inertiaQuotientStackSquare_fst` and
  `AlgebraicGeometry.Stack.inertiaQuotientStackSquare_snd`: the apex and the two legs of the
  square.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PC](https://stacks.math.columbia.edu/tag/06PC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this). -/
local instance hasPullbacks_presheaf_inertiaQuotientStackSquare :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_inertiaQuotientStackSquare
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- For a groupoid `(U, R, s, t, c)` in algebraic spaces over `B`, the square

```
R' --(r, g) ↦ r--> R
|                  |
s'                 s
v                  v
G ---------------> U
```

formed by the source maps of the inertia groupoid and of `(U, R, s, t, c)` and by the forgetful
morphism `inertiaForgetful` between them is cartesian. -/
theorem isPullback_inertiaForgetful_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback (inertiaForgetful G).toGroupoidHom.mapArrows
      (inertiaGroupoid G).source.hom G.source.hom
      (inertiaForgetful G).toGroupoidHom.mapObjects :=
  IsPullback.of_hasPullback G.source.hom (stabilizerToObjects G).hom

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- For a groupoid `(U, R, s, t, c)` in algebraic spaces over `B` with stabilizer group algebraic
space `G/U` (Stacks 0448), the 2-commutative square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

of stacks in groupoids over the big fppf site: the apex is the stack `𝒮_G` of the stabilizer,
the horizontal arrows are the 1-morphism of Stacks 0458 induced by `G → U` and the projection of
Stacks 044R for the inertia groupoid `(G, R', s', t', c')` of Stacks 06PB, and the vertical
arrows are that projection for `(U, R, s, t, c)` and the 1-morphism of Stacks 046Q induced by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaForgetful`. The filler is the 2-isomorphism
of Stacks 046Q. -/
@[stacks 06PC "the canonical square, lower-left corner as the quotient stack [G/R'] of 06PB"]
noncomputable def inertiaQuotientStackSquare (G : GroupoidInAlgebraicSpaces C S hS B) :
    let J := BigFppfOver.topology C S hS
    let Q : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩
    let I : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack (inertiaGroupoid G), isStackInGroupoids_quotientStack (inertiaGroupoid G)⟩
    let W : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory G.objects⟩
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) : W ⟶ Q)
      (Bicategory.InducedBicategory.mkHom (quotientStackMap (inertiaForgetful G)) : I ⟶ Q) :=
  (functorialitySquare (inertiaForgetful G)).swap

/-- The apex of `inertiaQuotientStackSquare G` is the stack `𝒮_G` of the stabilizer group algebraic
space of Stacks 0448, read over the big fppf site. -/
theorem inertiaQuotientStackSquare_pt (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaQuotientStackSquare G).pt.toBasedCategory =
      liftedFibredCategory (stabilizerOverBase G) := rfl

/-- The horizontal leg `𝒮_G ⟶ 𝒮_U` of `inertiaQuotientStackSquare G` is the 1-morphism of Stacks
0458 induced by the structure morphism `G → U` of the stabilizer. -/
theorem inertiaQuotientStackSquare_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaQuotientStackSquare G).fst.hom =
      liftedAssociatedMap (inertiaForgetful G).objectsMap := rfl

/-- The vertical leg `𝒮_G ⟶ [G/R']` of `inertiaQuotientStackSquare G` is the quotient-stack
projection of Stacks 044R for the inertia groupoid of Stacks 06PB. -/
theorem inertiaQuotientStackSquare_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    (inertiaQuotientStackSquare G).snd.hom =
      liftedQuotientStackProjection (inertiaGroupoid G) := rfl

/-- The square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

of `AlgebraicGeometry.Stack.inertiaQuotientStackSquare` is a 2-fibre product (Stacks 003Q) in the
bicategory of stacks in groupoids over the big fppf site, i.e. the diagram is 2-cartesian. -/
@[stacks 06PC "that square is 2-cartesian, lower-left corner as the quotient stack [G/R'] of 06PB"]
noncomputable def isTwoFibreProduct_inertiaQuotientStackSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (inertiaQuotientStackSquare G) :=
  Bicategory.isTwoFibreProduct_swap
    (isTwoFibreProduct_functorialitySquare_of_isPullback (inertiaForgetful G)
      (isPullback_inertiaForgetful_source G))

end AlgebraicGeometry.Stack

end
