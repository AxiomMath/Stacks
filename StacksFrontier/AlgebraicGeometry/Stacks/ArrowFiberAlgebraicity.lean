module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackIsomPresheaf

/-!
# The arrow fibre of a groupoid in algebraic spaces is an algebraic space

Let `G` be a groupoid in algebraic spaces over `S` and let `x`, `y` be two points of its object
space over a test object `T` of the big fppf site. The *arrow fibre*
`AlgebraicGeometry.Stack.arrowFiber G T x y` is the presheaf fibre product of the arrow space over
the pair of endpoints against the pair `(y, x)`, and **Stacks 044V** identifies it with the
isomorphism presheaf of the associated quotient stack at `x` and `y`.

This module records that the arrow fibre is an algebraic space, and that its projection to the
test object inherits being locally of finite type from the source map of the groupoid. Both are
needed to read a finiteness property of an isomorphism presheaf off the groupoid presenting the
stack.

The arrow fibre is a fibre product of algebraic spaces over the product of the object space with
itself, so the first statement is **Stacks 02X2** once that product is known to be an algebraic
space — which is the remaining ingredient proved here, the product being the fibre product over
the final object. The second is base-change stability of the chart condition, **Stacks 0AMM**,
applied to the cartesian square of the fibre product, after cancelling the second projection off
the pair of endpoints to see that the pair is locally of finite type.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_prod`: **Stacks 02X2** at the categorical product —
  a product of two algebraic spaces over `S` is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_arrowFiber`: the arrow fibre is an algebraic space.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_arrowFiber_fst`: its projection to the test
  object is locally of finite type as soon as the groupoid's source map is.

## Implementation notes

`isAlgebraicSpace_prod` is stated here rather than beside the other Stacks 02X2 results because
it is the product the pair of endpoints of the arrow space maps into, and the arrow-fibre results
are its only consumers in this development. It is the categorical product of presheaves, obtained
from the chosen fibre product over the final object of the site through the comparison of a
product cone with a cartesian square over a terminal object; the library's
`AlgebraicGeometry.isAlgebraicSpace_pullback_mkId` is the same special case stated for the
cartesian fibre product rather than for `F ⨯ G`, and does not apply to the product directly.

No Stacks tag attribute is placed on any of the three. Stacks 02X2 already carries its sites, on
`AlgebraicGeometry.isAlgebraicSpace_pullback` and on
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, and the product is a special case of
the fibre product those state, so a site here would be a second site for content already covered.
Stacks 044V likewise carries its site on
`AlgebraicGeometry.Stack.isomPresheaf_equiv_arrowFiber`, which is the identification; these are
properties of the object it identifies, not the identification. Stacks 0AMM is consumed, not
restated.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 02X2** at the categorical product: the product of two algebraic spaces over `S`,
taken in presheaves on the big fppf site, is an algebraic space.

The final object of the site is `S` over itself, its Yoneda image is an algebraic space, and a
product cone is the same thing as a cartesian square over a terminal object. So the product is
isomorphic to the chosen fibre product of the two structural morphisms, which is an algebraic
space by Stacks 02X2, and algebraicity transports along that isomorphism. -/
theorem isAlgebraicSpace_prod
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) :
    IsAlgebraicSpace B S hS (F ⨯ G) := by
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal T := Over.mkIdTerminal
  have hYT : IsTerminal (yoneda.obj T) := hT.isTerminalObj yoneda T
  let r : F ⟶ yoneda.obj T := hYT.from F
  let s : G ⟶ yoneda.obj T := hYT.from G
  exact isAlgebraicSpace_of_iso B S hS
    ((limit.isLimit (pair F G)).conePointUniqueUpToIso
      (isProductOfIsTerminalIsPullback r s (pullback.fst r s) (pullback.snd r s)
        hYT (pullbackIsPullback r s))).symm
    (isAlgebraicSpace_pullback B S hS r s hF hG (isAlgebraicSpace_yoneda B S hS T))

/-- The arrow fibre of a groupoid in algebraic spaces at a pair of points of its object space is
an algebraic space.

It is the fibre product of the arrow space against the pair `(y, x)` over the product of the
object space with itself, and all three of those are algebraic spaces, so this is
**Stacks 02X2**. -/
theorem isAlgebraicSpace_arrowFiber
    {Bs : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (T : BigFppfOver B S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    IsAlgebraicSpace B S hS (Stack.arrowFiber G T x y) :=
  isAlgebraicSpace_pullback B S hS
    (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
    (prod.lift G.target.hom G.source.hom)
    (isAlgebraicSpace_yoneda B S hS T) G.arrows.property
    (isAlgebraicSpace_prod B S hS G.objects.property G.objects.property)

/-- The projection of the arrow fibre to the test object is locally of finite type as soon as the
source map of the groupoid is.

The pair of endpoints is locally of finite type, because composing it with the second projection
of the product gives the source map and being locally of finite type cancels off a composite
(**Stacks 0462**); the projection in question is its base change along the pair `(y, x)`, and the
chart condition is stable under base change by **Stacks 0AMM**. -/
theorem isLocallyOfFiniteType_arrowFiber_fst
    {Bs : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Bs)
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (T : BigFppfOver B S hS)
    (x y : G.objects.obj.obj (Opposite.op T)) :
    IsLocallyOfFiniteType B S hS
      (pullback.fst (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
        (prod.lift G.target.hom G.source.hom)) := by
  let H : AlgebraicSpaces B S hS :=
    ⟨G.objects.obj ⨯ G.objects.obj,
      isAlgebraicSpace_prod B S hS G.objects.property G.objects.property⟩
  let Y : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let endpoints : G.arrows ⟶ H :=
    ObjectProperty.homMk (prod.lift G.target.hom G.source.hom)
  let points : Y ⟶ H :=
    ObjectProperty.homMk (prod.lift (yonedaEquiv.symm y) (yonedaEquiv.symm x))
  have he : IsLocallyOfFiniteType B S hS endpoints.hom := by
    apply isLocallyOfFiniteType_of_comp B S hS
      G.arrows.property H.property G.objects.property endpoints.hom prod.snd
    simpa [endpoints] using hs
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ f => IsLocallyOfFiniteType B S hS f.hom
  have : P.IsStableUnderBaseChange :=
    holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS points endpoints).flip he

end AlgebraicGeometry.Space

end
