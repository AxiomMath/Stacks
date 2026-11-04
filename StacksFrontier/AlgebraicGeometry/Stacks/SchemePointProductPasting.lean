module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableBySpaceDescent
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition

/-!
# The 2-fibre product of two points of a stack, as a base change of a presentation

Let `B` be a big fppf site, `S` a scheme contained in it, and let `u : 𝒰 ⟶ 𝒳` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. For two further 1-morphisms
`x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` this file exhibits a 2-fibre product square over the cospan
`(𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒳, u)`:

```text
    𝒯₁' ×_𝒰 𝒯₂' ------> 𝒰
         |               |
         |               | u
         v               v
    𝒯₁ ×_𝒳 𝒯₂ --------> 𝒳          where 𝒯ᵢ' = 𝒯ᵢ ×_𝒳 𝒰
```

so that the projection `𝒯₁' ×_𝒰 𝒯₂' ⟶ 𝒯₁ ×_𝒳 𝒯₂` is a base change of `u` and therefore inherits
representability by algebraic spaces (Stacks 0302) and every relative property of `u` in the sense
of Stacks 03YK (Stacks 045C). Its source is representable by an algebraic space as soon as `𝒰`,
`𝒯₁` and `𝒯₂` are and `u` is representable by algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.schemePointProductBaseChangeSquare`: the square above.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_schemePointProductBaseChangeSquare`: it is a 2-fibre
  product.
* `AlgebraicGeometry.Stack.schemePointProductBaseChangeSquare_pt`: its apex is the apex of
  `CategoryTheory.CatFiberedInGroupoids.tripleProductSquare`, which is a 2-fibre product of
  `𝒯₁ ×_𝒳 𝒰` and `𝒯₂ ×_𝒳 𝒰` over `𝒰`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_schemePointProductBaseChange`: the
  projection to `𝒯₁ ×_𝒳 𝒯₂` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.hasRelativeProperty_schemePointProductBaseChange`: it has every
  relative property that `u` has.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemePointProductBaseChangeSquare_pt`:
  its source is representable by an algebraic space.

## Implementation notes

The square is a single application of pasting, `CategoryTheory.Bicategory.TwoCommSq.pasteFst`: the
map `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒳` factors through `x`, so the base change of `u` along it is the base change
along `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁` of the base change of `u` along `x`, and
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst` says that the pasted rectangle is again a
2-fibre product.

The apex of that rectangle is `(𝒯₁ ×_𝒳 𝒰) ×_{𝒯₁} (𝒯₁ ×_𝒳 𝒯₂)`, and this is *syntactically* the
apex of `CategoryTheory.CatFiberedInGroupoids.tripleProductSquare` for the three 1-morphisms
`x`, `u`, `y` — so
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare` reads the same object
as a 2-fibre product of `𝒯₁ ×_𝒳 𝒰` and `𝒯₂ ×_𝒳 𝒰` over `𝒰`, with no comparison to construct.
That double reading is what the source of Stacks 05UL calls "a formal argument then shows that
`𝒯₁' ×_𝒰 𝒯₂' → 𝒯₁ ×_𝒳 𝒯₂` is the base change of `𝒰 → 𝒳`".

Representability of the apex by an algebraic space is read off the *other* square: its projection
to `𝒯₁ ×_𝒳 𝒰` is the base change of `𝒯₂ ×_𝒳 𝒰 ⟶ 𝒰`, a 1-morphism between two categories each
representable by an algebraic space and hence representable by algebraic spaces by Stacks 02ZZ;
Stacks 0300 then descends representability from `𝒯₁ ×_𝒳 𝒰`, which is itself representable by an
algebraic space because `𝒯₁ ×_𝒳 𝒰 ⟶ 𝒯₁` is a base change of `u`. No fibre product of algebraic
spaces is constructed and Stacks 02X2 is not used.

All four categories are taken at the universes of
`AlgebraicGeometry.Stack.schemeFibredCategory`, because
`CategoryTheory.CatFiberedInGroupoids.tripleProductSquare` quantifies over four categories sharing
one universe tuple. That is the same restriction `AlgebraicGeometry.Stack.AlgebraicStacks` carries.

Nothing here is tagged. The statements are instances of Stacks 003Q, 0300, 0302, 02ZZ and 045C
whose covering sets are already carried elsewhere, assembled for the diagonal clause of
Stacks 05UL; the clause itself is not proved here, since it needs Bootstrap 04S6 part (3).

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The canonical 2-fibre product square of Stacks 003Q, at the universes of
`AlgebraicGeometry.Stack.schemeFibredCategory`. -/
noncomputable abbrev twoFibreSquare
    {𝒜 𝒞 𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒜 ⟶ 𝒟) (g : 𝒞 ⟶ 𝒟) : TwoCommSq f g :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g

/-- `AlgebraicGeometry.Stack.twoFibreSquare` is a 2-fibre product. -/
noncomputable abbrev isTwoFibreSquare
    {𝒜 𝒞 𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒜 ⟶ 𝒟) (g : 𝒞 ⟶ 𝒟) : IsTwoFibreProduct (twoFibreSquare f g) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g

variable (B S hS)
variable {𝒳 𝒰 𝒯₁ 𝒯₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **The 2-fibre product of two points of `𝒳`, base changed along a 1-morphism `u : 𝒰 ⟶ 𝒳`.**
The square over the cospan `(𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒳, u)` obtained by pasting the base change of `u`
along `x` onto the first projection of `𝒯₁ ×_𝒳 𝒯₂`. Its first leg goes to `𝒯₁ ×_𝒳 𝒯₂` and its
second to `𝒰`. -/
noncomputable def schemePointProductBaseChangeSquare (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳) :
    TwoCommSq ((twoFibreSquare x y).fst ≫ x) u :=
  (twoFibreSquare x u).pasteFst
    (twoFibreSquare (twoFibreSquare x u).fst (twoFibreSquare x y).fst).swap

/-- **Stacks 003Q.** `AlgebraicGeometry.Stack.schemePointProductBaseChangeSquare` is a 2-fibre
product, by pasting two canonical ones. -/
noncomputable def isTwoFibreProduct_schemePointProductBaseChangeSquare
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳) :
    IsTwoFibreProduct (schemePointProductBaseChangeSquare B S hS u x y) :=
  isTwoFibreProduct_pasteFst (twoFibreSquare x u) (isTwoFibreSquare x u)
    (twoFibreSquare (twoFibreSquare x u).fst (twoFibreSquare x y).fst).swap
    (isTwoFibreProduct_swap
      (isTwoFibreSquare (twoFibreSquare x u).fst (twoFibreSquare x y).fst))

/-- **The apex is the triple 2-fibre product `(𝒯₁ ×_𝒳 𝒰) ×_{𝒯₁} (𝒯₁ ×_𝒳 𝒯₂)`**, syntactically.
Through `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare` the same
object is a 2-fibre product of `𝒯₁ ×_𝒳 𝒰` and `𝒯₂ ×_𝒳 𝒰` over `𝒰`, which is the identification
the proof of Stacks 05UL makes by hand. -/
theorem schemePointProductBaseChangeSquare_pt (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳) :
    (schemePointProductBaseChangeSquare B S hS u x y).pt
      = (CatFiberedInGroupoids.tripleProductSquare.{u, u, u + 1, u + 1} x u y).pt :=
  rfl

/-- The first leg of `AlgebraicGeometry.Stack.schemePointProductBaseChangeSquare` lands on the
2-fibre product `AlgebraicGeometry.Stack.twoFibreProduct` of `AlgebraicGeometry.Stack`'s own
rendering of condition (4) of Stacks 045G. -/
theorem twoFibreSquare_pt (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳) :
    (twoFibreSquare x y).pt = twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x.hom y.hom :=
  rfl

/-- **Stacks 0302.** The projection `𝒯₁' ×_𝒰 𝒯₂' ⟶ 𝒯₁ ×_𝒳 𝒯₂` is representable by algebraic
spaces, being a base change of `u`. -/
theorem isRepresentableByAlgebraicSpaces_schemePointProductBaseChange
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (schemePointProductBaseChangeSquare B S hS u x y).fst.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ u _
    (schemePointProductBaseChangeSquare B S hS u x y)
    (isTwoFibreProduct_schemePointProductBaseChangeSquare B S hS u x y) hu

/-- **Stacks 045C.** That projection has every relative property of `u` in the sense of
Stacks 03YK; for `u` surjective and smooth this is what the proof of Stacks 05UL needs of it. -/
theorem hasRelativeProperty_schemePointProductBaseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)]
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (hPu : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS P u hu) :
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS P
      (schemePointProductBaseChangeSquare B S hS u x y).fst
      (isRepresentableByAlgebraicSpaces_schemePointProductBaseChange B S hS u x y hu) :=
  hasRelativeProperty_baseChange.{u, u, u + 1} B S hS P _ _ _ u _
    (schemePointProductBaseChangeSquare B S hS u x y)
    (isTwoFibreProduct_schemePointProductBaseChangeSquare B S hS u x y) hu hPu

/-- **Stacks 0302.** The projection `𝒯 ×_𝒳 𝒰 ⟶ 𝒯` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_twoFibreProductSquare_fst
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom) :
    IsRepresentableByAlgebraicSpaces B S hS (twoFibreSquare x u).fst.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ u x
    (twoFibreSquare x u) (isTwoFibreSquare x u) hu

/-- **Stacks 0300.** `𝒯 ×_𝒳 𝒰` is representable by an algebraic space when `𝒯` is and `u` is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯₁) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreSquare x u).pt :=
  AlgebraicGeometry.isRepresentableByAlgebraicSpace_of_representable B S hS _ _
    (twoFibreSquare x u).fst
    (isRepresentableByAlgebraicSpaces_twoFibreProductSquare_fst B S hS u x hu) h𝒯

/-- **The source of the base change is representable by an algebraic space.** This is the step the
proof of Stacks 05UL takes by saying that `𝒯₁' ×_𝒰 𝒯₂'` is representable by the algebraic space
`T'₁ ×_U T'₂`; here it is Stacks 0300 applied to the projection to `𝒯₁ ×_𝒳 𝒰`, which is a base
change of the 1-morphism `𝒯₂ ×_𝒳 𝒰 ⟶ 𝒰` between two categories representable by algebraic
spaces. -/
theorem isRepresentableByAlgebraicSpace_schemePointProductBaseChangeSquare_pt
    (u : 𝒰 ⟶ 𝒳) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u.hom)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (h𝒯₁ : IsRepresentableByAlgebraicSpace B S hS 𝒯₁)
    (h𝒯₂ : IsRepresentableByAlgebraicSpace B S hS 𝒯₂) :
    IsRepresentableByAlgebraicSpace B S hS
      (schemePointProductBaseChangeSquare B S hS u x y).pt :=
  AlgebraicGeometry.isRepresentableByAlgebraicSpace_of_representable B S hS _ _
    (CatFiberedInGroupoids.tripleProductSquare.{u, u, u + 1, u + 1} x u y).fst
    (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _
      (twoFibreSquare y u).snd (twoFibreSquare x u).snd
      (CatFiberedInGroupoids.tripleProductSquare.{u, u, u + 1, u + 1} x u y)
      (CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare.{u, u, u + 1, u + 1} x u y)
      (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
        (twoFibreSquare y u).snd
        (isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS u y hu h𝒯₂) h𝒰))
    (isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS u x hu h𝒯₁)

end AlgebraicGeometry.Stack

end
