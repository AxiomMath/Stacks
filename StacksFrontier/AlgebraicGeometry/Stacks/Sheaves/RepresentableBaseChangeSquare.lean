module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceEtale

/-!
# A 2-fibre product square with a representable base (Stacks 075P)

Let `S` be a scheme and let

```
𝒳' --g'--> 𝒳
 |         |
 f'        f
 v         v
𝒴' --g-->  𝒴
```

be a 2-fibre product square of algebraic stacks over `S`, with `f` representable by algebraic
spaces and `𝒴'` representable by an algebraic space `G'`.  **Stacks 075P** asserts that `𝒳'` is
then representable by an algebraic space `F'` and that, writing `f' : F' ⟶ G'` for the induced
morphism of algebraic spaces, the identity

```
g⁻¹(Rf_*ℱ)|_{G'_étale} = Rf'_{small, *}((g')⁻¹ℱ|_{F'_étale})
```

holds for `ℱ` an abelian sheaf, or a sheaf of `𝒪_𝒳`-modules, on `𝒳_étale`.

This file covers the first sentence of that conclusion, which is what fixes the two objects the
displayed identity is about: representability of the apex, and the induced morphism of algebraic
spaces between the two representing spaces.  **The displayed identity is not proved**, and the
implementation notes say what it would need.

Representability of the apex is **Stacks 0300**: the apex of a 2-fibre product square over a
cospan whose other leg is representable by algebraic spaces is representable by an algebraic
space as soon as the base of that leg is.  It is proved as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`, which is the
statement of **Stacks 075P**'s first assertion at hypotheses weaker than the source's — the
three categories need only be fibred in groupoids, not algebraic stacks — and so is where the
`@[stacks 075P]` registration for that assertion belongs.  The induced morphism is the
construction of **Stacks 0GQA**, read at the square.

## Main definitions

* `AlgebraicGeometry.Stack.inducedSquareSpacesHom`: the morphism of algebraic spaces
  `f' : F' ⟶ G'` induced by the left-hand leg of the square, through chosen equivalences of
  the apex with `F'` and of `𝒴'` with `G'`.  This is the morphism of algebraic spaces the
  displayed identity pushes forward along.

## Implementation notes

### What the displayed identity would need

The source proves it by combining **Stacks 075H**, the base change identity
`g⁻¹Rf_*ℱ = Rf'_*(g')⁻¹ℱ` for the square, with **Stacks 075N**, the identification of the
restriction of a derived direct image along a 1-morphism between stacks representable by
algebraic spaces with the derived direct image on the small étale sites.  Neither is available
in the shape the combination needs.

**Stacks 075H** is proved as
`AlgebraicGeometry.Stack.abelianHigherDirectImageBaseChangeIso` only at abelian coefficients,
and there with its right-hand side read as the right derived functor of the composite
`(g')⁻¹ ⋙ f'_*` rather than as `Rⁱf'_* ∘ (g')⁻¹`; the two agree once `(g')⁻¹` carries
injective abelian sheaves to `f'_*`-acyclic ones, which the source gets from the value half of
**Stacks 075G** and which is absent.  At module coefficients only the comparison on underlying
abelian presheaves is available,
`AlgebraicGeometry.Stack.modulePresheafBaseChangeIso`, together with
`AlgebraicGeometry.Stack.nonempty_moduleHigherDirectImageBaseChangeIso`, which carries
`𝒪`-linearity of that comparison as a hypothesis.

**Stacks 075N** is proved in its module clause only,
`AlgebraicGeometry.Space.restrictedDerivedDirectImageIso`, and with the 2-isomorphism of the
two legs of the square of **Stacks 073N**, the two K-injectivity hypotheses of **Stacks 093Y**
and exactness of the two module-level restrictions carried as named hypotheses; its abelian
clause is absent.

So the displayed identity is blocked twice over, and at module coefficients the two sides
cannot even be compared in the source's form.  No conditional statement of it is offered: a
hypothesis strong enough to supply the missing halves of **Stacks 075H** and **Stacks 075N**
would be the identity itself.

### Universes

The square is taken at
`CategoryTheory.CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}`, the seating
at which the 2-category of categories fibred in groupoids over the big fppf site of `S` is
closed under forming the 2-fibre product of a cospan, so that the apex of an abstract square
can be compared with it.  It is the seating of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct`, which the
registration below names, and of the construction below.

## References

* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
* [Stacks Project, Tag 0GQA](https://stacks.math.columbia.edu/tag/0GQA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Stack

/-! ### The representability assertion of Stacks 075P -/

add_to_stacks 075P "the first assertion of the conclusion: the apex X' of the 2-fibre product
  square is representable by an algebraic space F', given that f is representable by algebraic
  spaces and that Y' is representable by an algebraic space. This is Tag 0300, at hypotheses
  weaker than the source's. The displayed base change identity of this tag is NOT proved; see
  the implementation notes of
  StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/RepresentableBaseChangeSquare.lean"
  AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isTwoFibreProduct

/-! ### The induced morphism of algebraic spaces -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of algebraic spaces `f' : F' ⟶ G'` of Stacks 075P.**  For a 2-fibre product
square over the cospan `(g, f)`, with the apex represented by an algebraic space `F'` and the
base `𝒴'` of `g` represented by an algebraic space `G'`, the left-hand leg `f'` of the square
induces a morphism `F' ⟶ G'` of algebraic spaces: an element of `F'` over `U` is an object of
the apex over `U`, whose image under `f'` is an object of `𝒴'` over `U`, hence an element of
`G'` over `U`.

This is the construction of **Stacks 0GQA**, `AlgebraicGeometry.Space.inducedSpacesHom`, read
at the left-hand leg of the square.  Only the two chosen equivalences and the verticality of
the leg over the site enter; representability of the apex, which **Stacks 0300** supplies, is
what makes such an equivalence available in the first place.

The displayed identity of **Stacks 075P**, which is the direct image along this morphism of a
restricted derived direct image, is not proved; see the implementation notes of this module. -/
@[stacks 075P "the induced morphism of algebraic spaces f' : F' ⟶ G' named in the conclusion,
  through chosen equivalences of the apex with F' and of Y' with G'. The displayed base change
  identity of this tag is NOT proved"]
noncomputable def inducedSquareSpacesHom
    {𝒳 𝒴 𝒴' : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴} (P : Bicategory.TwoCommSq g f)
    {F' G' : AlgebraicSpaces B S hS}
    (eF' : StacksRepresentableCFG.EquivalenceOver P.pt.val.p
      (presheafOfCategories (F'.1 ⋙ typeToCat)).p)
    (eG' : StacksRepresentableCFG.EquivalenceOver 𝒴'.val.p
      (presheafOfCategories (G'.1 ⋙ typeToCat)).p) :
    F' ⟶ G' :=
  Space.inducedSpacesHom B S hS P.pt.val.p 𝒴'.val.p eF' eG' P.fst.hom.toFunctor P.fst.hom.w

end AlgebraicGeometry.Stack

end
