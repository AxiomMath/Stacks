module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Thickening
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of a thickening of algebraic stacks (Stacks 0BPR)

Let `i : 𝒴 ⟶ 𝒴'` be a thickening of algebraic stacks over `S`, let `f : 𝒳' ⟶ 𝒴'` be any
1-morphism of algebraic stacks, and let `P` be a 2-fibre product of that cospan in the
2-category of algebraic stacks. **Stacks 0BPR** says that the second projection
`P.snd : 𝒴 ×_{𝒴'} 𝒳' ⟶ 𝒳'` is again a thickening, and that `P` exhibits it as a *morphism of
thickenings* over `i`, with ambient 1-morphism `f` and restricted 1-morphism `P.fst`. Its second
assertion, that the base change of a first-order thickening is first order, is
`StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickeningBaseChange`.

A thickening is a closed immersion which is surjective on points (**Stacks 0BPP**, part (1)), so
the proof is the conjunction of three base-change statements: of representability by algebraic
spaces (**Stacks 0302**), of the closed-immersion property of **Stacks 04XB** (**Stacks 045C**),
and of surjectivity on points (**Stacks 04ZU**).

## Main results

* `AlgebraicGeometry.Stack.isThickening_baseChange`: **Stacks 0BPR**, the base change of a
  thickening is a thickening.
* `AlgebraicGeometry.Stack.baseChangeThickeningMorphism`: **Stacks 0BPR**, the 2-fibre product
  square read as a morphism of thickenings.

Along the way, and reusable:

* `AlgebraicGeometry.Stack.isClosedImmersion_baseChange`: **Stacks 045C** at the closed-immersion
  property of Stacks 04XB, for an arbitrary 2-fibre product square of categories fibred in
  groupoids.
* `AlgebraicGeometry.Stack.isClosedImmersion_twoFibreProductSnd`: the same for the *second*
  projection of the canonical square.
* `AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProductAlgebraicStacks`: a comparison
  1-morphism between two 2-fibre products of one cospan **of algebraic stacks** has an
  underlying equivalence of categories.
* `AlgebraicGeometry.Stack.algebraicStacksTwoIsoHom`: the 2-isomorphism of categories fibred in
  groupoids underlying a 2-isomorphism of algebraic stacks.

## Implementation notes

The second assertion of Stacks 0BPR, that a base change of a **first order** thickening is first
order, is proved in `StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickeningBaseChange`, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isFirstOrderThickening_fst_of_isTwoFibreProduct`. It
needs the first-order notion of Stacks 0BPQ, hence the chartwise defining ideal of Stacks 03MB,
and so lives downstream of this module.

Two levels of the 2-categorical tower meet here, and this is the whole cost of the file. The
hypothesis `CategoryTheory.Bicategory.IsTwoFibreProduct` for a square of *algebraic stacks* is
strictly weaker than the same hypothesis for the underlying square of *categories fibred in
groupoids*: the 2-category of algebraic stacks is a `CategoryTheory.Bicategory.InducedBicategory`
over the subtype of the algebraic stacks, so its terminality quantifies over test squares whose
apex is an algebraic stack only. The base-change results — **Stacks 045C**
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) and **Stacks 0302**
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) — take the stronger
hypothesis, so they cannot be applied to the given square directly.

They are instead applied to the *canonical* square, which is a 2-fibre product at the level of
categories fibred in groupoids unconditionally, and the conclusion is transported to the given
square along the comparison 1-morphism, exactly as
`AlgebraicGeometry.Stack.exists_point_of_isTwoFibreProduct_algebraicStacks` does for Stacks 04XH.
The transport is `AlgebraicGeometry.Stack.relativeProperty_of_equivalences` (Stacks 0457 for the
relative property, which needs no hypothesis on the property) together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences`, and what it needs
of the comparison is that its underlying functor is an equivalence. That is
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` one level up, which is a different
statement and not an instance of it — the pre-morphism's 1-morphism is reached by one more `.hom`
projection — so it is reproved here from the two terminality relations, which are both available
at the level of algebraic stacks.

Everything is written through the *longhand* quantifier that
`AlgebraicGeometry.Stack.IsClosedImmersion` is, rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK. That abbreviation carries
`[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget …]` as instance arguments, and for the
closed-immersion property those are Stacks 0420 and 04XB-level Chapter 67 results this library
does not have; the arguments of `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` do not
*use* them, so `AlgebraicGeometry.Stack.isClosedImmersion_baseChange` is the same proof with the
same body and no instance in scope. It is a near-copy of that proof and should replace its
body once a longhand form of Stacks 045C is promoted into
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange`.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The level bridge: comparisons of squares of algebraic stacks -/

/-- The 2-isomorphism of 1-morphisms of categories fibred in groupoids underlying a
2-isomorphism of 1-morphisms of algebraic stacks.

This is the companion of `AlgebraicGeometry.Stack.twoIsoHomIso` one level up the tower: the
2-category of algebraic stacks is an induced bicategory, so its 2-morphisms are wrappers around
those of the 2-category of categories fibred in groupoids. -/
def algebraicStacksTwoIsoHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) :
    f.hom ≅ g.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
  inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id

/-- **A comparison of two 2-fibre products of one cospan of algebraic stacks has an underlying
equivalence of categories.** Both apexes are terminal in the category of 2-commutative squares of
Stacks 003O, so the comparison has a 1-morphism back whose two composites with it are
2-isomorphic to the identities; the underlying functors of those 2-isomorphisms are the unit and
counit of an equivalence.

This is `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct` for the 2-category of
algebraic stacks. It is not an instance of that result: the 1-morphism underlying a pre-morphism
of squares of algebraic stacks is reached by one more `.hom` projection, and the terminality
hypothesis there — at the level of categories fibred in groupoids — is strictly stronger than
the one available here. The two terminality relations used are both relations of squares of
algebraic stacks, so nothing of the argument changes. -/
theorem isEquivalence_of_isTwoFibreProductAlgebraicStacks
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    {P Q : Bicategory.TwoCommSq g f} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q) (a : Bicategory.TwoCommSq.PreHom P Q) :
    a.hom.hom.hom.toFunctor.IsEquivalence := by
  let b := Quotient.out (hP.from Q)
  obtain ⟨e₁, -, -⟩ := Quotient.exact (hP.hom_ext (Quotient.mk _ (a.comp b)) (𝟙 P))
  obtain ⟨e₂, -, -⟩ := Quotient.exact (hQ.hom_ext (Quotient.mk _ (b.comp a)) (𝟙 Q))
  exact (CategoryTheory.Equivalence.mk a.hom.hom.hom.toFunctor b.hom.hom.hom.toFunctor
    (CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS e₁)).symm
    (CatFiberedInGroupoids.underlyingIso
      (algebraicStacksTwoIsoHom B S hS e₂))).isEquivalence_functor

/-! ### Base change of the closed-immersion property of Stacks 04XB -/

/-- **Stacks 045C at the closed-immersion property of Stacks 04XB.** In a 2-fibre product square
over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site
of `S`, the projection to `𝒵` is a closed immersion as soon as `f` is.

No hypothesis on the closed-immersion property of morphisms of algebraic spaces is used: by
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` the algebraic space whose structural
morphism is tested at a point `z` of `𝒵` is one of those tested at the transported point
`z ⋙ g` of `𝒴`. This is why the statement is written through the longhand quantifier
`AlgebraicGeometry.Stack.IsClosedImmersion` and not through
`AlgebraicGeometry.Stack.HasRelativeProperty`, whose instance arguments are not available for
this property. -/
theorem isClosedImmersion_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : Stack.IsClosedImmersion B S hS f) :
    Stack.IsClosedImmersion B S hS R.fst := by
  intro U z hz F hF he
  refine hf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

/-- **Stacks 045C at the closed-immersion property, for the second projection.** The second
projection of the canonical 2-fibre product square over a cospan `(g, f)` of categories fibred in
groupoids is a closed immersion as soon as `g` is.

The second projection of the canonical square of `(g, f)` and the first projection of the
canonical square of the exchanged cospan `(f, g)` have equivalent base changes along every
scheme-valued point of their common target `𝒳`, by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProductSnd`, and the relative property
transports along such a family with no hypothesis on the property. -/
theorem isClosedImmersion_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : Stack.IsClosedImmersion B S hS g) :
    Stack.IsClosedImmersion B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd :=
  relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.closedImmersionProperty B S hS)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd
    (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
    (isClosedImmersion_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg)

/-! ### Base change along a 2-fibre product square of algebraic stacks -/

section AlgebraicStacksLevel

variable {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}

/-- A 2-fibre product of algebraic stacks maps to the canonical one by an equivalence. -/
private theorem exists_preHom_isEquivalence_canonical
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    ∃ d : Bicategory.TwoCommSq.PreHom P (twoFibreProductSquareAlgebraicStacks B S hS g f),
      Functor.IsEquivalence d.hom.hom.hom.toFunctor ∧
        Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor := by
  classical
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  exact ⟨Quotient.out (hQ.from P),
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hQ _,
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))⟩

/-- **Stacks 0302 for the second projection of a 2-fibre product square of algebraic stacks.**
If `g : 𝒵 ⟶ 𝒴` is representable by algebraic spaces and `P` is a 2-fibre product of the cospan
`(g, f)` in the 2-category of algebraic stacks, then `P.snd : P.pt ⟶ 𝒳` is representable by
algebraic spaces.

The library's forms of Stacks 0302 hypothesise a 2-fibre product at the level of categories fibred
in groupoids, which is strictly stronger than the hypothesis here, so the statement is obtained
at the canonical square and transported to `P` along the comparison 1-morphism using Stacks 0457.
It is left untagged: Stacks 0302's own sentence already has its site. -/
theorem isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS P.snd.hom.hom := by
  obtain ⟨d, hd, hb⟩ := exists_preHom_isEquivalence_canonical B S hS P hP
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS P.snd.hom.hom
    (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom d.hom.hom.hom
    (BasedFunctor.id 𝒳.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS d.isoSnd.symm))).1
    (isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS g.hom f.hom hg)

/-- **Stacks 045C at the closed-immersion property, for the second projection of a 2-fibre
product square of algebraic stacks.** If `g : 𝒵 ⟶ 𝒴` is a closed immersion in the sense of
Stacks 04XB and `P` is a 2-fibre product of the cospan `(g, f)` in the 2-category of algebraic
stacks, then so is `P.snd : P.pt ⟶ 𝒳`.

As for representability, the statement is obtained at the canonical square — where the stronger
terminality hypothesis of Stacks 045C holds unconditionally — and transported to `P` along the
comparison 1-morphism by Stacks 0457 for the relative property. -/
theorem isClosedImmersion_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : Stack.IsClosedImmersion B S hS g.hom) :
    Stack.IsClosedImmersion B S hS P.snd.hom := by
  obtain ⟨d, hd, hb⟩ := exists_preHom_isEquivalence_canonical B S hS P hP
  exact relativeProperty_of_equivalences B S hS (Space.closedImmersionProperty B S hS)
    P.snd.hom.hom (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom
    d.hom.hom.hom (BasedFunctor.id 𝒳.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS d.isoSnd.symm))
    (isClosedImmersion_twoFibreProductSnd B S hS g.hom f.hom hg)

end AlgebraicStacksLevel

/-! ### Stacks 0BPR -/

variable {𝒴 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0BPR.** Let `i : 𝒴 ⟶ 𝒴'` be a thickening of algebraic stacks over `S`, let
`f : 𝒳' ⟶ 𝒴'` be a 1-morphism of algebraic stacks, and let `P` be a 2-fibre product of that
cospan in the 2-category of algebraic stacks. Then the second projection
`P.snd : 𝒴 ×_{𝒴'} 𝒳' ⟶ 𝒳'` is a thickening.

A thickening is a closed immersion which is surjective on points, and each of its three
constituents base-changes: representability by algebraic spaces by Stacks 0302, the
closed-immersion property of Stacks 04XB by Stacks 045C, and surjectivity on points by
Stacks 04ZU. -/
@[stacks 0BPR "base-changed thickening"]
theorem isThickening_baseChange (i : 𝒴 ⟶ 𝒴') (f : 𝒳' ⟶ 𝒴')
    (P : Bicategory.TwoCommSq i f) (hP : Bicategory.IsTwoFibreProduct P)
    (hi : IsThickening i) :
    IsThickening P.snd :=
  ⟨⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hi.1.1,
      isClosedImmersion_snd_of_isTwoFibreProduct B S hS P hP hi.1.2⟩,
    isSurjective_of_isTwoFibreProduct B S hS P hP hi.2⟩

/-- **Stacks 0BPR.** A 2-fibre product square of a thickening `i : 𝒴 ⟶ 𝒴'` of algebraic stacks
along a 1-morphism `f : 𝒳' ⟶ 𝒴'` *is* a morphism of thickenings from the base-changed thickening
`P.snd` to `i`: its ambient 1-morphism is `f`, its restricted 1-morphism is the first projection
`P.fst`, and the 2-isomorphism filling the square is exactly the assertion that `f` restricts to
`P.fst`. -/
@[stacks 0BPR "morphism of thickenings"]
def baseChangeThickeningMorphism (i : 𝒴 ⟶ 𝒴') (f : 𝒳' ⟶ 𝒴')
    (P : Bicategory.TwoCommSq i f) (hP : Bicategory.IsTwoFibreProduct P)
    (hi : IsThickening i) :
    ThickeningMorphism P.snd i (isThickening_baseChange B S hS i f P hP hi) hi where
  outer := f
  inner := P.fst
  comm := P.iso

/-! ### The same statements on the exchanged cospan

The results above conclude about the *second* projection, which is the base change of the
*first* leg of the cospan. Consumers that present a base change as the *first* projection of a
square over the cospan taken in the other order need the mirror statements, which are obtained
by `CategoryTheory.Bicategory.TwoCommSq.swap`: exchanging the legs of a 2-fibre product gives a
2-fibre product again, and exchanges the two projections definitionally. -/

/-- **Stacks 04ZU for the first projection.** In a 2-fibre product square over the cospan
`g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the projection to the source of `g` is
surjective as soon as `f` is.

This is `AlgebraicGeometry.Stack.isSurjective_of_isTwoFibreProduct` read on the exchanged
square, whose second projection is the first projection of the given one. -/
theorem isSurjective_fst_of_isTwoFibreProduct
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsSurjective B S hS f) : IsSurjective B S hS P.fst :=
  isSurjective_of_isTwoFibreProduct B S hS P.swap (Bicategory.isTwoFibreProduct_swap hP) hf

namespace AlgebraicStacks

/-- **Stacks 045C at the closed-immersion property, for the first projection of a 2-fibre
product square of algebraic stacks.** If `f : 𝒳 ⟶ 𝒴` is a closed immersion in the sense of
Stacks 04YL part (2) and `P` is a 2-fibre product of the cospan `(g, f)` in the 2-category of
algebraic stacks, then so is `P.fst : P.pt ⟶ 𝒵`.

Both halves — representability by algebraic spaces and the closed-immersion property of
Stacks 04XB — are read off the exchanged square, whose second projection is `P.fst`. -/
theorem isClosedImmersion_baseChange {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS P.fst :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hf.1,
    isClosedImmersion_snd_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hf.2⟩

end AlgebraicStacks

/-- **Stacks 0BPR for the first projection.** Let `j : 𝒴 ⟶ 𝒴'` be a thickening of algebraic
stacks over `S`, let `g : 𝒳' ⟶ 𝒴'` be a 1-morphism of algebraic stacks, and let `P` be a
2-fibre product of the cospan `(g, j)`. Then the first projection `P.fst` is a thickening.

This is `AlgebraicGeometry.Stack.isThickening_baseChange` read on the exchanged square. -/
theorem isThickening_fst_of_isTwoFibreProduct
    {𝒴 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS} {j : 𝒴 ⟶ 𝒴'} {g : 𝒳' ⟶ 𝒴'}
    (hj : IsThickening j)
    (P : Bicategory.TwoCommSq g j) (hP : Bicategory.IsTwoFibreProduct P) :
    IsThickening P.fst :=
  isThickening_baseChange B S hS j g P.swap (Bicategory.isTwoFibreProduct_swap hP) hj

end AlgebraicGeometry.Stack

end
