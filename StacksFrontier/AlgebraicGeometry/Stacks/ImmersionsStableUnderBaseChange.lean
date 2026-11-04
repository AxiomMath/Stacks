module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange

/-!
# Immersions of algebraic stacks are stable under base change (Stacks 0501)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `g : 𝒵 ⟶ 𝒴` be an
immersion, respectively a closed immersion, respectively an open immersion, of algebraic stacks
in the sense of **Stacks 04YL**. **Stacks 0501** says that the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is again an immersion of the same kind.

The three statements below are the three readings of that one sentence, each at an arbitrary
2-fibre product square of the 2-category of algebraic stacks over `S` — the source's
`𝒵 ×_𝒴 𝒳` is one such square, namely
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, so nothing is lost and the
shape of the square is not constrained.

Each of the three kinds of immersion of Stacks 04YL is a conjunction: representability by
algebraic spaces, and the corresponding property of Stacks 04XB. Both conjuncts are stable
under base change — representability by **Stacks 0302** and the Stacks 04XB property by
**Stacks 045C** — so each of the three statements is the pairing of two base-change results
already in the library, and the work done here is the open-immersion half of the second
conjunct, which the library did not have for the *second* projection.

## Main results

* `AlgebraicGeometry.Stack.isOpenImmersion_twoFibreProductSnd`: the open-immersion property of
  Stacks 04XB holds for the second projection of the canonical 2-fibre product square, as soon
  as it holds for the first leg of the cospan. This is the open-immersion companion of
  `AlgebraicGeometry.Stack.isClosedImmersion_twoFibreProductSnd` and
  `AlgebraicGeometry.Stack.isImmersion_twoFibreProductSnd`.
* `AlgebraicGeometry.Stack.isOpenImmersion_snd_of_isTwoFibreProduct`: the same at an arbitrary
  2-fibre product square of algebraic stacks.
* stability of immersions under base change, **Stacks 0501**, is carried together with
  **Stacks 045C** by `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_snd_of_isTwoFibreProduct`
  (`StacksFrontier/AlgebraicGeometry/Stacks/ImmersionBaseChange.lean`), of which the theorem that
  used to stand here was a one-line restatement;
  `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_baseChange_snd` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_baseChange_snd`: **Stacks 0501**, in
  its three readings.

## Implementation notes

No hypothesis is carried that the source does not make. In particular none of the three
statements asks for the immersion property of morphisms of algebraic spaces to be local at the
target for the fppf precoverage: that hypothesis is what
`AlgebraicGeometry.Stack.HasRelativeProperty` asks for, and the three predicates of Stacks 04YL
are written out through the longhand quantifier
`AlgebraicGeometry.Stack.IsImmersion` and its companions instead, which is the same proposition
with no hypothesis on the property. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack`.

The two open-immersion results are the proofs of their closed-immersion counterparts in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange` with
`AlgebraicGeometry.Space.closedImmersionProperty` replaced by
`AlgebraicGeometry.Space.openImmersionProperty`: the second projection of the canonical square
over `(g, f)` and the first projection of the canonical square over the exchanged cospan
`(f, g)` have equivalent base changes along every scheme-valued point of their common target
`𝒳` (`AlgebraicGeometry.Stack.nonempty_equivalenceOver_twoFibreProductSnd`), and the relative
property transports along such a family with no hypothesis on the property; the passage from
the canonical square to an arbitrary one is Stacks 0457 for the relative property, through the
comparison 1-morphism of
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProductAlgebraicStacks`.

The immersion reading of Stacks 0501 has the same conclusion as
`AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_snd_of_isTwoFibreProduct` of
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionBaseChange`, which is a one-line application
of it. That declaration carries `@[stacks 045C]`, the tag of the general base-change statement
for a relative property, and its docstring records that it must not also carry Stacks 04YL,
which is a definition. Stacks 0501 is neither of those two sentences — it is the base-change
sentence for the three *named* notions of Stacks 04YL — so it is given its own three sites
here, alongside the closed and open readings, which have no form in the library for the
second projection at all.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0501](https://stacks.math.columbia.edu/tag/0501)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The open-immersion property of Stacks 04XB for a second projection -/

/-- **Stacks 045C at the open-immersion property of Stacks 04XB, for the second projection.**
The second projection of the canonical 2-fibre product square over a cospan `(g, f)` of
categories fibred in groupoids over the big fppf site of `S` is an open immersion as soon as
`g` is.

This is the open-immersion companion of
`AlgebraicGeometry.Stack.isClosedImmersion_twoFibreProductSnd`, with the same proof: the second
projection of the canonical square over `(g, f)` and the first projection of the canonical
square over the exchanged cospan `(f, g)` have equivalent base changes along every
scheme-valued point of their common target, and the relative property transports along such a
family with no hypothesis on the property. -/
theorem isOpenImmersion_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : Stack.IsOpenImmersion B S hS g) :
    Stack.IsOpenImmersion B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd :=
  relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.openImmersionProperty B S hS)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd
    (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
    (isOpenImmersion_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg)

section AlgebraicStacksLevel

variable {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}

/-- **Stacks 045C at the open-immersion property, for the second projection of a 2-fibre product
square of algebraic stacks.** If `g : 𝒵 ⟶ 𝒴` is an open immersion in the sense of Stacks 04XB
and `P` is a 2-fibre product of the cospan `(g, f)` in the 2-category of algebraic stacks over
`S`, then so is `P.snd : P.pt ⟶ 𝒳`.

The statement is obtained at the canonical square — where the stronger terminality hypothesis
of Stacks 045C holds unconditionally — and transported to `P` along the comparison 1-morphism by
Stacks 0457 for the relative property. -/
theorem isOpenImmersion_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : Stack.IsOpenImmersion B S hS g.hom) :
    Stack.IsOpenImmersion B S hS P.snd.hom := by
  classical
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  let d : Bicategory.TwoCommSq.PreHom P (twoFibreProductSquareAlgebraicStacks B S hS g f) :=
    Quotient.out (hQ.from P)
  have hd : Functor.IsEquivalence d.hom.hom.hom.toFunctor :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hQ d
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact relativeProperty_of_equivalences B S hS (Space.openImmersionProperty B S hS)
    P.snd.hom.hom (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom
    d.hom.hom.hom (BasedFunctor.id 𝒳.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS d.isoSnd.symm))
    (isOpenImmersion_twoFibreProductSnd B S hS g.hom f.hom hg)

/-! ### Stacks 0501 -/

namespace AlgebraicStacks

/-- **Stacks 0501 for closed immersions.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks
over `S` and let `g : 𝒵 ⟶ 𝒴` be a closed immersion of algebraic stacks. Then the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is a closed immersion of algebraic stacks.

Stated at an arbitrary 2-fibre product square `P` of the cospan `(g, f)` in the 2-category of
algebraic stacks; the source's `𝒵 ×_𝒴 𝒳` is the canonical such square. -/
@[stacks 0501 "closed immersions"]
theorem isClosedImmersion_baseChange_snd
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsClosedImmersion B S hS g) :
    IsClosedImmersion B S hS P.snd :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hg.1,
    Stack.isClosedImmersion_snd_of_isTwoFibreProduct B S hS P hP hg.2⟩

/-- **Stacks 0501 for open immersions.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks
over `S` and let `g : 𝒵 ⟶ 𝒴` be an open immersion of algebraic stacks. Then the projection
`𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is an open immersion of algebraic stacks.

Stated at an arbitrary 2-fibre product square `P` of the cospan `(g, f)` in the 2-category of
algebraic stacks; the source's `𝒵 ×_𝒴 𝒳` is the canonical such square. -/
@[stacks 0501 "open immersions"]
theorem isOpenImmersion_baseChange_snd
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsOpenImmersion B S hS g) :
    IsOpenImmersion B S hS P.snd :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hg.1,
    Stack.isOpenImmersion_snd_of_isTwoFibreProduct B S hS P hP hg.2⟩

end AlgebraicStacks

end AlgebraicStacksLevel

end AlgebraicGeometry.Stack

end
