module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange

/-!
# Base change of an immersion of algebraic stacks (Stacks 045C at the immersion property)

Let `g : 𝒵 ⟶ 𝒴` be an immersion of algebraic stacks over `S` in the sense of **Stacks 04YL**,
part (3), let `f : 𝒳 ⟶ 𝒴` be any 1-morphism of algebraic stacks, and let `P` be a 2-fibre product
of that cospan. Then the projection `P.snd : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is again an immersion.

This is **Stacks 045C** at the immersion property of **Stacks 04XB**, together with the base
change of representability by algebraic spaces (**Stacks 0302**).

## Main results

* `AlgebraicGeometry.Stack.isImmersion_baseChange`: the immersion property of Stacks 04XB is
  stable under base change, for the first projection of a 2-fibre product square of categories
  fibred in groupoids.
* `AlgebraicGeometry.Stack.isImmersion_twoFibreProductSnd`: the same for the second projection of
  the canonical square.
* `AlgebraicGeometry.Stack.isImmersion_snd_of_isTwoFibreProduct`: the same at an arbitrary
  2-fibre product square of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_snd_of_isTwoFibreProduct`: the same for
  being an immersion of algebraic stacks, i.e. conjoined with representability by algebraic
  spaces (Stacks 0302).

## Implementation notes

The proofs mirror the closed-immersion case,
`AlgebraicGeometry.Stack.isClosedImmersion_baseChange` and its companions in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange`, and for the same reason: no
hypothesis on the immersion property of morphisms of algebraic spaces is used, because
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` shows that the algebraic space
tested at a scheme-valued point of `𝒵` is one of those tested at the transported point of `𝒴`.
This matters here, because the generic route through
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` would need the hypothesis that being an
immersion is fppf local on the target for morphisms of algebraic spaces, a Chapter 67 result this
library does not have; that is also why the statements are written through the longhand
quantifier `AlgebraicGeometry.Stack.IsImmersion` rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045C at the immersion property of Stacks 04XB.** In a 2-fibre product square over a
cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`,
the projection to `𝒵` is an immersion as soon as `f` is. -/
@[stacks 045C "the immersion property of Stacks 04XB, for the first projection"]
theorem isImmersion_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : Stack.IsImmersion B S hS f) :
    Stack.IsImmersion B S hS R.fst := by
  rintro U z hz F hF ⟨e⟩
  refine hf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

/-- **Stacks 045C at the immersion property, for the second projection.** The second projection
of the canonical 2-fibre product square over a cospan `(g, f)` of categories fibred in groupoids
is an immersion as soon as `g` is. -/
@[stacks 045C "the immersion property of Stacks 04XB, for the canonical second projection"]
theorem isImmersion_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : Stack.IsImmersion B S hS g) :
    Stack.IsImmersion B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd :=
  relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.immersionProperty B S hS)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd
    (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
    (isImmersion_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg)

section AlgebraicStacksLevel

variable {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}

/-- **Stacks 045C at the immersion property, for the second projection of a 2-fibre product
square of algebraic stacks.** If `g : 𝒵 ⟶ 𝒴` is an immersion in the sense of Stacks 04XB and `P`
is a 2-fibre product of the cospan `(g, f)` in the 2-category of algebraic stacks, then so is
`P.snd : P.pt ⟶ 𝒳`.

The statement is obtained at the canonical square — where the stronger terminality hypothesis of
Stacks 045C holds unconditionally — and transported to `P` along the comparison 1-morphism by
Stacks 0457 for the relative property. -/
@[stacks 045C "the immersion property of Stacks 04XB, at a 2-fibre product of algebraic stacks"]
theorem isImmersion_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : Stack.IsImmersion B S hS g.hom) :
    Stack.IsImmersion B S hS P.snd.hom := by
  classical
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  let d : Bicategory.TwoCommSq.PreHom P (twoFibreProductSquareAlgebraicStacks B S hS g f) :=
    Quotient.out (hQ.from P)
  have hd : Functor.IsEquivalence d.hom.hom.hom.toFunctor :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hQ d
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact relativeProperty_of_equivalences B S hS (Space.immersionProperty B S hS)
    P.snd.hom.hom (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom
    d.hom.hom.hom (BasedFunctor.id 𝒳.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS d.isoSnd.symm))
    (isImmersion_twoFibreProductSnd B S hS g.hom f.hom hg)

namespace AlgebraicStacks

/-- Base change of an immersion of algebraic stacks. If `g : 𝒵 ⟶ 𝒴` is an immersion of
algebraic stacks over `S` and `P` is a 2-fibre product of the cospan `(g, f)` in the 2-category of
algebraic stacks, then `P.snd : P.pt ⟶ 𝒳` is an immersion of algebraic stacks.

Both halves are base-change statements: representability by algebraic spaces is Stacks 0302 and
the immersion property of Stacks 04XB is Stacks 045C. The attribute records the latter, at the
level of algebraic stacks. It deliberately does **not** record Stacks 04YL: that tag is a
definition — its three parts define open immersions, closed immersions and immersions in terms
of Section 04XB — and says nothing about stability under base change, so a theorem must not
carry it. The definition itself is carried by `AlgebraicStacks.IsImmersion`. -/
@[stacks 045C "the immersion property of Stacks 04XB, conjoined with representability, at a \
2-fibre product of algebraic stacks",
  stacks 0501 "immersions"]
theorem isImmersion_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsImmersion B S hS g) :
    IsImmersion B S hS P.snd :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hg.1,
    Stack.isImmersion_snd_of_isTwoFibreProduct B S hS P hP hg.2⟩

end AlgebraicStacks

end AlgebraicStacksLevel

end AlgebraicGeometry.Stack

end
