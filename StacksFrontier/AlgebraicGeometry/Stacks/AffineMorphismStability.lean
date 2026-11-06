module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange

/-!
# Affine 1-morphisms of algebraic stacks are stable under base change and composition

An affine 1-morphism of algebraic stacks over `S` is one which is representable by algebraic
spaces and affine in the sense of Stacks 04XB
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`, **Stacks 0CHQ**). This file proves the
two permanence properties of that notion: **Stacks 0CHR**, that a base change of an affine
1-morphism of algebraic stacks is affine, and **Stacks 0CHS**, that a composite of two affine
1-morphisms of algebraic stacks is affine.

## Main definitions

* `AlgebraicGeometry.Space.affineMorphismProperty`: affineness of a morphism of algebraic spaces
  over `S` (Stacks 03WF) as a `CategoryTheory.MorphismProperty` on the category of algebraic
  spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_etaleChart`: affineness of a morphism of algebraic
  spaces descends along a surjective étale scheme chart of its target.
* `AlgebraicGeometry.Space.affineMorphismProperty_of_pullbackSnd_atlas`: the same in the packaged
  spelling, which is the descent hypothesis of
  `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`.
* `AlgebraicGeometry.Stack.isAffineHom_baseChange`, `...isAffineHom_twoFibreProductSnd` and
  `...isAffineHom_snd_of_isTwoFibreProduct`: affineness in the sense of Stacks 04XB is inherited
  by the projections of a 2-fibre product square.
* `AlgebraicGeometry.Stack.isAffineHom_comp`: affineness in the sense of Stacks 04XB is stable
  under composition.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_snd_of_isTwoFibreProduct`: **Stacks 0CHR**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_comp`: **Stacks 0CHS**.

## Implementation notes

`AlgebraicGeometry.Stack.IsAffineHom` writes the condition of Stacks 04XB out longhand rather
than using `AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism`: that abbreviation carries locality at the
target for the fppf precoverage as an instance argument, and for affineness of morphisms of
algebraic spaces that is Stacks 041Z, which rests on Gabber's Stacks 0APL and is available in
this library only modulo the named hypothesis
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc`. So neither
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` nor
`AlgebraicGeometry.Stack.hasRelativeProperty_comp` can be used, and both results are obtained in
the longhand form. **Nothing is assumed**: each uses an input that needs no fppf locality.

For the base change this costs nothing at all, exactly as for the immersions of Stacks 04YL in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionBaseChange`: no hypothesis on the property is
used, because `AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` identifies the
algebraic space tested at a scheme-valued point of `𝒵` with one of those tested at the
transported point of `𝒴`, so the two conditions are the same condition reindexed.

For the composition the input is `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`, the form of
**Stacks 045B** in which locality at the target is weakened to the one consequence of it that the
proof of Stacks 045B actually draws — descent along a single surjective étale scheme chart of the
target. At affineness that descent is unconditional: it is the implication (4) ⇒ (2) of
**Stacks 03WG**, proved as `AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`, whose
own descent input is effective descent of affine morphisms along *surjective étale* morphisms of
the site and not along fpqc coverings. Composition-stability of the property itself is
**Stacks 03WH**, `AlgebraicGeometry.Space.isAffineHom_comp`.

Both tags sit on the statement for 1-morphisms of *algebraic stacks*, which is the notion of
Stacks 0CHQ; the statements in the `AlgebraicGeometry.Stack` namespace are about the Stacks 04XB
half alone and are untagged, as are the Stacks 045B and 045C inputs they instantiate, which are
already carried elsewhere.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0CHR](https://stacks.math.columbia.edu/tag/0CHR)
* [Stacks Project, Tag 0CHS](https://stacks.math.columbia.edu/tag/0CHS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_AffineMorphismStability
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Affineness of a morphism of algebraic spaces over `S` (Stacks 03WF) as a property of
morphisms in the category of algebraic spaces over `S`. This is the bundled form that the
relative-property statements of Stacks 03YK and Stacks 045B are stated at. -/
abbrev affineMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsAffineHom B S hS f.hom

/-- Affineness, as a morphism property of algebraic spaces over `S`, respects isomorphisms. -/
instance affineMorphismProperty_respectsIso :
    (affineMorphismProperty B S hS).RespectsIso :=
  respectsIso_isAffineHom

/-- **Stacks 03WH** at the packaged spelling: affineness, as a morphism property of algebraic
spaces over `S`, is stable under composition. -/
instance affineMorphismProperty_isStableUnderComposition :
    (affineMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem k l hk hl := isAffineHom_comp B S hS k.hom l.hom hk hl

/-- **Affineness of a morphism of algebraic spaces descends along a surjective étale scheme chart
of the target.** If `a : h_T ⟶ Y` is surjective and étale and the base change of `f : X ⟶ Y`
along `a` is affine, then `f` is affine.

This is the implication (4) ⇒ (2) of **Stacks 03WG**. -/
theorem isAffineHom_of_etaleChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : IsAffineHom B S hS (pullback.snd f a)) :
    IsAffineHom B S hS f := by
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f hX hY).out 4 2).1 ?_
  exact ⟨T, a, isSurjective_of_presheafSurjective B S hS a hsurj,
    isEtale_of_presheaf_etale B S hS hetale, h⟩

/-- **Affineness of morphisms of algebraic spaces over `S` may be tested on the base change to a
surjective étale scheme chart of the target.** This is the descent hypothesis that
`AlgebraicGeometry.Stack.prop_comp_of_atlasDescent` consumes, at affineness; it is
`AlgebraicGeometry.Space.isAffineHom_of_etaleChart` read on the chosen fibre product of the
category of algebraic spaces. -/
theorem affineMorphismProperty_of_pullbackSnd_atlas {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y)
    {T : BigFppfOver B S hS} {a : yoneda.obj T ⟶ Y.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : affineMorphismProperty B S hS (pullback.snd k (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y))) :
    affineMorphismProperty B S hS k :=
  isAffineHom_of_etaleChart B S hS X.property Y.property k.hom hsurj hetale
    ((prop_pullbackSnd_homMk_iff B S hS _ k a).1 h)

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045C at affineness in the sense of Stacks 04XB.** In a 2-fibre product square over a
cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S`,
the projection to `𝒵` is affine as soon as `f` is.

No hypothesis on affineness of morphisms of algebraic spaces is used: the algebraic space tested
at a scheme-valued point of `𝒵` is one of those tested at the transported point of `𝒴`. -/
theorem isAffineHom_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : Stack.IsAffineHom B S hS f) :
    Stack.IsAffineHom B S hS R.fst := by
  intro U z hz F hF he
  refine hf U (z ⋙ g.hom.toFunctor) (by rw [Functor.assoc, g.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

/-- **Stacks 045C at affineness, for the second projection.** The second projection of the
canonical 2-fibre product square over a cospan `(g, f)` of categories fibred in groupoids is
affine in the sense of Stacks 04XB as soon as `g` is. -/
theorem isAffineHom_twoFibreProductSnd
    {𝒵 𝒴 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (hg : Stack.IsAffineHom B S hS g) :
    Stack.IsAffineHom B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd :=
  relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.affineMorphismProperty B S hS)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd
    (nonempty_equivalenceOver_twoFibreProductSnd B S hS g f)
    (isAffineHom_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg)

/-- **Stacks 045B at affineness in the sense of Stacks 04XB.** A composite of two 1-morphisms of
categories fibred in groupoids over the big fppf site of `S` which are representable by algebraic
spaces and affine in the sense of Stacks 04XB is again affine in that sense.

This is `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`, the form of Stacks 045B whose
locality hypothesis is descent along a surjective étale scheme chart, at affineness; that descent
is the implication (4) ⇒ (2) of Stacks 03WG and composition-stability is Stacks 03WH, so the
statement carries no hypothesis on the property. -/
theorem isAffineHom_comp
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hPf : Stack.IsAffineHom B S hS f) (hPg : Stack.IsAffineHom B S hS g) :
    Stack.IsAffineHom B S hS (f ≫ g) :=
  prop_comp_of_atlasDescent B S hS (Space.affineMorphismProperty B S hS)
    (Space.affineMorphismProperty_of_pullbackSnd_atlas B S hS)
    f g hf hg hPf hPg

section AlgebraicStacksLevel

variable {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}

/-- **Stacks 045C at affineness, for the second projection of a 2-fibre product square of
algebraic stacks.** If `g : 𝒵 ⟶ 𝒴` is affine in the sense of Stacks 04XB and `P` is a 2-fibre
product of the cospan `(g, f)` in the 2-category of algebraic stacks, then so is
`P.snd : P.pt ⟶ 𝒳`.

The statement is obtained at the canonical square and transported to `P` along the comparison
1-morphism by Stacks 0457 for the relative property. -/
theorem isAffineHom_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : Stack.IsAffineHom B S hS g.hom) :
    Stack.IsAffineHom B S hS P.snd.hom := by
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  let d : Bicategory.TwoCommSq.PreHom P (twoFibreProductSquareAlgebraicStacks B S hS g f) :=
    Quotient.out (hQ.from P)
  have hd : Functor.IsEquivalence d.hom.hom.hom.toFunctor :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hQ d
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  exact relativeProperty_of_equivalences B S hS (Space.affineMorphismProperty B S hS)
    P.snd.hom.hom (twoFibreProductSquareAlgebraicStacks B S hS g f).snd.hom.hom
    d.hom.hom.hom (BasedFunctor.id 𝒳.val.val)
    (twoIsoHomIso B S hS (algebraicStacksTwoIsoHom B S hS d.isoSnd.symm))
    (isAffineHom_twoFibreProductSnd B S hS g.hom f.hom hg)

namespace AlgebraicStacks

/-- **Stacks 0CHR.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let
`g : 𝒵 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks, and let `P` be a 2-fibre product of the
cospan `(g, f)`. Then the base change `P.snd : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` of `g` along `f` is affine.

Both halves are base-change statements: representability by algebraic spaces is Stacks 0302 and
affineness in the sense of Stacks 04XB is Stacks 045C. The square is arbitrary, so this applies
to any square a consumer has already exhibited as a 2-fibre product rather than only to the
canonical one of Stacks 04T2. -/
@[stacks 0CHR]
theorem isAffineHom_snd_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsAffineHom B S hS g) :
    IsAffineHom B S hS P.snd :=
  ⟨isRepresentableByAlgebraicSpaces_snd_of_isTwoFibreProduct B S hS P hP hg.1,
    Stack.isAffineHom_snd_of_isTwoFibreProduct B S hS P hP hg.2⟩

end AlgebraicStacks

end AlgebraicStacksLevel

namespace AlgebraicStacks

/-- **Stacks 0CHS.** A composite of two affine 1-morphisms of algebraic stacks over `S` is
affine: representability by algebraic spaces composes by Stacks 0301, and affineness in the sense
of Stacks 04XB composes by Stacks 045B, whose two ingredients at affineness are Stacks 03WH and
the implication (4) ⇒ (2) of Stacks 03WG. -/
@[stacks 0CHS]
theorem isAffineHom_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsAffineHom B S hS f) (hg : IsAffineHom B S hS g) :
    IsAffineHom B S hS (f ≫ g) :=
  ⟨AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hf.1 hg.1,
    Stack.isAffineHom_comp B S hS f.hom g.hom hf.1 hg.1 hf.2 hg.2⟩

end AlgebraicStacks

end Stack

end AlgebraicGeometry

end
