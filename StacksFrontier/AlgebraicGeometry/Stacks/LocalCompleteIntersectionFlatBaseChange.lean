module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# Flat base change of a local complete intersection 1-morphism of algebraic stacks (Stacks 0CJ5)

**Stacks 0CJ5** says that a flat base change of a local complete intersection 1-morphism of
algebraic stacks over `S` is a local complete intersection 1-morphism.

The source proves it by arguing as in the base-change remark **Stacks 06FQ**, but only for a flat
1-morphism `𝒴' ⟶ 𝒴`, and using flat base change of the Koszul property of morphisms of algebraic
spaces, **Stacks 06C7**. That is the route taken here. The library's Stacks 06FQ,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange`, cannot be instantiated at the
Koszul property: it asks that the restriction of the property to algebraic spaces be stable under
*arbitrary* base change, which the Koszul property is not. So the three steps of its proof that use
that stability are reproved here with flatness threaded through them, which is exactly the
restriction the source's hint names.

The one place the stability enters the proof of Stacks 06FQ is base change of the top horizontal
morphism of a smooth diagram along the second projection of `𝒯 ×_𝒴 V`, read on representing
presheaves. In the present situation `𝒯 ⟶ 𝒴` is the composite of a smooth presentation
`𝒯 ⟶ 𝒴'` with the flat `𝒴' ⟶ 𝒴`, hence flat by **Stacks 06PX** at the flatness of a smooth
1-morphism; that projection is its base change, hence flat by the Stacks 06FQ chain at flatness —
where the stability hypothesis *is* available, by **Stacks 03MO** — and the morphism of
representing presheaves it induces is flat by the equivalence of conditions (2) and (3) of
**Stacks 06FM**. Stacks 06C7 then applies to it.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.prop_of_isPullback_of_isFlat`: a property of morphisms of algebraic
  spaces over `S` stable under flat base change onto the canonical pullback is stable under flat
  base change read off any cartesian square.
* `AlgebraicGeometry.Stack.prop_representingMap_fst_of_isFlat`: the flat form of
  `AlgebraicGeometry.Stack.prop_representingMap_fst`, the morphism of representing presheaves
  induced by the first projection of a 2-fibre product of represented categories.
* `AlgebraicGeometry.Stack.isFlat_representingMap_snd_of_isTwoFibreProduct`: the morphism of
  representing presheaves induced by the second projection of a 2-fibre product of a flat
  1-morphism with one out of an algebraic space is flat.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_flatBaseChange_of_representable`: the
  flat form of base change of the existential smooth-diagram criterion along a 1-morphism out of
  a category representable by an algebraic space.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat`: the flat form of
  **Stacks 06FQ** — base change of the existential smooth-diagram criterion along an arbitrary
  2-fibre-product square whose cospan leg is flat.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocalCompleteIntersection_baseChange`:
  **Stacks 0CJ5**.

## Implementation notes

Stacks 0CJ3 defines the Koszul property of a 1-morphism of algebraic stacks over the *universal*
smooth-diagram criterion of **Stacks 06FM**, while the base-change argument runs on the
*existential* one, so the hypothesis and the conclusion are both moved across the equivalence of
conditions (1) and (2) of Stacks 06FM, as for the siblings
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_baseChange`
(**Stacks 06Q4**) and `...isLocallyOfFiniteType_baseChange` (**Stacks 06FU**).

The four general statements are deliberately untagged. Stacks 06FQ already carries a bare tag, on
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange`; the flat forms below are the
same remark under a weaker hypothesis on the property and a stronger one on the cospan, so they
add nothing to that tag's covering set.

`AlgebraicGeometry.Stack.prop_representingMap_fst` reads base change off the cartesian square of
**Stacks 04SD** directly, which arbitrary base-change stability permits. Flat base change of the
Koszul property is available only onto Mathlib's chosen pullback (that is how Stacks 06C7 is
stated), so the comparison of the two cartesian squares has to be crossed; it is an isomorphism
over the base, and the property is invariant under composing with it by **Stacks 03MJ** read as
invariance under isomorphism of presheaves. That is the only structural difference from the
statement it copies.

## Carried hypothesis

The statement of Stacks 0CJ5 below carries one hypothesis beyond the source's.

It is that the Koszul property of morphisms of *algebraic spaces* over `S` is smooth local
on the source-and-target, which is **Stacks 06FC** at that property. It is what crosses the
equivalence of conditions (1) and (2) of Stacks 06FM, in both directions, and it is not available:
the criterion `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget` (**Stacks 06FB**) asks for
locality at the source and at the target for the smooth topology, and the transfer of those from
schemes to algebraic spaces is missing for the syntomic and fpqc topologies — the same two gaps,
**Stacks 06F0** and **Stacks 0428**, that
`AlgebraicGeometry.Space.isSyntomic_isSmoothLocalOnSourceAndTarget` carries, and for the same
reason; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/LocalOnSourceAndTarget/Syntomic.lean`.

Nothing else is assumed: the base-change argument itself is proved here in full. In particular
Stacks 06C7, `AlgebraicGeometry.Space.isLocalCompleteIntersection_pullback_snd`, now carries no
hypothesis beyond its source's: the étale source locality of the Koszul property of morphisms of
*schemes* it needs, **Stacks 069P** restricted to étale coverings, is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
* [Stacks Project, Tag 0CJ5](https://stacks.math.columbia.edu/tag/0CJ5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flat base change of the property on algebraic spaces -/

/-- **A flat base change, read off any cartesian square.** Let `P` be a property of morphisms of
algebraic spaces over `S` which is invariant under isomorphism and which passes to Mathlib's
chosen pullback along a flat morphism. Then for `m` with `P` and a flat `n` with the same target,
every cartesian square over `(m, n)` has `P` on its projection to the source of `n`.

The comparison of the given cartesian square with the chosen pullback is an isomorphism over the
source of `n`, across which invariance under isomorphism transports `P`. This is the flat form of
`AlgebraicGeometry.Stack.prop_of_isPullback`, which obtains the same conclusion from stability
under arbitrary base change and so needs no flatness. -/
theorem prop_of_isPullback_of_isFlat
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hiso : MorphismProperty.RespectsIso P)
    (hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → P m → P (pullback.snd m n))
    {X Y Y' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (_hW : IsAlgebraicSpace B S hS W)
    (m : X ⟶ Y) (n : Y' ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y')
    (sq : IsPullback p q m n) (hn : Space.IsFlat B S hS n) (hm : P m) :
    P q := by
  let : P.RespectsIso := hiso
  have hpb : IsPullback (pullback.fst m n) (pullback.snd m n) m n := IsPullback.of_hasPullback m n
  have hsnd : P (pullback.snd m n) := hbc hX hY hY' m n hn hm
  have he : (hpb.isoIsPullback X Y' sq).hom ≫ q = pullback.snd m n :=
    IsPullback.isoIsPullback_hom_snd X Y' hpb sq
  have hcomp : P ((hpb.isoIsPullback X Y' sq).inv ≫ (hpb.isoIsPullback X Y' sq).hom ≫ q) :=
    (P.cancel_left_of_respectsIso (hpb.isoIsPullback X Y' sq).inv
      ((hpb.isoIsPullback X Y' sq).hom ≫ q)).mpr (by rw [he]; exact hsnd)
  rwa [Iso.inv_hom_id_assoc] at hcomp

/-- **The first projection of a 2-fibre product of represented categories is a flat base change,
read on representing presheaves.** If the morphism of representing presheaves induced by `q` has
`P` and the one induced by `p` is flat, then the one induced by the first projection of the
canonical 2-fibre product square of `(p, q)` has `P`.

Under the 04SD identification `AlgebraicGeometry.Stack.fibreProductIsoRepresenting` the two
projections of the square become the two projections of the presheaf fibre product, by
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_fst` and `_snd`, so
the square of representing presheaves is cartesian and
`AlgebraicGeometry.Stack.prop_of_isPullback_of_isFlat` applies to it. This is the flat form of
`AlgebraicGeometry.Stack.prop_representingMap_fst`. -/
theorem prop_representingMap_fst_of_isFlat
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hiso : MorphismProperty.RespectsIso P)
    (hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → P m → P (pullback.snd m n))
    (𝒜 ℬ 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hT : IsAlgebraicSpace B S hS T)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      ℬ.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (p : 𝒜 ⟶ 𝒞) (q : ℬ ⟶ 𝒞)
    [(twoFibreProductStructureFunctor B S hS 𝒜 ℬ 𝒞 p q).IsFibered]
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒜 ℬ 𝒞 p q)
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hp : Space.IsFlat B S hS (representingMap B S hS 𝒜 𝒞 F H eF eH p))
    (hq : P (representingMap B S hS ℬ 𝒞 G H eG eH q)) :
    P (representingMap B S hS
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
        (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst) :=
  prop_of_isPullback_of_isFlat B S hS P hiso hbc hG hH hF hT
    (representingMap B S hS ℬ 𝒞 G H eG eH q)
    (representingMap B S hS 𝒜 𝒞 F H eF eH p)
    (representingMap B S hS
      (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt ℬ T G eT eG
      (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).snd)
    (representingMap B S hS
      (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
      (twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst)
    (isPullback_representingMap_twoFibreProduct B S hS 𝒜 ℬ 𝒞 F G H eF eG eH p q T eT) hp hq

/-! ### Flat base change of the smooth-diagram criterion -/

/-- **A base change of a flat 1-morphism along a 1-morphism out of an algebraic space is flat.**
If `c : 𝒯 ⟶ 𝒴` passes the existential smooth-diagram test at flatness and `E` is a 2-fibre
product of the cospan `(c, b)` for a `b` out of the category fibred in groupoids of an algebraic
space `V`, then `E.snd` passes that test too.

This is the Stacks 06FQ chain at flatness, where the base-change stability hypothesis it asks for
is available by **Stacks 03MO**. It concludes about the first projection of the canonical 2-fibre
product of the reversed cospan, which `E.swap` also is, so
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct` carries the
conclusion to `E.snd`. -/
theorem hasPropertyOnSomeSmoothDiagram_isFlat_snd_of_isTwoFibreProduct
    {𝒴 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (c : 𝒯 ⟶ 𝒴) {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (E : Bicategory.TwoCommSq c b) (hE : Bicategory.IsTwoFibreProduct E)
    (hcflat : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) c) :
    HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsFlat B S hS k) E.snd :=
  let : (spaceProperty B S hS
      (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS
    (fun _ _ k => Space.IsFlat B S hS k)
    (twoFibreProductSquare.{u, u, u + 1, u + 1} b c) E.swap
    (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b c)
    (Bicategory.isTwoFibreProduct_swap hE)
    (hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace B S hS
      (fun _ _ k => Space.IsFlat B S hS k) c b
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV) hcflat)

/-- **That base change is flat, read on representing presheaves.** In the situation of
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_isFlat_snd_of_isTwoFibreProduct`, the
morphism `V₁ ⟶ V` of representing presheaves induced by `E.snd` is flat.

This is the equivalence of conditions (2) and (3) of **Stacks 06FM** at flatness, which is smooth
local on the source-and-target by **Stacks 06FC**. -/
theorem isFlat_representingMap_snd_of_isTwoFibreProduct
    {𝒴 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (c : 𝒯 ⟶ 𝒴) {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (E : Bicategory.TwoCommSq c b) (hE : Bicategory.IsTwoFibreProduct E)
    (V₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV₁ : IsAlgebraicSpace B S hS V₁)
    (eE : StacksRepresentableCFG.EquivalenceOver
      E.pt.val.p (presheafOfCategories (V₁ ⋙ typeToCat)).p)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (fibredCategory B S hS V).val.p (presheafOfCategories (V ⋙ typeToCat)).p)
    (hcflat : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) c) :
    Space.IsFlat B S hS
      (representingMap B S hS E.pt (fibredCategory B S hS V) V₁ V eE eV E.snd) :=
  prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS
    (fun _ _ k => Space.IsFlat B S hS k)
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) V₁ V hV₁ hV eE eV E.snd
    (hasPropertyOnSomeSmoothDiagram_isFlat_snd_of_isTwoFibreProduct B S hS c hV b E hE hcflat)

/-- **Flat base change of condition (2) of Stacks 06FM along a 1-morphism out of a category
representable by an algebraic space.** Given a smooth diagram over `f : 𝒳 ⟶ 𝒴` whose left
vertical 1-morphism is surjective on objects and whose top horizontal morphism has `P`, the base
change of `f` along a flat `c : 𝒯 ⟶ 𝒴` carries one too, as soon as `𝒯` is representable by an
algebraic space.

This is the paragraph of Stacks 06FQ formalized as
`...hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace`, with flatness
threaded through its one use of base-change stability. The new diagram's apex is
`(𝒯 ×_𝒴 V) ×_V U`, whose projection to `𝒯 ×_𝒴 V` is the base change of the 1-morphism attached to
the top horizontal morphism along the second projection of `𝒯 ×_𝒴 V`. That projection is the base
change of the flat `c`, so it is flat by the Stacks 06FQ chain at flatness, and the morphism of
representing presheaves it induces is flat by the equivalence of conditions (2) and (3) of
Stacks 06FM — both steps being
`AlgebraicGeometry.Stack.isFlat_representingMap_snd_of_isTwoFibreProduct`;
`AlgebraicGeometry.Stack.prop_representingMap_fst_of_isFlat` then supplies `P` on the top
horizontal morphism of the new diagram. Everything else is as in the statement copied. -/
theorem hasPropertyOnSomeSmoothDiagram_flatBaseChange_of_representable
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hiso : MorphismProperty.RespectsIso P)
    (hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → P m → P (pullback.snd m n))
    {𝒳 𝒴 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (c : 𝒯 ⟶ 𝒴)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯)
    (hcflat : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) c)
    (hsome : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} c f).fst := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hsome
  obtain ⟨T₀, hT₀, ⟨e𝒯⟩⟩ := h𝒯
  set K := twoFibreProductSquare.{u, u, u + 1, u + 1} c f with hKdef
  set E := twoFibreProductSquare.{u, u, u + 1, u + 1} c b with hEdef
  have hE : Bicategory.IsTwoFibreProduct E :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c b
  have hEfst : IsRelativelySmooth.{u, u, u + 1} B S hS E.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴 𝒯 b c E hE hb
  obtain ⟨V₁, hV₁, ⟨eE⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒴 𝒯
    (fibredCategory B S hS V) c.hom b.hom hb.1 ⟨T₀, hT₀, ⟨e𝒯⟩⟩
  have hEsndFlat : Space.IsFlat B S hS
      (representingMap B S hS E.pt (fibredCategory B S hS V) V₁ V eE
        (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd) :=
    isFlat_representingMap_snd_of_isTwoFibreProduct B S hS c hV b E hE V₁ hV₁ eE
      (StacksRepresentableCFG.EquivalenceOver.refl _) hcflat
  have hMorRep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS h).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS h).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV)
  set F' := twoFibreProductSquare.{u, u, u + 1, u + 1} E.snd (associatedMap B S hS h).1
    with hF'def
  obtain ⟨A, hA, ⟨eA⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) E.pt (fibredCategory B S hS U) E.snd.hom
    (associatedMap B S hS h).1.hom hMorRep ⟨V₁, hV₁, ⟨eE⟩⟩
  have hFib : (twoFibreProductStructureFunctor B S hS E.pt (fibredCategory B S hS U)
      (fibredCategory B S hS V) E.snd (associatedMap B S hS h).1).IsFibered :=
    F'.pt.isFiberedInGroupoids.isFibered
  have hPTop : P (representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst) :=
    prop_representingMap_fst_of_isFlat B S hS P hiso hbc E.pt (fibredCategory B S hS U)
      (fibredCategory B S hS V) V₁ U V A hV₁ hU hV hA eE
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) E.snd (associatedMap B S hS h).1 eA
      hEsndFlat
      (by rw [representingMap_associatedMap B S hS U V h]; exact hPh)
  set D := twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a with hDdef
  have hD : Bicategory.IsTwoFibreProduct D :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} K.snd a
  have hDfst : IsRelativelySmooth.{u, u, u + 1} B S hS D.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS U) 𝒳 K.pt a
      K.snd D hD ha
  have haSu := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS a ha.1).1 hsurj
  have hDfstSurj := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u}
    B S hS D.fst hDfst.1).2
    (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳 K.pt a K.snd D hD
      ha.1 haSu)
  have hLD : Bicategory.IsTwoFibreProduct
      (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)
  have hLF : Bicategory.IsTwoFibreProduct
      (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η) :=
    isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1
      (a ≫ f) η
  have cPre : Bicategory.TwoCommSq.PreHom
      (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η)
      (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)) :=
    Quotient.out
      (hLD.from (cancelSndSquare.{u, u, u + 1, u + 1} c b (associatedMap B S hS h).1 (a ≫ f) η))
  have hcEq : Functor.IsEquivalence cPre.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hLF hLD cPre
  have hcomp : IsRelativelySmooth.{u, u, u + 1} B S hS (cPre.hom ≫ D.fst) :=
    isRelativelySmooth_of_isEquivalence_comp B S hS cPre.hom D.fst hcEq hDfst
  refine ⟨A, V₁, hA, hV₁,
    equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA ≫ (cPre.hom ≫ D.fst),
    equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ eE ≫ E.fst,
    representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst, ?_, ?_, ?_, ?_, hPTop⟩
  · have key : ∀ {𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
        (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (eW : StacksRepresentableCFG.EquivalenceOver
          𝒳'.val.p (presheafOfCategories (W ⋙ typeToCat)).p) (g : 𝒳' ⟶ 𝒯),
        representingMap B S hS (fibredCategory B S hS W) 𝒯 W T₀
          (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯
          (equivalenceOverInvMap B S hS W eW ≫ g) =
        representingMap B S hS 𝒳' 𝒯 W T₀ eW e𝒯 g := by
      intro 𝒳' W eW g
      rw [representingMap_comp (𝒜 := fibredCategory B S hS W) (ℬ := 𝒳') (𝒞 := 𝒯) B S hS W W T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) eW e𝒯,
        representingMap_equivalenceOverInvMap B S hS W eW, Category.id_comp]
    have hleft := representingMap_comp (𝒜 := fibredCategory B S hS A)
      (ℬ := fibredCategory B S hS V₁) (𝒞 := 𝒯) B S hS A V₁ T₀
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯
      (associatedMap B S hS (representingMap B S hS F'.pt E.pt A V₁ eA eE F'.fst)).1
      (equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ eE ≫ E.fst)
    erw [representingMap_associatedMap, key V₁ eE E.fst] at hleft
    have hright := (key (𝒳' := F'.pt) A eA
      (cPre.hom ≫ (cancelSndSquare.{u, u, u + 1, u + 1} c f a (a ≫ f) (Iso.refl _)).fst)).trans
      ((representingMap_congr_twoIso (𝒜 := F'.pt) (𝒞 := 𝒯) B S hS A T₀ eA e𝒯
        cPre.isoFst).symm.trans (representingMap_comp (𝒜 := F'.pt) (ℬ := E.pt) (𝒞 := 𝒯)
        B S hS A V₁ T₀ eA eE e𝒯 F'.fst E.fst))
    obtain ⟨e2, he2⟩ := Quotient.exact
      ((morphismSpaceEquiv B S hS (fibredCategory B S hS A) 𝒯 A T₀
        (StacksRepresentableCFG.EquivalenceOver.refl _) e𝒯).injective (hleft.trans hright.symm))
    exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e2 he2)⟩
  · exact isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := F'.pt) A hA eA) hcomp
  · exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS A).val.p F'.pt.val.p
      K.pt.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA))
      (CatFiberedInGroupoids.homFunctor (cPre.hom ≫ D.fst))
      (CatFiberedInGroupoids.homFunctor_comp_p (cPre.hom ≫ D.fst))
      (isSurjectiveOnObjects_equivalenceOverInvMap B S hS (𝒳 := F'.pt) A eA)
      (isSurjectiveOnObjects_comp B S hS F'.pt.val.p D.pt.val.p K.pt.val.p
        (CatFiberedInGroupoids.homFunctor cPre.hom)
        (CatFiberedInGroupoids.homFunctor D.fst)
        (CatFiberedInGroupoids.homFunctor_comp_p D.fst)
        (isSurjectiveOnObjects_of_isEquivalence B S hS cPre.hom hcEq) hDfstSurj)
  · exact isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_equivalenceOverInvMap B S hS (𝒳 := E.pt) V₁ hV₁ eE) hEfst

/-- **Flat base change of condition (2) of Stacks 06FM along an arbitrary 2-fibre-product square
of algebraic stacks.** A property of morphisms of algebraic spaces over `S` which is invariant
under isomorphism and stable under flat base change induces, through the existential
smooth-diagram criterion of Stacks 06FM, a property of 1-morphisms of algebraic stacks over `S`
stable under base change along a flat 1-morphism. This is **Stacks 06FQ** restricted to a flat
cospan leg, which is the restriction the hint of **Stacks 0CJ5** names, and with arbitrary
base-change stability of `P` correspondingly weakened to the flat form.

The proof is that of
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange`. A
smooth surjective presentation `𝒯 ⟶ 𝒴'` by a scheme is supplied by the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`; `𝒯` is representable by an algebraic space and the
composite `𝒯 ⟶ 𝒴' ⟶ 𝒴` is flat, a smooth 1-morphism being flat and flat 1-morphisms composing by
**Stacks 06PX**, so the flat form above applies to the base change of `f` along it. That base
change is at the same time the base change of the projection `𝒴' ×_𝒴 𝒳 ⟶ 𝒴'` along the
presentation, so
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas` descends the
conclusion to the projection itself, and
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct` transfers it to
the given square, whose underlying square is a 2-fibre product in the ambient 2-category by
`CategoryTheory.Bicategory.isTwoFibreProduct_of_section`. -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hiso : MorphismProperty.RespectsIso P)
    (hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → P m → P (pullback.snd m n))
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (hg : AlgebraicStacks.IsFlat B S hS g)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f.hom) :
    HasPropertyOnSomeSmoothDiagram B S hS P Q.fst.hom := by
  obtain ⟨hfib, hstack, hdiag, T, k, hk, hkprop⟩ := 𝒴'.property
  set t : schemeFibredCategory B S hS T ⟶ 𝒴'.val :=
    Bicategory.InducedBicategory.mkHom k with htdef
  have ht : IsRelativelySmooth.{u, u, u + 1} B S hS t :=
    ⟨hk, fun W y hy G hG he => (hkprop W y hy G hG he).2⟩
  have htSurj : IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS T).val.p
      𝒴'.val.val.p (CatFiberedInGroupoids.homFunctor t) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS t hk).mpr
      (fun W y hy G hG he => (hkprop W y hy G hG he).1)
  obtain ⟨F₀, hF₀, ⟨eF₀⟩⟩ := isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T
  have htFlat : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) t :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
      (fun _ _ k => Space.IsFlat B S hS k) t F₀ hF₀ eF₀ ht (Space.isFlat_id B S hS hF₀)
  have hcflat : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (t ≫ g.hom) :=
    hasPropertyOnSomeSmoothDiagram_isFlat_comp B S hS t g.hom htFlat
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).1 hg)
  set Rs := (twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).swap with hRsdef
  have hRs : Bicategory.IsTwoFibreProduct Rs :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
  set M := twoFibreProductSquare.{u, u, u + 1, u + 1} Rs.fst t with hMdef
  have hM : Bicategory.IsTwoFibreProduct M :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Rs.fst t
  have hL : Bicategory.IsTwoFibreProduct
      ((cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom) (Iso.refl _)).swap) :=
    Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom)
        (Iso.refl _))
  have hK := hasPropertyOnSomeSmoothDiagram_flatBaseChange_of_representable
    B S hS P hiso hbc f.hom (t ≫ g.hom)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS T) hcflat hf
  have hMsnd : HasPropertyOnSomeSmoothDiagram B S hS P M.snd :=
    hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P
      (twoFibreProductSquare.{u, u, u + 1, u + 1} (t ≫ g.hom) f.hom)
      ((cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom t (t ≫ g.hom) (Iso.refl _)).swap)
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} (t ≫ g.hom) f.hom) hL hK
  have hRsfst : HasPropertyOnSomeSmoothDiagram B S hS P Rs.fst :=
    hasPropertyOnSomeSmoothDiagram_of_baseChange_along_atlas B S hS P Rs.fst t M hM ht
      htSurj hMsnd
  set Rst := twoFibreProductSquareAlgebraicStacks B S hS g f with hRstdef
  have hRst : Bicategory.IsTwoFibreProduct Rst :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  have d : Bicategory.TwoCommSq.PreHom Rst Q := Quotient.out (hQ.from Rst)
  have k' : Bicategory.TwoCommSq.PreHom Q Rst := Quotient.out (hRst.from Q)
  obtain ⟨θ, -, -⟩ : Bicategory.TwoCommSq.PreHom.Rel (k'.comp d)
      (Bicategory.TwoCommSq.PreHom.id Q) :=
    Quotient.exact (hQ.hom_ext (Quotient.mk _ (k'.comp d)) (𝟙 Q))
  have hQu : Bicategory.IsTwoFibreProduct Q.underlying :=
    Bicategory.isTwoFibreProduct_of_section
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom)
      d.underlying k'.hom.hom
      (Bicategory.InducedBicategory.isoHom (f := (k'.comp d).hom)
        (g := (Bicategory.TwoCommSq.PreHom.id Q).hom) θ)
  exact hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS P Rs Q.underlying
    hRs hQu hRsfst

namespace AlgebraicStacks

/-- **Stacks 0CJ5.** A flat base change of a local complete intersection 1-morphism of algebraic
stacks over `S` is a local complete intersection 1-morphism: if `Q` is a 2-fibre product of the
cospan `(g, f)`, `g` is flat and `f` is Koszul, then the projection `Q.fst` is Koszul.

This is the flat base-change remark `hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat` — the
form of **Stacks 06FQ** the source's hint names — at the Koszul property of morphisms of algebraic
spaces, which is invariant under isomorphism by **Stacks 03MJ** and stable under flat base change
by **Stacks 06C7**. Stacks 0CJ3 is the universal smooth-diagram criterion of **Stacks 06FM** where
that remark concludes about the existential one, so both hypothesis and conclusion are moved
across the equivalence of conditions (1) and (2) of Stacks 06FM.

One hypothesis beyond the source's is carried: `hlocal`, that the Koszul property of morphisms of
algebraic spaces is smooth local on the source-and-target (**Stacks 06FC** at that property), which
is what crosses that equivalence. It is not available in this library; see the
carried-hypothesis note in the module docstring. -/
@[stacks 0CJ5 "the base-change argument in full, carrying one hypothesis this library does not \
prove: `hlocal`, Stacks 06FC at the Koszul property of morphisms of algebraic spaces"]
theorem isLocalCompleteIntersection_baseChange
    (hlocal : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k))
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (hg : IsFlat B S hS g)
    (Q : Bicategory.TwoCommSq g f)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsLocalCompleteIntersection B S hS f) :
    IsLocalCompleteIntersection B S hS Q.fst := by
  have hiso : MorphismProperty.RespectsIso
      (fun ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (k : F ⟶ G) =>
        Space.IsLocalCompleteIntersection B S hS k) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS _
  have hbc : ∀ {X₀ Y₀ Y₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hY' : IsAlgebraicSpace B S hS Y₀') (m : X₀ ⟶ Y₀) (n : Y₀' ⟶ Y₀),
      Space.IsFlat B S hS n → Space.IsLocalCompleteIntersection B S hS m →
      Space.IsLocalCompleteIntersection B S hS (Limits.pullback.snd m n) := by
    intro X₀ Y₀ Y₀' hX₀ hY₀ hY₀' m n hn hm
    exact Space.isLocalCompleteIntersection_pullback_snd B S hS
      (ObjectProperty.homMk m : (⟨X₀, hX₀⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY₀⟩)
      (ObjectProperty.homMk n : (⟨Y₀', hY₀'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY₀⟩) hn hm
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlocal
      Q.pt.property 𝒴'.property Q.fst.hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isFlat B S hS
      (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hiso hbc f g hg Q hQ
      ((Stack.hasPropertyOnEverySmoothDiagram_iff_some B S hS
        (fun _ _ k => Space.IsLocalCompleteIntersection B S hS k) hlocal
        𝒳.property 𝒴.property f.hom).1 hf))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
