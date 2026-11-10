module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery

/-!
# The étale-smooth diagram of Stacks 0CIF from an étale presentation of the 2-fibre product

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. The diagram data of condition (2)
of **Stacks 0CIF**, `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, is what the
implication (1) ⇒ (2) of that equivalence needs. This module builds it from two inputs:
a smooth presentation of `𝒴`, surjective on objects, by an algebraic space `V`, and a surjective
**étale** presentation by a scheme of the apex of the canonical 2-fibre product `𝒳 ×_𝒴 V`.

The construction is the étale reading of
`AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram`, the smooth
analogue for Stacks 06FM (1) ⇒ (2): the left vertical 1-morphism of the diagram is the
presentation of `𝒳 ×_𝒴 V` followed by the projection to `𝒳`, surjective on objects by
**Stacks 06D7**, and the comparison of the diagram's cone with the 2-fibre product is that
presentation itself — which is étale here rather than merely smooth, which is the whole
difference between Stacks 0CIF and Stacks 06FM.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProductSquarePt_algebraicSpaceStack`: the
  apex of the canonical 2-fibre product of `f` with a presentation of `𝒴` by an algebraic space
  is an algebraic stack (**Stacks 04TF**), so it is a stack an étale presentation may be sought
  for.
* `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_etalePresentation`: the diagram
  data of Stacks 0CIF condition (2), from a smooth presentation of `𝒴` and a surjective étale
  presentation of `𝒳 ×_𝒴 V`.
* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_etalePresentation`:
  the first assertion of Stacks 0CIF for an étale-smooth local `P`, given those two
  presentations.

## Implementation notes

The étale presentation is taken as data rather than produced. Producing it for a
Deligne–Mumford `f` is **Stacks 0CIA**, which rests on **Stacks 06N3** — a Deligne–Mumford
algebraic stack admits a surjective étale presentation by a scheme — and is done downstream, in
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward`, which feeds it to
the construction here. What is settled here is that nothing *else* is needed: given the
presentation, the diagram and with it the first assertion of Stacks 0CIF follow. The
presentation is asked for at the level of a *scheme*, which is the form both the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` and Stacks 06N3 deliver it in; the backward 1-morphism
of the representing equivalence of that scheme's presheaf is interposed, and it is relatively
étale by `AlgebraicGeometry.Stack.isRelativelyEtale_equivalenceOverInvMap`.

Two steps of the smooth construction are *not* transcribed, because at étaleness they are not
needed:

* the smooth analogue composes the presentation with that backward 1-morphism using
  `AlgebraicGeometry.Stack.isRelativelySmooth_comp` (**Stacks 045B**). Stacks 045B at étaleness
  is `AlgebraicGeometry.Stack.isRelativelyEtale_comp`, but the interposed 1-morphism is an
  *equivalence*, so the one-step transport
  `AlgebraicGeometry.Stack.isRelativelyEtale_of_isEquivalence_comp` suffices.
* the smooth analogue also proves the left vertical 1-morphism smooth. Condition (2) of
  Stacks 0CIF asks only that it be *surjective*, so only surjectivity on objects and
  representability of the composite are proved here; the latter is **Stacks 0301**.

The `∀`-quantification over *every* 2-fibre product of `(b, f)` and *every* comparison out of the
diagram's cone is discharged by `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one`, so the
comparison is only ever checked at the canonical square.

Nothing here carries `@[stacks 0CIF]`. The covering set of its key
`"equivalence of parts (1) and (2)"` is a statement for every Deligne–Mumford `f` with no
presentation supplied; everything here assumes one, so each statement is strictly weaker, exactly
as in `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram`. The key
is carried by `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_some`.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04TF for the canonical 2-fibre product of a 1-morphism of algebraic stacks with a
presentation of its target by an algebraic space.** The apex of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare b.hom f.hom` is an algebraic stack
over `S`.

This is what makes the étale presentation hypothesis of
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_etalePresentation` a statement
Stacks 06N3 can be applied to: that tag presents a Deligne–Mumford *algebraic stack*, and the
apex is one. -/
theorem isAlgebraicStack_twoFibreProductSquarePt_algebraicSpaceStack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) :
    IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt.val := by
  obtain ⟨h𝒴fib, h𝒴stack, h𝒴diag, -, -, -, -⟩ := 𝒴.property
  exact isAlgebraicStack_twoFibreProduct B S hS (fibredCategory B S hS V).val 𝒳.val.val
    𝒴.val.val b.hom.hom f.hom.hom h𝒴stack h𝒴diag
    (isAlgebraicStack_fibredCategory.{u, w} B S hS V hV) 𝒳.property

/-- **The diagram data of condition (2) of Stacks 0CIF, from an étale presentation of the
2-fibre product.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let
`b : 𝒮_V ⟶ 𝒴` be a smooth 1-morphism, surjective on objects, out of the category fibred in
groupoids of an algebraic space `V`, and let the apex of the canonical 2-fibre product of
`(b, f)` admit a relatively étale presentation by a scheme `W`, surjective on objects. Then `f`
admits a 2-commutative square of algebraic spaces over it whose right vertical 1-morphism is `b`,
whose left vertical 1-morphism is surjective, and whose every comparison 1-morphism to every
2-fibre product of `(b, f)` is étale.

This is the étale analogue of
`AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram`. The left
vertical 1-morphism is the given presentation — composed with the backward 1-morphism of the
representing equivalence of `yoneda.obj W`, so that it starts from an algebraic space —
followed by the projection of the 2-fibre product to `𝒳`, which is surjective on objects by
**Stacks 06D7** and representable by algebraic spaces by **Stacks 0302** read across the exchange
of the two factors. The comparison of the diagram's cone with the canonical 2-fibre product is
that composite presentation, which is étale, and
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one` carries that to every other 2-fibre
product and every other comparison.

Supplying the étale presentation for a Deligne–Mumford `f` is **Stacks 0CIA**, through
**Stacks 06N3**; that is done in
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward`, which is why it is a
hypothesis here. -/
theorem hasSurjectiveEtaleSmoothDiagram_of_etalePresentation
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (hbsm : IsRelativelySmooth B S hS b.hom)
    (hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V).val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hpres : ∃ (W : BigFppfOver B S hS)
      (pres : schemeFibredCategory B S hS W ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt),
      IsRelativelyEtale B S hS pres ∧
      IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt.val.p
        (CatFiberedInGroupoids.homFunctor pres)) :
    HasSurjectiveEtaleSmoothDiagram B S hS f := by
  classical
  set R : Bicategory.TwoCommSq b.hom f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  obtain ⟨W, pres, hpreset, hpressu⟩ := hpres
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom
  -- the projection to `𝒳` is the base change of `b`: Stacks 0302 in the other order of the
  -- two factors, transported across the exchange
  have hreprsnd : IsRepresentableByAlgebraicSpaces B S hS R.snd.hom :=
    isRepresentableByAlgebraicSpaces_twoFibreProductSnd B S hS b.hom f.hom hbsm.1
  -- surjectivity on objects of the projection to `𝒳` is Stacks 06D7 at the presentation
  have hsusnd : IsSurjectiveOnObjects B S hS R.pt.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor R.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS
      (fibredCategory B S hS V) 𝒴.val 𝒳.val b.hom f.hom hbsu
  -- the presentation of the 2-fibre product, read from the algebraic space `yoneda.obj W`
  have hU : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver W
  let aInv : fibredCategory B S hS (yoneda.obj W) ⟶ schemeFibredCategory B S hS W :=
    equivalenceOverInvMap B S hS (yoneda.obj W) eU
  have haInvEquiv : Functor.IsEquivalence aInv.hom.toFunctor := by
    change Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  let pU : fibredCategory B S hS (yoneda.obj W) ⟶ R.pt := aInv ≫ pres
  have hpUet : IsRelativelyEtale B S hS pU :=
    isRelativelyEtale_of_isEquivalence_comp B S hS aInv pres haInvEquiv hpreset
  have hpUsu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (yoneda.obj W)).val.p R.pt.val.p
      (CatFiberedInGroupoids.homFunctor pU) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj W)).val.p
      (schemeFibredCategory B S hS W).val.p R.pt.val.p
      (CatFiberedInGroupoids.homFunctor aInv) (CatFiberedInGroupoids.homFunctor pres)
      (CatFiberedInGroupoids.homFunctor_comp_p pres)
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS W) B S hS
        (yoneda.obj W) eU)
      hpressu
  -- the left vertical 1-morphism of the diagram
  let a₀ : fibredCategory B S hS (yoneda.obj W) ⟶ 𝒳.val := pU ≫ R.snd
  have hrepa : IsRepresentableByAlgebraicSpaces B S hS a₀.hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS pU R.snd hpUet.1 hreprsnd
  have hasu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (yoneda.obj W)).val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor a₀) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj W)).val.p
      R.pt.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor pU)
      (CatFiberedInGroupoids.homFunctor R.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p R.snd) hpUsu hsusnd
  -- the top horizontal morphism of algebraic spaces, from Stacks 04SW
  set hTop := representingMap B S hS (fibredCategory B S hS (yoneda.obj W))
    (fibredCategory B S hS V) (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (pU ≫ R.fst)
  -- the 1-morphism attached to it is 2-isomorphic to the comparison, by Stacks 04SW
  have hleft : representingMap B S hS (fibredCategory B S hS (yoneda.obj W))
      (fibredCategory B S hS V) (yoneda.obj W) V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS hTop).1 = hTop :=
    representingMap_associatedMap B S hS (yoneda.obj W) V hTop
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS (yoneda.obj W)) (fibredCategory B S hS V)
    (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hleft
  let eIso : (associatedMap B S hS hTop).1 ≅ pU ≫ R.fst :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)
  -- the invertible 2-cell of the diagram, built so that the comparison below has identity
  -- comparison 2-cell along the left vertical 1-morphism
  let η : (associatedMap B S hS hTop).1 ≫ b.hom ≅ a₀ ≫ f.hom :=
    Bicategory.whiskerRightIso eIso b.hom ≪≫ Bicategory.associator pU R.fst b.hom ≪≫
      Bicategory.whiskerLeftIso pU R.iso ≪≫ (Bicategory.associator pU R.snd f.hom).symm
  -- the comparison of the diagram's cone with the canonical 2-fibre product
  let k₁ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a₀ b.hom hTop η) R :=
    { hom := pU
      isoFst := eIso
      isoSnd := Iso.refl a₀
      compat := by
        have hid : Bicategory.whiskerRight (𝟙 a₀) f.hom = 𝟙 (a₀ ≫ f.hom) :=
          Bicategory.id_whiskerRight a₀ f.hom
        simp [η, hid] }
  refine ⟨yoneda.obj W, V, hU, hV, Bicategory.InducedBicategory.mkHom a₀, b, hTop, η, ?_, hbsm,
    isRelativelyEtale_preHom_of_one B S hS hR k₁ hpUet⟩
  exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS
    (Bicategory.InducedBicategory.mkHom a₀ :
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) hU ⟶ 𝒳) hrepa).2
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a₀
      hrepa).1 hasu)

/-- **The first assertion of Stacks 0CIF, from an étale presentation of the 2-fibre product.**
For a property `P` of morphisms of algebraic spaces over `S` which is étale-smooth local on the
source-and-target (**Stacks 0CFZ**) and a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
admitting a smooth presentation of `𝒴` surjective on objects together with a surjective étale
presentation of the apex of `𝒳 ×_𝒴 V`, the universal and existential étale-smooth diagram tests
of Stacks 0CIF agree.

Stacks 0CIF asserts this for every Deligne–Mumford `f`, with the presentations produced by
**Stacks 0CIA** rather than assumed, so this statement is weaker and carries no `@[stacks]`
attribute. It is the step that remains after that production: the two presentations are the only
inputs. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_etalePresentation
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (hbsm : IsRelativelySmooth B S hS b.hom)
    (hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V).val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor b.hom))
    (hpres : ∃ (W : BigFppfOver B S hS)
      (pres : schemeFibredCategory B S hS W ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt),
      IsRelativelyEtale B S hS pres ∧
      IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS W).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom).pt.val.p
        (CatFiberedInGroupoids.homFunctor pres)) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f ↔
      HasPropertyOnSomeEtaleSmoothDiagram B S hS P f :=
  hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_hasSurjectiveEtaleSmoothDiagram B S hS P hP f
    (hasSurjectiveEtaleSmoothDiagram_of_etalePresentation.{u, w} B S hS f V hV b hbsm hbsu hpres)

end AlgebraicGeometry.Stack

end
