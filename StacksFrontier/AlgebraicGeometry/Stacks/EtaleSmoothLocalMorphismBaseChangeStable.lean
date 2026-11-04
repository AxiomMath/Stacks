module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Base change of an étale-smooth local property of Deligne–Mumford morphisms (Stacks 0CII)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target (**Stacks 0CFZ**) and stable under base change. **Stacks 0CII** asserts
that the property of Deligne–Mumford 1-morphisms of algebraic stacks that **Stacks 0CIG**
induces from `P` is stable under arbitrary base change.

## Main results

* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_baseChange`: **Stacks 0CII**, for the
  canonical 2-fibre product square.

## Implementation notes

The proof is the source's. The Deligne–Mumford half is **Stacks 050F**, already proved as
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange`. For the diagram half it suffices to
exhibit *one* diagram of condition (2) of **Stacks 0CIF**, because the implication from the
existential test to the universal one — condition (2) ⇒ condition (1) of Stacks 0CIF, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse` — holds in full
generality.

The source builds that diagram from three choices: a smooth presentation `V ⟶ 𝒴` surjective on
objects, a surjective étale presentation `U ⟶ 𝒳 ×_𝒴 V` — this is the one appeal to
**Stacks 0CIA**, hence the hypothesis `hForward` — and a smooth presentation `V' ⟶ 𝒵 ×_𝒴 V`
surjective on objects. Its top-left corner is the algebraic space `V' ×_V U` and its top
horizontal morphism is the base change of `U ⟶ V` along `V' ⟶ V`, which is where stability of
`P` under base change is used, through **Stacks 04SD** in the form
`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProduct`.

Two cancellations of **Stacks 02XD** identify the apexes: `(𝒳 ×_𝒴 V) ×_V V'` is a 2-fibre
product of `(f, V' ⟶ 𝒴)` by `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` read at the
chart `V' ⟶ V`, and `(𝒳 ×_𝒴 𝒵) ×_𝒵 V'` is one by the same lemma read at `V' ⟶ 𝒵`; the
comparison of the two is an equivalence, and composing it with the base change of the étale
presentation along `V' ⟶ V` gives an étale chart of `(𝒳 ×_𝒴 𝒵) ×_𝒵 V'`, which is the apex of
the canonical 2-fibre product of the cospan the new diagram sits over. Every comparison
1-morphism out of the new diagram's cone is then étale by
`isRelativelyEtale_preHom_diagramCone_of_chart`, the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_diagramCone_of_chart`.

The statement is for the canonical 2-fibre product square, which is the shape
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange` is stated at.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base-change-stable property is inherited by the first projection of a 2-fibre product of
represented categories, read on representing presheaves.** If the morphism of algebraic spaces
induced by `q` has `P`, then so does the one induced by the first projection of the canonical
2-fibre product square of `(p, q)`.

Under the identification of **Stacks 04SD** the square of representing presheaves induced by the
canonical 2-fibre product square is cartesian, so this is stability of `P` under base change. -/
private theorem prop_representingMap_twoFibreProductFst
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
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
    (hq : P (ObjectProperty.homMk (representingMap B S hS ℬ 𝒞 G H eG eH q) :
      (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩)) :
    P (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst) :
      (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩) := by
  have hsq1 := isPullback_representingMap_twoFibreProduct B S hS 𝒜 ℬ 𝒞 F G H eF eG eH p q T eT
  have hsqA : IsPullback
      (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt ℬ T G eT eG
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).snd) :
          (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
      (ObjectProperty.homMk (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).pt 𝒜 T F eT eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} p q).fst) :
          (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk (representingMap B S hS ℬ 𝒞 G H eG eH q) :
        (⟨G, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩)
      (ObjectProperty.homMk (representingMap B S hS 𝒜 𝒞 F H eF eH p) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨H, hH⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq1
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqA hq

/-- **Stacks 0CII.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
étale-smooth local on the source-and-target and stable under base change. Then the property of
Deligne–Mumford 1-morphisms of algebraic stacks over `S` that **Stacks 0CIG** induces from `P`
is inherited by the base change of a 1-morphism along the canonical 2-fibre product square.

The Deligne–Mumford condition on the base change is **Stacks 050F**, and the diagram of
condition (2) of **Stacks 0CIF** is the source's: its top-left corner is `V' ×_V U` for a smooth
presentation `V ⟶ 𝒴`, a surjective étale presentation `U ⟶ 𝒳 ×_𝒴 V` and a smooth presentation
`V' ⟶ 𝒵 ×_𝒴 V`, and its top horizontal morphism is the base change of `U ⟶ V` along
`V' ⟶ V`. -/
@[stacks 0CII "for the canonical 2-fibre product square of Stacks 003Q, which is the shape the
  library version of Stacks 050F is stated at, and with the substantial direction of Stacks 06N3 as the
  explicit hypothesis hForward (the structure theorem behind it, Stacks 06MD, 06N0, 06N2, 06G2,
  06G3, is absent from the library); it enters only through Stacks 0CIA, which supplies the
  surjective etale presentation the source's argument chooses"]
theorem hasEtaleSmoothLocalProperty_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    [P.IsStableUnderBaseChange]
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : HasEtaleSmoothLocalProperty B S hS P f) :
    HasEtaleSmoothLocalProperty B S hS P
      (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd := by
  classical
  refine ⟨AlgebraicStacks.isDM_baseChange B S hS f g hf.1,
    hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
      B S hS P hP _ ?_⟩
  -- the smooth presentation of `𝒴`
  obtain ⟨V, hV, v, hvsm, hvsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒴.property
  set vS : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom v with hvS
  -- the surjective étale presentation of `𝒳 ×_𝒴 V` supplied by Stacks 0CIA
  set Jf₀ : Bicategory.TwoCommSq f.hom v :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom v with hJf₀
  have hJf₀FP : Bicategory.IsTwoFibreProduct Jf₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom v
  have hJfFP : Bicategory.IsTwoFibreProduct Jf₀.swap :=
    Bicategory.isTwoFibreProduct_swap hJf₀FP
  obtain ⟨W, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS (𝒜 := Jf₀.pt)
      (AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w}
        B S hS hZ hForward f hf.1 V hV vS)
  have hU : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  set eU := PresheafOfCategories.sliceElementsEquivalenceOver W with heU
  set cc : fibredCategory B S hS (yoneda.obj W) ⟶ Jf₀.pt :=
    equivalenceOverInvMap B S hS (yoneda.obj W) eU ≫ pres with hcc
  have hccet : IsRelativelyEtale B S hS cc :=
    isRelativelyEtale_of_isEquivalence_comp B S hS _ pres
      (by change Functor.IsEquivalence eU.inv.functor
          exact eU.toEquivalence.symm.isEquivalence_functor) hpreset
  have hccsu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (yoneda.obj W)).val.p Jf₀.pt.val.p
      (CatFiberedInGroupoids.homFunctor cc) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj W)).val.p
      (schemeFibredCategory B S hS W).val.p Jf₀.pt.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS (yoneda.obj W) eU))
      (CatFiberedInGroupoids.homFunctor pres)
      (CatFiberedInGroupoids.homFunctor_comp_p pres)
      (isSurjectiveOnObjects_equivalenceOverInvMap
        (𝒳 := schemeFibredCategory B S hS W) B S hS (yoneda.obj W) eU)
      hpressu
  -- the top horizontal morphism `U ⟶ V` of the first diagram, and its 2-cell
  set hTop := representingMap B S hS (fibredCategory B S hS (yoneda.obj W))
    (fibredCategory B S hS V) (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Jf₀.snd) with hTopdef
  obtain ⟨e₀, he₀, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS (yoneda.obj W)) (fibredCategory B S hS V) (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS (yoneda.obj W) V hTop)
  set e : (associatedMap B S hS hTop).1 ≅ cc ≫ Jf₀.snd :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e₀ he₀) with hedef
  -- `U ⟶ V` has `P`, by condition (1) of Stacks 0CIF for `f`
  have hPtop : P (ObjectProperty.homMk hTop :
      (⟨yoneda.obj W, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) :=
    hf.2 (yoneda.obj W) V hU hV
      (Bicategory.InducedBicategory.mkHom (cc ≫ Jf₀.swap.snd)) vS hTop
      (Bicategory.whiskerRightIso e v ≪≫ Bicategory.whiskerLeftIso cc Jf₀.swap.iso) hvsm
      (isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom v Jf₀.swap hJfFP cc hccet
        hTop e)
  -- the smooth presentation of `𝒵 ×_𝒴 V`
  set Gq : Bicategory.TwoCommSq v g.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} v g.hom with hGq
  have hGqFP : Bicategory.IsTwoFibreProduct Gq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} v g.hom
  obtain ⟨V', hV', pG, hpGsm, hpGsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      (isAlgebraicStack_twoFibreProductSquarePt_algebraicSpaceStack.{u, w} B S hS g V hV vS)
  have hv'sm : IsRelativelySmooth B S hS (pG ≫ Gq.snd) :=
    isRelativelySmooth_comp B S hS pG Gq.snd hpGsm
      (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS (fibredCategory B S hS V) 𝒴.val
        𝒵.val v g.hom Gq.swap (Bicategory.isTwoFibreProduct_swap hGqFP) hvsm)
  have hv'su : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V').val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor (pG ≫ Gq.snd)) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS V').val.p Gq.pt.val.p
      𝒵.val.val.p (CatFiberedInGroupoids.homFunctor pG)
      (CatFiberedInGroupoids.homFunctor Gq.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p Gq.snd) hpGsu
      (isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS (fibredCategory B S hS V)
        𝒴.val 𝒵.val v g.hom hvsu)
  -- the canonical 2-fibre product square the new diagram sits over
  set R : Bicategory.TwoCommSq f.hom g.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom with hR
  set T : Bicategory.TwoCommSq R.snd (pG ≫ Gq.snd) :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} R.snd (pG ≫ Gq.snd)
    with hT
  have hTFP : Bicategory.IsTwoFibreProduct T :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} R.snd
      (pG ≫ Gq.snd)
  have hTfstRep : IsRepresentableByAlgebraicSpaces B S hS T.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS V') 𝒵.val R.pt (pG ≫ Gq.snd) R.snd T hTFP hv'sm.1
  have hTfstSu : IsSurjectiveOnObjects B S hS T.pt.val.p R.pt.val.p
      (CatFiberedInGroupoids.homFunctor T.fst) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS T.fst
      hTfstRep).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS V') 𝒵.val R.pt
        (pG ≫ Gq.snd) R.snd T hTFP hv'sm.1
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
          (pG ≫ Gq.snd) hv'sm.1).1 hv'su))
  -- the two cancellations of Stacks 02XD comparing `(𝒳 ×_𝒴 V) ×_V V'` with `(𝒳 ×_𝒴 𝒵) ×_𝒵 V'`
  set Acan : Bicategory.TwoCommSq f.hom ((pG ≫ Gq.snd) ≫ g.hom) :=
    CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} f.hom v (pG ≫ Gq.fst)
      ((pG ≫ Gq.snd) ≫ g.hom) (Bicategory.whiskerLeftIso pG Gq.iso) with hAcan
  have hAcanFP : Bicategory.IsTwoFibreProduct Acan :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom v
      (pG ≫ Gq.fst) ((pG ≫ Gq.snd) ≫ g.hom) (Bicategory.whiskerLeftIso pG Gq.iso)
  set Bcan : Bicategory.TwoCommSq f.hom ((pG ≫ Gq.snd) ≫ g.hom) :=
    CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom (pG ≫ Gq.snd)
      ((pG ≫ Gq.snd) ≫ g.hom) (Iso.refl _) with hBcan
  have hBcanFP : Bicategory.IsTwoFibreProduct Bcan :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f.hom g.hom
      (pG ≫ Gq.snd) ((pG ≫ Gq.snd) ≫ g.hom) (Iso.refl _)
  have mcmp : Bicategory.TwoCommSq.PreHom Acan Bcan := Quotient.out (hBcanFP.from Acan)
  have hmEq : Functor.IsEquivalence mcmp.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hAcanFP hBcanFP mcmp
  -- the base change of the étale presentation along `V' ⟶ V`
  set Asq : Bicategory.TwoCommSq Jf₀.snd (pG ≫ Gq.fst) :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Jf₀.snd (pG ≫ Gq.fst)
    with hAsq
  set Zsq : Bicategory.TwoCommSq Asq.fst cc :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Asq.fst cc with hZsq
  have hZsqFP : Bicategory.IsTwoFibreProduct Zsq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Asq.fst cc
  have hZfstEt : IsRelativelyEtale B S hS Zsq.fst :=
    isRelativelyEtale_baseChange B S hS (fibredCategory B S hS (yoneda.obj W)) Jf₀.pt Asq.pt
      cc Asq.fst Zsq hZsqFP hccet
  have hZfstSu : IsSurjectiveOnObjects B S hS Zsq.pt.val.p Asq.pt.val.p
      (CatFiberedInGroupoids.homFunctor Zsq.fst) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS Zsq.fst
      hZfstEt.1).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS)
        (fibredCategory B S hS (yoneda.obj W)) Jf₀.pt Asq.pt cc Asq.fst Zsq hZsqFP hccet.1
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS cc
          hccet.1).1 hccsu))
  -- the presheaf fibre product `V' ×_V U`, as the apex of two 2-fibre products of one cospan
  set N : Bicategory.TwoCommSq (pG ≫ Gq.fst) (associatedMap B S hS hTop).1 :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (pG ≫ Gq.fst)
      (associatedMap B S hS hTop).1 with hN
  have hNFP : Bicategory.IsTwoFibreProduct N :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (pG ≫ Gq.fst) (associatedMap B S hS hTop).1
  set Csq : Bicategory.TwoCommSq (pG ≫ Gq.fst) (associatedMap B S hS hTop).1 :=
    CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} Jf₀.snd (pG ≫ Gq.fst) cc
      (associatedMap B S hS hTop).1 e.symm with hCsq
  have hCsqFP : Bicategory.IsTwoFibreProduct Csq :=
    CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} Jf₀.snd
      (pG ≫ Gq.fst) cc (associatedMap B S hS hTop).1 e.symm
  have dcmp : Bicategory.TwoCommSq.PreHom N Csq := Quotient.out (hCsqFP.from N)
  have hdEq : Functor.IsEquivalence dcmp.hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hNFP hCsqFP dcmp
  obtain ⟨W₂, hW₂, ⟨eW₂⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) (fibredCategory B S hS V')
    (fibredCategory B S hS (yoneda.obj W)) (pG ≫ Gq.fst).hom
    (associatedMap B S hS hTop).1.hom
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS hTop).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS (yoneda.obj W) hU)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV))
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS V' hV')
  have hNFib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS (yoneda.obj W)) (fibredCategory B S hS V) (pG ≫ Gq.fst)
      (associatedMap B S hS hTop).1).IsFibered :=
    N.pt.isFiberedInGroupoids.isFibered
  -- the top horizontal morphism `V' ×_V U ⟶ V'` of the new diagram, which has `P`
  have hleft : representingMap B S hS (fibredCategory B S hS W₂)
      (fibredCategory B S hS V') W₂ V'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (equivalenceOverInvMap B S hS (𝒳 := N.pt) W₂ eW₂ ≫ N.fst)
      = representingMap B S hS N.pt (fibredCategory B S hS V') W₂ V' eW₂
        (StacksRepresentableCFG.EquivalenceOver.refl _) N.fst := by
    rw [representingMap_comp (𝒜 := fibredCategory B S hS W₂) (ℬ := N.pt)
      (𝒞 := fibredCategory B S hS V') B S hS W₂ W₂ V'
      (StacksRepresentableCFG.EquivalenceOver.refl _) eW₂
      (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_equivalenceOverInvMap (𝒳 := N.pt) B S hS W₂ eW₂, Category.id_comp]
  set hTopB := representingMap B S hS N.pt (fibredCategory B S hS V') W₂ V' eW₂
    (StacksRepresentableCFG.EquivalenceOver.refl _) N.fst with hTopBdef
  have hPtopB : P (ObjectProperty.homMk hTopB :
      (⟨W₂, hW₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V', hV'⟩) :=
    prop_representingMap_twoFibreProductFst B S hS P (fibredCategory B S hS V')
      (fibredCategory B S hS (yoneda.obj W)) (fibredCategory B S hS V) V' (yoneda.obj W) V W₂
      hV' hU hV hW₂ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (pG ≫ Gq.fst)
      (associatedMap B S hS hTop).1 eW₂
      (by rw [representingMap_associatedMap B S hS (yoneda.obj W) V hTop]; exact hPtop)
  obtain ⟨ι₀, hι₀, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS W₂) (fibredCategory B S hS V') W₂ V'
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    ((representingMap_associatedMap B S hS W₂ V' hTopB).trans hleft.symm)
  -- the étale chart of `(𝒳 ×_𝒴 𝒵) ×_𝒵 V'` the new diagram is built from
  set chart : fibredCategory B S hS W₂ ⟶ T.pt :=
    equivalenceOverInvMap B S hS (𝒳 := N.pt) W₂ eW₂ ≫ dcmp.hom ≫ Zsq.fst ≫ mcmp.hom
    with hchart
  have hchartEt : IsRelativelyEtale B S hS chart :=
    isRelativelyEtale_comp B S hS _ _
      (isRelativelyEtale_equivalenceOverInvMap B S hS (𝒳 := N.pt) W₂ hW₂ eW₂)
      (isRelativelyEtale_of_isEquivalence_comp B S hS dcmp.hom _ hdEq
        (isRelativelyEtale_comp_of_isEquivalence B S hS Zsq.fst mcmp.hom hmEq hZfstEt))
  have hchartSu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS W₂).val.p R.pt.val.p
      (CatFiberedInGroupoids.homFunctor (chart ≫ T.fst)) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS W₂).val.p N.pt.val.p R.pt.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS (𝒳 := N.pt) W₂ eW₂))
      (CatFiberedInGroupoids.homFunctor (dcmp.hom ≫ Zsq.fst ≫ mcmp.hom ≫ T.fst))
      (CatFiberedInGroupoids.homFunctor_comp_p (dcmp.hom ≫ Zsq.fst ≫ mcmp.hom ≫ T.fst))
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := N.pt) B S hS W₂ eW₂)
      (isSurjectiveOnObjects_comp B S hS N.pt.val.p Csq.pt.val.p R.pt.val.p
        (CatFiberedInGroupoids.homFunctor dcmp.hom)
        (CatFiberedInGroupoids.homFunctor (Zsq.fst ≫ mcmp.hom ≫ T.fst))
        (CatFiberedInGroupoids.homFunctor_comp_p (Zsq.fst ≫ mcmp.hom ≫ T.fst))
        (isSurjectiveOnObjects_of_isEquivalence B S hS dcmp.hom hdEq)
        (isSurjectiveOnObjects_comp B S hS Zsq.pt.val.p Asq.pt.val.p R.pt.val.p
          (CatFiberedInGroupoids.homFunctor Zsq.fst)
          (CatFiberedInGroupoids.homFunctor (mcmp.hom ≫ T.fst))
          (CatFiberedInGroupoids.homFunctor_comp_p (mcmp.hom ≫ T.fst)) hZfstSu
          (isSurjectiveOnObjects_comp B S hS Asq.pt.val.p T.pt.val.p R.pt.val.p
            (CatFiberedInGroupoids.homFunctor mcmp.hom)
            (CatFiberedInGroupoids.homFunctor T.fst)
            (CatFiberedInGroupoids.homFunctor_comp_p T.fst)
            (isSurjectiveOnObjects_of_isEquivalence B S hS mcmp.hom hmEq) hTfstSu)))
  have eChart : (associatedMap B S hS hTopB).1 ≅ chart ≫ T.swap.fst :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ι₀ hι₀) ≪≫
      Bicategory.whiskerLeftIso (equivalenceOverInvMap B S hS (𝒳 := N.pt) W₂ eW₂)
        (dcmp.isoFst ≪≫ Bicategory.whiskerLeftIso dcmp.hom
          (Bicategory.whiskerLeftIso Zsq.fst mcmp.isoSnd))
  refine ⟨W₂, V', hW₂, hV',
    Bicategory.InducedBicategory.mkHom (chart ≫ T.swap.snd),
    Bicategory.InducedBicategory.mkHom (pG ≫ Gq.snd), hTopB,
    Bicategory.whiskerRightIso eChart (pG ≫ Gq.snd) ≪≫
      Bicategory.whiskerLeftIso chart T.swap.iso,
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (Bicategory.InducedBicategory.mkHom (chart ≫ T.swap.snd) :
        algebraicSpaceStack.{u, w} B S hS W₂ hW₂ ⟶
          (AlgebraicStacks.twoFibreProductSquare B S hS f g).pt) hchartSu,
    hv'sm,
    isRelativelyEtale_preHom_diagramCone_of_chart B S hS R.snd (pG ≫ Gq.snd) T.swap
      (Bicategory.isTwoFibreProduct_swap hTFP) chart hchartEt hTopB eChart,
    hPtopB⟩

end AlgebraicGeometry.Stack

end
