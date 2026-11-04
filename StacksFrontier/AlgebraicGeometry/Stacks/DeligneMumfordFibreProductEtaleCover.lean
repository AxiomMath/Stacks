module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedPermanence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Étale presentations of 2-fibre products along a Deligne–Mumford 1-morphism (Stacks 0CIA)

Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of algebraic stacks over `S`. **Stacks 0CIA**
says that for every Deligne–Mumford algebraic stack `𝒵` over `𝒴`, and in particular for every
algebraic space `Z` over `𝒴`, there is a scheme with a surjective étale 1-morphism onto
`𝒳 ×_𝒴 𝒵`. This file derives that, for every 2-fibre product of the cospan, from the substantial
direction of the structure theorem **Stacks 06N3**, and then derives from it the two diagram
statements the rest of the chapter takes from Stacks 0CIA.

Every statement here takes that direction of Stacks 06N3,
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, as the explicit argument
`hForward`, and none carries a `@[stacks]` attribute: they are the whole of the argument apart
from the structure theorem, so that a proof of the latter turns each into the statement of
record by a single application.

## Main results

* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isTwoFibreProduct_of_isDM_of_forward`:
  Stacks 0CIA, part (1), from `hForward`.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isTwoFibreProduct_algebraicSpace_of_forward`:
  Stacks 0CIA, part (2), from `hForward`.
* `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward`: a
  Deligne–Mumford 1-morphism admits a diagram of the shape condition (2) of **Stacks 0CIF** asks
  for.
* `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagramOver_of_isDM_of_forward`: for
  Deligne–Mumford `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵`, the nested diagrams the proofs of
  **Stacks 0CIH** and **0CIZ** choose: a smooth chart `W ⟶ 𝒵`, an étale chart `V ⟶ 𝒴 ×_𝒵 W` and
  an étale chart `U ⟶ 𝒳 ×_𝒴 V`.

## Implementation notes

The argument for Stacks 0CIA is the source's. The projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒵` is a base change of
`f`, hence Deligne–Mumford (**Stacks 050F**, at an arbitrary 2-fibre product through
`AlgebraicGeometry.Stack.isDM_baseChange_of_isTwoFibreProduct`), so the 2-fibre product is
Deligne–Mumford (**Stacks 050L**), and Stacks 06N3 gives the presentation. An algebraic space is
Deligne–Mumford (`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_algebraicSpaceStack`,
**Stacks 050E**), which reduces part (2) to part (1).

Deligne–Mumfordness is the absolute notion of **Stacks 050D**, part (5), read at the terminal
scheme, which every big fppf site contains (`AlgebraicGeometry.BigFppfSite.contains_terminal`);
so no hypothesis on the site occurs.

The single diagram is
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_etalePresentation` fed with a smooth
chart of `𝒴` and the presentation of part (2). For the nested one the outer rectangle over
`f ≫ g` is cut out by an étale chart of `𝒳 ×_𝒵 W`, obtained by pasting the two inner 2-fibre
products; both diagrams share the left vertical 1-morphism, which is the comparison of the inner
diagram with the pasted rectangle followed by its projection to `𝒳`.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
* [Stacks Project, Tag 0CIZ](https://stacks.math.columbia.edu/tag/0CIZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable
  (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)

include hForward

/-- **Stacks 0CIA, part (1), from the substantial direction of Stacks 06N3.** Let `f : 𝒳 ⟶ 𝒴`
be a Deligne–Mumford 1-morphism of algebraic stacks over `S` and `g : 𝒵 ⟶ 𝒴` a 1-morphism from a
Deligne–Mumford algebraic stack. Then every 2-fibre product `𝒳 ×_𝒴 𝒵` admits a scheme with a
surjective étale 1-morphism onto it.

Its projection to `𝒵` is Deligne–Mumford by Stacks 050F, so it is Deligne–Mumford by Stacks 050L,
and `hForward` gives the presentation. -/
theorem isDeligneMumfordStack_of_isTwoFibreProduct_of_isDM_of_forward
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsDM B S hS f)
    (h𝒵 : AlgebraicStacks.IsAbsolutelyDM B S hS B.contains_terminal 𝒵)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R) :
    IsDeligneMumfordStack.{u, w} B S hS R.pt.val.val :=
  hForward R.pt (AlgebraicStacks.isAbsolutelyDM_of_isDM B S hS B.contains_terminal R.snd h𝒵
    (isDM_baseChange_of_isTwoFibreProduct B S hS f g R hR hf))

/-- **Stacks 0CIA, part (2), from the substantial direction of Stacks 06N3.** Let `f : 𝒳 ⟶ 𝒴`
be a Deligne–Mumford 1-morphism of algebraic stacks over `S` and `g : Z ⟶ 𝒴` a 1-morphism from an
algebraic space. Then every 2-fibre product `𝒳 ×_𝒴 Z` admits a scheme with a surjective étale
1-morphism onto it.

This is part (1) at the algebraic space read as an algebraic stack, which is Deligne–Mumford by
Stacks 050E. -/
theorem isDeligneMumfordStack_of_isTwoFibreProduct_algebraicSpace_of_forward
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (g : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒴)
    (R : Bicategory.TwoCommSq f g) (hR : Bicategory.IsTwoFibreProduct R) :
    IsDeligneMumfordStack.{u, w} B S hS R.pt.val.val :=
  isDeligneMumfordStack_of_isTwoFibreProduct_of_isDM_of_forward B S hS hForward f g hf
    (AlgebraicStacks.isAbsolutelyDM_algebraicSpaceStack.{u, w} B S hS B.contains_terminal Z hZ)
    R hR

/-- **A Deligne–Mumford 1-morphism admits the diagram of condition (2) of Stacks 0CIF.** For
`f : 𝒳 ⟶ 𝒴` Deligne–Mumford there is a 2-commutative square of algebraic spaces over `f` with
smooth right-hand vertical 1-morphism, surjective left-hand vertical 1-morphism, and étale
comparison to every 2-fibre product of its cospan.

The right-hand vertical 1-morphism is a smooth chart `V ⟶ 𝒴`, surjective on objects, and the
square is cut out by the surjective étale presentation of `𝒳 ×_𝒴 V` of Stacks 0CIA, part (2),
which is where `hForward` is used. -/
theorem hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f) :
    HasSurjectiveEtaleSmoothDiagram B S hS f := by
  obtain ⟨V, hV, v, hvsm, hvsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒴.property
  let b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom v
  let Q := AlgebraicStacks.twoFibreProductSquare B S hS b f
  have hQ : Bicategory.IsTwoFibreProduct Q.swap := Bicategory.isTwoFibreProduct_swap
    (AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS b f)
  exact hasSurjectiveEtaleSmoothDiagram_of_etalePresentation B S hS f V hV b hvsm hvsu
    (exists_etalePresentation_of_isDeligneMumfordStack B S hS (𝒜 := Q.pt.val)
      (isDeligneMumfordStack_of_isTwoFibreProduct_algebraicSpace_of_forward B S hS hForward f hf
        V hV b Q.swap hQ))

/-- **An étale chart of a 2-fibre product of a Deligne–Mumford 1-morphism with an algebraic
space, with its top horizontal morphism.** For `f : 𝒳 ⟶ 𝒴` Deligne–Mumford and
`b : 𝒮_V ⟶ 𝒴` out of an algebraic space, the canonical 2-fibre product `𝒳 ×_{f, 𝒴, b} V` admits
an étale chart `cc` by an algebraic space, surjective on objects, whose composite with the
projection to `V` is induced by a morphism `h : U ⟶ V` of algebraic spaces (**Stacks 04SW**). -/
private theorem exists_etaleChart_of_isDM
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hU : IsAlgebraicSpace B S hS U)
      (cc : fibredCategory B S hS U ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt)
      (h : U ⟶ V)
      (_e : (associatedMap B S hS h).1 ≅
        cc ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).snd),
      IsRelativelyEtale B S hS cc ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt.val.p
        (CatFiberedInGroupoids.homFunctor cc) := by
  classical
  set J₀ : Bicategory.TwoCommSq f.hom b.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom with hJ₀def
  obtain ⟨Wsch, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS (𝒜 := J₀.pt)
      (isDeligneMumfordStack_of_isTwoFibreProduct_algebraicSpace_of_forward B S hS hForward f hf
        V hV b (twoFibreProductSquareAlgebraicStacks B S hS f b)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f b))
  have hU : IsAlgebraicSpace B S hS (yoneda.obj Wsch) := isAlgebraicSpace_yoneda B S hS Wsch
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver Wsch
  let aInv : fibredCategory B S hS (yoneda.obj Wsch) ⟶ schemeFibredCategory B S hS Wsch :=
    equivalenceOverInvMap B S hS (yoneda.obj Wsch) eU
  have haInvEquiv : Functor.IsEquivalence aInv.hom.toFunctor := by
    show Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  let cc : fibredCategory B S hS (yoneda.obj Wsch) ⟶ J₀.pt := aInv ≫ pres
  have hccet : IsRelativelyEtale B S hS cc :=
    isRelativelyEtale_of_isEquivalence_comp B S hS aInv pres haInvEquiv hpreset
  have hccsu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (yoneda.obj Wsch)).val.p J₀.pt.val.p
      (CatFiberedInGroupoids.homFunctor cc) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj Wsch)).val.p
      (schemeFibredCategory B S hS Wsch).val.p J₀.pt.val.p
      (CatFiberedInGroupoids.homFunctor aInv) (CatFiberedInGroupoids.homFunctor pres)
      (CatFiberedInGroupoids.homFunctor_comp_p pres)
      (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS Wsch)
        B S hS (yoneda.obj Wsch) eU)
      hpressu
  set h := representingMap B S hS (fibredCategory B S hS (yoneda.obj Wsch))
    (fibredCategory B S hS V) (yoneda.obj Wsch) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ J₀.snd) with hhdef
  obtain ⟨e₀, he₀, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS (yoneda.obj Wsch)) (fibredCategory B S hS V) (yoneda.obj Wsch) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS (yoneda.obj Wsch) V h)
  exact ⟨yoneda.obj Wsch, hU, cc, h,
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e₀ he₀), hccet, hccsu⟩

/-- **Nested étale-smooth diagrams over two Deligne–Mumford 1-morphisms.** For Deligne–Mumford
`f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` there are a diagram over `f` and a diagram over `f ≫ g` of the shape
condition (2) of Stacks 0CIF asks for, sharing their left vertical 1-morphism, whose top
horizontal morphisms are `h : U ⟶ V` and `h ≫ k : U ⟶ W`.

These are the choices of the proofs of Stacks 0CIH and 0CIZ: a smooth chart `W ⟶ 𝒵` surjective on
objects, an étale chart `V ⟶ 𝒴 ×_𝒵 W` and an étale chart `U ⟶ 𝒳 ×_𝒴 V`, the last two from
Stacks 0CIA, part (2). The outer rectangle is cut out by an étale chart of `𝒳 ×_𝒵 W`, obtained by
pasting the two inner 2-fibre products. -/
theorem hasSurjectiveEtaleSmoothDiagramOver_of_isDM_of_forward
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsDM B S hS f) (hg : IsDM B S hS g) :
    HasSurjectiveEtaleSmoothDiagramOver.{u, w} B S hS f g := by
  classical
  -- a smooth chart of `𝒵`, surjective on objects, by an algebraic space
  obtain ⟨W, hW, w₀, hwsm, hwsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  let wS : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom w₀
  -- the étale chart of `𝒴 ×_𝒵 W`
  obtain ⟨V₁, hV₁, cc₁, h₁, e₁, hcc₁et, hcc₁su⟩ :=
    exists_etaleChart_of_isDM B S hS hForward g hg W hW wS
  let Jg : Bicategory.TwoCommSq g.hom wS.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom wS.hom
  have hJg : Bicategory.IsTwoFibreProduct Jg :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom wS.hom
  let b₁ : fibredCategory B S hS V₁ ⟶ 𝒴.val := cc₁ ≫ Jg.fst
  let b₁S : algebraicSpaceStack.{u, w} B S hS V₁ hV₁ ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom b₁
  have hJgfstsm : IsRelativelySmooth B S hS Jg.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ wS.hom g.hom Jg hJg hwsm
  have hb₁sm : IsRelativelySmooth B S hS b₁ :=
    isRelativelySmooth_comp B S hS cc₁ Jg.fst
      (isRelativelySmooth_of_isRelativelyEtale B S hS cc₁ hcc₁et) hJgfstsm
  -- a surjective chart of the 2-fibre product composed with its projection, surjective on objects
  have hcomp : ∀ {𝒰 𝒳' 𝒴' 𝒵' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
      (p : 𝒳' ⟶ 𝒴') (q : 𝒵' ⟶ 𝒴') (R : Bicategory.TwoCommSq q p)
      (hR : Bicategory.IsTwoFibreProduct R) (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
      (c : 𝒰 ⟶ R.pt),
      IsSurjectiveOnObjects B S hS 𝒰.val.p R.pt.val.p (CatFiberedInGroupoids.homFunctor c) →
      IsSurjectiveOnObjects B S hS 𝒳'.val.p 𝒴'.val.p (CatFiberedInGroupoids.homFunctor p) →
      IsSurjectiveOnObjects B S hS 𝒰.val.p 𝒵'.val.p
        (CatFiberedInGroupoids.homFunctor (c ≫ R.fst)) :=
    fun p q R hR hp c hc hsu =>
      isSurjectiveOnObjects_comp B S hS _ R.pt.val.p _ (CatFiberedInGroupoids.homFunctor c)
        (CatFiberedInGroupoids.homFunctor R.fst) (CatFiberedInGroupoids.homFunctor_comp_p R.fst) hc
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS R.fst
            (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ p q R hR hp)).2
          (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
            (Space.surjectiveMorphismProperty B S hS) _ _ _ p q R hR hp
            ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS p
              hp).1 hsu)))
  have hb₁su := hcomp wS.hom g.hom Jg hJg hwsm.1 cc₁ hcc₁su hwsu
  -- the étale chart of `𝒳 ×_𝒴 V₁`
  obtain ⟨U₁, hU₁, cc₂, h₂, e₂, hcc₂et, hcc₂su⟩ :=
    exists_etaleChart_of_isDM B S hS hForward f hf V₁ hV₁ b₁S
  let Jf : Bicategory.TwoCommSq f.hom b₁ :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  have hJf : Bicategory.IsTwoFibreProduct Jf :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  have hJfswap : Bicategory.IsTwoFibreProduct Jf.swap := Bicategory.isTwoFibreProduct_swap hJf
  let a₂ : fibredCategory B S hS U₁ ⟶ 𝒳.val := cc₂ ≫ Jf.fst
  -- the pasted rectangles: `Jg.swap.paste T` over `(wS, f ≫ g)` and `T.pasteFst outer` over
  -- `(b₁, f)`
  let T : Bicategory.TwoCommSq Jg.fst f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Jg.fst f.hom
  have hT' : Bicategory.IsTwoFibreProduct T :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Jg.fst f.hom
  let Kout : Bicategory.TwoCommSq wS.hom (f.hom ≫ g.hom) := Jg.swap.paste T
  have hKout : Bicategory.IsTwoFibreProduct Kout :=
    Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hJg) hT'
  let outer : Bicategory.TwoCommSq cc₁ T.fst :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} cc₁ T.fst
  have houter : Bicategory.IsTwoFibreProduct outer :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cc₁ T.fst
  have hpaste : Bicategory.IsTwoFibreProduct (T.pasteFst outer) :=
    Bicategory.isTwoFibreProduct_pasteFst T hT' outer houter
  -- the comparison of the chart's diagram over `f` with the inner rectangle, which is étale
  let k₂ : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS f.hom a₂ b₁ h₂
        (Bicategory.whiskerRightIso e₂ b₁ ≪≫ Bicategory.whiskerLeftIso cc₂ Jf.swap.iso))
      (T.pasteFst outer) :=
    Bicategory.twoFibreProductPreHom hpaste _
  have hk₂et : IsRelativelyEtale B S hS k₂.hom :=
    isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b₁ Jf.swap hJfswap cc₂ hcc₂et
      h₂ e₂ (T.pasteFst outer) hpaste k₂
  have houtersndet : IsRelativelyEtale B S hS outer.snd :=
    isRelativelyEtale_baseChange B S hS _ _ _ cc₁ T.fst outer.swap
      (Bicategory.isTwoFibreProduct_swap houter) hcc₁et
  let ccOut : fibredCategory B S hS U₁ ⟶ Kout.pt := k₂.hom ≫ outer.snd
  have hccOutet : IsRelativelyEtale B S hS ccOut :=
    isRelativelyEtale_comp B S hS k₂.hom outer.snd hk₂et houtersndet
  -- the top horizontal morphism of the outer rectangle is `h₂ ≫ h₁`
  let eOut : (associatedMap B S hS (h₂ ≫ h₁)).1 ≅ ccOut ≫ Kout.fst :=
    eqToIso (associatedMap_comp B S hS h₂ h₁) ≪≫
      Bicategory.whiskerLeftIso (associatedMap B S hS h₂).1 e₁ ≪≫
      Bicategory.whiskerRightIso k₂.isoFst (cc₁ ≫ Jg.snd) ≪≫
      Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso k₂.hom outer.iso) Jg.snd
  let aOut : algebraicSpaceStack.{u, w} B S hS U₁ hU₁ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (k₂.hom ≫ (T.pasteFst outer).snd)
  refine ⟨U₁, V₁, W, hU₁, hV₁, hW, aOut, b₁S, wS, h₂, h₁,
    Bicategory.whiskerRightIso k₂.isoFst b₁ ≪≫
      Bicategory.whiskerLeftIso k₂.hom (T.pasteFst outer).iso,
    Bicategory.whiskerRightIso eOut wS.hom ≪≫ Bicategory.whiskerLeftIso ccOut Kout.iso,
    ?_, hb₁sm, hwsm,
    (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b₁
      (T.pasteFst outer) hpaste k₂.hom hk₂et h₂ k₂.isoFst Q hQ k),
    (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS (f.hom ≫ g.hom) wS.hom
      Kout hKout ccOut hccOutet (h₂ ≫ h₁) eOut Q hQ k)⟩
  -- surjectivity of the left vertical 1-morphism, transported along `k₂`
  let a₂S : algebraicSpaceStack.{u, w} B S hS U₁ hU₁ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom a₂
  have hsu := hcomp b₁ f.hom Jf hJf hb₁sm.1 cc₂ hcc₂su hb₁su
  have hpt : AlgebraicStacks.pointsMap B S hS a₂S = AlgebraicStacks.pointsMap B S hS aOut :=
    AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (Bicategory.InducedBicategory.isoMk (f := a₂S) (g := aOut) k₂.isoSnd).hom
  show Function.Surjective (AlgebraicStacks.pointsMap B S hS aOut)
  rw [← hpt]
  exact pointsMap_surjective_of_isSurjectiveOnObjects B S hS a₂S hsu

end AlgebraicGeometry.Stack

end
