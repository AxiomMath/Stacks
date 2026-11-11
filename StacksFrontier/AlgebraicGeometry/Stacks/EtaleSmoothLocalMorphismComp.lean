module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Composition of an étale-smooth local property of 1-morphisms of algebraic stacks (Stacks 0CIH)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target (**Stacks 0CFZ**) and stable under composition. **Stacks 0CIH** asserts
that the property of Deligne–Mumford 1-morphisms of algebraic stacks which **Stacks 0CIG**
attaches to `P` is stable under composition.

The proof is the source's. The composite is Deligne–Mumford by **Stacks 050K**. Choose a smooth
presentation `W ⟶ 𝒵`, surjective on objects, by an algebraic space; an étale chart
`V ⟶ 𝒴 ×_𝒵 W` of the 2-fibre product, which **Stacks 0CIA** provides; and then an étale chart
`U ⟶ 𝒳 ×_𝒴 V`. The morphisms `V ⟶ W` and `U ⟶ V` have `P`, hence so does `U ⟶ W`, and the
outer rectangle `U ⟶ W` over `f ≫ g` is a diagram of condition (2) of **Stacks 0CIF** because
its apex is an étale chart of `𝒳 ×_𝒵 W`, obtained by pasting the two inner 2-fibre products.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_preHom_diagramCone_of_chart`: the comparison
  1-morphisms of a diagram of Stacks 06FM cut out by an étale chart of a 2-fibre product are
  étale.
* `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp`: the argument of **Stacks 0CIH**,
  over the forward direction of Stacks 06N3 as the argument `hForward`; **Stacks 0CIH** itself is
  `AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal`.

## Implementation notes

The étale clause of condition (2) of Stacks 0CIF — every comparison 1-morphism from the
diagram's cone to every 2-fibre product of the cospan is étale — is what makes the source's
choices matter. It is discharged for all three diagrams by
`isRelativelyEtale_preHom_diagramCone_of_chart`, the étale reading of
`AlgebraicGeometry.Stack.isRelativelySmooth_preHom_diagramCone_of_chart`: a diagram whose apex is
an étale chart `cc` of a chosen 2-fibre product has `cc` itself as a comparison, and
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_preHom` moves that to every other product
and every other comparison. So each diagram is produced together with the chart that cuts it out,
which is why the charts rather than the diagrams are what the construction below carries.

For the outer diagram the chart is built by pasting. With `Jg` the 2-fibre product `𝒴 ×_𝒵 W`,
`T` the 2-fibre product `Jg ×_𝒴 𝒳` and `outer` the 2-fibre product of `cc₁` and `T.fst`, the
rectangle `Jg.paste T` is a 2-fibre product of `(W ⟶ 𝒵, f ≫ g)` by **Stacks 003Q**, the
rectangle `T.pasteFst outer` is one of `(V ⟶ 𝒴, f)`, and the comparison of the second diagram
with the latter, followed by the projection of `outer`, is an étale chart of the former.

The 2-fibre products of Stacks 0CIA are taken in the orientation `𝒳 ×_𝒴 V` in which
**Stacks 0CIA** states them, and read over the reversed cospan by
`CategoryTheory.Bicategory.TwoCommSq.swap`, which keeps the apex on the nose; so the
Deligne–Mumford condition Stacks 0CIA supplies needs no transport.

The forward direction of **Stacks 06N3** is the argument `hForward`, as in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation`; it enters only through
Stacks 0CIA, and `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` proves it.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIG](https://stacks.math.columbia.edu/tag/0CIG)
* [Stacks Project, Tag 0CIH](https://stacks.math.columbia.edu/tag/0CIH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism between categories of elements of presheaves is 2-isomorphic to the
1-morphism attached to a morphism of those presheaves.** The morphism is the one **Stacks 04SW**
reads off, and the 2-isomorphism is the uniqueness clause of that tag through
`AlgebraicGeometry.Stack.representingMap_associatedMap`. -/
private theorem exists_associatedMap_twoIso
    (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (k : fibredCategory B S hS U ⟶ fibredCategory B S hS V) :
    ∃ h : U ⟶ V, Nonempty ((associatedMap B S hS h).1 ≅ k) := by
  classical
  refine ⟨representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) k, ?_⟩
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS U) (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS U V
      (representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) k))
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)⟩

/-- **The projection of a 2-fibre product away from a relatively representable 1-morphism that is
surjective on objects is again surjective on objects.** -/
private theorem isSurjectiveOnObjects_fst_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsu : IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)) :
    IsSurjectiveOnObjects B S hS R.pt.val.p 𝒵.val.p (CatFiberedInGroupoids.homFunctor R.fst) :=
  (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS R.fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f g R hR hf)).2
    (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) _ _ _ f g R hR hf
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS f hf).1 hsu))

/-- **The étale chart of a 2-fibre product over a prescribed smooth chart of the target, with
its diagram.** Let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism passing the universal
étale-smooth diagram test at `P`, and let `b : 𝒮_V ⟶ 𝒴` be a smooth 1-morphism out of an
algebraic space. Then the canonical 2-fibre product `𝒳 ×_{f, 𝒴, b} V` admits an étale chart `cc`
by an algebraic space, surjective on objects, whose composite with the projection to `V` is
induced by a morphism `h : U ⟶ V` of algebraic spaces having `P`. -/
private theorem exists_etaleChart_diagram
    (hT : B.Contains (⊤_ Scheme.{u}))
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : HasEtaleSmoothLocalProperty B S hS P f)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (hbsm : IsRelativelySmooth B S hS b.hom) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (cc : fibredCategory B S hS U ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt)
      (h : U ⟶ V)
      (_e : (associatedMap B S hS h).1 ≅
        cc ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).snd),
      IsRelativelyEtale B S hS cc ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt.val.p
        (CatFiberedInGroupoids.homFunctor cc) ∧
      P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) := by
  classical
  set J₀ : Bicategory.TwoCommSq f.hom b.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom with hJ₀def
  have hJ₀ : Bicategory.IsTwoFibreProduct J₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom b.hom
  have hJ : Bicategory.IsTwoFibreProduct J₀.swap := Bicategory.isTwoFibreProduct_swap hJ₀
  -- Stacks 0CIA, part (2): the apex is a Deligne–Mumford algebraic stack, so it has a
  -- surjective étale presentation by a scheme of the site
  have hDM : IsDeligneMumfordStack.{u, w} B S hS J₀.pt.val :=
    AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w} B S hS hT
      hForward f hf.1 V hV b
  obtain ⟨Wsch, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS hDM
  -- read the presentation from the algebraic space `yoneda.obj Wsch`
  have hU : IsAlgebraicSpace B S hS (yoneda.obj Wsch) := isAlgebraicSpace_yoneda B S hS Wsch
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver Wsch
  let aInv : fibredCategory B S hS (yoneda.obj Wsch) ⟶ schemeFibredCategory B S hS Wsch :=
    equivalenceOverInvMap B S hS (yoneda.obj Wsch) eU
  have haInvEquiv : Functor.IsEquivalence aInv.hom.toFunctor := by
    change Functor.IsEquivalence eU.inv.functor
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
  -- the top horizontal morphism of the diagram, from Stacks 04SW
  obtain ⟨h, ⟨e⟩⟩ := exists_associatedMap_twoIso B S hS (yoneda.obj Wsch) V (cc ≫ J₀.snd)
  refine ⟨yoneda.obj Wsch, hU, cc, h, e, hccet, hccsu, ?_⟩
  exact hf.2 (yoneda.obj Wsch) V hU hV
    (Bicategory.InducedBicategory.mkHom (cc ≫ J₀.fst)) b h
    (Bicategory.whiskerRightIso e b.hom ≪≫ Bicategory.whiskerLeftIso cc J₀.swap.iso) hbsm
    (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b.hom
      J₀.swap hJ cc hccet h e Q hQ k)

/-- **Stacks 0CIH.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
étale-smooth local on the source-and-target and stable under composition. Then the property of
Deligne–Mumford 1-morphisms of algebraic stacks over `S` which **Stacks 0CIG** induces from `P`
is stable under composition.

The composite is Deligne–Mumford by **Stacks 050K**. For the diagram test, take a smooth chart
`W ⟶ 𝒵` surjective on objects, an étale chart `V ⟶ 𝒴 ×_𝒵 W` and an étale chart `U ⟶ 𝒳 ×_𝒴 V`,
the last two by **Stacks 0CIA**; the morphisms `V ⟶ W` and `U ⟶ V` have `P`, hence so does
`U ⟶ W`, and pasting the two 2-fibre products exhibits `U` as an étale chart of `𝒳 ×_𝒵 W`.

The forward direction of **Stacks 06N3** enters as the argument `hForward`, through Stacks 0CIA;
it is discharged by `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` in
`AlgebraicGeometry.Stack.hasEtaleSmoothLocalProperty_comp_of_isEtaleSmoothLocal`. -/
theorem hasEtaleSmoothLocalProperty_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hcomp : ∀ {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z), P p → P q → P (p ≫ q))
    (hT : B.Contains (⊤_ Scheme.{u}))
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hT)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasEtaleSmoothLocalProperty B S hS P f)
    (hg : HasEtaleSmoothLocalProperty B S hS P g) :
    HasEtaleSmoothLocalProperty B S hS P (f ≫ g) := by
  classical
  refine ⟨AlgebraicStacks.isDM_comp B S hS f g hf.1 hg.1,
    hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS P hP
      (f ≫ g) ?_⟩
  -- a smooth chart of `𝒵`, surjective on objects, by an algebraic space
  obtain ⟨W, hW, w₀, hwsm, hwsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  let wS : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom w₀
  -- the chart of `𝒴 ×_𝒵 W` and its diagram over `g`
  obtain ⟨V₁, hV₁, cc₁, h₁, e₁, hcc₁et, hcc₁su, hP₁⟩ :=
    exists_etaleChart_diagram B S hS hT hForward P g hg W hW wS hwsm
  let Jg : Bicategory.TwoCommSq g.hom wS.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom wS.hom
  have hJg : Bicategory.IsTwoFibreProduct Jg :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom wS.hom
  -- the left vertical 1-morphism of that diagram, smooth and surjective on objects
  let b₁ : fibredCategory B S hS V₁ ⟶ 𝒴.val := cc₁ ≫ Jg.fst
  let b₁S : algebraicSpaceStack.{u, w} B S hS V₁ hV₁ ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom b₁
  have hJgfstsm : IsRelativelySmooth B S hS Jg.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ wS.hom g.hom Jg hJg hwsm
  have hb₁sm : IsRelativelySmooth B S hS b₁ :=
    isRelativelySmooth_comp B S hS cc₁ Jg.fst
      (isRelativelySmooth_of_isRelativelyEtale B S hS cc₁ hcc₁et) hJgfstsm
  have hJgfstsu : IsSurjectiveOnObjects B S hS Jg.pt.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor Jg.fst) :=
    isSurjectiveOnObjects_fst_of_isTwoFibreProduct B S hS wS.hom g.hom Jg hJg hwsm.1 hwsu
  have hb₁su : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V₁).val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor b₁) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS V₁).val.p Jg.pt.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor cc₁) (CatFiberedInGroupoids.homFunctor Jg.fst)
      (CatFiberedInGroupoids.homFunctor_comp_p Jg.fst) hcc₁su hJgfstsu
  -- the chart of `𝒳 ×_𝒴 V₁` and its diagram over `f`
  obtain ⟨U₁, hU₁, cc₂, h₂, e₂, hcc₂et, hcc₂su, hP₂⟩ :=
    exists_etaleChart_diagram B S hS hT hForward P f hf V₁ hV₁ b₁S hb₁sm
  let Jf : Bicategory.TwoCommSq f.hom b₁ :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  have hJf : Bicategory.IsTwoFibreProduct Jf :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  have hJfswap : Bicategory.IsTwoFibreProduct Jf.swap := Bicategory.isTwoFibreProduct_swap hJf
  let a₂ : fibredCategory B S hS U₁ ⟶ 𝒳.val := cc₂ ≫ Jf.fst
  -- the pasted rectangles: `Jg.paste T` over `(wS, f ≫ g)` and `T.pasteFst outer` over `(b₁, f)`
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
  -- the comparison of the diagram over `f` with the inner rectangle, which is étale
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
  have hPout : P ((ObjectProperty.homMk h₂ :
        (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V₁, hV₁⟩) ≫
      (ObjectProperty.homMk h₁ : (⟨V₁, hV₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)) :=
    hcomp _ _ hP₂ hP₁
  let a₂S : algebraicSpaceStack.{u, w} B S hS U₁ hU₁ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom a₂
  let aOut : algebraicSpaceStack.{u, w} B S hS U₁ hU₁ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (ccOut ≫ Kout.snd)
  refine ⟨U₁, W, hU₁, hW, aOut, wS,
    h₂ ≫ h₁, Bicategory.whiskerRightIso eOut wS.hom ≪≫ Bicategory.whiskerLeftIso ccOut Kout.iso,
    ?_, hwsm,
    (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS (f.hom ≫ g.hom) wS.hom
      Kout hKout ccOut hccOutet (h₂ ≫ h₁) eOut Q hQ k),
    hPout⟩
  -- surjectivity of the left vertical 1-morphism, transported along `k₂`
  have hsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U₁).val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor a₂) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U₁).val.p Jf.pt.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor cc₂) (CatFiberedInGroupoids.homFunctor Jf.fst)
      (CatFiberedInGroupoids.homFunctor_comp_p Jf.fst) hcc₂su
      (isSurjectiveOnObjects_fst_of_isTwoFibreProduct B S hS b₁ f.hom Jf hJf hb₁sm.1 hb₁su)
  have hpt : AlgebraicStacks.pointsMap B S hS a₂S = AlgebraicStacks.pointsMap B S hS aOut :=
    AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (Bicategory.InducedBicategory.isoMk (f := a₂S) (g := aOut) k₂.isoSnd).hom
  change Function.Surjective (AlgebraicStacks.pointsMap B S hS aOut)
  rw [← hpt]
  exact pointsMap_surjective_of_isSurjectiveOnObjects B S hS a₂S hsu

end AlgebraicGeometry.Stack

end
