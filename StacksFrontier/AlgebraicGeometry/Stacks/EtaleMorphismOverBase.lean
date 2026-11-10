module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# A morphism between two stacks étale over a base is étale (Stacks 0CIR)

Let `𝒳` and `𝒴` be algebraic stacks étale over an algebraic stack `𝒵`, with structure
1-morphisms `p : 𝒳 ⟶ 𝒵` and `q : 𝒴 ⟶ 𝒵`, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism over `𝒵`, i.e.
with a 2-isomorphism `η : p ≅ f ≫ q`. **Stacks 0CIR** says that `f` is étale in the sense of
**Stacks 0CIL**.

The proof is the source's. `f` is Deligne–Mumford by **Stacks 050M**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_isEtale_over_base`). Choose a smooth chart
`W ⟶ 𝒵`, surjective on objects, by an algebraic space; an étale chart `V₁ ⟶ 𝒴 ×_𝒵 W`; and an
étale chart `U₁ ⟶ 𝒳 ×_𝒴 V₁`, the last two by **Stacks 0CIA**. Then `V₁ ⟶ W` is étale because `q`
is, and `U₁ ⟶ W` is étale because `p` is: pasting the two 2-fibre products exhibits `U₁` as an
étale chart of `𝒳 ×_𝒵 W`, read over `p` through `η`. So `U₁ ⟶ V₁` is étale by the version for
algebraic spaces, **Stacks 05W3**, and the diagram `U₁ ⟶ V₁` over `f` is one of condition (2) of
**Stacks 0CIF**, which gives the universal test of Stacks 0CIL.

## Main results

* `AlgebraicGeometry.Stack.exists_etaleChart_of_isDeligneMumfordStack_twoFibreProduct`: an
  étale chart of a 2-fibre product with an algebraic space, surjective on objects, read off a
  Deligne–Mumford apex together with the morphism of algebraic spaces it cuts out.
* `AlgebraicGeometry.Stack.isEtale_of_isEtale_over_base_of_isDeligneMumfordStack_twoFibreProduct`:
  the argument of Stacks 0CIR, from the existence form of Stacks 0CIA, part (2).

## Implementation notes

The étale charts are the only input the argument takes beyond the library: the hypothesis
`hchart` is the conclusion of **Stacks 0CIA**, part (2), in its existence form (the apex of the
canonical 2-fibre product of a Deligne–Mumford 1-morphism with an algebraic space is a
Deligne–Mumford stack in the sense of Stacks 03YO), stated exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace`
concludes it.

The source works with `𝒳` over `𝒵` through `f`; the structure 1-morphism `p` of `𝒳` agrees with
`f ≫ q` only up to the 2-isomorphism `η`, and the outer rectangle, a 2-fibre product of
`(W ⟶ 𝒵, f ≫ q)`, is moved to the cospan `(W ⟶ 𝒵, p)` by
`CategoryTheory.Bicategory.TwoCommSq.reindexSnd`, which keeps its apex and projections.

## References

* [Stacks Project, Tag 03YO](https://stacks.math.columbia.edu/tag/03YO)
* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 05W3](https://stacks.math.columbia.edu/tag/05W3)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIR](https://stacks.math.columbia.edu/tag/0CIR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale chart of a 2-fibre product with an algebraic space, from a Deligne–Mumford apex.**
Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids and `b : 𝒮_V ⟶ 𝒴` a
1-morphism out of the category fibred in groupoids of a presheaf `V`. If the apex of the
canonical 2-fibre product `𝒳 ×_{f, 𝒴, b} V` is a Deligne–Mumford stack (Stacks 03YO), it has a
relatively étale chart `cc` by an algebraic space `U`, surjective on objects, and the composite
of `cc` with the projection to `V` is 2-isomorphic to the 1-morphism attached to a morphism
`h : U ⟶ V` of presheaves (**Stacks 04SW**). -/
theorem exists_etaleChart_of_isDeligneMumfordStack_twoFibreProduct
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (b : fibredCategory B S hS V ⟶ 𝒴)
    (hDM : IsDeligneMumfordStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b).pt.val) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hU : IsAlgebraicSpace B S hS U)
      (cc : fibredCategory B S hS U ⟶
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b).pt)
      (h : U ⟶ V)
      (_e : (associatedMap B S hS h).1 ≅
        cc ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b).snd),
      IsRelativelyEtale B S hS cc ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b).pt.val.p
        (CatFiberedInGroupoids.homFunctor cc) := by
  set J₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b
  obtain ⟨Wsch, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS hDM
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver Wsch
  let aInv : fibredCategory B S hS (yoneda.obj Wsch) ⟶ schemeFibredCategory B S hS Wsch :=
    equivalenceOverInvMap B S hS (yoneda.obj Wsch) eU
  have haInvEquiv : Functor.IsEquivalence aInv.hom.toFunctor := by
    change Functor.IsEquivalence eU.inv.functor
    exact eU.toEquivalence.symm.isEquivalence_functor
  let cc : fibredCategory B S hS (yoneda.obj Wsch) ⟶ J₀.pt := aInv ≫ pres
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
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ J₀.snd)
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS (yoneda.obj Wsch)) (fibredCategory B S hS V) (yoneda.obj Wsch) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS (yoneda.obj Wsch) V h)
  exact ⟨yoneda.obj Wsch, isAlgebraicSpace_yoneda B S hS Wsch, cc, h,
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee),
    isRelativelyEtale_of_isEquivalence_comp B S hS aInv pres haInvEquiv hpreset, hccsu⟩

/-- A chart `cc` of the apex of a 2-fibre product, surjective on objects, composed with the
projection of the base change of a surjective-on-objects `g` representable by algebraic spaces,
is surjective on objects. -/
private theorem isSurjectiveOnObjects_comp_fst_twoFibreProduct
    {𝒰 𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (J : Bicategory.TwoCommSq g f) (hJ : Bicategory.IsTwoFibreProduct J)
    (cc : 𝒰 ⟶ J.pt)
    (hcc : IsSurjectiveOnObjects B S hS 𝒰.val.p J.pt.val.p (CatFiberedInGroupoids.homFunctor cc))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsu : IsSurjectiveOnObjects B S hS 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor f)) :
    IsSurjectiveOnObjects B S hS 𝒰.val.p 𝒵.val.p
      (CatFiberedInGroupoids.homFunctor (cc ≫ J.fst)) :=
  isSurjectiveOnObjects_comp B S hS 𝒰.val.p J.pt.val.p 𝒵.val.p
    (CatFiberedInGroupoids.homFunctor cc) (CatFiberedInGroupoids.homFunctor J.fst)
    (CatFiberedInGroupoids.homFunctor_comp_p J.fst) hcc
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS J.fst
        (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ f g J hJ hf)).2
      (hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) _ _ _ f g J hJ hf
        ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS f
          hf).1 hsu)))

/-- **Stacks 0CIR, from the existence form of Stacks 0CIA, part (2).** Let `p : 𝒳 ⟶ 𝒵` and
`q : 𝒴 ⟶ 𝒵` be étale 1-morphisms of algebraic stacks and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism over
`𝒵`, i.e. with a 2-isomorphism `η : p ≅ f ≫ q`. If the apex of the canonical 2-fibre product of
every Deligne–Mumford 1-morphism with a 1-morphism out of an algebraic space is a
Deligne–Mumford stack, then `f` is étale. -/
theorem isEtale_of_isEtale_over_base_of_isDeligneMumfordStack_twoFibreProduct
    (hchart : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴), IsDM B S hS f →
      ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
        (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴),
        IsDeligneMumfordStack.{u, w} B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).pt.val)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (p : 𝒳 ⟶ 𝒵) (q : 𝒴 ⟶ 𝒵) (η : p ≅ f ≫ q)
    (hp : IsEtale B S hS p) (hq : IsEtale B S hS q) : IsEtale B S hS f := by
  have hfDM : IsDM B S hS f := AlgebraicStacks.isDM_of_isEtale_over_base B S hS f p q η hp
  refine ⟨hfDM, hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
    B S hS _ (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) f ?_⟩
  -- a smooth chart of `𝒵`, surjective on objects, by an algebraic space
  obtain ⟨W, hW, w₀, hwsm, hwsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒵.property
  let wS : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom w₀
  -- the étale chart of `𝒴 ×_𝒵 W`, and the étale morphism `V₁ ⟶ W` it cuts out
  let Jq : Bicategory.TwoCommSq q.hom wS.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} q.hom wS.hom
  have hJq : Bicategory.IsTwoFibreProduct Jq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      q.hom wS.hom
  obtain ⟨V₁, hV₁, cc₁, h₁, e₁, hcc₁et, hcc₁su⟩ :=
    exists_etaleChart_of_isDeligneMumfordStack_twoFibreProduct.{u, w} B S hS q.hom W wS.hom
      (hchart q hq.1 W hW wS)
  have hh₁ : Space.IsEtale B S hS
      (ObjectProperty.homMk h₁ : (⟨V₁, hV₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩).hom :=
    hq.2 V₁ W hV₁ hW (Bicategory.InducedBicategory.mkHom (cc₁ ≫ Jq.fst)) wS h₁
      (Bicategory.whiskerRightIso e₁ wS.hom ≪≫ Bicategory.whiskerLeftIso cc₁ Jq.swap.iso) hwsm
      (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS q.hom wS.hom
        Jq.swap (Bicategory.isTwoFibreProduct_swap hJq) cc₁ hcc₁et h₁ e₁ Q hQ k)
  -- the right vertical 1-morphism of the diagram over `f`, smooth and surjective on objects
  let b₁ : fibredCategory B S hS V₁ ⟶ 𝒴.val := cc₁ ≫ Jq.fst
  let b₁S : algebraicSpaceStack.{u, w} B S hS V₁ hV₁ ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom b₁
  have hJqfstsm : IsRelativelySmooth B S hS Jq.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ wS.hom q.hom Jq hJq hwsm
  have hb₁sm : IsRelativelySmooth B S hS b₁ :=
    isRelativelySmooth_comp B S hS cc₁ Jq.fst
      (isRelativelySmooth_of_isRelativelyEtale B S hS cc₁ hcc₁et) hJqfstsm
  have hb₁su : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V₁).val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor b₁) :=
    isSurjectiveOnObjects_comp_fst_twoFibreProduct B S hS wS.hom q.hom Jq hJq cc₁ hcc₁su
      hwsm.1 hwsu
  -- the étale chart of `𝒳 ×_𝒴 V₁`, and the morphism `U₁ ⟶ V₁` it cuts out
  obtain ⟨U₁, hU₁, cc₂, h₂, e₂, hcc₂et, hcc₂su⟩ :=
    exists_etaleChart_of_isDeligneMumfordStack_twoFibreProduct.{u, w} B S hS f.hom V₁ b₁
      (hchart f hfDM V₁ hV₁ b₁S)
  let Jf : Bicategory.TwoCommSq f.hom b₁ :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  have hJf : Bicategory.IsTwoFibreProduct Jf :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b₁
  let a₂ : fibredCategory B S hS U₁ ⟶ 𝒳.val := cc₂ ≫ Jf.fst
  -- the pasted rectangles: `Jq.swap.paste T` over `(wS, f ≫ q)` and `T.pasteFst outer`
  -- over `(b₁, f)`
  let T : Bicategory.TwoCommSq Jq.fst f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Jq.fst f.hom
  have hT : Bicategory.IsTwoFibreProduct T :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Jq.fst f.hom
  let Kout : Bicategory.TwoCommSq wS.hom (f.hom ≫ q.hom) := Jq.swap.paste T
  let outer : Bicategory.TwoCommSq cc₁ T.fst :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} cc₁ T.fst
  have houter : Bicategory.IsTwoFibreProduct outer :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cc₁ T.fst
  have hpaste : Bicategory.IsTwoFibreProduct (T.pasteFst outer) :=
    Bicategory.isTwoFibreProduct_pasteFst T hT outer houter
  -- the comparison of the diagram over `f` with the inner rectangle, which is étale
  let k₂ : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS f.hom a₂ b₁ h₂
        (Bicategory.whiskerRightIso e₂ b₁ ≪≫ Bicategory.whiskerLeftIso cc₂ Jf.swap.iso))
      (T.pasteFst outer) :=
    Bicategory.twoFibreProductPreHom hpaste _
  let ccOut : fibredCategory B S hS U₁ ⟶ Kout.pt := k₂.hom ≫ outer.snd
  have hccOutet : IsRelativelyEtale B S hS ccOut :=
    isRelativelyEtale_comp B S hS k₂.hom outer.snd
      (isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b₁ Jf.swap
        (Bicategory.isTwoFibreProduct_swap hJf) cc₂ hcc₂et h₂ e₂ (T.pasteFst outer) hpaste k₂)
      (isRelativelyEtale_baseChange B S hS _ _ _ cc₁ T.fst outer.swap
        (Bicategory.isTwoFibreProduct_swap houter) hcc₁et)
  -- the top horizontal morphism of the outer rectangle is `h₂ ≫ h₁`
  let eOut : (associatedMap B S hS (h₂ ≫ h₁)).1 ≅ ccOut ≫ Kout.fst :=
    eqToIso (associatedMap_comp B S hS h₂ h₁) ≪≫
      Bicategory.whiskerLeftIso (associatedMap B S hS h₂).1 e₁ ≪≫
      Bicategory.whiskerRightIso k₂.isoFst (cc₁ ≫ Jq.snd) ≪≫
      Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso k₂.hom outer.iso) Jq.snd
  -- the outer rectangle, read over `p` through `η`, is a diagram of the test of `p`
  let θ : f.hom ≫ q.hom ≅ p.hom := (Bicategory.InducedBicategory.isoHom η).symm
  let KoutP : Bicategory.TwoCommSq wS.hom p.hom := Kout.reindexSnd θ
  have hKoutP : Bicategory.IsTwoFibreProduct KoutP :=
    Bicategory.isTwoFibreProduct_reindexSnd θ
      (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hJq) hT)
  have hout : Space.IsEtale B S hS
      (ObjectProperty.homMk (h₂ ≫ h₁) : (⟨U₁, hU₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩).hom :=
    hp.2 U₁ W hU₁ hW (Bicategory.InducedBicategory.mkHom (ccOut ≫ KoutP.snd)) wS (h₂ ≫ h₁)
      (Bicategory.whiskerRightIso eOut wS.hom ≪≫ Bicategory.whiskerLeftIso ccOut KoutP.iso) hwsm
      (fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS p.hom wS.hom
        KoutP hKoutP ccOut hccOutet (h₂ ≫ h₁) eOut Q hQ k)
  -- Stacks 05W3: `U₁ ⟶ V₁` is étale, both being étale over `W`
  have hh₂ : Space.IsEtale B S hS h₂ :=
    Space.isEtale_of_isEtale_over B S hS hU₁ hV₁ hW h₂ (h₂ ≫ h₁) h₁ hout hh₁ rfl
  -- the diagram over `f`
  let a₂S : algebraicSpaceStack.{u, w} B S hS U₁ hU₁ ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom a₂
  have hsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U₁).val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor a₂) :=
    isSurjectiveOnObjects_comp_fst_twoFibreProduct B S hS b₁ f.hom Jf hJf cc₂ hcc₂su hb₁sm.1 hb₁su
  exact ⟨U₁, V₁, hU₁, hV₁, a₂S, b₁S, h₂,
    Bicategory.whiskerRightIso e₂ b₁ ≪≫ Bicategory.whiskerLeftIso cc₂ Jf.swap.iso,
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS a₂S hsu, hb₁sm,
    fun Q hQ k => isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom b₁ Jf.swap
      (Bicategory.isTwoFibreProduct_swap hJf) cc₂ hcc₂et h₂ e₂ Q hQ k,
    hh₂⟩

end AlgebraicGeometry.Stack

end
