module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack

/-!
# The universal smooth-diagram criterion implies the existential one

Let `P` be a property of morphisms of algebraic spaces over `S` and let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`. If every diagram of algebraic spaces over `f` with smooth
vertical 1-morphisms and smooth comparison to a 2-fibre product has `P` on its top horizontal
morphism, then some such diagram has its left vertical 1-morphism surjective on objects: condition
(1) of [Stacks, Tag 06FM] implies condition (2).

## Main results

* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation`: an
  algebraic stack has a smooth presentation, surjective on objects, by the category of elements of
  an algebraic space.
* `AlgebraicGeometry.Stack.exists_smoothDiagram_smoothComparison`: over a prescribed smooth
  presentation of the target, a diagram of algebraic spaces over `f` with its 2-cell, whose left
  vertical 1-morphism is smooth and surjective on objects and all of whose comparison 1-morphisms
  to 2-fibre products are smooth.
* `AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram`: under the
  universal criterion, such a diagram whose top horizontal morphism has `P`.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram`:
  condition (1) of Stacks 06FM implies condition (2).

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack has a smooth presentation, surjective on objects, by the category of
elements of an algebraic space. -/
theorem exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hV : IsAlgebraicSpace B S hS V)
      (b : fibredCategory B S hS V ⟶ 𝒴),
      IsRelativelySmooth B S hS b ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS V).val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor b) := by
  obtain ⟨h𝒴fib, h𝒴stack, h𝒴diag, W, pres, hpresrep, hpresprop⟩ := h𝒴
  let pMor : schemeFibredCategory B S hS W ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom pres
  have hp : IsRepresentableByAlgebraicSpaces B S hS pMor.hom := hpresrep
  have hpsm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) pMor hp :=
    fun V y hy G hG he => (hpresprop V y hy G hG he).2
  have hpsu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) pMor hp :=
    fun V y hy G hG he => (hpresprop V y hy G hG he).1
  have hV : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  let eV := PresheafOfCategories.sliceElementsEquivalenceOver W
  let bInv : fibredCategory B S hS (yoneda.obj W) ⟶ schemeFibredCategory B S hS W :=
    equivalenceOverInvMap B S hS (yoneda.obj W) eV
  refine ⟨yoneda.obj W, hV, bInv ≫ pMor, isRelativelySmooth_comp B S hS bInv pMor
    (isRelativelySmooth_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS W) B S hS
      (yoneda.obj W) hV eV) ⟨hp, hpsm⟩, ?_⟩
  exact isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj W)).val.p
    (schemeFibredCategory B S hS W).val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor bInv) (CatFiberedInGroupoids.homFunctor pMor)
    (CatFiberedInGroupoids.homFunctor_comp_p pMor)
    (isSurjectiveOnObjects_equivalenceOverInvMap (𝒳 := schemeFibredCategory B S hS W) B S hS
      (yoneda.obj W) eV)
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS pMor hp).2 hpsu)

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `b : 𝒮_V ⟶ 𝒴` be a smooth
1-morphism, surjective on objects, out of the category fibred in groupoids of an algebraic space
`V`. Then there is an algebraic space `U`, a smooth 1-morphism `a : 𝒮_U ⟶ 𝒳` surjective on objects,
a morphism `h : U ⟶ V` and an invertible 2-cell filling the square over `f`, such that *every*
comparison 1-morphism of the resulting diagram to *every* 2-fibre product of the cospan `(b, f)` is
smooth. -/
theorem exists_smoothDiagram_smoothComparison
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (hbsm : IsRelativelySmooth B S hS b)
    (hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor b)) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hU : IsAlgebraicSpace B S hS U)
      (a : fibredCategory B S hS U ⟶ 𝒳) (h : U ⟶ V)
      (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f),
      IsRelativelySmooth B S hS a ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.p
        (CatFiberedInGroupoids.homFunctor a) ∧
      ∀ (Q : Bicategory.TwoCommSq b f) (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q),
          IsRelativelySmooth B S hS k.hom := by
  classical
  obtain ⟨h𝒴fib, h𝒴stack, h𝒴diag, -, -, -, -⟩ := h𝒴
  set R : Bicategory.TwoCommSq b f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f with hRdef
  set R' : Bicategory.TwoCommSq f b :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f b with hR'def
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b f
  have hR' : Bicategory.IsTwoFibreProduct R' :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f b
  have hreprfst' : IsRepresentableByAlgebraicSpaces B S hS R'.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS V) 𝒴 𝒳 b f R' hR' hbsm.1
  have hsmfst' : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R'.fst hreprfst' :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      (fibredCategory B S hS V) 𝒴 𝒳 b f R' hR' hbsm.1 hbsm.2
  let sw := twoFibreProductSwapMap B S hS f b
  have hswEquiv : Functor.IsEquivalence sw.hom.toFunctor := by
    show Functor.IsEquivalence (TwoFibreProductOver.swap _ _ _ _ _)
    infer_instance
  have he : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj), y ⋙ 𝒳.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) R.pt.val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor R.snd))
        (TwoFibreProductOver.fst (Over.map V.hom) R'.pt.val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor R'.fst))) :=
    fun V y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS sw.hom R'.fst.hom
      V y hy
  have hreprsnd : IsRepresentableByAlgebraicSpaces B S hS R.snd.hom :=
    isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst he hreprfst'
  have hsmsnd : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R.snd hreprsnd :=
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
      (Space.smoothMorphismProperty B S hS) R'.fst R.snd he hsmfst'
  have hsusnd : IsSurjectiveOnObjects B S hS R.pt.val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor R.snd) :=
    isSurjectiveOnObjects_twoFibreProductSnd.{u, u, u} B S hS
      (fibredCategory B S hS V) 𝒴 𝒳 b f hbsu
  have hRalg : IsAlgebraicStack.{u, w} B S hS R.pt.val :=
    isAlgebraicStack_twoFibreProduct B S hS (fibredCategory B S hS V).val 𝒳.val
      𝒴.val b.hom f.hom h𝒴stack h𝒴diag
      (isAlgebraicStack_fibredCategory.{u, w} B S hS V hV) h𝒳
  obtain ⟨U, hU, pU, hpUsm, hpUsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS hRalg
  let a : fibredCategory B S hS U ⟶ 𝒳 := pU ≫ R.snd
  have hasm : IsRelativelySmooth B S hS a :=
    isRelativelySmooth_comp B S hS pU R.snd hpUsm ⟨hreprsnd, hsmsnd⟩
  have hasu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS U).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor a) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS U).val.p
      R.pt.val.p 𝒳.val.p (CatFiberedInGroupoids.homFunctor pU)
      (CatFiberedInGroupoids.homFunctor R.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p R.snd) hpUsu hsusnd
  set hTop := representingMap B S hS (fibredCategory B S hS U)
    (fibredCategory B S hS V) U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (pU ≫ R.fst) with hTopDef
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS U) (fibredCategory B S hS V)
    U V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS U V hTop)
  let eIso : (associatedMap B S hS hTop).1 ≅ pU ≫ R.fst :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)
  let η : (associatedMap B S hS hTop).1 ≫ b ≅ a ≫ f :=
    Bicategory.whiskerRightIso eIso b ≪≫ Bicategory.associator pU R.fst b ≪≫
      Bicategory.whiskerLeftIso pU R.iso ≪≫ (Bicategory.associator pU R.snd f).symm
  let k₁ : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b hTop η) R :=
    { hom := pU
      isoFst := eIso
      isoSnd := Iso.refl a
      compat := by simp [η, Bicategory.id_whiskerRight a f] }
  exact ⟨U, hU, a, hTop, η, hasm, hasu,
    fun Q hQ k => isRelativelySmooth_preHom_of_isTwoFibreProduct B S hS hR hQ k₁ k hpUsm⟩

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `b : 𝒮_V ⟶ 𝒴` be a smooth
1-morphism, surjective on objects, out of the category fibred in groupoids of an algebraic space
`V`. If every diagram of algebraic spaces over `f` with smooth vertical 1-morphisms and smooth
comparison to a 2-fibre product has `P` on its top horizontal morphism, then there is an algebraic
space `U`, a smooth 1-morphism `a : 𝒮_U ⟶ 𝒳` surjective on objects and a morphism `h : U ⟶ V` with
`P`, filling a 2-commutative square over `f` whose right vertical 1-morphism is the given `b`. -/
theorem exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (hbsm : IsRelativelySmooth B S hS b)
    (hbsu : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V).val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor b))
    (hevery : HasPropertyOnEverySmoothDiagram B S hS P f) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hU : IsAlgebraicSpace B S hS U)
      (a : fibredCategory B S hS U ⟶ 𝒳) (h : U ⟶ V),
      Nonempty ((associatedMap B S hS h).1 ≫ b ≅ a ≫ f) ∧
      IsRelativelySmooth B S hS a ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.p
        (CatFiberedInGroupoids.homFunctor a) ∧ P h := by
  obtain ⟨U, hU, a, h, η, hasm, hasu, hk⟩ :=
    exists_smoothDiagram_smoothComparison.{u, w} B S hS h𝒳 h𝒴 f V hV b hbsm hbsu
  exact ⟨U, hU, a, h, ⟨η⟩, hasm, hasu, hevery U V hU hV a b h η hasm hbsm hk⟩

/-- Condition (1) of Stacks 06FM implies condition (2): for a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S`, if every diagram of algebraic spaces over `f` with smooth vertical
1-morphisms and smooth comparison to a 2-fibre product has `P` on its top horizontal morphism,
then there is one such diagram whose left vertical 1-morphism is surjective on objects. -/
theorem hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴)
    (hevery : HasPropertyOnEverySmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P f := by
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS h𝒴
  obtain ⟨U, hU, a, h, hη, hasm, hasu, hPh⟩ :=
    exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS P h𝒳 h𝒴 f V hV b
      hbsm hbsu hevery
  exact ⟨U, V, hU, hV, a, b, h, hη, hasm, hasu, hbsm, hPh⟩

end AlgebraicGeometry.Stack

end
