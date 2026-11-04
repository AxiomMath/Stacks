module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation

/-!
# The étale-smooth diagram over a prescribed chart of the target (Stacks 0CIF)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` passing the universal étale-smooth
diagram test of **Stacks 0CIF** at a property `P` of morphisms of algebraic spaces over `S`, let
`b : 𝒮_V ⟶ 𝒴` be a smooth 1-morphism, surjective on objects, out of an algebraic space `V`, and
let the 2-fibre product `𝒳 ×_𝒴 V` admit a surjective étale presentation by a scheme. This file
produces the diagram of condition (2) of Stacks 0CIF over *that* `b`, keeping the diagram
itself rather than the proposition it witnesses, and records that its left vertical 1-morphism is
smooth as well as surjective.

Both are what the composition and base-change remarks **Stacks 0CIH** and **Stacks 0CII** need:
they chain two such diagrams, and the left vertical 1-morphism of the first has to serve as the
prescribed right vertical 1-morphism of the second, which asks it to be smooth and surjective on
objects.

## Main results

* `AlgebraicGeometry.Stack.exists_etaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`:
  the diagram of condition (2) of Stacks 0CIF over a prescribed chart of the target, with its
  left vertical 1-morphism smooth.

## Implementation notes

This strengthens `AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_etalePresentation`
in two ways, and is otherwise its construction verbatim: the chart `b` of the target stays
visible in the conclusion instead of being existentially quantified away, and the left vertical
1-morphism is proved smooth. Smoothness is not part of condition (2) of Stacks 0CIF — which asks
only for surjectivity — but it holds: the left vertical 1-morphism is the given étale
presentation followed by the projection of `𝒳 ×_𝒴 V` to `𝒳`, the first smooth by
`AlgebraicGeometry.Stack.isRelativelySmooth_of_isRelativelyEtale` and the second a base change of
`b` by **Stacks 045C**, read across the exchange of the two factors exactly as its
representability is. The composite is smooth by **Stacks 045B**.

The clause about `P` is condition (1) of Stacks 0CIF applied to the diagram just built, whose
comparison with the canonical 2-fibre product is the presentation itself;
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one` carries étaleness of that one
comparison to every 2-fibre product of `(b, f)` and every comparison out of the diagram's cone,
so the universally quantified clause is discharged at a single square.

No `@[stacks]` attribute. Stacks 0CIF asserts its first assertion for every Deligne–Mumford `f`,
with the chart and the presentation produced by **Stacks 0CIA**; both are hypotheses here, so the
statement is strictly weaker, as in
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEvery`.

## References

* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06D5](https://stacks.math.columbia.edu/tag/06D5)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagram of condition (2) of Stacks 0CIF over a prescribed chart of the target.** Let
`f : 𝒳 ⟶ 𝒴` pass the universal étale-smooth diagram test at `P`, let `b : 𝒮_V ⟶ 𝒴` be smooth and
surjective on objects out of an algebraic space `V`, and let `𝒳 ×_𝒴 V` admit a relatively étale
presentation by a scheme, surjective on objects. Then there is an algebraic space `U`, a
1-morphism `a : 𝒮_U ⟶ 𝒳` which is smooth and surjective, and a morphism `h : U ⟶ V` with `P`,
filling a 2-commutative square over `f` whose right vertical 1-morphism is the given `b` and
whose every comparison to a 2-fibre product of `(b, f)` is étale. -/
theorem exists_etaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
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
        (CatFiberedInGroupoids.homFunctor pres))
    (hevery : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳) (h : U ⟶ V)
      (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsSurjective B S hS a ∧
      IsRelativelySmooth B S hS a.hom ∧
      IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor a.hom) ∧
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
        IsRelativelyEtale B S hS k.hom) ∧
      P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) := by
  classical
  set R : Bicategory.TwoCommSq b.hom f.hom :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom f.hom
  obtain ⟨W, pres, hpreset, hpressu⟩ := hpres
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      b.hom f.hom
  -- the projection to `𝒳` is the base change of `b`: Stacks 0302 and Stacks 045C in the other
  -- order of the two factors, transported across the exchange
  have hsmsnd : IsRelativelySmooth B S hS R.snd :=
    isRelativelySmooth_twoFibreProductSnd B S hS b.hom f.hom hbsm
  -- surjectivity on objects of the projection to `𝒳` is Stacks 06D5 at the chart
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
    show Functor.IsEquivalence eU.inv.functor
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
    isRepresentableByAlgebraicSpaces_comp B S hS pU R.snd hpUet.1 hsmsnd.1
  have hasm : IsRelativelySmooth B S hS a₀ :=
    isRelativelySmooth_comp B S hS pU R.snd
      (isRelativelySmooth_of_isRelativelyEtale B S hS pU hpUet) hsmsnd
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
  have hket := isRelativelyEtale_preHom_of_one B S hS hR k₁ hpUet
  refine ⟨yoneda.obj W, hU, Bicategory.InducedBicategory.mkHom a₀, hTop, η, ?_, hasm, hasu, hket,
    hevery (yoneda.obj W) V hU hV (Bicategory.InducedBicategory.mkHom a₀) b hTop η hbsm hket⟩
  exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u + 1} B S hS
    _ hrepa).2
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS a₀
      hrepa).1 hasu)

end AlgebraicGeometry.Stack

end
