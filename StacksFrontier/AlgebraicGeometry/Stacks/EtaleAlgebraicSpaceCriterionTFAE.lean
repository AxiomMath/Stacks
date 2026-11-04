module

public import StacksCore.Tactic.StacksAttribute
public import
    StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordSpecialPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleAlgebraicSpaceCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismBaseChangeStable
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange

/-!
# The three equivalent conditions of Stacks 0CIQ

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0CIQ** asserts that the
following are equivalent:

1. `f` is étale (**Stacks 0CIL**), `AlgebraicGeometry.Stack.IsEtale`;
2. `f` is Deligne–Mumford and for every `V ⟶ 𝒴` with `V` an algebraic space and every étale
   `U ⟶ V ×_𝒴 𝒳` with `U` an algebraic space, `U ⟶ V` is étale,
   `AlgebraicGeometry.Stack.EtaleOnEveryAlgebraicSpaceDiagram`;
3. there are a surjective, flat, locally finitely presented `W ⟶ 𝒴` with `W` an algebraic space
   and a surjective étale `T ⟶ W ×_𝒴 𝒳` with `T` an algebraic space such that `T ⟶ W` is étale,
   `AlgebraicGeometry.Stack.HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`.

Conditions (2) and (3) are those of
    `StacksFrontier.AlgebraicGeometry.Stacks.EtaleAlgebraicSpaceCriterion`,
which proves (2) ⟹ (1) and the Deligne–Mumford half of (3) ⟹ (1).

## Main results

* `AlgebraicGeometry.Stack.isEtale_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`: (3) ⟹ (1).
* `AlgebraicGeometry.Stack.etaleOnEveryAlgebraicSpaceDiagram_of_isEtale_of_forward`: (1) ⟹ (2),
  given the forward direction of **Stacks 06N3**.
* `AlgebraicGeometry.Stack.hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange_of_forward`: (2) ⟹ (3),
  given the forward direction of **Stacks 06N3**.
* `AlgebraicGeometry.Stack.isEtale_tfae_of_forward`: the three conditions are equivalent, given
  the forward direction of **Stacks 06N3**.

## Implementation notes

The proofs are the source's.

* (1) ⟹ (2): étaleness is stable under base change (**Stacks 0CII** at étaleness, which is
  **Stacks 0CIN**), so `V ×_𝒴 𝒳 ⟶ V` passes the étale-smooth diagram test; the given étale
  `U ⟶ V ×_𝒴 𝒳` is an étale chart of the trivial 2-fibre product of `(𝟙 V, V ×_𝒴 𝒳 ⟶ V)`
  (`CategoryTheory.Bicategory.trivialBaseChangeSquare`), and `𝟙 V` is smooth, so the test applies
  to it and `U ⟶ V` is étale.
* (2) ⟹ (3): `W` is a smooth surjective presentation of `𝒴` by an algebraic space, which is flat
  and locally of finite presentation; `T` is a surjective étale presentation of `W ×_𝒴 𝒳`
  (**Stacks 0CIA**), and `T ⟶ W` is étale by (2).
* (3) ⟹ (1): the Deligne–Mumford half is
  `AlgebraicGeometry.Stack.isDM_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange`, at
  `AlgebraicGeometry.BigFppfSite.contains_terminal`. For the diagram test, the cover `T` is an
  étale chart of the trivial 2-fibre product over `𝟙 W`, so `W ×_𝒴 𝒳 ⟶ W` passes the existential
  étale-smooth test, hence the universal one (Stacks 0CIF, (2) ⟹ (1), which holds in full
  generality); and the universal test descends along the fppf `W ⟶ 𝒴` by
  `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange`, which is the
  source's appeal to **Stacks 042B**.

Stacks 0CIA and Stacks 0CIN enter only through the existence of surjective étale presentations of
Deligne–Mumford algebraic stacks, the forward direction of **Stacks 06N3**, which is the
hypothesis `hForward` of the conditional statements here.

## References

* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CII](https://stacks.math.columbia.edu/tag/0CII)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
* [Stacks Project, Tag 0CIN](https://stacks.math.columbia.edu/tag/0CIN)
* [Stacks Project, Tag 0CIQ](https://stacks.math.columbia.edu/tag/0CIQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The data of condition (3) of Stacks 0CIQ is an étale-smooth diagram over the base
change.** Given a surjective étale `e : T ⟶ W ×_𝒴 𝒳` and `h : T ⟶ W` inducing `e` followed by the
projection, with `h` étale, the base change `W ×_𝒴 𝒳 ⟶ W` passes the existential étale-smooth
diagram test of Stacks 0CIF at étaleness: the diagram has right-hand vertical 1-morphism the
identity of `W`, which is smooth, left-hand vertical 1-morphism `e`, and `e` is an étale chart of
the trivial 2-fibre product of the identity with the projection. -/
theorem hasPropertyOnSomeEtaleSmoothDiagram_snd_of_etaleCover
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (g : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (e : algebraicSpaceStack.{u, w} B S hS T hT ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f g).pt)
    (h : T ⟶ W) (heSurj : IsSurjective B S hS e) (heEt : IsRelativelyEtale B S hS e.hom)
    (ι : (associatedMap B S hS h).1 ≅
      e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom)
    (hh : Space.IsEtale B S hS h) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS
      (fun {_ _} (k : _ ⟶ _) => Space.IsEtale B S hS k.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (twoFibreProductSquareAlgebraicStacks B S hS f g).snd := by
  have hQ₁ : Bicategory.IsTwoFibreProduct
      (Bicategory.trivialBaseChangeSquare (twoFibreProductSquareAlgebraicStacks B S hS f
          g).snd.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare (twoFibreProductSquareAlgebraicStacks B
          S hS f g).snd.hom
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom (𝟙 _)))
  exact ⟨T, W, hT, hW, e, 𝟙 _, h,
    Bicategory.whiskerRightIso ι (𝟙 _) ≪≫
      Bicategory.whiskerLeftIso e.hom (Bicategory.trivialBaseChangeSquare
          (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom).swap.iso,
    heSurj, isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS W
        hW),
    isRelativelyEtale_preHom_diagramCone_of_chart B S hS (twoFibreProductSquareAlgebraicStacks B S
        hS f g).snd.hom (𝟙 _) _ hQ₁ e.hom heEt h ι,
    hh⟩

/-- **Stacks 0CIQ, (3) ⟹ (1).** A 1-morphism of algebraic stacks admitting a surjective, flat,
locally finitely presented `W ⟶ 𝒴` from an algebraic space and a surjective étale
`T ⟶ W ×_𝒴 𝒳` from an algebraic space with `T ⟶ W` étale is étale. -/
theorem isEtale_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS f) : IsEtale B S hS f := by
  refine ⟨isDM_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS B.contains_terminal hf, ?_⟩
  obtain ⟨W, hW, g, T, hT, e, h, hgSurj, hgFlat, hgLfp, heSurj, heEt, ⟨ι⟩, hh⟩ := hf
  have : (Space.etaleMorphisms B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.etaleMorphisms_isLocalAtTarget_fppf B S hS
  exact hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange B S hS (Space.etaleMorphisms B S hS)
    f g hgSurj hgFlat hgLfp
    (hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS _
      (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) _
      (hasPropertyOnSomeEtaleSmoothDiagram_snd_of_etaleCover B S hS f hW g hT e h heSurj heEt ι
        hh))

/-- **Stacks 0CIQ, (1) ⟹ (2), given the forward direction of Stacks 06N3.** An étale
1-morphism of algebraic stacks is Deligne–Mumford and every étale algebraic-space chart of every
algebraic-space base change of it is étale over the base. -/
theorem etaleOnEveryAlgebraicSpaceDiagram_of_isEtale_of_forward
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} (hf : IsEtale B S hS f) :
    EtaleOnEveryAlgebraicSpaceDiagram B S hS f := by
  classical
  refine ⟨hf.1, fun U V hU hV a b h η hk => ?_⟩
  have hbc := hasEtaleSmoothLocalProperty_baseChange B S hS (Space.etaleMorphisms B S hS)
    (Space.isEtale_isEtaleSmoothLocalOnSourceAndTarget B S hS) B.contains_terminal hForward f b hf
  have hQ₀ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom b.hom)
  let k := Quotient.out (hQ₀.from (diagramCone B S hS f.hom a.hom b.hom h η))
  have hQ₁ : Bicategory.IsTwoFibreProduct
      (Bicategory.trivialBaseChangeSquare
        (AlgebraicStacks.twoFibreProductSquare B S hS f b).snd.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare _
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (AlgebraicStacks.twoFibreProductSquare B S hS f b).snd.hom (𝟙 _)))
  exact prop_of_etaleChart B S hS (Space.etaleMorphisms B S hS)
    (AlgebraicStacks.twoFibreProductSquare B S hS f b).snd hbc.2 hU hV (𝟙 _)
    (isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV))
    _ hQ₁ k.hom (hk _ hQ₀ k) h k.isoFst

/-- **Stacks 0CIQ, (2) ⟹ (3), given the forward direction of Stacks 06N3.** The base is a
smooth surjective presentation `V ⟶ 𝒴` by an algebraic space, the cover a surjective étale
presentation of `V ×_𝒴 𝒳` by a scheme (Stacks 0CIA), and étaleness of the cover over `V` is
condition (2) applied to it. -/
theorem hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange_of_forward
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : EtaleOnEveryAlgebraicSpaceDiagram B S hS f) :
    HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS f := by
  classical
  -- the smooth presentation of `𝒴`
  obtain ⟨V, hV, v, hvsm, hvsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒴.property
  set vS : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom v
  have hvSm : AlgebraicStacks.IsSmooth B S hS vS :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ v V hV
      (StacksRepresentableCFG.EquivalenceOver.refl _) hvsm (Space.isSmooth_id B S hS hV)
  -- the surjective étale presentation of `𝒳 ×_𝒴 V`
  set Jf₀ : Bicategory.TwoCommSq f.hom v :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom v
  have hJfFP : Bicategory.IsTwoFibreProduct Jf₀.swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom v)
  obtain ⟨W, pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS (𝒜 := Jf₀.pt)
      (AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w}
        B S hS B.contains_terminal hForward f hf.1 V hV vS)
  have hU : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  set eU := PresheafOfCategories.sliceElementsEquivalenceOver W
  set cc : fibredCategory B S hS (yoneda.obj W) ⟶ Jf₀.pt :=
    equivalenceOverInvMap B S hS (yoneda.obj W) eU ≫ pres
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
  set eS : algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) hU ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f vS).pt :=
    Bicategory.InducedBicategory.mkHom cc
  -- the morphism `T ⟶ W` of algebraic spaces, and its 2-cell
  set hTop := representingMap B S hS (fibredCategory B S hS (yoneda.obj W))
    (fibredCategory B S hS V) (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (cc ≫ Jf₀.snd)
  obtain ⟨e₀, he₀, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS (yoneda.obj W)) (fibredCategory B S hS V) (yoneda.obj W) V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS (yoneda.obj W) V hTop)
  set e : (associatedMap B S hS hTop).1 ≅ cc ≫ Jf₀.snd :=
    Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e₀ he₀)
  have hTopEt : Space.IsEtale B S hS hTop :=
    hf.2 (yoneda.obj W) V hU hV
      (Bicategory.InducedBicategory.mkHom (cc ≫ Jf₀.swap.snd)) vS hTop
      (Bicategory.whiskerRightIso e v ≪≫ Bicategory.whiskerLeftIso cc Jf₀.swap.iso)
      (isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom v Jf₀.swap hJfFP cc hccet
        hTop e)
  exact ⟨V, hV, vS, yoneda.obj W, hU, eS, hTop,
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS vS hvsu,
    AlgebraicStacks.isFlat_of_isSmooth B S hS vS hvSm,
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS vS hvSm,
    pointsMap_surjective_of_isSurjectiveOnObjects B S hS eS hccsu,
    hccet, ⟨e⟩, hTopEt⟩

/-- **Stacks 0CIQ, given the forward direction of Stacks 06N3.** For a 1-morphism `f` of
algebraic stacks over `S`, the conditions (1) `f` is étale, (2)
`AlgebraicGeometry.Stack.EtaleOnEveryAlgebraicSpaceDiagram`, and (3)
`AlgebraicGeometry.Stack.HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange` are equivalent. -/
theorem isEtale_tfae_of_forward
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE [IsEtale B S hS f, EtaleOnEveryAlgebraicSpaceDiagram B S hS f,
      HasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS f] := by
  tfae_have 1 → 2 := etaleOnEveryAlgebraicSpaceDiagram_of_isEtale_of_forward B S hS hForward
  tfae_have 2 → 3 := hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange_of_forward B S hS hForward
  tfae_have 3 → 1 := isEtale_of_hasEtaleAlgebraicSpaceCoverAfterFppfBaseChange B S hS
  tfae_finish

end AlgebraicGeometry.Stack

end
