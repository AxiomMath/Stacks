module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismBaseChangeStable
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothDiagramFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedEtaleDiagram
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedMorphismPermanence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TrivialBaseChange

/-!
# Characterizations of unramified 1-morphisms of algebraic stacks (Stacks 0CIY)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0CIY** asserts the
equivalence of

1. `f` is unramified (**Stacks 0CIT**), `AlgebraicGeometry.Stack.IsUnramified`;
2. `f` is DM and for every algebraic space `V` with a 1-morphism `V ⟶ 𝒴` and every algebraic
   space `U` with an étale 1-morphism `U ⟶ V ×_𝒴 𝒳`, the morphism `U ⟶ V` is unramified,
   `AlgebraicGeometry.Stack.IsUnramifiedOnEveryEtaleDiagram`;
3. there are a surjective, flat, locally finitely presented `W ⟶ 𝒴` out of an algebraic space and
   a surjective étale `T ⟶ W ×_𝒴 𝒳` out of an algebraic space with `T ⟶ W` unramified,
   `AlgebraicGeometry.Stack.HasUnramifiedEtalePresentationOverFlatCover`.

## Main definitions

* `AlgebraicGeometry.Stack.HasUnramifiedEtalePresentationOverFlatCover`: condition (3).

## Main results

* `AlgebraicGeometry.Stack.isUnramified_of_hasUnramifiedEtalePresentationOverFlatCover`:
  (3) ⇒ (1), with no hypothesis.
* `AlgebraicGeometry.Stack.isUnramifiedOnEveryEtaleDiagram_of_isUnramified_baseChange`: (2) from
  unramifiedness of the base changes along 1-morphisms out of algebraic spaces, which is how
  (1) ⇒ (2) goes through **Stacks 0CIV**.
* `Stack.hasUnramifiedEtalePresentationOverFlatCover_of_isUnramifiedOnEveryEtaleDiagram`:
  (2) ⇒ (3), given the forward direction of **Stacks 06N3** (through **Stacks 0CIA**).
* `AlgebraicGeometry.Stack.isUnramified_tfae_of_existsEtalePresentationOfIsAbsolutelyDM`: the
  three-way equivalence, given the forward direction of Stacks 06N3.

## Implementation notes

The proof is the source's. For (3) ⇒ (1) the Deligne–Mumford half is
`AlgebraicGeometry.Stack.isDM_of_surjectiveEtalePresentation_flatBaseChange` (Stacks 06N3, easy
direction, then **Stacks 06TZ**). For the unramified half, the data `(T, W)` of (3) is a diagram
of condition (2) of **Stacks 0CIF** for the base change `𝒳 ×_𝒴 W ⟶ W` whose right-hand leg is the
identity of `W`: the trivial base change square of the projection is a 2-fibre product of
`(𝟙 W, 𝒳 ×_𝒴 W ⟶ W)`, and the comparison into it is the given étale `T ⟶ 𝒳 ×_𝒴 W`. So the base
change passes the universal étale-smooth test by Stacks 0CIF (2) ⇒ (1), which needs no
presentation, and the test descends along the fppf covering `W ⟶ 𝒴` by
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange`, unramifiedness
being fppf local on the target by **Stacks 042A**.

For (1) ⇒ (2) the source uses base change and composition. Here only base change is needed: a
diagram `(U, V, b)` over `f` whose comparison `U ⟶ 𝒳 ×_𝒴 V` is étale is, through that comparison,
a diagram over the base change `𝒳 ×_𝒴 V ⟶ V` with identity right-hand leg, which is smooth, so
unramifiedness of the base change (**Stacks 0CIV**) applies to it directly.

The forward direction of Stacks 06N3 is used twice: in (2) ⇒ (3), where `𝒳 ×_𝒴 V` must have a
surjective étale presentation (**Stacks 0CIA**, part (2)), and in Stacks 0CIV. The site containing
the terminal scheme, which is how this library spells absolute Deligne–Mumfordness, is
`AlgebraicGeometry.BigFppfSite.contains_terminal`, so it is not a hypothesis.

## References

* [Stacks Project, Tag 042A](https://stacks.math.columbia.edu/tag/042A)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (3) of Stacks 0CIY.** There are an algebraic space `W` with a surjective, flat,
locally finitely presented 1-morphism `c : W ⟶ 𝒴` and an algebraic space `T` with a surjective
étale 1-morphism `t : T ⟶ 𝒳 ×_𝒴 W` such that the induced morphism `T ⟶ W` of algebraic spaces is
unramified. -/
abbrev HasUnramifiedEtalePresentationOverFlatCover
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (c : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴),
    IsSurjective B S hS c ∧ AlgebraicStacks.IsFlat B S hS c ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c ∧
      ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
        (t : algebraicSpaceStack.{u, w} B S hS T hT ⟶
          (twoFibreProductSquareAlgebraicStacks B S hS f c).pt),
        IsSurjective B S hS t ∧ IsRelativelyEtale B S hS t.hom ∧
          Space.IsUnramified B S hS
            (representingMap B S hS (fibredCategory B S hS T) (fibredCategory B S hS W) T W
              (StacksRepresentableCFG.EquivalenceOver.refl _)
              (StacksRepresentableCFG.EquivalenceOver.refl _)
              (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom)

/-- **The étale clause of Stacks 0CIF for a diagram with identity right-hand leg.** Let
`g : 𝒜 ⟶ V` be a 1-morphism into the category fibred in groupoids of an algebraic space and
`cc : U ⟶ 𝒜` an étale 1-morphism out of the one of an algebraic space, with `h : U ⟶ V` inducing
`cc ≫ g` up to a 2-isomorphism. Then the diagram `(cc, 𝟙 V, h)` over `g` has étale comparison to
every 2-fibre product of `(𝟙 V, g)`: the trivial base change square of `g` is one of them, and
the comparison into it is `cc`. -/
theorem isRelativelyEtale_preHom_diagramCone_trivialBaseChange
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : 𝒜 ⟶ fibredCategory B S hS V)
    (cc : fibredCategory B S hS U ⟶ 𝒜) (hcc : IsRelativelyEtale B S hS cc)
    (h : U ⟶ V) (e : (associatedMap B S hS h).1 ≅ cc ≫ g)
    (Q : Bicategory.TwoCommSq (𝟙 (fibredCategory B S hS V)) g)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS g (cc ≫ (Bicategory.trivialBaseChangeSquare g).swap.snd) (𝟙 _) h
        (Bicategory.whiskerRightIso e (𝟙 _) ≪≫
          Bicategory.whiskerLeftIso cc (Bicategory.trivialBaseChangeSquare g).swap.iso)) Q) :
    IsRelativelyEtale B S hS k.hom :=
  isRelativelyEtale_preHom_diagramCone_of_chart B S hS g (𝟙 _)
    (Bicategory.trivialBaseChangeSquare g).swap
    (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare g
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g
        (𝟙 _))))
    cc hcc h e Q hQ k

/-- A 1-morphism `g` between categories of elements is 2-isomorphic to the one induced by the
morphism of presheaves that it represents. -/
private theorem nonempty_iso_associatedMap_representingMap
    {T W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : fibredCategory B S hS T ⟶ fibredCategory B S hS W) :
    Nonempty ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS T)
      (fibredCategory B S hS W) T W (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) g)).1 ≅ g) := by
  obtain ⟨α, hα, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS T) (fibredCategory B S hS W) T W
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (representingMap_associatedMap B S hS T W (representingMap B S hS (fibredCategory B S hS T)
      (fibredCategory B S hS W) T W (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) g))
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso α hα)⟩

/-- **The presentation of condition (3) of Stacks 0CIY is a diagram of condition (2) of
Stacks 0CIF for the base change.** If `t : T ⟶ 𝒳 ×_𝒴 W` is surjective and étale and the induced
`T ⟶ W` is unramified, then the diagram `(t, 𝟙 W, T ⟶ W)` over the projection `𝒳 ×_𝒴 W ⟶ W`
witnesses the existential étale-smooth diagram test at unramifiedness. -/
theorem hasPropertyOnSomeEtaleSmoothDiagram_unramified_snd
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (c : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒴)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (t : algebraicSpaceStack.{u, w} B S hS T hT ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt)
    (htSurj : IsSurjective B S hS t) (htEt : IsRelativelyEtale B S hS t.hom)
    (hunr : Space.IsUnramified B S hS
      (representingMap B S hS (fibredCategory B S hS T) (fibredCategory B S hS W) T W
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom)) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS (Space.unramifiedMorphismProperty B S hS)
      (twoFibreProductSquareAlgebraicStacks B S hS f c).snd := by
  classical
  set hTW := representingMap B S hS (fibredCategory B S hS T) (fibredCategory B S hS W) T W
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom with hTWdef
  obtain ⟨e⟩ := nonempty_iso_associatedMap_representingMap B S hS
    (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom
  exact ⟨T, W, hT, hW,
    Bicategory.InducedBicategory.mkHom
      (t.hom ≫ (Bicategory.trivialBaseChangeSquare
        (twoFibreProductSquareAlgebraicStacks B S hS f c).snd.hom).swap.snd),
    Bicategory.InducedBicategory.mkHom (𝟙 _), hTW,
    Bicategory.whiskerRightIso e (𝟙 _) ≪≫
      Bicategory.whiskerLeftIso t.hom (Bicategory.trivialBaseChangeSquare
        (twoFibreProductSquareAlgebraicStacks B S hS f c).snd.hom).swap.iso,
    htSurj,
    isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS W hW),
    isRelativelyEtale_preHom_diagramCone_trivialBaseChange B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f c).snd.hom t.hom htEt hTW e,
    hunr⟩

/-- **Unramifiedness from condition (3) of Stacks 0CIY.** If `f : 𝒳 ⟶ 𝒴` admits the data of
condition (3) — a surjective, flat, locally finitely presented `c : W ⟶ 𝒴` out of an algebraic
space and a surjective étale `t : T ⟶ 𝒳 ×_𝒴 W` out of an algebraic space with `T ⟶ W`
unramified — then `f` is unramified in the sense of Stacks 0CIT.

The Deligne–Mumford condition is
`AlgebraicGeometry.Stack.isDM_of_surjectiveEtalePresentation_flatBaseChange`. The presentation is
a diagram of condition (2) of Stacks 0CIF for the base change `𝒳 ×_𝒴 W ⟶ W`, with identity
right-hand leg, so that base change passes the universal étale-smooth test by Stacks 0CIF
(2) ⇒ (1); and the test descends along `c` by
`AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange`, unramifiedness
being local on the target for the fppf topology (**Stacks 042A**). -/
theorem isUnramified_of_hasUnramifiedEtalePresentationOverFlatCover
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h3 : HasUnramifiedEtalePresentationOverFlatCover.{u, w} B S hS f) :
    IsUnramified B S hS f := by
  obtain ⟨W, hW, c, hcSurj, hcFlat, hcLfp, T, hT, t, htSurj, htEt, hunr⟩ := h3
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact ⟨isDM_of_surjectiveEtalePresentation_flatBaseChange B S hS B.contains_terminal f W hW c
      hcSurj hcFlat hcLfp T hT t htSurj htEt,
    hasPropertyOnEveryEtaleSmoothDiagram_of_baseChange B S hS _ f c hcSurj hcFlat hcLfp
      (hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS _
        (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS) _
        (hasPropertyOnSomeEtaleSmoothDiagram_unramified_snd B S hS f W hW c T hT t htSurj htEt
          hunr))⟩

/-- **Condition (2) of Stacks 0CIY from unramified base changes over algebraic spaces.** If
`f : 𝒳 ⟶ 𝒴` is Deligne–Mumford and its base change `𝒳 ×_𝒴 V ⟶ V` along every 1-morphism
`b : V ⟶ 𝒴` out of an algebraic space is unramified, then every étale diagram of algebraic spaces
over `f` has unramified top horizontal morphism.

A diagram `(U, V, a, b, h)` over `f` with étale comparison is, through that comparison
`U ⟶ 𝒳 ×_𝒴 V`, a diagram over the base change with identity right-hand leg, which is smooth; so
the universal étale-smooth test of the base change applies to it. -/
theorem isUnramifiedOnEveryEtaleDiagram_of_isUnramified_baseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f)
    (hbc : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴),
      IsUnramified B S hS (twoFibreProductSquareAlgebraicStacks B S hS f b).snd) :
    IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f := by
  classical
  refine ⟨hf, ?_⟩
  intro U V hU hV a b h η hk
  have hJfFP : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom b.hom)
  have kk : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a.hom b.hom h η)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom b.hom).swap :=
    Quotient.out (hJfFP.from _)
  have hccet : IsRelativelyEtale B S hS kk.hom := hk _ hJfFP kk
  have e : (associatedMap B S hS h).1 ≅
      kk.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom := kk.isoFst
  exact (hbc V hV b).2 U V hU hV
    (Bicategory.InducedBicategory.mkHom (kk.hom ≫
      (Bicategory.trivialBaseChangeSquare
        (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom).swap.snd))
    (Bicategory.InducedBicategory.mkHom (𝟙 _)) h
    (Bicategory.whiskerRightIso e (𝟙 _) ≪≫
      Bicategory.whiskerLeftIso kk.hom (Bicategory.trivialBaseChangeSquare
        (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom).swap.iso)
    (isRelativelySmooth_id B S hS (isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV))
    (isRelativelyEtale_preHom_diagramCone_trivialBaseChange B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f b).snd.hom kk.hom hccet h e)

/-- **Condition (3) of Stacks 0CIY from condition (2), given the forward direction of
Stacks 06N3.** Choose a surjective smooth `c : V ⟶ 𝒴` out of an algebraic space; it is surjective,
flat and locally of finite presentation. The 2-fibre product `𝒳 ×_𝒴 V` is Deligne–Mumford
(**Stacks 0CIA**, part (2)), so it has a surjective étale presentation `T ⟶ 𝒳 ×_𝒴 V` by a
scheme; and `T ⟶ V` is unramified, being the top horizontal morphism of an étale diagram over
`f`. -/
theorem hasUnramifiedEtalePresentationOverFlatCover_of_isUnramifiedOnEveryEtaleDiagram
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f) :
    HasUnramifiedEtalePresentationOverFlatCover.{u, w} B S hS f := by
  classical
  obtain ⟨V, hV, v, hvsm, hvsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒴.property
  set c : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴 :=
    Bicategory.InducedBicategory.mkHom v with hc
  obtain ⟨W', pres, hpreset, hpressu⟩ :=
    exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS
      (𝒜 := (twoFibreProductSquareAlgebraicStacks B S hS f c).pt.val)
      (AlgebraicStacks.isDeligneMumfordStack_twoFibreProduct_algebraicSpace.{u, w}
        B S hS B.contains_terminal hForward f hf.1 V hV c)
  have hT : IsAlgebraicSpace B S hS (yoneda.obj W') := isAlgebraicSpace_yoneda B S hS W'
  set eU := PresheafOfCategories.sliceElementsEquivalenceOver W' with heU
  set cc : fibredCategory B S hS (yoneda.obj W') ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt.val :=
    equivalenceOverInvMap B S hS (yoneda.obj W') eU ≫ pres with hcc
  have hccet : IsRelativelyEtale B S hS cc :=
    isRelativelyEtale_of_isEquivalence_comp B S hS _ pres
      (by change Functor.IsEquivalence eU.inv.functor
          exact eU.toEquivalence.symm.isEquivalence_functor) hpreset
  have hccsu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (yoneda.obj W')).val.p
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt.val.val.p
      (CatFiberedInGroupoids.homFunctor cc) :=
    isSurjectiveOnObjects_comp B S hS (fibredCategory B S hS (yoneda.obj W')).val.p
      (schemeFibredCategory B S hS W').val.p
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt.val.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS (yoneda.obj W') eU))
      (CatFiberedInGroupoids.homFunctor pres)
      (CatFiberedInGroupoids.homFunctor_comp_p pres)
      (isSurjectiveOnObjects_equivalenceOverInvMap
        (𝒳 := schemeFibredCategory B S hS W') B S hS (yoneda.obj W') eU)
      hpressu
  set t : algebraicSpaceStack.{u, w} B S hS (yoneda.obj W') hT ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS f c).pt :=
    Bicategory.InducedBicategory.mkHom cc with htdef
  -- the morphism `T ⟶ V` and its 2-cell
  set hTW := representingMap B S hS (fibredCategory B S hS (yoneda.obj W'))
    (fibredCategory B S hS V) (yoneda.obj W') V
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom with hTWdef
  obtain ⟨e⟩ := nonempty_iso_associatedMap_representingMap B S hS
    (t ≫ (twoFibreProductSquareAlgebraicStacks B S hS f c).snd).hom
  have hJfFP : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom c.hom).swap :=
    Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom c.hom)
  have hunr : Space.IsUnramified B S hS hTW :=
    hf.2 (yoneda.obj W') V hT hV
      (Bicategory.InducedBicategory.mkHom (cc ≫
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom c.hom).swap.snd)) c hTW
      (Bicategory.whiskerRightIso e v ≪≫ Bicategory.whiskerLeftIso cc
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom c.hom).swap.iso)
      (isRelativelyEtale_preHom_diagramCone_of_chart B S hS f.hom v
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom c.hom).swap
        hJfFP cc hccet hTW e)
  -- the smooth presentation is surjective, flat and locally of finite presentation
  have hcFlat : AlgebraicStacks.IsFlat B S hS c :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS c).2
      (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ c.hom V hV
        (StacksRepresentableCFG.EquivalenceOver.refl _) hvsm (Space.isFlat_id B S hS hV))
  have hcLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c :=
    hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) c.hom
      (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ c.hom V hV
        (StacksRepresentableCFG.EquivalenceOver.refl _) hvsm
        (Space.isLocallyOfFinitePresentation_id B S hS hV))
  exact ⟨V, hV, c, pointsMap_surjective_of_isSurjectiveOnObjects B S hS c hvsu, hcFlat, hcLfp,
    yoneda.obj W', hT, t, pointsMap_surjective_of_isSurjectiveOnObjects B S hS t hccsu, hccet,
    hunr⟩

/-- **Stacks 0CIY, given the forward direction of Stacks 06N3.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are equivalent:
(1) `f` is unramified (Stacks 0CIT); (2) condition (2) of Stacks 0CIY; (3) condition (3) of
Stacks 0CIY.

(1) ⇒ (2) is base change (**Stacks 0CIV**) read on the identity diagram of each base change;
(2) ⇒ (3) is `hasUnramifiedEtalePresentationOverFlatCover_of_isUnramifiedOnEveryEtaleDiagram`;
(3) ⇒ (1) is `isUnramified_of_hasUnramifiedEtalePresentationOverFlatCover`. The forward
direction of Stacks 06N3 enters through Stacks 0CIA, in (2) ⇒ (3) and in Stacks 0CIV. -/
theorem isUnramified_tfae_of_existsEtalePresentationOfIsAbsolutelyDM
    (hForward : ExistsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    [IsUnramified B S hS f, IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f,
      HasUnramifiedEtalePresentationOverFlatCover.{u, w} B S hS f].TFAE := by
  tfae_have 1 → 2 := fun hf =>
    isUnramifiedOnEveryEtaleDiagram_of_isUnramified_baseChange B S hS f hf.1
      (fun _ _ b => isUnramified_baseChange.{u, w} B S hS B.contains_terminal hForward f b hf)
  tfae_have 2 → 3 :=
    hasUnramifiedEtalePresentationOverFlatCover_of_isUnramifiedOnEveryEtaleDiagram B S hS
      hForward f
  tfae_have 3 → 1 := isUnramified_of_hasUnramifiedEtalePresentationOverFlatCover B S hS f
  tfae_finish

end AlgebraicGeometry.Stack

end
