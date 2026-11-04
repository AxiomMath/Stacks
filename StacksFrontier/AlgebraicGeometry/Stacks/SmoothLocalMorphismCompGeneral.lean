module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# Composition of a property of morphisms of algebraic stacks (Stacks 06FP)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target (**Stacks 06F8**) and stable under composition. **Stacks 06FP** says that the
property of 1-morphisms of algebraic stacks that **Stacks 06FN** attaches to `P` is stable under
composition: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` have it, so does `f ≫ g`.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp`: **Stacks 06FP**, for
  arbitrary categories fibred in groupoids.

## Implementation notes

### Relation to the sibling statement of Stacks 06FP

`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp` proves Stacks 06FP from the
*universal* smooth-diagram form of **Stacks 06FM**, and therefore assumes `P` smooth local on the
source-and-target and assumes the three categories fibred in groupoids to be algebraic stacks.
Neither hypothesis is needed for the argument below, which never invokes condition (1) of Stacks
06FM, so neither statement implies the other: this one applies to a 1-morphism out of a category
fibred in groupoids that is not an algebraic stack — the case the flat objects of **Stacks 0787**
need, where the source is `AlgebraicGeometry.Stack.schemeFibredCategory` — while the sibling
asks less of `P`. Both are kept.

### The diagram, and why no universal test is needed

The source argues through the *universal* half of **Stacks 06FM**: it chooses a smooth surjective
presentation `W → 𝒵`, then `V → 𝒴 ×_𝒵 W`, then `U → 𝒳 ×_𝒴 V`, and concludes that `V → W` and
`U → V` have `P` "by definition", i.e. by condition (1) of Stacks 06FM applied to two diagrams
it did not choose.

That is avoidable. The diagram below is built from the two *given* diagrams and nothing else, so
only condition (2) — the existential test `AlgebraicGeometry.Stack`
`.HasPropertyOnSomeSmoothDiagram` — is ever used, in the hypotheses and in the conclusion alike.
Writing `a₁ : U₁ → 𝒳`, `b₁ : V₁ → 𝒴`, `h₁ : U₁ → V₁` for the diagram of `f` and
`a₂ : U₂ → 𝒴`, `b₂ : V₂ → 𝒵`, `h₂ : U₂ → V₂` for that of `g`, the new diagram is

```
  A  --- pr ≫ h₂ --->  V₂
  |                     |
  pr ≫ a₁               b₂
  v                     v
  𝒳  ----- f ≫ g ---->  𝒵
```

with `A = W ×_{V₁} U₁` for `W` an algebraic space representing the 2-fibre product
`U₂ ×_𝒴 V₁`. So exactly one 2-fibre product of categories fibred in groupoids is formed, over the
cospan `(a₂, b₁)` where both legs are already representable by algebraic spaces; everything else
happens in presheaves, where it is an ordinary fibre product of algebraic spaces.

Consequently the hypotheses on `P` are only the three closure properties the construction uses:
stability under base change on algebraic spaces, under precomposition with a smooth morphism, and
under composition. Smooth locality on the source-and-target is not assumed as such — it is what
makes the notion of Stacks 06FN well behaved, and a caller holding it supplies
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget.precomp` for the second.

### Where each leg's property comes from

* the top morphism `A → W → U₂ → V₂` is the base change of `h₁` (so it has `P`) followed by the
  morphism of representing presheaves of the projection `U₂ ×_𝒴 V₁ → U₂` — the base change of
  `b₁`, hence smooth by **Stacks 045C** — followed by `h₂`. Precomposition-stability makes the
  last two into one morphism with `P`, and composition-stability joins it to the first;
* the left vertical 1-morphism is the base change of the projection `U₂ ×_𝒴 V₁ → V₁` — the base
  change of `a₂`, hence smooth and surjective on objects — composed with `a₁`, so it is smooth by
  **Stacks 045B** and surjective on objects by **Stacks 06D6**;
* the right vertical 1-morphism is `b₂` itself.

Both projections of the one 2-fibre product square are needed, and **Stacks 045C is stated for
the first projection only**. Rather than transport along
`AlgebraicGeometry.Stack.twoFibreProductSwapMap`, as the modules that need a *specific* model of
the product must, the second projection is read as the first projection of
`CategoryTheory.Bicategory.TwoCommSq.swap` of the same square, which is again a 2-fibre product
by `CategoryTheory.Bicategory.isTwoFibreProduct_swap` and has the same apex on the nose. The two
base-change results then apply to the square and to its swap, and no comparison of apexes
arises.

### The 2-cell

The filler is assembled from the two given 2-cells, the filler of the 2-fibre product square, and
two comparisons of the shape "the 1-morphism attached to a morphism of representing presheaves is
the original 1-morphism, read through the representing equivalence". Each of those two has a
target that is the category of elements of a presheaf, so each is obtained from the uniqueness
half of **Stacks 04SW**: the two sides induce the same morphism of representing presheaves —
by `AlgebraicGeometry.Stack.representingMap_comp`,
`AlgebraicGeometry.Stack.representingMap_associatedMap` and
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap` — and
`AlgebraicGeometry.Stack.morphismSpaceEquiv` is injective. For the second of the two that
computation ends at `CategoryTheory.Limits.pullback.condition`, which is the only thing the
cartesian square of presheaves is used for.

## References

* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Precomposing with the inverse comparison `equivalenceOverInvMap` does not change the
induced morphism of representing presheaves. -/
private theorem representingMap_equivalenceOverInvMap_comp
    {𝒳 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p) (c : 𝒳 ⟶ 𝒞) :
    representingMap B S hS (fibredCategory B S hS F) 𝒞 F G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eG
        (equivalenceOverInvMap B S hS F eF ≫ c) =
      representingMap B S hS 𝒳 𝒞 F G eF eG c := by
  rw [representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := 𝒳) (𝒞 := 𝒞) B S hS F F G
    (StacksRepresentableCFG.EquivalenceOver.refl _) eF eG,
    representingMap_equivalenceOverInvMap, Category.id_comp]

/-- Two 1-morphisms between representable categories inducing the same morphism of presheaves
are isomorphic. -/
private theorem nonempty_iso_of_representingMap_eq (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {f g : fibredCategory B S hS F ⟶ fibredCategory B S hS G}
    (h : representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS G) F G
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) f =
      representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS G) F G
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) g) :
    Nonempty (f ≅ g) :=
  (nonempty_unique_twoIso_of_representingMap_eq B S hS _ _ F G _ _ h).map fun u => u.default

/-- **Stacks 06FP.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under precomposition with a smooth morphism, stable under composition, and whose
restriction to algebraic spaces is stable under base change. The property of 1-morphisms of
categories fibred in groupoids over the big fppf site of `S` that **Stacks 06FN** attaches to `P`
is stable under composition: if `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` both pass the existential
smooth-diagram test of condition (2) of **Stacks 06FM**, then so does `f ≫ g`.

Stacks 06FP assumes `P` smooth local on the source-and-target, which is what makes the property
of Stacks 06FN well behaved; of its three clauses only precomposition-stability is used here, so
the hypothesis is taken in that weaker form and
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget.precomp` is what a caller holding the
full condition supplies. No hypothesis is made on the three categories beyond their being fibred
in groupoids: the diagram is built from the two given ones, so no presentation of `𝒵` is chosen.
See the implementation notes of this module, which also compare this with the sibling
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`. -/
@[stacks 06FP]
theorem hasPropertyOnSomeSmoothDiagram_comp_of_precomp
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hprecomp : ∀ {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hZ : IsAlgebraicSpace B S hS Z₀) (p : X₀ ⟶ Y₀) (q : Y₀ ⟶ Z₀),
      Space.IsSmooth B S hS p → P q → P (p ≫ q))
    (hcomp : ∀ {X₀ Y₀ Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X₀) (_hY : IsAlgebraicSpace B S hS Y₀)
      (_hZ : IsAlgebraicSpace B S hS Z₀) (p : X₀ ⟶ Y₀) (q : Y₀ ⟶ Z₀),
      P p → P q → P (p ≫ q))
    [(spaceProperty B S hS P).IsStableUnderBaseChange]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS P g) :
    HasPropertyOnSomeSmoothDiagram B S hS P (f ≫ g) := by
  classical
  have hsmBC : (spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  have hsuBC : (spaceProperty B S hS
      (fun _ _ k => Space.IsSurjective B S hS k)).IsStableUnderBaseChange :=
    Space.surjectiveMorphismProperty_isStableUnderBaseChange B S hS
  obtain ⟨U₁, V₁, hU₁, hV₁, a₁, b₁, h₁, ⟨η₁⟩, ha₁, ha₁surj, hb₁, hPh₁⟩ := hf
  obtain ⟨U₂, V₂, hU₂, hV₂, a₂, b₂, h₂, ⟨η₂⟩, ha₂, ha₂surj, hb₂, hPh₂⟩ := hg
  -- the one 2-fibre product: `U₂ ×_𝒴 V₁`, over a cospan with both legs representable
  set R : Bicategory.TwoCommSq a₂ b₁ :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} a₂ b₁ with hRdef
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} a₂ b₁
  -- the first projection is the base change of `b₁`, hence smooth (Stacks 045C)
  have hRfstRep : IsRepresentableByAlgebraicSpaces B S hS R.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS V₁) 𝒴 (fibredCategory B S hS U₂) b₁ a₂ R hR hb₁.1
  have hRfstSm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R.fst hRfstRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) (fibredCategory B S hS V₁) 𝒴
      (fibredCategory B S hS U₂) b₁ a₂ R hR hb₁.1 hb₁.2
  -- the second projection is the first projection of the swapped square, hence the base change
  -- of `a₂`: smooth and surjective on objects
  have hRsndRep : IsRepresentableByAlgebraicSpaces B S hS R.snd.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U₂) 𝒴 (fibredCategory B S hS V₁) a₂ b₁ R.swap
      (Bicategory.isTwoFibreProduct_swap hR) ha₂.1
  have hRsndSm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) R.snd hRsndRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) (fibredCategory B S hS U₂) 𝒴
      (fibredCategory B S hS V₁) a₂ b₁ R.swap (Bicategory.isTwoFibreProduct_swap hR)
      ha₂.1 ha₂.2
  have hRsndSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) R.snd hRsndRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U₂) 𝒴
      (fibredCategory B S hS V₁) a₂ b₁ R.swap (Bicategory.isTwoFibreProduct_swap hR) ha₂.1
      ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
        a₂ ha₂.1).1 ha₂surj)
  -- the apex is representable by an algebraic space, by Stacks 0300
  obtain ⟨W, hW, ⟨eW₀⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS (fibredCategory B S hS V₁) 𝒴 (fibredCategory B S hS U₂) b₁ a₂ R hR hb₁.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U₂ hU₂)
  set eW : StacksRepresentableCFG.EquivalenceOver R.pt.val.p
    (presheafOfCategories (W ⋙ typeToCat)).p := eW₀ with heWdef
  set ι : fibredCategory B S hS W ⟶ R.pt := equivalenceOverInvMap B S hS W eW with hιdef
  -- the two projections, read as morphisms of algebraic spaces
  set nfst : W ⟶ U₂ := representingMap B S hS R.pt (fibredCategory B S hS U₂) W U₂ eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) R.fst with hnfstDef
  set nsnd : W ⟶ V₁ := representingMap B S hS R.pt (fibredCategory B S hS V₁) W V₁ eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) R.snd with hnsndDef
  have hnfstSm : Space.IsSmooth B S hS nfst :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS R.fst hRfstRep W U₂ hW hU₂ eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 ⟨hRfstRep, hRfstSm⟩
  have hnsndSm : Space.IsSmooth B S hS nsnd :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS R.snd hRsndRep W V₁ hW hV₁ eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 ⟨hRsndRep, hRsndSm⟩
  have hnsndSu : Space.IsSurjective B S hS nsnd :=
    (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) R.snd hRsndRep W V₁ hW hV₁ eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hRsndSu
  -- the apex of the new diagram: the fibre product `W ×_{V₁} U₁` of algebraic spaces
  have hA : IsAlgebraicSpace B S hS (pullback nsnd h₁) :=
    isAlgebraicSpace_pullback B S hS nsnd h₁ hW hU₁ hV₁
  set qA : pullback nsnd h₁ ⟶ U₁ := pullback.snd nsnd h₁ with hqADef
  set pA : pullback nsnd h₁ ⟶ W := pullback.fst nsnd h₁ with hpADef
  have hcond : pA ≫ nsnd = qA ≫ h₁ := pullback.condition
  have hqASm : Space.IsSmooth B S hS qA :=
    prop_pullbackSnd B S hS (fun _ _ k => Space.IsSmooth B S hS k) hW hV₁ hU₁ nsnd h₁ hnsndSm
  have hqASu : Space.IsSurjective B S hS qA :=
    prop_pullbackSnd B S hS (fun _ _ k => Space.IsSurjective B S hS k) hW hV₁ hU₁ nsnd h₁ hnsndSu
  have hPpA : P pA :=
    prop_of_isPullback B S hS P hprecomp hU₁ hV₁ hW hA h₁ nsnd qA pA
      (IsPullback.of_hasPullback nsnd h₁).flip hPh₁
  -- the left vertical 1-morphism of the new diagram
  have hqARep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS qA).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS qA).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS (pullback nsnd h₁) hA)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U₁ hU₁)
  have hqAmSm : IsRelativelySmooth B S hS (associatedMap B S hS qA).1 :=
    (isRelativelySmooth_iff_isSmooth_representingMap B S hS (associatedMap B S hS qA).1 hqARep
      (pullback nsnd h₁) U₁ hA hU₁ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).2
      (by rw [representingMap_associatedMap]; exact hqASm)
  have hqAmSu : IsSurjectiveOnObjects B S hS
      (fibredCategory B S hS (pullback nsnd h₁)).val.p (fibredCategory B S hS U₁).val.p
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS qA).1) :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
      (associatedMap B S hS qA).1 hqARep).2
      ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) (associatedMap B S hS qA).1 hqARep
        (pullback nsnd h₁) U₁ hA hU₁ (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)).2
        (by rw [representingMap_associatedMap]; exact hqASu))
  -- the two comparisons of a 1-morphism with the one attached to its morphism of presheaves
  have ψ₁ : Nonempty ((associatedMap B S hS nfst).1 ≅ ι ≫ R.fst) :=
    nonempty_iso_of_representingMap_eq B S hS W U₂
      ((representingMap_associatedMap B S hS W U₂ nfst).trans
        (representingMap_equivalenceOverInvMap_comp B S hS W U₂ eW _ R.fst).symm)
  have ψ₂ : Nonempty ((associatedMap B S hS pA).1 ≫ (ι ≫ R.snd) ≅
      (associatedMap B S hS qA).1 ≫ (associatedMap B S hS h₁).1) :=
    nonempty_iso_of_representingMap_eq B S hS (pullback nsnd h₁) V₁ (by
      rw [representingMap_comp (𝒜 := fibredCategory B S hS (pullback nsnd h₁))
        (ℬ := fibredCategory B S hS W) (𝒞 := fibredCategory B S hS V₁) B S hS
        (pullback nsnd h₁) W V₁ (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _), representingMap_associatedMap,
        hιdef, representingMap_equivalenceOverInvMap_comp B S hS W V₁ eW
          (StacksRepresentableCFG.EquivalenceOver.refl _) R.snd,
        ← associatedMap_comp, representingMap_associatedMap, hcond])
  refine ⟨pullback nsnd h₁, V₂, hA, hV₂, (associatedMap B S hS qA).1 ≫ a₁, b₂,
    pA ≫ (nfst ≫ h₂), ?_,
    isRelativelySmooth_comp B S hS (associatedMap B S hS qA).1 a₁ hqAmSm ha₁, ?_, hb₂, ?_⟩
  · obtain ⟨ψ₁⟩ := ψ₁
    obtain ⟨ψ₂⟩ := ψ₂
    -- the 2-cell of the new diagram, over `𝒴` first and then over `𝒵`
    have key : (associatedMap B S hS pA).1 ≫ ((associatedMap B S hS nfst).1 ≫ a₂) ≅
        ((associatedMap B S hS qA).1 ≫ a₁) ≫ f :=
      Bicategory.whiskerLeftIso _ (Bicategory.whiskerRightIso ψ₁ a₂) ≪≫
        Bicategory.whiskerLeftIso _ (Bicategory.associator ι R.fst a₂) ≪≫
        Bicategory.whiskerLeftIso _ (Bicategory.whiskerLeftIso ι R.iso) ≪≫
        Bicategory.whiskerLeftIso _ (Bicategory.associator ι R.snd b₁).symm ≪≫
        (Bicategory.associator (associatedMap B S hS pA).1 (ι ≫ R.snd) b₁).symm ≪≫
        Bicategory.whiskerRightIso ψ₂ b₁ ≪≫
        Bicategory.associator (associatedMap B S hS qA).1 (associatedMap B S hS h₁).1 b₁ ≪≫
        Bicategory.whiskerLeftIso _ η₁ ≪≫
        (Bicategory.associator (associatedMap B S hS qA).1 a₁ f).symm
    rw [associatedMap_comp, associatedMap_comp]
    exact ⟨Bicategory.associator (associatedMap B S hS pA).1
        ((associatedMap B S hS nfst).1 ≫ (associatedMap B S hS h₂).1) b₂ ≪≫
      Bicategory.whiskerLeftIso _ (Bicategory.associator
        (associatedMap B S hS nfst).1 (associatedMap B S hS h₂).1 b₂) ≪≫
      Bicategory.whiskerLeftIso _ (Bicategory.whiskerLeftIso _ η₂) ≪≫
      Bicategory.whiskerLeftIso _
        (Bicategory.associator (associatedMap B S hS nfst).1 a₂ g).symm ≪≫
      (Bicategory.associator (associatedMap B S hS pA).1
        ((associatedMap B S hS nfst).1 ≫ a₂) g).symm ≪≫
      Bicategory.whiskerRightIso key g ≪≫
      Bicategory.associator ((associatedMap B S hS qA).1 ≫ a₁) f g⟩
  · exact isSurjectiveOnObjects_comp B S hS
      (fibredCategory B S hS (pullback nsnd h₁)).val.p (fibredCategory B S hS U₁).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS qA).1)
      (CatFiberedInGroupoids.homFunctor a₁)
      (CatFiberedInGroupoids.homFunctor_comp_p a₁) hqAmSu ha₁surj
  · exact hcomp hA hW hV₂ pA (nfst ≫ h₂) hPpA
      (hprecomp hW hU₂ hV₂ nfst h₂ hnfstSm hPh₂)

end AlgebraicGeometry.Stack

end
