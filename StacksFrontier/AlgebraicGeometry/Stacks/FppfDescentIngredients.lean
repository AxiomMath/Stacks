module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# Ingredients for fppf descent of a property of 1-morphisms of algebraic stacks

**Stacks 0DN6** descends a property of morphisms of algebraic spaces which is smooth local on the
source-and-target and fppf local on the target along a surjective, flat, locally finitely
presented 1-morphism of algebraic stacks. Its proof needs three things that this module supplies,
none of which carries a Stacks tag of its own:

* the identity 1-morphism of a category representable by an algebraic space is smooth;
* a smooth 1-morphism out of a category representable by an algebraic space passes the
  existential smooth-diagram test of **Stacks 06FM** for any property holding of the identity of
  that space — which is how "smooth implies flat" and "smooth implies locally of finite
  presentation" are read at the level of algebraic stacks;
* consequently, the composite of a smooth presentation of a base change of a flat (resp. locally
  finitely presented) 1-morphism with that base change induces a flat (resp. locally finitely
  presented) morphism of representing algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isRelativelySmooth_id`: **Stacks 04XB** at an identity.
* `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_id`: the 1-morphism attached to an
  identity morphism of presheaves is 2-isomorphic to the identity.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth`: the
  identity-diagram criterion.
* `AlgebraicGeometry.Stack.isFlat_representingMap_of_isFlat` and its locally-finitely-presented
  companion `…isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation`,
  the two analogues of
  `AlgebraicGeometry.Stack.isSmooth_representingMap_of_isSmooth`.
* `AlgebraicGeometry.Stack.isFlat_representingMap_comp_of_isRelativelySmooth` and its companion
  `…isLocallyOfFinitePresentation_representingMap_comp_of_isRelativelySmooth`.

## Implementation notes

`AlgebraicGeometry.Stack.isRelativelySmooth_id` is stated for a category *representable by an
algebraic space*, which is all its consumers need and is where the proof is one line over
`AlgebraicGeometry.Space.isSmooth_id`: smoothness of a 1-morphism between two such
categories is smoothness of the induced morphism of representing presheaves (**Stacks 04XB**),
and the induced morphism of an identity is an identity. The identity 1-morphism of an arbitrary
category fibred in groupoids is smooth as well, but that statement needs the 2-fibre product of
a scheme-valued point with an identity identified with the point, and no consumer asks for it.

**Stacks 06PW** renders flatness of a 1-morphism of algebraic stacks by the *existential*
smooth-diagram condition and **Stacks 06Q2** part (1) renders local finite presentation by the
*universal* one, so the two composite statements below are not symmetric: the locally finitely
presented one transports each half across the equivalence of conditions (1) and (2) of
**Stacks 06FM**, and the flat one does not.

Base change of the two concrete properties uses **Stacks 06FQ**, whose base-change-stability
hypothesis is supplied locally from the theorems
`AlgebraicGeometry.Space.isFlat_isStableUnderBaseChange` and
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isStableUnderBaseChange`; these are
theorems rather than instances, so the hypothesis is discharged by a local `have` at each use.
The two composite statements pin the source and target algebraic stacks explicitly, because
leaving them to unification makes the elaborator identify `⟨_, _⟩.val` with
`AlgebraicGeometry.Stack.fibredCategory` by `isDefEq` and exceed the heartbeat budget.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04XB at an identity.** The identity 1-morphism of a category fibred in groupoids
over the big fppf site of `S` which is representable by an algebraic space is smooth: it induces
the identity of the representing algebraic space, which is smooth. -/
theorem isRelativelySmooth_id
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRelativelySmooth.{u, u, u + 1} B S hS (𝟙 𝒳) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := h𝒳
  have hrep := isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS (𝟙 𝒳)
    ⟨F, hF, ⟨eF⟩⟩ ⟨F, hF, ⟨eF⟩⟩
  refine (isRelativelySmooth_iff_isSmooth_representingMap B S hS (𝟙 𝒳) hrep F F hF hF eF eF).2 ?_
  rw [representingMap_id]
  exact Space.isSmooth_id B S hS hF

/-- **The 1-morphism attached to an identity morphism of presheaves is 2-isomorphic to the
identity.** Both induce the identity as their morphism of representing presheaves — the left by
`AlgebraicGeometry.Stack.representingMap_associatedMap` and the right by
`AlgebraicGeometry.Stack.representingMap_id` — so the uniqueness half of **Stacks 04SW** produces
the 2-isomorphism. -/
theorem nonempty_twoIso_associatedMap_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Nonempty ((associatedMap B S hS (𝟙 F)).1 ≅ 𝟙 (fibredCategory B S hS F)) := by
  have heq : representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS F) F F
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS (𝟙 F)).1 =
      representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS F) F F
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (𝟙 (fibredCategory B S hS F)) :=
    (representingMap_associatedMap B S hS F F (𝟙 F)).trans
      (representingMap_id B S hS (fibredCategory B S hS F) F
        (StacksRepresentableCFG.EquivalenceOver.refl _)).symm
  obtain ⟨e, he, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS F) (fibredCategory B S hS F) F F
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) heq
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e he)⟩

/-- **The identity-diagram criterion.** A smooth 1-morphism `q` whose source is representable by
an algebraic space `F` passes the existential smooth-diagram test of **Stacks 06FM** for any
property holding of the identity of `F`.

The diagram is the one over `q` whose left vertical 1-morphism is the inverse of the
representability equivalence — smooth and surjective on objects — whose right vertical
1-morphism is that composed with `q`, and whose top horizontal morphism of algebraic spaces is
the identity of `F`. -/
theorem hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (q : 𝒳 ⟶ 𝒴)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hq : IsRelativelySmooth.{u, u, u + 1} B S hS q)
    (hid : P (𝟙 F)) :
    HasPropertyOnSomeSmoothDiagram B S hS P q := by
  obtain ⟨κ⟩ := nonempty_twoIso_associatedMap_id B S hS F
  refine ⟨F, F, hF, hF, equivalenceOverInvMap B S hS F eF,
    equivalenceOverInvMap B S hS F eF ≫ q, 𝟙 F, ⟨?_⟩,
    isRelativelySmooth_equivalenceOverInvMap B S hS F hF eF,
    isSurjectiveOnObjects_equivalenceOverInvMap B S hS F eF,
    isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_equivalenceOverInvMap B S hS F hF eF) hq, hid⟩
  exact Bicategory.whiskerRightIso κ (equivalenceOverInvMap B S hS F eF ≫ q) ≪≫ Iso.refl _

/-- **A flat 1-morphism of algebraic stacks between objects representable by algebraic spaces
induces a flat morphism of those algebraic spaces**, by the equivalence of conditions (2) and (3)
of **Stacks 06FM** at flatness. -/
theorem isFlat_representingMap_of_isFlat {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f) :
    Space.IsFlat B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒳.property 𝒴.property F G hF hG eF eG
    f.hom).mp hf

/-- The equivalence of conditions (1) and (2) of **Stacks 06FM** at local finite presentation. -/
private theorem hasPropertyOnEverySmoothDiagram_lfp_iff_some
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (f : 𝒳 ⟶ 𝒴) :
    HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k) f ↔
    HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k) f :=
  hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) h𝒳 h𝒴 f

/-- **A 1-morphism of algebraic stacks locally of finite presentation between objects
representable by algebraic spaces induces a morphism of those algebraic spaces locally of finite
presentation.** **Stacks 06Q2** part (1) is the universal smooth-diagram condition, so the
hypothesis is first transported across the equivalence of conditions (1) and (2) of
**Stacks 06FM**. -/
theorem isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    Space.IsLocallyOfFinitePresentation B S hS
      (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) 𝒳.property
    𝒴.property F G hF hG eF eG f.hom).mp
      ((hasPropertyOnEverySmoothDiagram_lfp_iff_some.{u, w} B S hS
        𝒳.property 𝒴.property f.hom).1 hf)

/-- **The composite of a smooth presentation of a base change with that base change induces a
flat morphism of algebraic spaces.** If `g` is flat and `Q` is a 2-fibre product of the cospan
`(g, c)` with `c` out of an algebraic space `V`, then `Q.snd` is flat by **Stacks 06FQ**, a
smooth 1-morphism out of an algebraic space `V'` is flat by the identity-diagram criterion
together with `AlgebraicGeometry.Space.isFlat_id`, and the composite is flat by
**Stacks 06PX**. -/
theorem isFlat_representingMap_comp_of_isRelativelySmooth
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (c : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g c) (hQ : Bicategory.IsTwoFibreProduct Q)
    {V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV' : IsAlgebraicSpace B S hS V')
    (b₁ : algebraicSpaceStack.{u, w} B S hS V' hV' ⟶ Q.pt)
    (hb₁sm : IsRelativelySmooth.{u, u, u + 1} B S hS b₁.hom) :
    Space.IsFlat B S hS (representingMap B S hS (fibredCategory B S hS V')
      (fibredCategory B S hS V) V' V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫ Q.snd).hom) := by
  have : (spaceProperty B S hS (fun _ _ k => Space.IsFlat B S hS k)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  refine isFlat_representingMap_of_isFlat.{u, w} B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS V' hV')
    (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) V' V hV' hV
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫ Q.snd) ?_
  refine AlgebraicStacks.isFlat_comp B S hS b₁ Q.snd ?_ ?_
  · exact hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ b₁.hom V' hV'
      (StacksRepresentableCFG.EquivalenceOver.refl _) hb₁sm (Space.isFlat_id B S hS hV')
  · exact hasPropertyOnSomeSmoothDiagram_baseChange.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) g c Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hgflat

/-- **The companion of
`AlgebraicGeometry.Stack.isFlat_representingMap_comp_of_isRelativelySmooth` for local finite
presentation.** **Stacks 06Q2** part (1) is the universal smooth-diagram condition, so each half
is transported across the equivalence of conditions (1) and (2) of **Stacks 06FM** and the
composite is formed by **Stacks 06Q3**. -/
theorem isLocallyOfFinitePresentation_representingMap_comp_of_isRelativelySmooth
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒵 ⟶ 𝒴)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (c : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g c) (hQ : Bicategory.IsTwoFibreProduct Q)
    {V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV' : IsAlgebraicSpace B S hS V')
    (b₁ : algebraicSpaceStack.{u, w} B S hS V' hV' ⟶ Q.pt)
    (hb₁sm : IsRelativelySmooth.{u, u, u + 1} B S hS b₁.hom) :
    Space.IsLocallyOfFinitePresentation B S hS (representingMap B S hS
      (fibredCategory B S hS V') (fibredCategory B S hS V) V' V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫ Q.snd).hom) := by
  have : (spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
    B S hS (𝒳 := algebraicSpaceStack.{u, w} B S hS V' hV')
    (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) V' V hV' hV
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (b₁ ≫ Q.snd) ?_
  refine AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS b₁ Q.snd ?_ ?_
  · exact (hasPropertyOnEverySmoothDiagram_lfp_iff_some.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS V' hV').property Q.pt.property b₁.hom).2
        (hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ b₁.hom V' hV'
          (StacksRepresentableCFG.EquivalenceOver.refl _) hb₁sm
          (Space.isLocallyOfFinitePresentation_id B S hS hV'))
  · exact (hasPropertyOnEverySmoothDiagram_lfp_iff_some.{u, w} B S hS
      Q.pt.property (algebraicSpaceStack.{u, w} B S hS V hV).property Q.snd.hom).2
        (hasPropertyOnSomeSmoothDiagram_baseChange.{u, w} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) g c Q.swap
          (Bicategory.isTwoFibreProduct_swap hQ)
          ((hasPropertyOnEverySmoothDiagram_lfp_iff_some.{u, w} B S hS
            𝒵.property 𝒴.property g.hom).1 hglfp))

end AlgebraicGeometry.Stack

end
