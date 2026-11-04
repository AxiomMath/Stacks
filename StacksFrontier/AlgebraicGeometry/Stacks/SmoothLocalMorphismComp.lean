module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# Composition of a smooth-local property of 1-morphisms of algebraic stacks (Stacks 06FP)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target (**Stacks 06F8**) and whose restriction to algebraic spaces is stable under
composition. **Stacks 06FP** asserts that the induced property of 1-morphisms of algebraic
stacks — the existential smooth-diagram criterion of **Stacks 06FM**, which is
**Definition 06FN** — is stable under composition.

The proof is the source's, and it is the *universal* form of the criterion that makes it short.
Choose a smooth presentation `W ⟶ 𝒵` surjective on objects by an algebraic space; choose a
diagram over `g : 𝒴 ⟶ 𝒵` whose right vertical 1-morphism is that presentation, which the
universal form provides, and whose left vertical 1-morphism is then itself a smooth presentation
`V ⟶ 𝒴` surjective on objects; choose a diagram over `f : 𝒳 ⟶ 𝒴` whose right vertical
1-morphism is *that* one. The two top horizontal morphisms `U ⟶ V` and `V ⟶ W` have `P`, so
their composite has `P` by hypothesis, and the outer square is a diagram over `f ≫ g`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_twoIso_associatedMap_comp`: the 1-morphism attached to a
  composite of morphisms of presheaves is the composite of the attached 1-morphisms.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp`: **Stacks 06FP**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp`: **Stacks 06PX**, the composite of flat
  1-morphisms of algebraic stacks is flat.

## Implementation notes

Prescribing the right vertical 1-morphism of each of the two diagrams is exactly what
`AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram` is for; it is
the source's construction for Stacks 06FM (1) ⇒ (2) with the presentation of the target taken as
data rather than chosen, so nothing of that argument is repeated here. Passing from the
existential form in the hypotheses to the universal form and back is
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` (**Stacks 06FM**), and that
is the only place smooth locality of `P` is used.

The 2-cell of the outer square is the pasting of the two given ones. It needs the 1-morphism
attached to the composite `U ⟶ V ⟶ W` to be the composite of the two attached 1-morphisms, which
is `nonempty_twoIso_associatedMap_comp`: both induce `U ⟶ W` as their morphism of representing
presheaves, so the uniqueness half of **Stacks 04SW** identifies them up to a 2-isomorphism
lying over identities. The rest is three associators.

The composition hypothesis is stated for morphisms of *algebraic spaces* rather than for all
morphisms of presheaves, as the source states it; the three top horizontal morphisms of the
diagrams are morphisms of algebraic spaces, so nothing more is needed.

Stacks 06PX is this result at flatness: the library's **Stacks 06PW**
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` inlines condition (2) at flatness of morphisms
of algebraic spaces, so the bridge
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram` is
`Iff.rfl`, and the two hypotheses are **Stacks 06FC** at the flat case and **Stacks 03MN**.

## References

* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism attached to a composite of morphisms of presheaves is the composite of the
attached 1-morphisms**, up to a 2-isomorphism whose components lie over identities.

Both sides induce `p ≫ q` as their morphism of representing presheaves, read through the
identity comparisons: the left by `AlgebraicGeometry.Stack.representingMap_associatedMap`, the
right by `AlgebraicGeometry.Stack.representingMap_comp` and that computation at each factor. The
uniqueness half of **Stacks 04SW** then produces the 2-isomorphism. -/
theorem nonempty_twoIso_associatedMap_comp
    (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : F ⟶ G) (q : G ⟶ H) :
    Nonempty ((associatedMap B S hS (p ≫ q)).1 ≅
      (associatedMap B S hS p).1 ≫ (associatedMap B S hS q).1) := by
  have hcomp : representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS H) F H
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      ((associatedMap B S hS p).1 ≫ (associatedMap B S hS q).1) =
      representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS H) F H
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (associatedMap B S hS (p ≫ q)).1 := by
    rw [representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := fibredCategory B S hS G)
      (𝒞 := fibredCategory B S hS H) B S hS F G H
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_associatedMap, representingMap_associatedMap,
      representingMap_associatedMap]
  obtain ⟨e, he, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS F) (fibredCategory B S hS H) F H
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hcomp
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e he)⟩

/-- **Stacks 06FP.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
smooth local on the source-and-target and whose restriction to algebraic spaces is stable under
composition. Then the induced property of 1-morphisms of algebraic stacks over `S` — the
existential smooth-diagram criterion of **Stacks 06FM**, which is **Definition 06FN** — is
stable under composition.

The proof is the source's. Choose a smooth presentation `W ⟶ 𝒵`, surjective on objects, by an
algebraic space; then a diagram over `g` whose right vertical 1-morphism is that presentation,
which exists by condition (1) of Stacks 06FM — its left vertical 1-morphism is a smooth
presentation `V ⟶ 𝒴` surjective on objects; then a diagram over `f` whose right vertical
1-morphism is *that* one. The two top horizontal morphisms `U ⟶ V` and `V ⟶ W` have `P` by
condition (1), so their composite has `P` by hypothesis, and the outer square is a diagram over
`f ≫ g` whose left vertical 1-morphism is the one of the diagram over `f` — smooth and
surjective on objects — and whose right vertical 1-morphism is the presentation of `𝒵`. -/
@[stacks 06FP]
theorem hasPropertyOnSomeSmoothDiagram_comp
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hcomp : ∀ {U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
      IsAlgebraicSpace B S hS U → IsAlgebraicSpace B S hS V → IsAlgebraicSpace B S hS W →
      ∀ (p : U ⟶ V) (q : V ⟶ W), P p → P q → P (p ≫ q))
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (h𝒵 : IsAlgebraicStack.{u, w} B S hS 𝒵.val)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS P g) :
    HasPropertyOnSomeSmoothDiagram B S hS P (f ≫ g) := by
  have hfE : HasPropertyOnEverySmoothDiagram B S hS P f :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP h𝒳 h𝒴 f).2 hf
  have hgE : HasPropertyOnEverySmoothDiagram B S hS P g :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hP h𝒴 h𝒵 g).2 hg
  obtain ⟨W, hW, w, hwsm, hwsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS h𝒵
  obtain ⟨V, hV, b, hTopG, ⟨ηG⟩, hbsm, hbsu, hPG⟩ :=
    exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS P h𝒴 h𝒵 g W hW w
      hwsm hwsu hgE
  obtain ⟨U, hU, a, hTopF, ⟨ηF⟩, hasm, hasu, hPF⟩ :=
    exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS P h𝒳 h𝒴 f V hV b
      hbsm hbsu hfE
  obtain ⟨κ⟩ := nonempty_twoIso_associatedMap_comp B S hS U V W hTopF hTopG
  refine ⟨U, W, hU, hW, a, w, hTopF ≫ hTopG, ⟨?_⟩, hasm, hasu, hwsm,
    hcomp hU hV hW hTopF hTopG hPF hPG⟩
  calc (associatedMap B S hS (hTopF ≫ hTopG)).1 ≫ w
      ≅ ((associatedMap B S hS hTopF).1 ≫ (associatedMap B S hS hTopG).1) ≫ w :=
        Bicategory.whiskerRightIso κ w
    _ ≅ (associatedMap B S hS hTopF).1 ≫ ((associatedMap B S hS hTopG).1 ≫ w) :=
        Bicategory.associator _ _ _
    _ ≅ (associatedMap B S hS hTopF).1 ≫ (b ≫ g) := Bicategory.whiskerLeftIso _ ηG
    _ ≅ ((associatedMap B S hS hTopF).1 ≫ b) ≫ g := (Bicategory.associator _ _ _).symm
    _ ≅ (a ≫ f) ≫ g := Bicategory.whiskerRightIso ηF g
    _ ≅ a ≫ (f ≫ g) := Bicategory.associator _ _ _

namespace AlgebraicStacks

/-- **Stacks 06PX.** The composite of two flat 1-morphisms of algebraic stacks over `S` is flat.

Stacks 06PW is condition (2) of Stacks 06FM at flatness of morphisms of algebraic spaces, on the
nose (`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram`), so
this is Stacks 06FP at that property: flatness is smooth local on the source-and-target by
**Stacks 06FC** and stable under composition by **Stacks 03MN**, which is the source's own
proof. -/
@[stacks 06PX]
theorem isFlat_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsFlat B S hS f) (hg : IsFlat B S hS g) :
    IsFlat B S hS (f ≫ g) := by
  rw [isFlat_iff_hasPropertyOnSomeSmoothDiagram]
  exact hasPropertyOnSomeSmoothDiagram_comp.{u, w} B S hS
    (fun _ _ h => Space.IsFlat B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    (fun hU hV hW p q hp hq => Space.isFlat_comp B S hS hU hV hW p q hp hq)
    𝒳.property 𝒴.property 𝒵.property f.hom g.hom
    ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hf)
    ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).1 hg)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
