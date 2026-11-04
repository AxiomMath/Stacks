module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism

/-!
# The smooth-diagram criterion at representable source and target (Stacks 06FM)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target in the sense of **Stacks 06F8**, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` whose source and target are
representable by algebraic spaces `F` and `G`. The third assertion of Stacks 06FM says that `f`
passes the existential smooth-diagram test of its condition (2) exactly when the induced
morphism `F ⟶ G` of representing presheaves has `P`.

The forward implication is
`AlgebraicGeometry.Stack.prop_representingMap_of_hasPropertyOnSomeSmoothDiagram`. The converse is
the source's own argument: *take `V = G` and `U = F`*, that is, test the condition on the one
diagram whose two vertical 1-morphisms are the representing equivalences themselves. This module
builds that diagram and closes the equivalence.

## Main definitions

* `AlgebraicGeometry.Stack.equivalenceOverInvMap`: the 1-morphism from the category of elements
  of a representing presheaf to the category it represents, given by the backward 1-morphism of
  the representing equivalence.

## Main results

* `AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`: that 1-morphism induces the
  identity of the representing presheaf.
* `AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_equivalenceOverInvMap`: it is smooth in the
  sense of Stacks 04XB and surjective on objects in the sense of Stacks 06D4.
* `AlgebraicGeometry.Stack.nonempty_twoIso_equivalenceOverInvMap`: the square it forms with the
  induced morphism of representing presheaves is 2-commutative.
* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`:
  **Stacks 06FM**, the assertion for representable source and target.

## Implementation notes

The four facts above are what the diagram `U = F`, `V = G` needs, and each is a short consequence
of results already in the library.

The identity computation must go through
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj` rather than through the more
convenient `AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_comp_eq`: the latter asks for an
equality of functors of categories of elements, which for the backward 1-morphism of an
equivalence holds only up to isomorphism. On a named section both sides read the element the
object names — `CategoryTheory.PresheafOfCategories.sectionOfObj_refl` on the left and
`CategoryTheory.PresheafOfCategories.sectionOfObj_inv_obj` on the right.

Smoothness of the two vertical 1-morphisms is the §04XB bridge
`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap` read at the identity,
which is smooth by `AlgebraicGeometry.Space.isSmooth_id`; representability of the 1-morphism is
free, since source and target are both representable by algebraic spaces (**Stacks 02ZZ**).
Surjectivity on objects holds with no field extension at all: the required lift of an object `y`
of `𝒳` is the inverse of the unit of the equivalence at `y`, whose components lie over
identities.

The 2-cell is the uniqueness half of **Stacks 04SW**: the two 1-morphisms around the square
induce the same morphism of representing presheaves, by functoriality
(`AlgebraicGeometry.Stack.representingMap_comp`), by
`AlgebraicGeometry.Stack.representingMap_associatedMap` and by the identity computation above, so
the equivalence of Stacks 04SW being injective they are 2-isomorphic.

Neither `AlgebraicGeometry.Stack.IsAlgebraicStack` hypothesis is used: Stacks 06FM states its
third assertion for algebraic stacks, but the argument needs only that source and target are
representable by algebraic spaces. They are kept, with underscored names, because they are part
of the statement of the tagged assertion.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 1-morphism from the category of elements of a presheaf `F` representing a category `𝒳`
fibred in groupoids over the big fppf site of `S` to `𝒳` itself: the backward 1-morphism of the
representing equivalence, read as a 1-morphism of the 2-category of categories fibred in
groupoids.

This is the left vertical arrow of the diagram that the proof of the third assertion of
Stacks 06FM tests condition (2) on, and — applied to the target — its right vertical arrow. -/
def equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    fibredCategory B S hS F ⟶ 𝒳 :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm ⟨eX.inv.functor, eX.inv.w⟩

/-- **The backward 1-morphism of a representing equivalence induces the identity.** Read through
the identity comparison on the source and the given one on the target, the morphism of
representing presheaves induced by `AlgebraicGeometry.Stack.equivalenceOverInvMap` is the
identity of `F`.

A morphism of representing presheaves is determined by its values on named sections, and on the
section named by an object `z` of the category of elements of `F` both sides read off the element
`z` carries: the left by `CategoryTheory.PresheafOfCategories.sectionOfObj_refl` and the right by
`CategoryTheory.PresheafOfCategories.sectionOfObj_inv_obj`. -/
theorem representingMap_equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    representingMap B S hS (fibredCategory B S hS F) 𝒳 F F
        (StacksRepresentableCFG.EquivalenceOver.refl _) eX
        (equivalenceOverInvMap B S hS F eX) = 𝟙 F := by
  refine morphismSpaceEquiv_eq_of_sectionOfObj B S hS (fibredCategory B S hS F) 𝒳 F F
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX _ (𝟙 F) (fun z W hz => ?_)
  subst hz
  exact (PresheafOfCategories.sectionOfObj_inv_obj eX z).symm

/-- **Stacks 02ZZ for the backward 1-morphism of a representing equivalence.** Source and target
are both representable by algebraic spaces, so the 1-morphism is representable by algebraic
spaces. -/
theorem isRepresentableByAlgebraicSpaces_equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsRepresentableByAlgebraicSpaces B S hS (equivalenceOverInvMap B S hS F eX).hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (equivalenceOverInvMap B S hS F eX)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF) ⟨F, hF, ⟨eX⟩⟩

/-- **The backward 1-morphism of a representing equivalence is smooth** in the sense of
Stacks 04XB: by the bridge of Stacks 04XB for represented source and target it is enough that the
morphism of representing presheaves it induces be smooth, and that morphism is the identity. -/
theorem isRelativelySmooth_equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsRelativelySmooth B S hS (equivalenceOverInvMap B S hS F eX) := by
  refine (isRelativelySmooth_iff_isSmooth_representingMap B S hS
    (equivalenceOverInvMap B S hS F eX)
    (isRepresentableByAlgebraicSpaces_equivalenceOverInvMap B S hS F hF eX) F F hF hF
    (StacksRepresentableCFG.EquivalenceOver.refl _) eX).2 ?_
  rw [representingMap_equivalenceOverInvMap]
  exact Space.isSmooth_id B S hS hF

/-- **The backward 1-morphism of a representing equivalence is surjective on objects** in the
sense of Stacks 06D4, and with no field extension: an object `y` of `𝒳` over a field object `U`
is the target of the inverse of the unit of the equivalence at `y`, whose source lies over `U`
and which lies over the identity of `U`. -/
theorem isSurjectiveOnObjects_equivalenceOverInvMap
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p) :
    IsSurjectiveOnObjects B S hS (fibredCategory B S hS F).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor (equivalenceOverInvMap B S hS F eX)) := by
  intro U hU y hy
  refine ⟨U, hU, 𝟙 U, eX.hom.functor.obj y,
    (Functor.congr_obj eX.hom.w y).trans hy, (eX.unitIso.app y).inv, ?_⟩
  have h := eX.isHomLift_unitIso_inv_app y
  rw [hy] at h
  exact h

/-- **The square of a representing pair is 2-commutative.** For `f : 𝒳 ⟶ 𝒴` between categories
represented by `F` and `G`, the 1-morphism attached by Stacks 0458 to the induced morphism
`F ⟶ G` followed by the backward 1-morphism of the comparison of `𝒴` is 2-isomorphic to the
backward 1-morphism of the comparison of `𝒳` followed by `f`.

Both 1-morphisms induce the induced morphism itself: the first by
`AlgebraicGeometry.Stack.representingMap_associatedMap` and the identity computation at `𝒴`, the
second by that computation at `𝒳`. The equivalence of Stacks 04SW is injective, so the two lie in
one 2-isomorphism class. -/
theorem nonempty_twoIso_equivalenceOverInvMap
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) :
    Nonempty ((associatedMap B S hS (representingMap B S hS 𝒳 𝒴 F G eX eY f)).1 ≫
      equivalenceOverInvMap B S hS G eY ≅ equivalenceOverInvMap B S hS F eX ≫ f) := by
  set h := representingMap B S hS 𝒳 𝒴 F G eX eY f with hh
  have hleft : representingMap B S hS (fibredCategory B S hS F) 𝒴 F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY
      ((associatedMap B S hS h).1 ≫ equivalenceOverInvMap B S hS G eY) = h := by
    rw [representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := fibredCategory B S hS G)
      (𝒞 := 𝒴) B S hS F G G (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY,
      representingMap_associatedMap, representingMap_equivalenceOverInvMap, Category.comp_id]
  have hright : representingMap B S hS (fibredCategory B S hS F) 𝒴 F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY
      (equivalenceOverInvMap B S hS F eX ≫ f) = h := by
    rw [representingMap_comp (𝒜 := fibredCategory B S hS F) (ℬ := 𝒳) (𝒞 := 𝒴) B S hS F F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX eY,
      representingMap_equivalenceOverInvMap, Category.id_comp]
  obtain ⟨e, he⟩ := Quotient.exact
    ((morphismSpaceEquiv B S hS (fibredCategory B S hS F) 𝒴 F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY).injective (hleft.trans hright.symm))
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e he)⟩

/-- **The converse half of the third assertion of Stacks 06FM.** If `𝒳` and `𝒴` are representable
by algebraic spaces `F` and `G` and the induced morphism `F ⟶ G` of representing presheaves has
`P`, then `f` passes the existential smooth-diagram test.

The diagram is the source's: `U = F` and `V = G`, with the two representing equivalences as its
vertical 1-morphisms and the induced morphism as its top horizontal morphism. No hypothesis on
`P` is needed for this direction. -/
theorem hasPropertyOnSomeSmoothDiagram_of_prop_representingMap
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴)
    (hprop : P (representingMap B S hS 𝒳 𝒴 F G eX eY f)) :
    HasPropertyOnSomeSmoothDiagram B S hS P f :=
  ⟨F, G, hF, hG, equivalenceOverInvMap B S hS F eX, equivalenceOverInvMap B S hS G eY,
    representingMap B S hS 𝒳 𝒴 F G eX eY f,
    nonempty_twoIso_equivalenceOverInvMap B S hS F G eX eY f,
    isRelativelySmooth_equivalenceOverInvMap B S hS F hF eX,
    isSurjectiveOnObjects_equivalenceOverInvMap B S hS F eX,
    isRelativelySmooth_equivalenceOverInvMap B S hS G hG eY, hprop⟩

/-- **Stacks 06FM, the assertion for representable source and target.** For a property `P` of
morphisms of algebraic spaces over `S` smooth local on the source-and-target, and a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` whose source and target are representable by algebraic
spaces `F` and `G`, the existential smooth-diagram test of condition (2) holds for `f` exactly
when the induced morphism `F ⟶ G` of representing presheaves has `P`.

Forward: the given diagram becomes a diagram of morphisms of algebraic spaces and criterion (3)
of Stacks 06FA applies. Backward: test condition (2) on the diagram given by the two representing
equivalences. -/
@[stacks 06FM "representable source and target"]
theorem hasPropertyOnSomeSmoothDiagram_iff_represented
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (_h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (_h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴) :
    HasPropertyOnSomeSmoothDiagram B S hS P f ↔
      P (representingMap B S hS 𝒳 𝒴 F G eX eY f) :=
  ⟨prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS P hP F G hF hG eX eY f,
    hasPropertyOnSomeSmoothDiagram_of_prop_representingMap B S hS P F G hF hG eX eY f⟩

end AlgebraicGeometry.Stack

end
