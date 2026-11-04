module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsPoints

/-!
# Properties of morphisms of algebraic stacks smooth local on the source and target (Stacks 06FM)

Let `P` be a property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target in the sense of **Stacks 06F8**, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S`. Stacks 06FM considers 2-commutative
squares

```
U ---h---> V
|          |
a          b
v          v
𝒳 ---f---> 𝒴
```

in which `U` and `V` are algebraic spaces — read as categories fibred in groupoids through
`AlgebraicGeometry.Stack.fibredCategory` — and the two vertical 1-morphisms are smooth in the
sense of Stacks 04XB, and asserts that the universal test over all such squares whose comparison
to a 2-fibre product is smooth agrees with the existential test over one square whose left
vertical arrow is surjective on objects. This module states those two tests and relates them to
the vocabulary they are consumed in.

## Main definitions

* `AlgebraicGeometry.Stack.spaceProperty`: a property of morphisms of presheaves on the big fppf
  site of `S`, read as a property of morphisms in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.diagramCone`: the square above, as a 2-commutative square over the
  cospan `(b, f)`.
* `AlgebraicGeometry.Stack.HasPropertyOnEverySmoothDiagram`: condition (1) of **Stacks 06FM**.
* `AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram`: condition (2) of **Stacks 06FM**,
  which is also the definition of **Stacks 06FN** of a 1-morphism of algebraic stacks *having*
  the property `P`.

## Main results

* `AlgebraicGeometry.Stack.spaceProperty_eq_inverseImage`: the two spellings of the restriction
  of a presheaf-morphism property to algebraic spaces agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram`: the library's
  **Stacks 06PW** is condition (2) at flatness of morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.prop_representingMap_of_hasPropertyOnSomeSmoothDiagram`: the forward
  half of the third assertion of **Stacks 06FM** — for representable source and target,
  condition (2) implies that the induced morphism of representing presheaves has `P`.

## Implementation notes

The smoothness of the two vertical 1-morphisms is `AlgebraicGeometry.Stack.IsRelativelySmooth`,
the relative property of **Stacks 03YK** at `AlgebraicGeometry.Space.smoothMorphismProperty`;
both instance hypotheses of that notion are discharged for smoothness, so neither test carries a
hypothesis on the smooth property. Surjectivity of the left vertical arrow is surjectivity *on
objects*, `AlgebraicGeometry.Stack.IsSurjectiveOnObjects` (**Stacks 06D4**), the form
**Stacks 06PW** consumes; it is not `AlgebraicGeometry.Space.IsSurjective`, which is surjectivity
on points.

`spaceProperty` is definitionally the inverse image of `P` along the inclusion of the category of
algebraic spaces over `S` into presheaves — that is the content of
`AlgebraicGeometry.Stack.spaceProperty_eq_inverseImage`, proved by `rfl` — so everything the
Stacks 06F9 module proves about the inverse-image spelling is available at this one, and the two
must not be allowed to drift into parallel notions.

`prop_representingMap_of_hasPropertyOnSomeSmoothDiagram` carries no `@[stacks]` attribute
because it is one implication of a statement Stacks 06FM asserts as an equivalence, so it is not
the tag's covering set. The converse — condition (2) from `P` of the induced morphism — needs the
1-morphism attached to the comparison equivalence `eX`, the computation of its induced morphism
of representing presheaves, its surjectivity on objects, and the 2-cell of the resulting square,
with one subtlety among them (the computation must go through
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj`, not through
`..._eq_of_comp_eq`, which asks for an equality of functors that holds only up to isomorphism).

The two tests are abbreviations, so that
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat`
(**Stacks 06PW**), whose body inlines condition (2) at flatness rather than importing it, is the
same proposition on the nose; `isFlat_iff_hasPropertyOnSomeSmoothDiagram` records that by
`Iff.rfl`, which is the bridge needed between the two.

## References

* [Stacks Project, Tag 06F8](https://stacks.math.columbia.edu/tag/06F8)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of presheaves on the big fppf site of `S`, read as a property of
morphisms in the category of algebraic spaces over `S` by applying it to the underlying morphism
of presheaves. -/
abbrev spaceProperty
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ g => P g.hom

/-- `AlgebraicGeometry.Stack.spaceProperty` is the inverse image of `P` along the inclusion of
the category of algebraic spaces over `S` into presheaves, which is the spelling the Stacks 06F9
locality results use. -/
theorem spaceProperty_eq_inverseImage
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    spaceProperty B S hS P =
      P.inverseImage (ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) :=
  rfl

/-- The 2-commutative square over the cospan `(b, f)` attached to a diagram of Stacks 06FM: its
apex is the category fibred in groupoids of `U`, its first projection is the 1-morphism induced
by `h`, its second projection is `a`, and its invertible 2-cell is the given one. This is the
source of the comparison 1-morphisms that condition (1) tests for smoothness. -/
abbrev diagramCone
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f) :
    Bicategory.TwoCommSq b f where
  pt := fibredCategory B S hS U
  fst := (associatedMap B S hS h).1
  snd := a
  iso := η

/-- **Condition (1) of Stacks 06FM.** For every 2-commutative square of algebraic spaces over
`f` whose two vertical 1-morphisms are smooth and whose every comparison 1-morphism to a 2-fibre
product of `(b, f)` is smooth, the top horizontal morphism of algebraic spaces has `P`.

The comparison is tested on every morphism of 2-commutative squares into every 2-fibre product,
which makes the condition independent of the chosen product. -/
abbrev HasPropertyOnEverySmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∀ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hU : IsAlgebraicSpace B S hS U)
    (_hV : IsAlgebraicSpace B S hS V)
    (a : fibredCategory B S hS U ⟶ 𝒳)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f),
      IsRelativelySmooth B S hS a →
      IsRelativelySmooth B S hS b →
      (∀ (Q : Bicategory.TwoCommSq b f)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f a b h η) Q),
          IsRelativelySmooth B S hS k.hom) →
      P h

/-- **Condition (2) of Stacks 06FM, and the definition of Stacks 06FN.** There is a
2-commutative square of algebraic spaces over `f` whose two vertical 1-morphisms are smooth,
whose left vertical 1-morphism is surjective on objects, and whose top horizontal morphism of
algebraic spaces has `P`.

By **Stacks 06FN** this is what it means for a 1-morphism of algebraic stacks to *have the
property* `P`, for `P` smooth local on the source-and-target: Stacks 06FN defines that notion by
the equivalent conditions of Stacks 06FM, and
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some` is that equivalence, so either
condition may serve as the definition. The existential one is taken, because it carries the
diagram data its consumers need. -/
@[stacks 06FN "the definition, as condition (2) of Stacks 06FM"]
abbrev HasPropertyOnSomeSmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hU : IsAlgebraicSpace B S hS U)
    (_hV : IsAlgebraicSpace B S hS V)
    (a : fibredCategory B S hS U ⟶ 𝒳)
    (b : fibredCategory B S hS V ⟶ 𝒴)
    (h : U ⟶ V),
      Nonempty ((associatedMap B S hS h).1 ≫ b ≅ a ≫ f) ∧
      IsRelativelySmooth B S hS a ∧
      IsSurjectiveOnObjects B S hS
        (fibredCategory B S hS U).val.p 𝒳.val.p
        (CatFiberedInGroupoids.homFunctor a) ∧
      IsRelativelySmooth B S hS b ∧ P h

/-- **The forward half of the third assertion of Stacks 06FM.** If `𝒳` and `𝒴` are representable
by algebraic spaces `F` and `G`, and `f : 𝒳 ⟶ 𝒴` passes the existential smooth-diagram test for a
property `P` smooth local on the source-and-target, then the induced morphism `F ⟶ G` of
representing presheaves has `P`.

The given diagram becomes a diagram of morphisms of algebraic spaces: its two vertical
1-morphisms become smooth morphisms by the bridge of Stacks 04XB
(`AlgebraicGeometry.Stack.isRelativelySmooth_iff_isSmooth_representingMap`), its left vertical
1-morphism becomes surjective on points by
`AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjectiveOnObjects`, and its 2-cell
becomes a commuting square by
`AlgebraicGeometry.Stack.representingMap_square_comm`. That is exactly criterion (3) of
Stacks 06FA — one smooth diagram surjective on the source — which is equivalent to `P` itself.

The converse is not proved here; see the implementation notes. -/
theorem prop_representingMap_of_hasPropertyOnSomeSmoothDiagram
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eX : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    P (representingMap B S hS 𝒳 𝒴 F G eX eY f) := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hsurj, hb, hPh⟩ := hf
  obtain ⟨harep, hapr⟩ := ha
  obtain ⟨hbrep, hbpr⟩ := hb
  refine ((Space.smoothLocalOnSourceAndTarget_tfae.{u, u, u} B S hS P hP hF hG
    (representingMap B S hS 𝒳 𝒴 F G eX eY f)).out 3 1).mp ?_
  refine ⟨U, V, hU, hV,
      representingMap B S hS (fibredCategory B S hS U) 𝒳 U F
        (StacksRepresentableCFG.EquivalenceOver.refl _) eX a,
      representingMap B S hS (fibredCategory B S hS V) 𝒴 V G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eY b,
      h, ?_, ?_, ?_, ?_, hPh⟩
  · exact (isRelativelySmooth_iff_isSmooth_representingMap B S hS a harep U F hU hF
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX).1 ⟨harep, hapr⟩
  · exact isSurjective_representingMap_of_isSurjectiveOnObjects B S hS a U F
      (StacksRepresentableCFG.EquivalenceOver.refl _) eX hsurj
  · exact (isRelativelySmooth_iff_isSmooth_representingMap B S hS b hbrep V G hV hG
      (StacksRepresentableCFG.EquivalenceOver.refl _) eY).1 ⟨hbrep, hbpr⟩
  · exact representingMap_square_comm B S hS f F G eX eY a b h η

namespace AlgebraicStacks

/-- The library's **Stacks 06PW** is condition (2) of Stacks 06FM at flatness of morphisms of
algebraic spaces over `S`. Its body inlines that condition rather than importing it, so the two
are the same proposition and the identification is `Iff.rfl`. -/
theorem isFlat_iff_hasPropertyOnSomeSmoothDiagram
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsFlat B S hS f ↔
      HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ h => Space.IsFlat B S hS h) f.hom :=
  Iff.rfl

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
