module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation

/-!
# The big fppf site of a scheme is a Deligne-Mumford stack (Stacks 03YS, part (3))

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a scheme over `S` in that
site. The big fppf site of `X`, read as a category fibred in groupoids over the big fppf site of
`S`, is an algebraic stack, and in fact a Deligne-Mumford stack.

Stacks derives this from part (2) by remarking that `(Sch/X)_fppf` *is* the category of elements
of the algebraic space `yoneda.obj X`, which in this library is an equivalence over the site
rather than an equality, so transporting part (2) would need Stacks 03YQ. It is cheaper, and
closer to the source's own proof of part (2), to run that proof again with `X` in place of the
atlas: three of the four clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` hold for any
category fibred in groupoids representable by an algebraic space, which `(Sch/X)_fppf` is by
Stacks 04SV, and the presentation clause is satisfied by the **identity** 1-morphism, whose
relative test is the test of the identity of `yoneda.obj X` — surjective, smooth and étale.

That last step is `AlgebraicGeometry.Stack.prop_identityPresentation`: the 2-fibre product of a
scheme-valued point with the identity of `(Sch/X)_fppf` is, over the site of the point, the one
taken with the 1-morphism `(Sch/X)_fppf ⟶ S_{h_X}` induced by the identity of `yoneda.obj X`,
because the two differ only by postcomposing both legs with an equivalence over the site
(`CategoryTheory.TwoFibreProductOver.mapBase`). So the instance of Stacks 045A for
categories of elements, `AlgebraicGeometry.Stack.prop_presentationBasedFunctor`, applies
unchanged.

## Main results

* `AlgebraicGeometry.Stack.prop_identityPresentation`: the presentation clause of
  `AlgebraicGeometry.Stack.IsAlgebraicStack` for the identity 1-morphism of `(Sch/X)_fppf` and
  an arbitrary property of morphisms of algebraic spaces over `S` stable under base change.
* `AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`: **Stacks 026O** for
  `(Sch/X)_fppf`.
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_schemeFibredCategory`: **Stacks 03YS**,
  part (3).
* `AlgebraicGeometry.Stack.schemeStack`: `(Sch/X)_fppf` as an object of the 2-category of
  algebraic stacks over `S`.

## Implementation notes

No locality hypothesis on the property is used, exactly as in part (2): the relative test is
identified with the test of one fixed morphism, not glued from a covering, so the combined
surjective-and-smooth and surjective-and-étale conditions — for which no
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instance is available — can be discharged.

The descent universe of the stack condition is free, since `(Sch/X)_fppf` is a stack in sets at
every descent universe.

The three relative properties of the identity that the presentation clause needs are stated,
for an arbitrary presheaf on the big fppf site of `S`, outside this file:
`AlgebraicGeometry.Space.isSurjective_id` and `AlgebraicGeometry.Space.isEtale_id` in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeNormalization.lean` and
`AlgebraicGeometry.Space.isSmooth_id` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothLocalProperties.lean`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 041D](https://stacks.math.columbia.edu/tag/041D)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PresheafOfCategories

namespace CategoryTheory.PresheafOfCategories

universe vE uE aE

/-- **The functor of categories of elements induced by the identity of a presheaf is an
equivalence.** It is the identity on objects and keeps the base of a morphism, so fullness and
faithfulness are `CategoryTheory.PresheafOfCategories.elements_hom_ext` and essential
surjectivity is trivial. It is not stated as an equality with the identity functor, because the
fibre component of a morphism of a category of elements lies in a discrete category and two such
components are equal only propositionally. -/
theorem isEquivalence_elementsMap_id {C : Type uE} [Category.{vE} C] (F : Cᵒᵖ ⥤ Type aE) :
    (elementsMap (𝟙 F)).IsEquivalence := by
  have : (elementsMap (𝟙 F)).Faithful :=
    ⟨fun {_ _} u w h => elements_hom_ext u w (congrArg (fun k => k.base) h)⟩
  have : (elementsMap (𝟙 F)).Full := ⟨fun f => ⟨f, elements_hom_ext _ _ rfl⟩⟩
  have : (elementsMap (𝟙 F)).EssSurj := ⟨fun Z => ⟨Z, ⟨Iso.refl _⟩⟩⟩
  exact Functor.IsEquivalence.mk

end CategoryTheory.PresheafOfCategories

namespace CategoryTheory.TwoFibreProductOver

universe vC vT vA vB vD uC uT uA uB uD

/-- **Changing the target of a 2-fibre product over `𝒞` along an equivalence over `𝒞` does not
change its first projection, up to equivalence over the first factor.** This is
`CategoryTheory.TwoFibreProductOver.mapBase`, which commutes with the first projection on the
nose, read through
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`; it is the companion of
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source`, which moves the
second factor instead. -/
theorem nonempty_equivalenceOver_mapBase {𝒞 : Type uC} [Category.{vC} 𝒞]
    {T : Type uT} [Category.{vT} T] {𝒜 : Type uA} [Category.{vA} 𝒜]
    {ℬ : Type uB} [Category.{vB} ℬ] {𝒟 : Type uD} [Category.{vD} 𝒟]
    {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}
    (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒟) (hb : b ⋙ p𝒟 = pℬ) [Functor.IsEquivalence b]
    (h : (fst pT p𝒜 pℬ G F).IsFiberedInGroupoids)
    (h' : (fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b)).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (fst pT p𝒜 pℬ G F)
      (fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b))) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h h'
    (mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb) (mapBase_comp_fst G F b hb)
    (isEquivalence_mapBase hb)

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Stack

/-- **The presentation clause of Stacks 026O for the identity 1-morphism of `(Sch/X)_fppf`.**
Let `P` be a property of morphisms of algebraic spaces over `S` stable under base change which
holds for the identity of the algebraic space `yoneda.obj X` of Stacks 025Z. Then every
algebraic space representing the base change of the identity 1-morphism of `(Sch/X)_fppf` along
a scheme-valued point of `(Sch/X)_fppf` has structural morphism with `P`.

Postcomposing both legs of that 2-fibre product with the 1-morphism
`AlgebraicGeometry.Stack.presentationBasedFunctor` of the identity of `yoneda.obj X` — an
equivalence over the site, being the equivalence of Stacks 04SV between the slice and the
category of elements of the presheaf it represents — changes neither the first projection nor
the representing presheaf, so this is
`AlgebraicGeometry.Stack.prop_presentationBasedFunctor`. -/
theorem prop_identityPresentation
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    (X : BigFppfOver B S hS)
    (hP : P (ObjectProperty.homMk (𝟙 (yoneda.obj X)) :
      (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩))
    (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ (schemeFibredCategory B S hS X).val.obj)
    (hy : y ⋙ (schemeFibredCategory B S hS X).val.p = Over.map V.hom)
    (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
    (hG : IsAlgebraicSpace B V.left.1 V.left.2 G)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) (schemeFibredCategory B S hS X).val.p
        (schemeFibredCategory B S hS X).val.p y
        (BasedFunctor.id (schemeFibredCategory B S hS X).val).toFunctor)
      (presheafOfCategories (G ⋙ typeToCat)).p)) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) := by
  have : Functor.IsEquivalence (sliceToElements X) :=
    (sliceElementsEquivalenceOver X).isEquivalence_hom_functor
  have := isEquivalence_elementsMap_id (yoneda.obj X)
  set Φ := presentationBasedFunctor B S hS X (𝟙 (yoneda.obj X))
  have hbe : Functor.IsEquivalence Φ.toFunctor :=
    inferInstanceAs (Functor.IsEquivalence
      (sliceToElements X ⋙ elementsMap (𝟙 (yoneda.obj X))))
  have hy' : (y ⋙ Φ.toFunctor) ⋙ (fibredCategory B S hS (yoneda.obj X)).val.p =
      Over.map V.hom := by
    rw [Functor.assoc, Φ.w, hy]
  exact prop_presentationBasedFunctor B S hS P X (isAlgebraicSpace_yoneda B S hS X)
    (𝟙 (yoneda.obj X)) hP V (y ⋙ Φ.toFunctor) hy' G hG
    (he.map fun e => (TwoFibreProductOver.nonempty_equivalenceOver_mapBase y
      (BasedFunctor.id (schemeFibredCategory B S hS X).val).toFunctor Φ.toFunctor Φ.w
      (fst_isFiberedInGroupoids_overMap V.hom _ _ y _
        (schemeFibredCategory B S hS X).isFiberedInGroupoids
        (schemeFibredCategory B S hS X).isFiberedInGroupoids hy
        (BasedFunctor.id (schemeFibredCategory B S hS X).val).w)
      (fst_isFiberedInGroupoids_overMap V.hom _ _ _ _
        (schemeFibredCategory B S hS X).isFiberedInGroupoids
        (fibredCategory B S hS (yoneda.obj X)).isFiberedInGroupoids hy' Φ.w)).some.symm.trans e)

/-- **Stacks 026O for the big fppf site of a scheme over `S`.** The big fppf site of a scheme
`X` over `S`, read as a category fibred in groupoids over the big fppf site of `S`, is an
algebraic stack.

It is representable by the algebraic space `yoneda.obj X` by Stacks 04SV, so it is a stack in
groupoids and its diagonal is representable by algebraic spaces; the identity 1-morphism
presents it, being representable by algebraic spaces by Stacks 02ZZ and surjective and smooth
by `AlgebraicGeometry.Stack.prop_identityPresentation`.

Taken at `X = S/S'` for a morphism `g : S ⟶ S'` of the site, this is the clause of the
2-categorical correspondence of Stacks 04X5 asserting that the base of the right-hand
2-category is itself an algebraic stack over `S'`; the rest of that correspondence is in
`StacksFrontier/AlgebraicGeometry/Stacks/ChangeOfBaseCorrespondence.lean`. -/
@[stacks 04X5 "the stack of a scheme of the big fppf site is algebraic"]
theorem isAlgebraicStack_schemeFibredCategory (X : BigFppfOver B S hS) :
    IsAlgebraicStack.{u, w} B S hS (schemeFibredCategory B S hS X).val := by
  refine ⟨(schemeFibredCategory B S hS X).isFiberedInGroupoids,
    ⟨isStack_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X),
     isStackInGroupoids_of_isRepresentableByAlgebraicSpace.{u, w} B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X)⟩,
    isRepresentableByAlgebraicSpaces_diagonalBasedFunctor B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X),
    X, BasedFunctor.id _,
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X) X (BasedFunctor.id _),
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_identityPresentation B S hS (Space.surjectiveMorphismProperty B S hS) X
      (Space.isSurjective_id B S hS (yoneda.obj X)) V y hy G hG he
  · exact prop_identityPresentation B S hS (Space.smoothMorphismProperty B S hS) X
      (Space.isSmooth_id B S hS (isAlgebraicSpace_yoneda B S hS X)) V y hy G hG he

/-- **Stacks 03YS, part (3).** The big fppf site of a scheme `X` over `S`, read as a category
fibred in groupoids over the big fppf site of `S`, is a Deligne-Mumford stack.

It is an algebraic stack by
`AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`, and the same identity
1-morphism presents it étale-ly, since the identity of `yoneda.obj X` is surjective and
étale. -/
@[stacks 03YS "part (3)"]
theorem isDeligneMumfordStack_schemeFibredCategory (X : BigFppfOver B S hS) :
    IsDeligneMumfordStack.{u, w} B S hS (schemeFibredCategory B S hS X).val := by
  refine ⟨isAlgebraicStack_schemeFibredCategory.{u, w} B S hS X,
    (schemeFibredCategory B S hS X).isFiberedInGroupoids, X,
    Bicategory.InducedBicategory.mkHom (BasedFunctor.id _),
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X) X (BasedFunctor.id _),
    fun V y hy G hG he => ⟨?_, ?_⟩⟩
  · exact prop_identityPresentation B S hS (Space.surjectiveMorphismProperty B S hS) X
      (Space.isSurjective_id B S hS (yoneda.obj X)) V y hy G hG he
  · exact prop_identityPresentation B S hS (Space.etaleMorphisms B S hS) X
      (Space.isEtale_id B S hS (yoneda.obj X)) V y hy G hG he

/-- **The big fppf site of a scheme `X` over `S`, regarded as an algebraic stack over `S`**,
together with `AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`. This is the
object the lisse-étale site of Stacks 0787 and the structure morphism of Stacks 050D are formed
from. -/
abbrev schemeStack (X : BigFppfOver B S hS) : AlgebraicStacks.{u, w} B S hS :=
  ⟨schemeFibredCategory B S hS X, isAlgebraicStack_schemeFibredCategory.{u, w} B S hS X⟩

end Stack

end AlgebraicGeometry

end
