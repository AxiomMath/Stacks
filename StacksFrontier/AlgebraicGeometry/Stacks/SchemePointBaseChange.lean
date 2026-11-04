module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeSlice
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeElementsProjection

/-!
# Scheme-valued points and the representing presheaf of a base change along one

Let `U` be a scheme over `S` in a big fppf site `B`. The big fppf site of `U` is a category
fibred in groupoids over the big fppf site of `S` (`AlgebraicGeometry.Stack.schemeSlice`), and a
scheme-valued point of a category `𝒴` fibred in groupoids over the big fppf site of `S` is
exactly a 1-morphism out of it (`AlgebraicGeometry.Stack.schemeSliceMap`). This file supplies the
two facts about such points that Stacks 04XC needs.

The first is that a *section* of a representing presheaf over `U` is such a point: if `𝒵` is
represented by `G`, then every `a : h_U ⟶ G` is the morphism of representing presheaves induced
by a 1-morphism `U → 𝒵`, because the bijection of Stacks 04SW is onto
(`AlgebraicGeometry.Stack.schemePointMap`).

The second is the representing presheaf of the base change of `f : 𝒳 ⟶ 𝒴` along a point
`y : U → 𝒴`. That base change lives over the big fppf site of `U`, so it is represented by a
presheaf `T` on that site, compared with the *first projection* of the 2-fibre product; what a
property of morphisms of algebraic spaces over `S` sees is the lower-shriek extension `Λ_U T` of
Stacks 03I5, compared with the *structure functor* of the 2-fibre product
(`AlgebraicGeometry.Stack.relocalizeFibreEquivalence`). The morphism of representing presheaves
induced by the first projection of the 2-fibre product is then the structural morphism
`Λ_U T ⟶ h_U` of the lower-shriek extension
(`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`).

## Main definitions

* `AlgebraicGeometry.Stack.schemeSliceMap`: a scheme-valued point of `𝒴`, as a 1-morphism.
* `AlgebraicGeometry.Stack.schemePointMap`: the point named by a section of a representing
  presheaf.
* `AlgebraicGeometry.Stack.relocalizeFibreEquivalence`: the lower-shriek extension of a presheaf
  representing a base change represents it over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Stack.representingMap_schemePointMap`: the morphism of representing
  presheaves induced by `AlgebraicGeometry.Stack.schemePointMap` is the given section.
* `AlgebraicGeometry.Stack.representingMap_relocalizeFibre`: the morphism of representing
  presheaves induced by the first projection of the 2-fibre product is
  `CategoryTheory.OverShriek.relocalizeToYoneda`.

## Implementation notes

`AlgebraicGeometry.Stack.schemePointMap` is `CategoryTheory.Quotient.out` of the inverse
bijection of Stacks 04SW, so that `representingMap_schemePointMap` is
`Equiv.apply_symm_apply` after `Quotient.out_eq`; no 1-morphism has to be written down by hand.

`AlgebraicGeometry.Stack.relocalizeFibreEquivalence` is the composite of
`StacksRepresentableCFG.EquivalenceOver.compRight` along `CategoryTheory.Over.map U.hom` with
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`, read through
`CategoryTheory.TwoFibreProductOver.fst_comp_eq` by
`StacksRepresentableCFG.EquivalenceOver.ofEq`: the first projection composed with the structure
functor of the first factor is the structure functor of the 2-fibre product, but only up to that
equality, not syntactically.

The proof of `representingMap_relocalizeFibre` is then the commuting-square criterion
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_comp_eq`, whose hypothesis holds because
`CategoryTheory.PresheafOfCategories.relocalizeToElements` followed by the functor of categories
of elements induced by the structural morphism of the extension *is*
`CategoryTheory.PresheafOfCategories.overMapToElements`, by definition.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

section Point

variable {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- A scheme-valued point of `𝒴`, read as a 1-morphism from the big fppf site of `U` viewed as a
category fibred in groupoids over the big fppf site of `S`. -/
def schemeSliceMap (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) : schemeSlice B S hS U ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom ⟨y, hy⟩

/-- The functor underlying `AlgebraicGeometry.Stack.schemeSliceMap` is the given point. -/
@[simp] lemma homFunctor_schemeSliceMap (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    CatFiberedInGroupoids.homFunctor (schemeSliceMap B S hS U y hy) = y :=
  rfl

end Point

section SchemePoint

variable {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eG : StacksRepresentableCFG.EquivalenceOver 𝒵.val.p
    (presheafOfCategories (G ⋙ typeToCat)).p)

/-- The scheme-valued point of `𝒵` named by a section `a : h_U ⟶ G` of its representing
presheaf: a 1-morphism from the big fppf site of `U` to `𝒵` whose induced morphism of
representing presheaves is `a`, chosen from the 2-isomorphism class that Stacks 04SW attaches
to `a`. -/
noncomputable def schemePointMap (a : yoneda.obj U ⟶ G) : schemeSlice B S hS U ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom
    ⟨(Quotient.out ((morphismSpaceEquiv B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
        (schemeSliceEquivalenceOver B S hS U) eG).symm a)).1,
      (Quotient.out ((morphismSpaceEquiv B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
        (schemeSliceEquivalenceOver B S hS U) eG).symm a)).2⟩

/-- **The scheme-valued points of a represented stack are the sections of its representing
presheaf.** The morphism of representing presheaves induced by the point named by `a` is `a`. -/
theorem representingMap_schemePointMap (a : yoneda.obj U ⟶ G) :
    representingMap B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
        (schemeSliceEquivalenceOver B S hS U) eG (schemePointMap B S hS U G eG a) = a := by
  set e := morphismSpaceEquiv B S hS (schemeSlice B S hS U) 𝒵 (yoneda.obj U) G
    (schemeSliceEquivalenceOver B S hS U) eG with he
  have hout : (⟨CatFiberedInGroupoids.homFunctor (schemePointMap B S hS U G eG a),
      CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS U G eG a)⟩ :
      {H : (schemeSlice B S hS U).val.obj ⥤ 𝒵.val.obj //
        H ⋙ 𝒵.val.p = (schemeSlice B S hS U).val.p}) = Quotient.out (e.symm a) :=
    Subtype.ext rfl
  show e (Quotient.mk _ _) = a
  rw [hout, Quotient.out_eq]
  exact e.apply_symm_apply a

end SchemePoint

section RelocalizeFibre

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
  (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
  (e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
      (CatFiberedInGroupoids.homFunctor f))
    (presheafOfCategories (T ⋙ typeToCat)).p)

/-- **The lower-shriek extension of a presheaf representing a base change represents it over the
big fppf site of `S`.** A presheaf `T` on the big fppf site of `U` representing the first
projection of the 2-fibre product of `f` with a point `y : U → 𝒴` has its lower-shriek extension
`Λ_U T` of Stacks 03I5 representing the *structure functor* of that 2-fibre product. -/
noncomputable def relocalizeFibreEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (presheafOfCategories
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T ⋙ typeToCat)).p :=
  ((e.compRight (Over.map U.hom)).trans
    (PresheafOfCategories.relocalizeElementsEquivalenceOver U.hom T)).ofEq
      TwoFibreProductOver.fst_comp_eq

/-- The forward 1-morphism of `AlgebraicGeometry.Stack.relocalizeFibreEquivalence` is the given
one followed by `CategoryTheory.PresheafOfCategories.relocalizeToElements`. -/
lemma relocalizeFibreEquivalence_hom_functor :
    (relocalizeFibreEquivalence B S hS U f y T e).hom.functor =
      e.hom.functor ⋙ PresheafOfCategories.relocalizeToElements U.hom T :=
  StacksRepresentableCFG.EquivalenceOver.ofEq_hom_functor _ _

/-- The commuting square of 1-morphisms behind
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`: the forward 1-morphism of
`AlgebraicGeometry.Stack.relocalizeFibreEquivalence`, followed by the functor of categories of
elements induced by the structural morphism of the lower-shriek extension, is the first
projection of the 2-fibre product followed by the forward 1-morphism of the equivalence
presenting the big fppf site of `U` as a category of elements. -/
lemma relocalizeFibreEquivalence_comp_elementsMap :
    (relocalizeFibreEquivalence B S hS U f y T e).hom.functor ⋙
        PresheafOfCategories.elementsMap (OverShriek.relocalizeToYoneda U.hom T) =
      TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f) ⋙
        PresheafOfCategories.overMapToElements U.hom := by
  rw [relocalizeFibreEquivalence_hom_functor]
  have h₁ : (e.hom.functor ⋙ PresheafOfCategories.relocalizeToElements U.hom T) ⋙
        PresheafOfCategories.elementsMap (OverShriek.relocalizeToYoneda U.hom T) =
      e.hom.functor ⋙ (presheafOfCategories (T ⋙ typeToCat)).p ⋙
        PresheafOfCategories.overMapToElements U.hom :=
    congrArg (fun k => e.hom.functor ⋙ k)
      (PresheafOfCategories.relocalizeToElements_comp_elementsMap U.hom T)
  have h₂ : e.hom.functor ⋙ (presheafOfCategories (T ⋙ typeToCat)).p ⋙
        PresheafOfCategories.overMapToElements U.hom =
      TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f) ⋙
        PresheafOfCategories.overMapToElements U.hom :=
    congrArg (fun k => k ⋙ PresheafOfCategories.overMapToElements U.hom) e.hom.w
  exact h₁.trans h₂

/-- **Stacks 04SW for the base change along a scheme-valued point.** With the 2-fibre product of
`y` and `f` represented by `Λ_U T` and the big fppf site of `U` represented by `h_U`, the
morphism of representing presheaves induced by the first projection of the 2-fibre product is the
structural morphism `Λ_U T ⟶ h_U` of the lower-shriek extension. -/
theorem representingMap_relocalizeFibre (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).pt
        (schemeSlice B S hS U)
        ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
        (relocalizeFibreEquivalence B S hS U f y T e)
        (schemeSliceEquivalenceOver B S hS U)
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).fst =
      OverShriek.relocalizeToYoneda U.hom T :=
  morphismSpaceEquiv_eq_of_comp_eq B S hS _ _ _ _ _ _ _ _
    (relocalizeFibreEquivalence_comp_elementsMap B S hS U f y T e)

end RelocalizeFibre

end AlgebraicGeometry.Stack

end
