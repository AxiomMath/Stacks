module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Injectives.DerivedCategory.Existence

/-!
# The locally small model of the derived category is the standard one, on the nose on objects

`HasDerivedCategory.{w} C` is the *choice* of a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms with morphisms in `Type w`. A Grothendieck abelian category locally small in
`w` carries two such choices that both occur in this development: `HasDerivedCategory.standard C`,
with morphisms in `max u v`, and `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian C`
(Tag 079Q), with morphisms in `w` — the latter being the one named
`SheafOfModules.hasDerivedCategory` for sheaves of modules, so that a declaration stated in a file
pinning `HasDerivedCategory.standard` and a declaration stated in a file activating that model are
about *different* category structures, even when their objects are the same.

`StacksDraft.DerivedModel.modelEquiv` already compares two arbitrary models. That comparison is
built from `CategoryTheory.Localization.uniq` on the homotopy category, so it is choice-laden and
in particular **not** the identity on objects: it cannot identify a term written at one model with
the *same* term read at the other.

This file supplies the comparison that can. Tag 079Q produces its model by
`MorphismProperty.hasLocalizationOfLocallySmall`, which shrinks the morphisms of the standard
model: the objects are literally the objects of the standard model and the localization functor is
literally the standard one followed by `ShrinkHoms.equivalence`. So the comparison here is
`ShrinkHoms.equivalence` itself, the identity on objects, and the two localization functors agree
on the nose rather than up to isomorphism.

What that buys is the transport of a *derived functor*: `Functor.mapDerivedCategory` is a lift
along the localization functor of the source, so the two models give two lifts of one and the same
functor, and uniqueness of lifts identifies them. Because the comparison is the identity on
objects, the identification reads on an object of the derived category as an isomorphism between
the two derived functors evaluated at the *same* object.

## Main definitions

* `Stacks.Injectives.grothendieckModelEquiv`: **the comparison equivalence** between the standard
  model of the derived category and the model of Tag 079Q.
* `Stacks.Injectives.mapDerivedCategoryModelIso`: the derived functor of an exact functor computed
  at the standard model of its source is the comparison equivalence followed by the derived
  functor computed at the model of Tag 079Q.
* `Stacks.Injectives.mapDerivedCategoryObjIso`: that identification evaluated at an object.

## Main results

* `Stacks.Injectives.grothendieckModelEquiv_functor_obj` and
  `Stacks.Injectives.grothendieckModelEquiv_inverse_obj`: the comparison and its inverse are the
  identity on objects.
* `Stacks.Injectives.grothendieckModelEquiv_comp_Q`: the comparison carries the standard
  localization functor to the one of Tag 079Q, by definition.

## Implementation notes

`locallySmall_standardDerivedCategory` is a one-line application of Mathlib's
`MorphismProperty.locallySmall_of_hasLocalization`: a model with morphisms in `w` exists, and that
alone forces every localization of the same morphism property to be locally `w`-small. The same
fact is proved for an arbitrary model, with a direct K-injective-resolution proof, as the instance
`Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory`; it is not used here
only because that file is not in this one's import closure, and nothing below reproves it.

`LocallySmall` is a `Prop`, so the instance used to put the `ShrinkHoms` category structure on the
standard model cannot disagree with the one baked into Tag 079Q's model: the two are equal by
proof irrelevance, which is exactly what makes `grothendieckModelEquiv` typecheck and
`grothendieckModelEquiv_comp_Q` hold by `rfl`.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u w' v₂ u₂

namespace Stacks.Injectives

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The standard model of the derived category of a Grothendieck abelian category locally small
in `w` is itself locally `w`-small: Tag 079Q provides a model with morphisms in `Type w`, and a
localization of a morphism property is locally `w`-small as soon as one exists. -/
theorem locallySmall_standardDerivedCategory :
    LocallySmall.{w} (@DerivedCategory C _ _ (HasDerivedCategory.standard C)) :=
  let := hasDerivedCategory_of_isGrothendieckAbelian.{w} C
  MorphismProperty.locallySmall_of_hasLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))

attribute [local instance] locallySmall_standardDerivedCategory

/-- **The comparison equivalence between the two models of the derived category** of a
Grothendieck abelian category locally small in `w`: the standard model, with morphisms in
`max u v`, and the model of Tag 079Q, with morphisms in `w`.

The second is obtained from the first by shrinking the morphisms, so the comparison is
`ShrinkHoms.equivalence` and is the identity on objects
(`grothendieckModelEquiv_functor_obj`). -/
def grothendieckModelEquiv :
    @DerivedCategory C _ _ (HasDerivedCategory.standard C) ≌
      @DerivedCategory C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) :=
  ShrinkHoms.equivalence _

/-- The comparison equivalence is the identity on objects. -/
theorem grothendieckModelEquiv_functor_obj
    (X : @DerivedCategory C _ _ (HasDerivedCategory.standard C)) :
    (grothendieckModelEquiv.{w} C).functor.obj X = X := rfl

/-- The inverse of the comparison equivalence is the identity on objects. -/
theorem grothendieckModelEquiv_inverse_obj
    (X : @DerivedCategory C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C)) :
    (grothendieckModelEquiv.{w} C).inverse.obj X = X := rfl

/-- The comparison equivalence carries the standard localization functor to the localization
functor of Tag 079Q's model, by definition. -/
theorem grothendieckModelEquiv_comp_Q :
    (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)) ⋙
        (grothendieckModelEquiv.{w} C).functor =
      @DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) := rfl

variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [hd₂ : HasDerivedCategory.{w'} C₂]
  (F : C ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The derived functor of an exact functor does not depend on the chosen model of the source
derived category.** Both candidates lift `F` on cochain complexes along the localization functor
of their model, the comparison equivalence matches the two localization functors on the nose, and
a lift along a localization is unique up to a unique isomorphism. -/
def mapDerivedCategoryModelIso :
    @Functor.mapDerivedCategory C _ _ (HasDerivedCategory.standard C) C₂ _ _ hd₂ F _ _ _ ≅
      (grothendieckModelEquiv.{w} C).functor ⋙
        @Functor.mapDerivedCategory C _ _
          (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) C₂ _ _ hd₂ F _ _ _ :=
  letI inst := hasDerivedCategory_of_isGrothendieckAbelian.{w} C
  letI model : CochainComplex C ℤ ⥤ @DerivedCategory C₂ _ _ hd₂ :=
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ @DerivedCategory.Q C₂ _ _ hd₂
  letI : Localization.Lifting (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) model
      ((grothendieckModelEquiv.{w} C).functor ⋙
        @Functor.mapDerivedCategory C _ _ inst C₂ _ _ hd₂ F _ _ _) :=
    ⟨@Functor.mapDerivedCategoryFactors C _ _ inst C₂ _ _ hd₂ F _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) model model
    (@Functor.mapDerivedCategory C _ _ (HasDerivedCategory.standard C) C₂ _ _ hd₂ F _ _ _)
    ((grothendieckModelEquiv.{w} C).functor ⋙
      @Functor.mapDerivedCategory C _ _ inst C₂ _ _ hd₂ F _ _ _) (Iso.refl _)

/-- **The two models compute the derived functor of an exact functor at the same object.** This is
`mapDerivedCategoryModelIso` evaluated at an object, which is a comparison at the *same* object
because the comparison equivalence is the identity on objects. -/
def mapDerivedCategoryObjIso
    (Z : @DerivedCategory C _ _ (HasDerivedCategory.standard C)) :
    (@Functor.mapDerivedCategory C _ _ (HasDerivedCategory.standard C) C₂ _ _ hd₂ F _ _ _).obj Z ≅
      (@Functor.mapDerivedCategory C _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) C₂ _ _ hd₂ F _ _ _).obj Z :=
  (mapDerivedCategoryModelIso C F).app Z

end Stacks.Injectives

end
