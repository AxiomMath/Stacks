module

public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomContravariant
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPull

/-!
# The presheaf of a semi-representable object over `X`, and localization push-pull

For a semi-representable object `Z = {Z_i → X}` of `C` over an object `X`, two presheaves on `C`
are attached to `Z` in the literature, by two different routes:

* the coproduct of the universe-lifted representables of the underlying objects,
  `associatedPresheafFunctorOver`, which is the presheaf whose augmentation towards the
  representable presheaf of `X` carries the local-surjectivity conditions of Stacks 01G9; and
* the semi-representable presheaf `FormalCoproduct.yoneda` of the semi-representable object
  `{Z_i}` of `C` obtained by forgetting the structure morphisms, which is the presheaf whose
  sheafification appears in the push-pull identification of Stacks 0D86.

For a small site, that is for `C : Type u` with `Category.{u} C` and index universe `u`, the two
agree: the index and hom universes coincide, so the universe lift in the first is redundant, and
forgetting the structure morphisms of `Z` componentwise is `mapFormalCoproduct (Over.forget X)`.
This file records that identification and transports Stacks 0D86 and the coproduct decomposition
of the sheafification across it, so that a local-surjectivity statement about the first presheaf
and a push-pull statement about the second are statements about the same objects.

## Main results

* `Stacks.CategoryTheory.Hypercovering.associatedPresheafFunctorOver_eq`: the presheaf functor of
  Stacks 01G9 is the universe-lifted semi-representable presheaf functor of `C` precomposed with
  forgetting the structure morphisms.
* `Stacks.CategoryTheory.Hypercovering.associatedPresheafFunctorOverIsoYoneda`: at a small site it
  is the semi-representable presheaf functor itself precomposed with that forgetful functor, the
  universe lift being redundant.
* `Stacks.CategoryTheory.Hypercovering.sheafifiedAssociatedPresheafOverIso`: the sheafification of
  the presheaf of `Z` is the coproduct of the sheafifications of the representables of the
  underlying objects of the components of `Z`.
* `Stacks.CategoryTheory.Hypercovering.localizationPushforwardPullbackNatIsoSheafHomOver`:
  **Stacks 0D86 for that presheaf**, the product of the localization push-pull functors at the
  underlying objects of the components of `Z` is the internal hom out of its sheafification.

## Implementation notes

The identification of the two presheaf functors is an equality, not merely an isomorphism, once
the universe lift is left in place: both send `Z` to the coproduct over the index type of `Z` of
the universe-lifted representables of the underlying objects. The isomorphism enters only when
the lift is removed, and is `uliftYonedaIsoYoneda` applied inside `FormalCoproduct.eval`.

Transporting Stacks 0D86 needs the internal hom to be functorial in its *source*, which is
`CategoryTheory.SheafHomAdj.sheafHomFunctorMapIso`.

## References

* [Stacks Project, Tag 01G9](https://stacks.math.columbia.edu/tag/01G9)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.OverShriek

universe u

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C]

/-- The presheaf attached to a semi-representable object over `X` is the universe-lifted
semi-representable presheaf of the semi-representable object of `C` obtained by forgetting the
structure morphisms: both are the coproduct, over the index type, of the universe-lifted
representables of the underlying objects. -/
theorem associatedPresheafFunctorOver_eq (X : C) :
    (associatedPresheafFunctorOver (X := X) :
        FormalCoproduct.{u} (Over X) ⥤ Cᵒᵖ ⥤ Type u) =
      mapFormalCoproduct (Over.forget X) ⋙
        (FormalCoproduct.uliftYoneda : FormalCoproduct.{u} C ⥤ Cᵒᵖ ⥤ Type u) :=
  rfl

/-- On a small site the universe lift in `associatedPresheafFunctorOver` is redundant: the
presheaf attached to a semi-representable object over `X` is the semi-representable presheaf of
the underlying semi-representable object of `C`. -/
def associatedPresheafFunctorOverIsoYoneda (X : C) :
    (associatedPresheafFunctorOver (X := X) :
        FormalCoproduct.{u} (Over X) ⥤ Cᵒᵖ ⥤ Type u) ≅
      mapFormalCoproduct (Over.forget X) ⋙
        (FormalCoproduct.yoneda : FormalCoproduct.{u} C ⥤ Cᵒᵖ ⥤ Type u) :=
  eqToIso (associatedPresheafFunctorOver_eq X) ≪≫
    Functor.isoWhiskerLeft _ ((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type u)).mapIso uliftYonedaIsoYoneda)

/-- Sheafifying the presheaf attached to a semi-representable object `Z` over `X` gives the
coproduct of the sheafifications of the representables of the underlying objects of the
components of `Z`. -/
def sheafifiedAssociatedPresheafOverIso (J : GrothendieckTopology C) {X : C}
    (Z : FormalCoproduct.{u} (Over X)) :
    (presheafToSheaf J (Type u)).obj ((associatedPresheafFunctorOver (X := X)).obj Z) ≅
      ∐ (fun i : Z.I ↦ (presheafToSheaf J (Type u)).obj (yoneda.obj (Z.obj i).left)) :=
  (presheafToSheaf J (Type u)).mapIso ((associatedPresheafFunctorOverIsoYoneda X).app Z) ≪≫
    SemiRepresentable.sheafifiedFormalCoproductIso J ((mapFormalCoproduct (Over.forget X)).obj Z)

/-- **Stacks 0D86 for the presheaf of a semi-representable object over `X`.** Restricting a sheaf
of sets to the localized sites `C / Z_i` and pushing it forward again, one component at a time, is
the internal hom out of the sheafification of the presheaf attached to `Z`, naturally in the
sheaf. -/
def localizationPushforwardPullbackNatIsoSheafHomOver
    (J : GrothendieckTopology C) {X : C} (Z : FormalCoproduct.{u} (Over X)) :
    (Functor.pi' (fun i : Z.I ↦
        localizationPullback (Z.obj i).left J ⋙ localizationPushforward (Z.obj i).left J) ⋙
          Pi.functor Z.I) ≅
      SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj
        ((associatedPresheafFunctorOver (X := X)).obj Z)) :=
  SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom J
      ((mapFormalCoproduct (Over.forget X)).obj Z) ≪≫
    (SheafHomAdj.sheafHomFunctorMapIso ((presheafToSheaf J (Type u)).mapIso
      ((associatedPresheafFunctorOverIsoYoneda X).app Z))).symm

end Stacks.CategoryTheory.Hypercovering

end
