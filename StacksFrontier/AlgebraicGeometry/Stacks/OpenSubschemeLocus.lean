module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable

/-!
# Algebraic spaces represented by an open subscheme of the base

Let `U` be a scheme over `S` in the big fppf site `B`. This file collects three facts about the
algebraic spaces over `U` represented by an open subscheme `V ⊆ U`, which are what a proof that
a full subcategory of a stack is an open substack consumes once it has cut out, over each
scheme-valued point, the open subscheme of the base along which an object lies in the
subcategory.

## Main results

* `AlgebraicGeometry.Stack.nonempty_iso_of_subsingleton`: two presheaves of sets with
  subsingleton values and the same support are isomorphic.
* `AlgebraicGeometry.Stack.subsingleton_hom_of_isOpenImmersion`: there is at most one morphism
  of the big fppf site of `U` into an open subscheme of `U`.
* `AlgebraicGeometry.Stack.isOpenImmersion_algebraicSpaceMap_of_iso_yoneda`: an algebraic space
  over `U` isomorphic to an open subscheme of `U` has open immersion structural morphism, read
  as a morphism of algebraic spaces over `S` through **Stacks 04SG**.

## Implementation notes

The structural morphism of Stacks 04SG is replaced, through
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, by the structural morphism of the
lower-shriek extension, which on the presheaf represented by `V` is the identification of
**Stacks 03I4** followed by the structure morphism of `V`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Stack

section Subsingleton

variable {C : Type*} [Category C]

/-- Two subsingleton-valued presheaves with the same support are isomorphic. -/
theorem nonempty_iso_of_subsingleton (P Q : Cᵒᵖ ⥤ Type v)
    (hP : ∀ X, Subsingleton (P.obj X)) (hQ : ∀ X, Subsingleton (Q.obj X))
    (h : ∀ X, Nonempty (P.obj X) ↔ Nonempty (Q.obj X)) : Nonempty (P ≅ Q) := by
  let e (X : Cᵒᵖ) : P.obj X ≃ Q.obj X :=
    { toFun := fun a => ((h X).mp ⟨a⟩).some
      invFun := fun b => ((h X).mpr ⟨b⟩).some
      left_inv := fun _ => (hP X).elim _ _
      right_inv := fun _ => (hQ X).elim _ _ }
  exact ⟨NatIso.ofComponents (fun X => (e X).toIso) (fun {X Y} f => by
    ext a
    exact (hQ Y).elim _ _)⟩

end Subsingleton

section Structural

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- There is at most one morphism to an object of the big fppf site of `U` whose structure
morphism is an open immersion, that morphism being a monomorphism. -/
theorem subsingleton_hom_of_isOpenImmersion (U : BigFppfOver B S hS)
    (V : BigFppfOver B U.left.1 U.left.2) (hV : IsOpenImmersion V.hom.hom)
    (T : BigFppfOver B U.left.1 U.left.2) : Subsingleton (T ⟶ V) := by
  have : Mono V.hom := B.inclusion.mono_of_mono_map (by
    change Mono V.hom.hom
    infer_instance)
  exact ⟨fun a b ↦ Over.OverMorphism.ext <|
    (cancel_mono V.hom).mp ((Over.w a).trans (Over.w b).symm)⟩

/-- The structural morphism of the lower-shriek extension of a presheaf on a slice site is
natural in the presheaf. -/
theorem relocalizeToYoneda_comp_map {C : Type*} [Category C] {X Y : C} (a : X ⟶ Y)
    {P Q : (Over X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) :
    (OverShriek.relocalizePresheafFunctor a).map α ≫ OverShriek.relocalizeToYoneda a Q =
      OverShriek.relocalizeToYoneda a P := by
  ext W s
  rfl

/-- On a representable presheaf, the structural morphism of the lower-shriek extension is the
identification of Stacks 03I4 (2) followed by the structure morphism of the representing
object. -/
theorem relocalizeToYoneda_yoneda {C : Type*} [Category C] {X Y : C} (a : X ⟶ Y)
    (V : Over X) :
    ((OverShriek.relocalizeYonedaIso a).app V).hom ≫
        yoneda.map (Over.homMk V.hom rfl : (Over.map a).obj V ⟶ Over.mk a) =
      OverShriek.relocalizeToYoneda a (yoneda.obj V) := by
  ext W s
  exact Over.OverMorphism.ext (Over.w s.1.2)

/-- **An algebraic space over `U` isomorphic to an open subscheme of `U` has open immersion
structural morphism over `S`.** This is the structural morphism of Stacks 04SG, the one the
open-immersion condition of Stacks 04XB tests. -/
theorem isOpenImmersion_algebraicSpaceMap_of_iso_yoneda (U : BigFppfOver B S hS)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B U.left.1 U.left.2 P)
    (V : BigFppfOver B U.left.1 U.left.2) (e : P ≅ yoneda.obj V)
    (hV : IsOpenImmersion V.hom.hom) :
    Space.IsOpenImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  refine (prop_algebraicSpaceMap_iff B S hS (Space.openImmersionProperty B S hS) U P hP).mpr ?_
  let k : (Over.map U.hom).obj V ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let j : (OverShriek.relocalizePresheafFunctor U.hom).obj P ≅
      yoneda.obj ((Over.map U.hom).obj V) :=
    (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso U.hom).app V
  have hj : j.hom ≫ yoneda.map k = OverShriek.relocalizeToYoneda U.hom P := by
    dsimp only [j, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, relocalizeToYoneda_yoneda, relocalizeToYoneda_comp_map]
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have := MorphismProperty.isStableUnderBaseChange_inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)
  have hk : Space.IsOpenImmersion B S hS (yoneda.map k) :=
    MorphismProperty.relative_map (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)) hV
  change Space.IsOpenImmersion B S hS (OverShriek.relocalizeToYoneda U.hom P)
  rw [← hj]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))) j.hom (yoneda.map k)).mpr hk

end Structural

end AlgebraicGeometry.Stack

end
