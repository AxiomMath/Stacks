module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification

/-!
# The underlying map of sheaves of sets of the abelian inverse image comparison

The pullback of abelian sheaves along a cocontinuous functor is the pullback of sheaves of sets
with its group operations transported, and
`Stacks.Sites.AbelianPullback.cocontinuousAbelianInverseImageIso` is the resulting comparison of
the two descriptions.  That comparison is a composite of eight isomorphisms, seven of which are
built out of unitors, associators, the compatibility of `Functor.mapCommGrp` with composition, and
the two elementary comparisons `Stacks.Sites.AbelianPullback.sheafToPresheafInternalIso` and
`Stacks.Sites.AbelianPullback.precompInternalIso`, whose components are the identity on sections.
This file proves that on underlying sheaves of sets only the eighth factor, the sheafification
comparison `Stacks.Sites.AbelianPullback.sheafificationInternalIso`, survives.

## Main results

* `CategoryTheory.Sites.AbelianSheaf.externalSheaf_map_forget`: reading an internal commutative
  group in sheaves of sets as an abelian sheaf and then forgetting the addition returns the
  morphism one started from.
* `Stacks.Sites.AbelianPullback.sheafToPresheafInternalIso_inv_app_forget` and
  `Stacks.Sites.AbelianPullback.precompInternalIso_inv_app_forget`: the two elementary comparisons
  are the identity on underlying sheaves, respectively presheaves, of sets.
* `Stacks.Sites.AbelianPullback.cocontinuousAbelianInverseImageIso_hom_app_forget`: on underlying
  sheaves of sets the comparison of the two descriptions of the pullback of abelian sheaves is the
  sheafification comparison of the restricted presheaf.

## Implementation notes

The objects are kept in the form `G.obj (H.obj X)` rather than `(H ⋙ G).obj X`, which is what
the `dsimp only` pass arranges: the two spellings are identified only by comparing the functors
themselves, and here these differ by the content of the two elementary comparisons.

## References

* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf Opposite

universe u u₁ u₂ v₁ v₂

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

namespace CategoryTheory.Sites.AbelianSheaf

/-- Reading a morphism of internal commutative groups in sheaves of sets as a morphism of abelian
sheaves and then forgetting the addition gives back the morphism of sheaves of sets. -/
theorem externalSheaf_map_forget {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    {X Y : CommGrp (Sheaf J (Type u))} (f : X ⟶ Y) :
    (sheafCompose J (forget AddCommGrpCat.{u})).map ((externalSheaf J).map f) =
      f.hom.hom.hom := rfl

end CategoryTheory.Sites.AbelianSheaf

namespace Stacks.Sites.AbelianPullback

/-- Changing the braiding of a functor does not change the underlying morphism of the induced
isomorphism of functors on commutative group objects. -/
theorem mapCommGrpBraidedIso_forget {A : Type u₁} [Category.{v₁} A]
    [CartesianMonoidalCategory A] [BraidedCategory A] {B : Type u₂} [Category.{v₂} B]
    [CartesianMonoidalCategory B] [BraidedCategory B] (G : A ⥤ B) (b₁ b₂ : G.Braided)
    (X : CommGrp A) :
    ((mapCommGrpBraidedIso G b₁ b₂).hom.app X).hom.hom.hom = 𝟙 (G.obj X.X) := by
  obtain rfl : b₁ = b₂ := Subsingleton.elim _ _
  rfl

/-- Internalizing the group operations of the underlying presheaf of an abelian sheaf is the
identity on sections: the components of `sheafToPresheafInternalIso` have underlying morphism of
presheaves of sets the identity. -/
theorem sheafToPresheafInternalIso_inv_app_forget {D : Type u} [Category.{u} D]
    (K : GrothendieckTopology D) (X' : Sheaf K AddCommGrpCat.{u}) :
    ((sheafToPresheafInternalIso K).inv.app X').hom.hom.hom = 𝟙 _ :=
  (Category.comp_id _).trans <| (Category.comp_id _).trans <| Category.comp_id _

/-- Restricting an abelian presheaf along a functor is the identity on sections: the components of
`precompInternalIso` have underlying morphism of presheaves of sets the identity. -/
theorem precompInternalIso_inv_app_forget {C : Type u} [Category.{u} C] {D : Type u}
    [Category.{u} D] (G : C ⥤ D) (Q : D ⥤ AddCommGrpCat.{u}) :
    ((precompInternalIso G).inv.app Q).hom.hom.hom = 𝟙 _ := rfl

/-- A factor of a composite which is the identity may be dropped. -/
private theorem comp_eq_of_eq_id {Z : Type u₁} [Category.{v₁} Z] {a : Z} {f : a ⟶ a}
    (hf : f = 𝟙 a) {c : Z} (g : a ⟶ c) : f ≫ g = g :=
  Eq.trans (congrArg (fun k => k ≫ g) hf) (Category.id_comp g)

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]

/-- Restricting along `F.op` and sheafifying the underlying morphism of presheaves of sets of a
component of `sheafToPresheafInternalIso` gives the identity. -/
private theorem map_sheafToPresheafInternalIso_inv_app_forget (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [HasSheafify J (Type u)]
    (X' : Sheaf K AddCommGrpCat.{u}) :
    (presheafToSheaf J (Type u)).map
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op).map
          (((sheafToPresheafInternalIso K).inv.app X').hom.hom.hom)) = 𝟙 _ :=
  Eq.trans (congrArg (fun k => (presheafToSheaf J (Type u)).map
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op).map k))
      (sheafToPresheafInternalIso_inv_app_forget K X'))
    (Eq.trans (congrArg (fun k => (presheafToSheaf J (Type u)).map k)
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op).map_id _))
      ((presheafToSheaf J (Type u)).map_id _))

/-- Sheafifying the underlying morphism of presheaves of sets of a component of
`precompInternalIso` gives the identity. -/
private theorem map_precompInternalIso_inv_app_forget (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [HasSheafify J (Type u)]
    (X' : Sheaf K AddCommGrpCat.{u}) :
    (presheafToSheaf J (Type u)).map
        (((precompInternalIso F.op).inv.app
          ((sheafToPresheaf K AddCommGrpCat.{u}).obj X')).hom.hom.hom) = 𝟙 _ :=
  Eq.trans (congrArg (fun k => (presheafToSheaf J (Type u)).map k)
      (precompInternalIso_inv_app_forget F.op _))
    ((presheafToSheaf J (Type u)).map_id _)

/-- **On underlying sheaves of sets the comparison of the two descriptions of the pullback of
abelian sheaves along a cocontinuous functor is the sheafification comparison**
`sheafificationInternalIso` of the restricted presheaf. -/
theorem cocontinuousAbelianInverseImageIso_hom_app_forget (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type u)] [HasWeakSheafify J AddCommGrpCat.{u}]
    (X' : Sheaf K AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((cocontinuousAbelianInverseImageIso F J K).hom.app X') =
      (sheafCompose J (forget AddCommGrpCat.{u})).map
        ((sheafificationInternalIso J).hom.app (F.op ⋙ X'.obj)) := by
  dsimp only [cocontinuousAbelianInverseImageIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Functor.comp_obj,
    externalSheaf_map_forget, mapCommGrpBraidedIso_forget,
    Functor.mapCommGrpCompIso_hom_app_hom_hom_hom]
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (comp_eq_of_eq_id
    (map_sheafToPresheafInternalIso_inv_app_forget F J K X') _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (comp_eq_of_eq_id
    ((sheafCompose J (forget AddCommGrpCat.{u})).map_id _) _) ?_
  refine Eq.trans (comp_eq_of_eq_id (map_precompInternalIso_inv_app_forget F J K X') _) ?_
  rfl

end Stacks.Sites.AbelianPullback

end
