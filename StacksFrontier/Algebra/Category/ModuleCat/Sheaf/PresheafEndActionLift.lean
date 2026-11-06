module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift

/-!
# The lift to `Λ`-modules of a presheaf-valued additive functor on abelian sheaves

Let `Λ` be a ring and let `G` be an additive functor from abelian sheaves on a site to presheaves
of abelian groups on another category. This file lifts `G` to a functor from sheaves of
`Λ`-modules to presheaves of `Λ`-modules, the `Λ`-action being the image under `G` of
multiplication by scalars.

## Main definitions

* `Stacks.ModuleCatLift.presheafLift` — the lift.

## Main results

* `Stacks.ModuleCatLift.presheafLift_obj_comp_forget₂` and
  `Stacks.ModuleCatLift.forget₂_map_presheafLift_map_app` — the lift is a lift: forgetting the
  `Λ`-module structure gives `G` applied to the underlying abelian sheaf, on the nose.
* `Stacks.ModuleCatLift.presheafLift_obj_smul` — the scalar action on sections.

## Implementation notes

This is the presheaf-valued companion of `Stacks.ModuleCatLift.moduleLift`, which lifts a functor
landing in sheaves, and of `Stacks.ModuleCatLift.valueLift`, which lifts one landing in a single
abelian group. Lifting into presheaves needs no sheaf condition on the target, so the
construction is `Stacks.ModuleCatLift.ofEndAction` applied directly, with none of the
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` step of `moduleLift`.

A ring suffices; commutativity is not needed. The values of the scalar action are endomorphisms
of the underlying abelian presheaf, as for `Stacks.ModuleCatLift.sheafScalarEnd`.

Nothing here carries a `stacks` attribute: this is formal category theory used to give
coefficients to a construction tagged elsewhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂

namespace Stacks.ModuleCatLift

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {K : Type u₂} [Category.{v₂} K]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  (G : Sheaf J AddCommGrpCat.{w} ⥤ (K ⥤ AddCommGrpCat.{w})) [G.Additive]

/-- The action of `Λ` on the presheaf an additive functor produces from the abelian sheaf
underlying a sheaf of `Λ`-modules. -/
public def presheafLiftScalarEnd (F : Sheaf J (ModuleCat.{w} Λ)) :
    Λ →+* End (G.obj ((sheafCompose J
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F)) :=
  (mapEndRingHom G _).comp (sheafScalarEnd Λ J F)

/-- The presheaf of `Λ`-modules whose underlying abelian presheaf is `G` applied to the abelian
sheaf underlying `F`. -/
public def presheafLiftObj (F : Sheaf J (ModuleCat.{w} Λ)) : K ⥤ ModuleCat.{w} Λ :=
  ofEndAction Λ _ (presheafLiftScalarEnd Λ J G F)

/-- The morphism of presheaves of `Λ`-modules whose underlying morphism of abelian presheaves is
`G` applied to the underlying morphism of `φ`; it is `Λ`-linear because `φ` is. -/
public def presheafLiftMap {F₁ F₂ : Sheaf J (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂) :
    presheafLiftObj Λ J G F₁ ⟶ presheafLiftObj Λ J G F₂ :=
  ofEndActionMap Λ _ _
    (G.map ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ))
    fun a => by
      change G.map (sheafScalarEnd Λ J F₁ a).asHom ≫ _ = _ ≫ G.map (sheafScalarEnd Λ J F₂ a).asHom
      rw [← G.map_comp, ← G.map_comp, sheafScalarEnd_naturality]

@[simp]
public lemma forget₂_map_presheafLiftMap_app {F₁ F₂ : Sheaf J (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂)
    (U : K) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map ((presheafLiftMap Λ J G φ).app U) =
      (G.map ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ)).app U :=
  rfl

/-- **The lift of a presheaf-valued additive functor on abelian sheaves to sheaves of
`Λ`-modules.** The underlying abelian presheaf of `presheafLift G F` is `G` applied to the
abelian sheaf underlying `F`, and its `Λ`-action is the image under `G` of multiplication by
scalars on that sheaf. -/
public def presheafLift : Sheaf J (ModuleCat.{w} Λ) ⥤ (K ⥤ ModuleCat.{w} Λ) where
  obj := presheafLiftObj Λ J G
  map := presheafLiftMap Λ J G
  map_id F := NatTrans.ext (funext fun U =>
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
      rw [forget₂_map_presheafLiftMap_app, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
      rfl))
  map_comp φ ψ := NatTrans.ext (funext fun U =>
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
      rw [forget₂_map_presheafLiftMap_app, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp]
      rfl))

/-- The abelian presheaf underlying `presheafLift G F` is `G` applied to the abelian sheaf
underlying `F`. -/
public lemma presheafLift_obj_comp_forget₂ (F : Sheaf J (ModuleCat.{w} Λ)) :
    (presheafLift Λ J G).obj F ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} =
      G.obj ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F) :=
  rfl

/-- The scalar action on the sections of `presheafLift G F` is the image under `G` of
multiplication by that scalar, evaluated on the object. -/
public lemma presheafLift_obj_smul (F : Sheaf J (ModuleCat.{w} Λ)) (U : K) (a : Λ) :
    (((presheafLift Λ J G).obj F).obj U).smul a =
      .of ((G.map (sheafScalarEnd Λ J F a).asHom).app U) :=
  rfl

@[simp]
public lemma forget₂_map_presheafLift_map_app {F₁ F₂ : Sheaf J (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂)
    (U : K) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map (((presheafLift Λ J G).map φ).app U) =
      (G.map ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ)).app U :=
  rfl

/-- Forgetting the `Λ`-module structure of `presheafLift` gives `G` on the underlying abelian
sheaves, on the nose. -/
public lemma presheafLift_comp_whiskeringRight_forget₂ :
    presheafLift Λ J G ⋙
        (Functor.whiskeringRight K (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ G :=
  rfl

/-- **The lift is a lift:** forgetting the `Λ`-module structure of `presheafLift G F` gives `G`
applied to the abelian sheaf underlying `F`. The isomorphism is the identity, the two composites
being the same functor. -/
public def presheafLiftForgetIso :
    presheafLift Λ J G ⋙
        (Functor.whiskeringRight K (ModuleCat.{w} Λ) AddCommGrpCat.{w}).obj
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ G :=
  eqToIso (presheafLift_comp_whiskeringRight_forget₂ Λ J G)

end Stacks.ModuleCatLift

end
