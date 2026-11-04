module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction

/-!
# Functoriality of the lift of additive functors on abelian sheaves

Let `Λ` be a ring. An additive functor between categories of abelian sheaves lifts to a functor
between the corresponding categories of sheaves of `Λ`-modules, by
`Stacks.ModuleCatLift.moduleLift`. This file records that the lift is functorial: it takes a
natural transformation to a natural transformation, an isomorphism to an isomorphism, and a
composite of functors to the composite of the lifts.

## Main definitions

* `Stacks.ModuleCatLift.moduleLiftNatTrans` — the lift of a natural transformation.
* `Stacks.ModuleCatLift.moduleLiftNatIso` — the lift of a natural isomorphism.

## Main results

* `Stacks.ModuleCatLift.moduleLift_additive` — the lift of an additive functor is additive.
* `Stacks.ModuleCatLift.moduleLift_comp` — the lift of a composite is the composite of the
  lifts, on the nose.

## Implementation notes

Forgetting the `Λ`-module structure of a sheaf is `CategoryTheory.sheafCompose` along
`forget₂ (ModuleCat Λ) AddCommGrpCat`; it is faithful and takes the lift of `G` to `G` on the
nose, by `Stacks.ModuleCatLift.moduleLift_comp_sheafCompose`. So every equation between
morphisms of lifts is checked after forgetting, where it is an equation between morphisms of
abelian sheaves, and the lift of a composite needs no comparison map at all.

A morphism of abelian sheaves is `Λ`-linear exactly when it commutes with multiplication by
scalars, which for a lift is the image of multiplication by scalars under the functor; so the
component of the lift of `e : G ⟶ G'` at `F` is the component of `e`, whose `Λ`-linearity is the
naturality of `e` at multiplication by the scalar.

Nothing here carries a `stacks` attribute: this is formal category theory used to give
coefficients to constructions that are tagged elsewhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂ u₃ v₃

namespace Stacks.ModuleCatLift

section Functorial

variable (Λ : Type r) [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₃.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Forgetting the `Λ`-module structure of sheaves of `Λ`-modules is additive. -/
public instance sheafCompose_forget₂_additive :
    (sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).Additive where
  map_add := by intros; rfl

/-- **The lift of a natural transformation of additive functors on abelian sheaves.** Its
component at a sheaf of `Λ`-modules `F` is the component of `e` at the abelian sheaf underlying
`F`, which is `Λ`-linear by naturality of `e` at multiplication by a scalar. -/
public def moduleLiftNatTrans (G G' : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w})
    [G.Additive] [G'.Additive] (e : G ⟶ G') :
    moduleLift Λ J₁ J₂ G ⟶ moduleLift Λ J₁ J₂ G' where
  app F := sheafHomOfScalarComm Λ J₂ (e.app _) fun a => e.naturality _
  naturality F₁ F₂ φ :=
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
      simp only [Functor.map_comp, sheafCompose_map_moduleLift_map]
      exact e.naturality _)

/-- **The lift of a natural isomorphism of additive functors on abelian sheaves.** -/
public def moduleLiftNatIso (G G' : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w})
    [G.Additive] [G'.Additive] (e : G ≅ G') :
    moduleLift Λ J₁ J₂ G ≅ moduleLift Λ J₁ J₂ G' where
  hom := moduleLiftNatTrans Λ J₁ J₂ G G' e.hom
  inv := moduleLiftNatTrans Λ J₁ J₂ G' G e.inv
  hom_inv_id := NatTrans.ext (funext fun F =>
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
      simp only [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp]
      exact e.hom_inv_id_app _))
  inv_hom_id := NatTrans.ext (funext fun F =>
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
      simp only [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp]
      exact e.inv_hom_id_app _))

/-- The lift of an additive functor is additive: forgetting the `Λ`-module structure is additive
and faithful, and takes the lift to the functor it was lifted from. -/
public instance moduleLift_additive
    (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive] :
    (moduleLift Λ J₁ J₂ G).Additive where
  map_add := (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
    simp only [Functor.map_add, sheafCompose_map_moduleLift_map]
    rfl)

/-- The lift of a composite of additive functors is the composite of their lifts, on the nose:
both have the same underlying abelian sheaf and the same action of `Λ` on it. -/
public lemma moduleLift_comp (G₁ : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w})
    [G₁.Additive] (G₂ : Sheaf J₂ AddCommGrpCat.{w} ⥤ Sheaf J₃ AddCommGrpCat.{w}) [G₂.Additive] :
    moduleLift Λ J₁ J₃ (G₁ ⋙ G₂) = moduleLift Λ J₁ J₂ G₁ ⋙ moduleLift Λ J₂ J₃ G₂ :=
  rfl

end Functorial

end Stacks.ModuleCatLift

end
