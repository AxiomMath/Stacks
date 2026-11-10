module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition

/-!
# The explicit pseudofunctor of small étale sheaves into adjunctions

For a big étale site `B`, small étale sheaves of sets, their inverse images `f⁻¹` and direct
images `f_*` along small étale base change form a pseudofunctor from `(LocallyDiscrete Bᵒᵖ)` to
the bicategory of adjunctions in `Cat`. This file writes it down explicitly, with the canonical
composition and identity comparisons, so that its fibres are the sheaf categories, its transition
functors are the inverse images, and its composition constraint is
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`, all by definition. A descent argument
needs exactly these identifications on the nose, together with the direct-image adjunctions.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafAdjPseudofunctor`: the pseudofunctor into adjunctions.
* `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`: its inverse-image part, a
  pseudofunctor into `Cat`.
* `AlgebraicGeometry.smallEtaleSheafInverseImageDescentFunctor`: the functor sending a small
  étale sheaf on the target of `f` to its canonical descent datum along `f`.

## Implementation notes

The base's `AlgebraicGeometry.smallEtaleSheafPullbackSystem` records the same data, but it is
chosen by `Classical.choice` from an existence statement, so its fibres and transition functors
agree with the sheaf categories and the inverse images only up to `eqToHom`. The construction
here is the one used in that existence proof (the coherence obligations are the associativity and
unit laws of the composition comparisons of small étale base change, checked after forgetting the
étale condition), kept as a definition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Base change is defined by lifting slice pullback along a full subcategory inclusion, so
-- recognizing a base-changed object as the corresponding slice pullback is a round trip through
-- structure projections, which instance-level definitional unfolding has to see through.
attribute [local implicit_reducible] smallEtaleBaseChange

/-- The inverse of the composition comparison of small étale base change is, after forgetting the
étale condition, the composition comparison of slice pullbacks. -/
private theorem smallEtaleBaseChange_compIso_inv_app_map (B : BigEtaleSite.{u}) {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (U : SmallEtale B Z.1 Z.property) :
    (SmallEtale.inclusion B X.1 X.property).map
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) =
      (Over.pullbackComp f g).hom.app U.obj :=
  congrArg Iso.inv
    (show (SmallEtale.inclusion B X.1 X.property).mapIso
        ((smallEtaleBaseChange_compIso B X Y Z f g).val.app U) =
        (Over.pullbackComp f g).symm.app U.obj from
      Iso.ext (smallEtaleBaseChange_compIso_app B X Y Z f g U))

/-- **The identity comparison of small étale base change.** After forgetting the étale condition,
the identity comparison `smallEtaleBaseChange_idIso` is the canonical comparison of slice pullback
along an identity, and composing base change along `𝟙 Y ≫ r` with it is inverse to the composition
comparison `smallEtaleBaseChange_compIso`: the left unit law of the composition comparisons. -/
public theorem smallEtaleBaseChange_idIso_coherence (B : BigEtaleSite.{u}) :
    (∀ (X : B.Scheme) (U : SmallEtale B X.1 X.property),
      (SmallEtale.inclusion B X.1 X.property).map ((smallEtaleBaseChange_idIso B X).hom.app U) =
        Over.pullbackId.hom.app U.obj) ∧
    (∀ {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property),
      (smallEtaleBaseChange_compIso B Y Y X (𝟙 Y) r).val.inv.app U ≫
        (smallEtaleBaseChange_idIso B Y).hom.app ((smallEtaleBaseChange B r).obj U) =
      𝟙 ((smallEtaleBaseChange B r).obj U)) := by
  have baseChangeIdIso_hom_app : ∀ (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.1
      X.property), (SmallEtale.inclusion B X.1 X.property).map ((smallEtaleBaseChange_idIso B
      X).hom.app U) = Over.pullbackId.hom.app U.obj := by
    intro B X U
    simp only [smallEtaleBaseChange_idIso, Functor.fullyFaithfulCancelRight]
    simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Functor.id_obj, eqToIso_refl,
      Iso.refl_trans, NatIso.trans_app, Functor.comp_obj, NatIso.ofComponents_hom_app,
      Functor.preimageIso_hom, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.symm_hom,
      Functor.leftUnitor_inv_app, Category.comp_id, ObjectProperty.ι_map]
    exact (SmallEtale.inclusion B X.1 X.property).map_preimage _
  have baseChangeCompIso_id_comp : ∀ (B : BigEtaleSite.{u}) {Y X : B.Scheme} (r : Y ⟶ X) (U :
      SmallEtale B X.1 X.property), (smallEtaleBaseChange_compIso B Y Y X (𝟙 Y) r).val.inv.app U ≫
      (smallEtaleBaseChange_idIso B Y).hom.app ((smallEtaleBaseChange B r).obj U) = 𝟙
      ((smallEtaleBaseChange B r).obj U) := by
    intro B Y X r U
    apply (SmallEtale.inclusion B _ _).map_injective
    simp only [Functor.map_comp, smallEtaleBaseChange_compIso_inv_app_map, baseChangeIdIso_hom_app]
    apply (Over.forget _).map_injective
    apply Limits.pullback.hom_ext <;>
      simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Over.forget_obj,
        Over.pullback_obj_left, Functor.id_obj, Functor.comp_obj, Over.pullbackComp,
        conjugateIsoEquiv, conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv,
        Over.mapPullbackAdj, Over.map_obj_left, Equiv.trans_apply, Iso.homCongr_apply,
        Iso.symm_inv, Iso.symm_hom, Equiv.coe_fn_mk,
        Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc,
        Equiv.symm_trans, Equiv.symm_mk,
        Iso.symm_symm_eq, Over.mapComp, NatTrans.comp_app, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Adjunction.comp_unit_app, Adjunction.mkOfHomEquiv_unit_app,
        Over.map_obj_hom, Over.pullback_obj_hom, Over.id_left, Category.comp_id,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app, Functor.comp_map, CategoryTheory.Functor.map_id,
        NatIso.ofComponents_inv_app, Adjunction.mkOfHomEquiv_counit_app, Category.id_comp,
        Functor.id_map, Over.pullbackId, Adjunction.id_unit, Functor.whiskerLeft_id',
        Adjunction.id_counit, Functor.whiskerRight_id', Over.mapId, Over.forget_map,
        Over.comp_left, Over.homMk_left, Over.pullback_map_left, Over.isoMk_inv_left,
        Iso.refl_inv, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Limits.pullback.lift_fst_assoc] <;>
      cat_disch
  exact ⟨fun X U ↦ baseChangeIdIso_hom_app B X U, fun r U ↦ baseChangeCompIso_id_comp B r U⟩

/-- **The composition comparisons of small étale base change are associative and right unital.**
The comparison isomorphisms `smallEtaleBaseChange_compIso` of base change along a composite with
the composite of base changes agree for the two bracketings of a triple composite, and composing
with the identity comparison `smallEtaleBaseChange_idIso` on the right is inverse to the comparison
for `r ≫ 𝟙 X`. Together with `smallEtaleBaseChange_idIso_coherence` these are the coherence laws
that make sheaf inverse and direct image along small étale base change into a pseudofunctor; they
are checked after forgetting the étale condition, where base change is slice pullback. -/
public theorem smallEtaleBaseChange_compIso_coherence (B : BigEtaleSite.{u}) :
    (∀ {W Z Y X : B.Scheme} (p : W ⟶ Z) (q : Z ⟶ Y) (r : Y ⟶ X) (U : SmallEtale B X.1 X.property),
      (smallEtaleBaseChange_compIso B W Z X p (q ≫ r)).val.inv.app U ≫
        (smallEtaleBaseChange B p).map
          ((smallEtaleBaseChange_compIso B Z Y X q r).val.inv.app U) ≫
        (smallEtaleBaseChange_compIso B W Z Y p q).val.hom.app
          ((smallEtaleBaseChange B r).obj U) ≫
        (smallEtaleBaseChange_compIso B W Y X (p ≫ q) r).val.hom.app U =
      𝟙 ((smallEtaleBaseChange B (p ≫ q ≫ r)).obj U)) ∧
    (∀ {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property),
      (smallEtaleBaseChange_compIso B Y X X r (𝟙 X)).val.inv.app U ≫
        (smallEtaleBaseChange B r).map ((smallEtaleBaseChange_idIso B X).hom.app U) =
      𝟙 ((smallEtaleBaseChange B r).obj U)) := by
  have baseChange_map_inclusion : ∀ (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) {U V :
      SmallEtale B Y.1 Y.property} (a : U ⟶ V), (SmallEtale.inclusion B X.1 X.property).map
      ((smallEtaleBaseChange B f).map a) = (Over.pullback f).map ((SmallEtale.inclusion B Y.1
      Y.property).map a) := by
    intro B X Y f U V a
    exact rfl
  have baseChangeCompIso_assoc : ∀ (B : BigEtaleSite.{u}) {W Z Y X : B.Scheme} (p : W ⟶ Z) (q : Z ⟶
      Y) (r : Y ⟶ X) (U : SmallEtale B X.1 X.property), (smallEtaleBaseChange_compIso B W Z X p (q
      ≫ r)).val.inv.app U ≫ (smallEtaleBaseChange B p).map ((smallEtaleBaseChange_compIso B Z Y X q
      r).val.inv.app U) ≫ (smallEtaleBaseChange_compIso B W Z Y p q).val.hom.app
      ((smallEtaleBaseChange B r).obj U) ≫ (smallEtaleBaseChange_compIso B W Y X (p ≫ q)
      r).val.hom.app U = 𝟙 ((smallEtaleBaseChange B (p ≫ q ≫ r)).obj U) := by
    intro B W Z Y X p q r U
    apply (SmallEtale.inclusion B _ _).map_injective
    simp only [Functor.map_comp, baseChange_map_inclusion,
      smallEtaleBaseChange_compIso_app, smallEtaleBaseChange_compIso_inv_app_map]
    apply (Over.forget _).map_injective
    apply Limits.pullback.hom_ext <;>
      simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Over.forget_obj,
        Over.pullback_obj_left, Functor.comp_obj, Over.pullbackComp, conjugateIsoEquiv,
        conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv, Over.mapPullbackAdj,
        Over.map_obj_left, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
        Equiv.coe_fn_mk, Functor.whiskerRight_comp,
        Functor.whiskerLeft_comp, Category.assoc,
        Equiv.symm_trans, Equiv.symm_mk, Iso.symm_symm_eq, Over.mapComp,
        NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Adjunction.comp_unit_app, Adjunction.mkOfHomEquiv_unit_app,
        Over.map_obj_hom, Over.pullback_obj_hom, Over.id_left, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
        Functor.comp_map, CategoryTheory.Functor.map_id, NatIso.ofComponents_inv_app,
        Adjunction.mkOfHomEquiv_counit_app, Category.id_comp, Functor.id_map,
        Category.comp_id, Functor.map_comp, NatIso.ofComponents_hom_app,
        Adjunction.comp_counit_app, Over.forget_map, Over.comp_left, Over.homMk_left,
        Over.pullback_map_left, Over.isoMk_inv_left, Iso.refl_inv, Over.isoMk_hom_left,
        Iso.refl_hom, Over.map_map_left, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
        Limits.pullback.lift_fst_assoc] <;>
      cat_disch
  have baseChangeCompIso_comp_id : ∀ (B : BigEtaleSite.{u}) {Y X : B.Scheme} (r : Y ⟶ X) (U :
      SmallEtale B X.1 X.property), (smallEtaleBaseChange_compIso B Y X X r (𝟙 X)).val.inv.app U ≫
      (smallEtaleBaseChange B r).map ((smallEtaleBaseChange_idIso B X).hom.app U) = 𝟙
      ((smallEtaleBaseChange B r).obj U) := by
    intro B Y X r U
    apply (SmallEtale.inclusion B _ _).map_injective
    simp only [Functor.map_comp, baseChange_map_inclusion,
      smallEtaleBaseChange_compIso_inv_app_map, (smallEtaleBaseChange_idIso_coherence B).1]
    apply (Over.forget _).map_injective
    apply Limits.pullback.hom_ext <;>
      simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Over.forget_obj,
        Over.pullback_obj_left, Functor.id_obj, Functor.comp_obj, Over.pullbackComp,
        conjugateIsoEquiv, conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv,
        Over.mapPullbackAdj, Over.map_obj_left, Equiv.trans_apply, Iso.homCongr_apply,
        Iso.symm_inv, Iso.symm_hom, Equiv.coe_fn_mk,
        Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc,
        Equiv.symm_trans, Equiv.symm_mk,
        Iso.symm_symm_eq, Over.mapComp, NatTrans.comp_app, Functor.rightUnitor_inv_app,
        Functor.whiskerLeft_app, Adjunction.comp_unit_app, Adjunction.mkOfHomEquiv_unit_app,
        Over.map_obj_hom, Over.pullback_obj_hom, Over.id_left, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
        Functor.comp_map, CategoryTheory.Functor.map_id, NatIso.ofComponents_inv_app,
        Adjunction.mkOfHomEquiv_counit_app, Category.id_comp, Functor.id_map,
        Category.comp_id, Over.pullbackId, Adjunction.id_unit, Functor.whiskerLeft_id',
        Adjunction.id_counit, Functor.whiskerRight_id', Over.mapId, Functor.map_comp,
        Over.forget_map, Over.comp_left, Over.homMk_left, Over.pullback_map_left,
        Over.isoMk_inv_left, Iso.refl_inv, Limits.pullback.lift_fst,
        Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc] <;>
      cat_disch
  exact ⟨fun p q r U ↦ baseChangeCompIso_assoc B p q r U, fun r U ↦ baseChangeCompIso_comp_id B r U⟩

/-- **The pseudofunctor of small étale sheaves into adjunctions.** Its value at a morphism `f`
is the adjunction `f⁻¹ ⊣ f_*` between the sheaf inverse image and direct image along small étale
base change; its composition and identity comparisons are the canonical ones. Forgetting the right
adjoints gives `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`, and keeping them gives
the direct-image/inverse-image adjunctions that a descent argument needs. -/
public noncomputable def smallEtaleSheafAdjPseudofunctor (B : BigEtaleSite.{u}) :
    Pseudofunctor (LocallyDiscrete B.Schemeᵒᵖ) (Bicategory.Adj Cat) := by
  have adjHom_ext_right : ∀ {a b : Bicategory.Adj Cat.{u + 1, u + 2}} {f g : a ⟶ b} {α β : f ⟶ g}
      (h : α.τr = β.τr), α = β := by
    intro a b f g α β h
    apply Bicategory.Adj.hom₂_ext
    apply (Bicategory.conjugateEquiv g.adj f.adj).injective
    simpa only [Bicategory.Adj.Hom₂.conjugateEquiv_τl] using h
  have adj_eqToHom_right : ∀ {a b : Bicategory.Adj Cat.{u + 1, u + 2}} {f g : a ⟶ b} (h : f = g),
      (eqToHom h).τr = eqToHom (congrArg Bicategory.Adj.Hom.r h.symm) := by
    intro a b f g h
    subst h
    rfl
  let adj {X Y : B.Scheme} (f : X ⟶ Y) :=
    (smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
  let pushId (X : B.Scheme) :=
    Functor.sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B X) (Type (u + 1))
      (SmallEtale.topology B X.1 X.property)
  exact LocallyDiscrete.mkPseudofunctor
    (fun X => Bicategory.Adj.mk (Cat.of
      (Sheaf (SmallEtale.topology B X.unop.1 X.unop.property) (Type (u + 1)))))
    (fun f => .mk (adj f.unop).toCat)
    (fun X => Bicategory.Adj.iso₂Mk
      (Cat.Hom.isoMk (Adjunction.leftAdjointIdIso (adj (𝟙 X.unop)) (pushId X.unop)))
      (Cat.Hom.isoMk (pushId X.unop).symm) (by
        ext1
        simp [Bicategory.toNatTrans_conjugateEquiv]))
    (fun f g => Bicategory.Adj.iso₂Mk
      (Cat.Hom.isoMk (smallEtaleMorphism_comp_inverseImageIso B
        _ _ _ g.unop f.unop).symm)
      (Cat.Hom.isoMk (smallEtaleMorphism_comp_pushforwardIso B
        _ _ _ g.unop f.unop)) (by
        ext1
        simp [Bicategory.toNatTrans_conjugateEquiv,
          smallEtaleMorphism_comp_inverseImageIso, adj,
          Bicategory.Adjunction.ofCat_comp]))
    (map₂_associator := by
      intro X Y Z W f g h
      apply adjHom_ext_right
      ext1
      simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.iso₂Mk_hom_τr,
        Bicategory.Adj.iso₂Mk_inv_τr, Bicategory.Adj.whiskerRight_τr,
        Bicategory.Adj.whiskerLeft_τr, Bicategory.Adj.associator_hom_τr,
        adj_eqToHom_right]
      apply NatTrans.ext
      funext M
      apply (sheafToPresheaf _ _).map_injective
      apply NatTrans.ext
      funext U
      simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
        Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
        Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
        Functor.sheafPushforwardContinuous, Category.assoc,
        Functor.map_comp, op_comp] using!
          (congrArg (fun a => M.obj.map a.op)
            ((smallEtaleBaseChange_compIso_coherence B).1 h.unop g.unop f.unop U.unop)).trans
              (M.obj.map_id _))
    (map₂_left_unitor := by
      intro X Y f
      apply adjHom_ext_right
      ext1
      simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.iso₂Mk_hom_τr,
        Bicategory.Adj.whiskerRight_τr, Bicategory.Adj.leftUnitor_hom_τr,
        adj_eqToHom_right]
      apply NatTrans.ext
      funext M
      apply (sheafToPresheaf _ _).map_injective
      apply NatTrans.ext
      funext U
      simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
        Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
        Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
        Functor.sheafPushforwardContinuous, Category.assoc,
        Functor.map_comp, op_comp] using!
          (congrArg (fun a => M.obj.map a.op)
            ((smallEtaleBaseChange_compIso_coherence B).2 f.unop U.unop)).trans
              (M.obj.map_id _))
    (map₂_right_unitor := by
      intro X Y f
      apply adjHom_ext_right
      ext1
      simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.iso₂Mk_hom_τr,
        Bicategory.Adj.whiskerLeft_τr, Bicategory.Adj.rightUnitor_hom_τr,
        adj_eqToHom_right]
      apply NatTrans.ext
      funext M
      apply (sheafToPresheaf _ _).map_injective
      apply NatTrans.ext
      funext U
      simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
        Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
        Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
        Functor.sheafPushforwardContinuous, Category.assoc,
        Functor.map_comp, op_comp] using!
          (congrArg (fun a => M.obj.map a.op)
            ((smallEtaleBaseChange_idIso_coherence B).2 f.unop U.unop)).trans
              (M.obj.map_id _))

/-- The pseudofunctor of small étale sheaves and their inverse images: the left-adjoint part of
`AlgebraicGeometry.smallEtaleSheafAdjPseudofunctor`. Its value at a scheme is the category of
sheaves of sets on its small étale site and its value at a morphism is the sheaf inverse image,
both by definition. -/
public abbrev smallEtaleSheafInverseImagePseudofunctor (B : BigEtaleSite.{u}) :
    Pseudofunctor (LocallyDiscrete B.Schemeᵒᵖ) Cat :=
  (smallEtaleSheafAdjPseudofunctor B).comp Bicategory.Adj.forget₁

/-- The functor sending a small étale sheaf on `Y` to its canonical descent datum along
`f : X ⟶ Y`, for the pseudofunctor `AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`. -/
public abbrev smallEtaleSheafInverseImageDescentFunctor (B : BigEtaleSite.{u}) {X Y : B.Scheme}
    (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      (smallEtaleSheafInverseImagePseudofunctor B).DescentData (fun _ : Unit ↦ f) :=
  (smallEtaleSheafInverseImagePseudofunctor B).toDescentData (fun _ : Unit ↦ f)

end AlgebraicGeometry

end
