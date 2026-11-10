module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of small étale sheaves along a split morphism

For a morphism of schemes admitting a section, the canonical functor from small étale sheaves
on the target to descent data on the source is an equivalence.

## Main definitions

* `AlgebraicGeometry.SmallEtaleSheafPullbackSystem` packages the inverse-image pseudofunctor
  with its actual fibres, transition functors, and canonical composition comparison.
* `AlgebraicGeometry.smallEtaleSheafDescentFunctor` is the canonical descent functor.

## Main results

* `AlgebraicGeometry.smallEtaleSheafDescentFunctor_isEquivalence_of_section` is the
  equivalence for a morphism with a section.

## Implementation notes

The pseudofunctor is specified by the categories of sheaves on the small étale sites and by the
sheaf inverse-image functors. Its coherence is the canonical coherence of inverse image, which
is obtained by building the pseudofunctor into the bicategory of adjunctions in `Cat` and then
forgetting the right adjoints: the three coherence conditions are then checked on the direct
images, where they reduce to the canonical comparisons of iterated fibre products. Descent data
use Mathlib's invariant presentation, with compatible transition isomorphisms over every common
base change. The section supplies the inverse functor by inverse image along the section.

## References

* [Stacks Project, Tag 0GEY](https://stacks.math.columbia.edu/tag/0GEY)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v u' v'

namespace AlgebraicGeometry

/-- The pseudofunctor of small étale sheaves, with its actual small-site inverse-image
functors and canonical comparison for their composition. -/
public structure SmallEtaleSheafPullbackSystem (B : BigEtaleSite.{u}) where
  /-- The underlying pseudofunctor into `Cat`. -/
  pseudofunctor : Pseudofunctor (LocallyDiscrete B.Schemeᵒᵖ) Cat
  /-- Its value at a scheme is the category of sheaves on the small étale site. -/
  fiber (X : B.Scheme) :
    pseudofunctor.obj (.mk (.op X)) =
      Cat.of (Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))
  /-- Its transition functor along `f` is the small étale sheaf inverse image. -/
  pullback {X Y : B.Scheme} (f : X ⟶ Y) :
    (eqToHom (fiber Y).symm ≫ pseudofunctor.map f.op.toLoc ≫ eqToHom (fiber X)) =
      ((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
        (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B X.1 X.property)).toCatHom
  /-- Its composition comparison is the canonical one. -/
  mapComp_canonical {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (pseudofunctor.mapComp g.op.toLoc f.op.toLoc)
      (Cat.Hom.isoMk (smallEtaleMorphism_comp_inverseImageIso B X Y Z f g).symm)

/-- Two 2-morphisms of adjunctions agree as soon as their right components do. -/
private theorem adjHom_ext_right
    {D : Type*} [Bicategory D] {a b : Bicategory.Adj D}
    {f g : a ⟶ b} {α β : f ⟶ g} (h : α.τr = β.τr) : α = β := by
  apply Bicategory.Adj.hom₂_ext
  apply (Bicategory.conjugateEquiv g.adj f.adj).injective
  simpa only [Bicategory.Adj.Hom₂.conjugateEquiv_τl] using h

/-- The right component of an `eqToHom` between morphisms of adjunctions. -/
private theorem adj_eqToHom_right
    {D : Type*} [Bicategory D] {a b : Bicategory.Adj D}
    {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).τr = eqToHom (congrArg Bicategory.Adj.Hom.r h.symm) := by
  subst h
  rfl

/-- The inverse of the composition comparison of small étale base changes, after forgetting
the étale condition. -/
private theorem baseChangeComp_inv (B : BigEtaleSite.{u})
    {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : SmallEtale B Z.1 Z.property) :
    (SmallEtale.inclusion B X.1 X.property).map
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app U) =
      (Over.pullbackComp f g).hom.app U.obj := by
  have hh : (SmallEtale.inclusion B X.1 X.property).mapIso
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.app U) =
      (Over.pullbackComp f g).symm.app U.obj :=
    Iso.ext (smallEtaleBaseChange_compIso_app B X Y Z f g U)
  exact congrArg Iso.inv hh

/-- Small étale base change is slice pullback after forgetting the étale condition. -/
private theorem baseChange_map_inclusion (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) {U V : SmallEtale B Y.1 Y.property} (a : U ⟶ V) :
    (SmallEtale.inclusion B X.1 X.property).map ((smallEtaleBaseChange B f).map a) =
      (Over.pullback f).map ((SmallEtale.inclusion B Y.1 Y.property).map a) := rfl

-- Base change is defined by lifting slice pullback along a full subcategory inclusion, so
-- recognizing a base-changed object as the corresponding slice pullback is a round trip through
-- structure projections, which instance-level definitional unfolding has to see through.
attribute [local implicit_reducible] smallEtaleBaseChange

/-- Base change along an identity morphism is the identity of the small étale category. -/
private noncomputable def baseChangeIdIso (B : BigEtaleSite.{u}) (X : B.Scheme) :
    smallEtaleBaseChange B (𝟙 X) ≅ 𝟭 (SmallEtale B X.1 X.property) :=
  NatIso.ofComponents (fun U =>
    (Functor.FullyFaithful.ofFullyFaithful (SmallEtale.inclusion B X.1 X.property)).preimageIso
      (Over.pullbackId.app U.obj)) (by
    intro U V f
    apply (SmallEtale.inclusion B X.1 X.property).map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, baseChange_map_inclusion, Functor.id_map]
    exact Over.pullbackId.hom.naturality
      ((SmallEtale.inclusion B X.1 X.property).map f))

/-- Forgetting the étale condition identifies the identity comparison with the canonical
comparison for slice pullback along an identity. -/
private theorem baseChangeIdIso_hom_app (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.1 X.property) :
    (SmallEtale.inclusion B X.1 X.property).map ((baseChangeIdIso B X).hom.app U) =
      Over.pullbackId.hom.app U.obj :=
  (Functor.FullyFaithful.ofFullyFaithful
    (SmallEtale.inclusion B X.1 X.property)).map_preimage _

/-- The composition comparisons of small étale base change are associative: the two ways of
comparing a triple composite of base changes with base change along the composite agree. -/
private theorem baseChangeCompIso_assoc (B : BigEtaleSite.{u})
    {W Z Y X : B.Scheme} (p : W ⟶ Z) (q : Z ⟶ Y) (r : Y ⟶ X)
    (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_compIso B W Z X p (q ≫ r)).val.inv.app U ≫
        (smallEtaleBaseChange B p).map
          ((smallEtaleBaseChange_compIso B Z Y X q r).val.inv.app U) ≫
        (smallEtaleBaseChange_compIso B W Z Y p q).val.hom.app
          ((smallEtaleBaseChange B r).obj U) ≫
        (smallEtaleBaseChange_compIso B W Y X (p ≫ q) r).val.hom.app U =
      𝟙 ((smallEtaleBaseChange B (p ≫ q ≫ r)).obj U) := by
  apply (SmallEtale.inclusion B _ _).map_injective
  simp only [Functor.map_comp, baseChange_map_inclusion,
    smallEtaleBaseChange_compIso_app, baseChangeComp_inv]
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

/-- The composition comparison against an identity on the right is inverse to the identity
comparison. -/
private theorem baseChangeCompIso_comp_id (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_compIso B Y X X r (𝟙 X)).val.inv.app U ≫
        (smallEtaleBaseChange B r).map ((baseChangeIdIso B X).hom.app U) =
      𝟙 ((smallEtaleBaseChange B r).obj U) := by
  apply (SmallEtale.inclusion B _ _).map_injective
  simp only [Functor.map_comp, baseChange_map_inclusion,
    baseChangeComp_inv, baseChangeIdIso_hom_app]
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

/-- The composition comparison against an identity on the left is inverse to the identity
comparison. -/
private theorem baseChangeCompIso_id_comp (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_compIso B Y Y X (𝟙 Y) r).val.inv.app U ≫
        (baseChangeIdIso B Y).hom.app ((smallEtaleBaseChange B r).obj U) =
      𝟙 ((smallEtaleBaseChange B r).obj U) := by
  apply (SmallEtale.inclusion B _ _).map_injective
  simp only [Functor.map_comp, baseChangeComp_inv, baseChangeIdIso_hom_app]
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

/-- There is a pseudofunctor of small étale sheaf inverse images with canonical coherence. -/
public theorem smallEtaleSheafPullbackSystem_nonempty
    (B : BigEtaleSite.{u}) : Nonempty (SmallEtaleSheafPullbackSystem B) := by
  refine ⟨?_⟩
  let adj {X Y : B.Scheme} (f : X ⟶ Y) :=
    (smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
  let pushId (X : B.Scheme) :=
    Functor.sheafPushforwardContinuousId' (baseChangeIdIso B X) (Type (u + 1))
      (SmallEtale.topology B X.1 X.property)
  let P : Pseudofunctor (LocallyDiscrete B.Schemeᵒᵖ) (Bicategory.Adj Cat) :=
    LocallyDiscrete.mkPseudofunctor
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
        ext M : 2
        apply Sheaf.hom_ext
        ext U : 2
        simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
          Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
          Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
          Functor.sheafPushforwardContinuous, Category.assoc, Functor.map_comp, op_comp] using!
            (congrArg (fun a => M.obj.map a.op)
              (baseChangeCompIso_assoc B h.unop g.unop f.unop U.unop)).trans (M.obj.map_id _))
      (map₂_left_unitor := by
        intro X Y f
        apply adjHom_ext_right
        ext1
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.iso₂Mk_hom_τr,
          Bicategory.Adj.whiskerRight_τr, Bicategory.Adj.leftUnitor_hom_τr,
          adj_eqToHom_right]
        ext M : 2
        apply Sheaf.hom_ext
        ext U : 2
        simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
          Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
          Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
          Functor.sheafPushforwardContinuous, Category.assoc, Functor.map_comp, op_comp] using!
            (congrArg (fun a => M.obj.map a.op)
              (baseChangeCompIso_comp_id B f.unop U.unop)).trans (M.obj.map_id _))
      (map₂_right_unitor := by
        intro X Y f
        apply adjHom_ext_right
        ext1
        simp only [Bicategory.Adj.comp_τr, Bicategory.Adj.iso₂Mk_hom_τr,
          Bicategory.Adj.whiskerLeft_τr, Bicategory.Adj.rightUnitor_hom_τr,
          adj_eqToHom_right]
        ext M : 2
        apply Sheaf.hom_ext
        ext U : 2
        simpa [smallEtaleMorphism_comp_pushforwardIso, pushId,
          Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousId',
          Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
          Functor.sheafPushforwardContinuous, Category.assoc, Functor.map_comp, op_comp] using!
            (congrArg (fun a => M.obj.map a.op)
              (baseChangeCompIso_id_comp B f.unop U.unop)).trans (M.obj.map_id _))
  exact ⟨P.comp Bicategory.Adj.forget₁, fun _ => rfl, fun _ => rfl, by intro X Y Z f g; rfl⟩

/-- The canonically coherent pullback pseudofunctor of small étale sheaves. -/
public noncomputable def smallEtaleSheafPullbackSystem
    (B : BigEtaleSite.{u}) : SmallEtaleSheafPullbackSystem B :=
  Classical.choice (smallEtaleSheafPullbackSystem_nonempty B)

/-- The functor sending a small étale sheaf to its canonical descent datum. -/
public noncomputable def smallEtaleSheafDescentFunctor
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) ⥤
      (smallEtaleSheafPullbackSystem B).pseudofunctor.DescentData
        (fun _ : Unit ↦ f) :=
  (eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor ⋙
    (smallEtaleSheafPullbackSystem B).pseudofunctor.toDescentData (fun _ : Unit ↦ f)

end AlgebraicGeometry

namespace CategoryTheory.Pseudofunctor.DescentData

/-- The single-member family consisting of the identity of `Y`. -/
private def identityFamily {C : Type u} [Category.{v} C] (Y : C) :=
  fun _ : Unit ↦ 𝟙 Y

/-- Evaluation of a descent datum for the identity family at its unique index. -/
private def evaluateIdentityDescentData {C : Type u} [Category.{v} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (Y : C) :
    P.DescentData (identityFamily Y) ⥤ P.obj (.mk (.op Y)) where
  obj D := D.obj ()
  map α := α.hom ()

/-- A descent datum for the identity family is the canonical one on its value. -/
private def identityDescentDataIso {C : Type u} [Category.{v} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (Y : C)
    (D : P.DescentData (identityFamily Y)) :
    (P.toDescentData (identityFamily Y)).obj (D.obj ()) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun _ => (Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).app (D.obj ())) (by
    rintro Z q ⟨⟩ ⟨⟩ g h hg hh
    have hg' : g = q := by simpa [identityFamily] using hg
    have hh' : h = q := by simpa [identityFamily] using hh
    subst g
    subst h
    have hself : D.hom q q q (i₁ := ()) (i₂ := ()) = 𝟙 _ := by
      simpa [identityFamily] using
        (D.hom_self (q := q) (i := ()) q (by simp [identityFamily]))
    rw [hself]
    simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj])

/-- Descent along the identity is an equivalence. -/
private def identityDescentDataEquivalence {C : Type u} [Category.{v} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (Y : C) :
    P.obj (.mk (.op Y)) ≌ P.DescentData (identityFamily Y) where
  functor := P.toDescentData (identityFamily Y)
  inverse := evaluateIdentityDescentData P Y
  unitIso := NatIso.ofComponents
    (fun M => (Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).symm.app M)
    (fun g => (Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).inv.naturality g)
  counitIso := NatIso.ofComponents (identityDescentDataIso P Y) (by
    intro D E α
    ext i
    cases i
    exact (Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).hom.naturality (α.hom ()))
  functor_unitIso_comp := by
    intro M
    ext i
    cases i
    change
      (P.map (𝟙 (.mk (.op Y)))).toFunctor.map
          ((Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).symm.hom.app M) ≫
        (Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).hom.app
          ((P.map (𝟙 (.mk (.op Y)))).toFunctor.obj M) = 𝟙 _
    rw [(Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).hom.naturality
      ((Cat.Hom.toNatIso (P.mapId (.mk (.op Y)))).symm.hom.app M)]
    simp

/-- **Stacks 0GEY (categorical core).** Split morphisms give effective descent for any
contravariant pseudofunctor. -/
@[sga "4 VIII 9.4.1"]
public theorem isEquivalence_toDescentData_of_section
    {C : Type u} [Category.{v} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {X Y : C} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    (P.toDescentData (fun _ : Unit ↦ f)).IsEquivalence := by
  let J : GrothendieckTopology C := ⊥
  have : P.IsPrestack J := by
    refine ⟨fun {S} M N => ?_⟩
    have hOver : J.over S = (⊥ : GrothendieckTopology (Over S)) := by
      ext T R
      simp [J, GrothendieckTopology.mem_over_iff]
    rw [hOver]
    exact Presheaf.isSheaf_bot (P := P.presheafHom M N)
  have hIdSieve : Sieve.ofArrows _ (fun _ : Unit ↦ 𝟙 Y) = ⊤ := by
    apply top_unique
    intro Z g _
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨(), g, by simp⟩
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ 𝟙 Y) ∈ J Y := by
    simp [J, hIdSieve]
  have hle : Sieve.ofArrows _ (fun _ : Unit ↦ 𝟙 Y) ≤
      Sieve.ofArrows _ (fun _ : Unit ↦ f) := by
    intro Z g _
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨(), g ≫ s, by simp [Category.assoc, hs]⟩
  have : (P.toDescentData (fun _ : Unit ↦ 𝟙 Y)).IsEquivalence :=
    (identityDescentDataEquivalence P Y).isEquivalence_functor
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le P hcov hle

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry

/-- Transport of an equivalence of categories along an equality in `Cat`. -/
private theorem eqToHomFunctor_isEquivalence {A B : Cat.{v', u'}} (h : A = B) :
    (eqToHom h).toFunctor.IsEquivalence := by
  cases h
  exact CategoryTheory.Equivalence.refl.isEquivalence_functor

/-- **Stacks 0GEY.** The canonical small étale sheaf descent functor for a morphism of schemes
admitting a section is an equivalence. -/
@[stacks 0GEY]
public theorem smallEtaleSheafDescentFunctor_isEquivalence_of_section
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    (smallEtaleSheafDescentFunctor B f).IsEquivalence := by
  let P := (smallEtaleSheafPullbackSystem B).pseudofunctor
  have : (P.toDescentData (fun _ : Unit ↦ f)).IsEquivalence :=
    Pseudofunctor.DescentData.isEquivalence_toDescentData_of_section P f s hs
  have : ((eqToHom ((smallEtaleSheafPullbackSystem B).fiber Y).symm).toFunctor).IsEquivalence :=
    eqToHomFunctor_isEquivalence _
  dsimp [smallEtaleSheafDescentFunctor]
  exact Functor.isEquivalence_trans _ _

end AlgebraicGeometry

end
