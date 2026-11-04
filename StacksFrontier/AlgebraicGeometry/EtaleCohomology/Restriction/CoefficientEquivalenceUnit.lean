module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence

/-!
# The unit of the inverse image across a change of coefficients

Let `f : C ⥤ D` be a continuous functor of sites and let `e : A ≌ B` be an equivalence of
coefficient categories. The comparison
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` of the two inverse images is the uniqueness
of a left adjoint, so it is determined by what it does to the units of the two inverse-image
adjunctions. This file records that determination, both as an identity of morphisms of sheaves
and — the form in which it is used on germs — as an identity of maps on sections.

The two adjunctions at issue are the inverse image on `A`-valued sheaves followed by the change
of coefficients, and the change of coefficients followed by the inverse image on `B`-valued
sheaves. Both are left adjoint to the same functor, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` compares their units; the unit of the
change of coefficients, which is the unit of `e` applied to sections, is an isomorphism and is
cancelled, and the change of coefficients is faithful, which removes it.

## Main results

* `CategoryTheory.Sheaf.sheafCompose_map_unit_app` — the change of coefficients applied to the
  unit of the inverse image on `A`-valued sheaves is the unit of the inverse image on
  `B`-valued sheaves followed by the comparison of the two inverse images.
* `CategoryTheory.Sheaf.unit_comp_sheafPullbackCoefficientIso_inv_app_app` — the same on
  sections over an object of the site.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe va vb a b v u v' u'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B] (e : A ≌ B)
  [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse]
  [K.HasSheafCompose e.functor] [K.HasSheafCompose e.inverse]
  [f.IsContinuous J K]
  [(f.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(f.sheafPushforwardContinuous B J K).IsRightAdjoint]

/-- **The comparison of the two inverse images is the mate of the two units.** The change of
coefficients applied to the unit of the inverse image on `A`-valued sheaves is the unit of the
inverse image on `B`-valued sheaves, followed by the comparison
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` read backwards.

Both composites are left adjoint to the same functor, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` relates the two units through the
comparison; the unit of the change of coefficients is an isomorphism, which is cancelled, and
the change of coefficients along the inverse equivalence is faithful, which removes it. -/
public theorem sheafCompose_map_unit_app (G : Sheaf J A) :
    (sheafCompose J e.functor).map ((f.sheafAdjunctionContinuous A J K).unit.app G) =
      (f.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J e.functor).obj G) ≫
        (f.sheafPushforwardContinuous B J K).map
          ((sheafPullbackCoefficientIso f J K e).inv.app G) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((coefficientEquivalence J e).toAdjunction.comp
      (f.sheafAdjunctionContinuous B J K)).ofNatIsoRight (Iso.refl _))
    ((f.sheafAdjunctionContinuous A J K).comp (coefficientEquivalence K e).toAdjunction) G
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app, Equivalence.toAdjunction_unit,
    Category.comp_id, Category.assoc] at h
  have hnat : (f.sheafAdjunctionContinuous A J K).unit.app G ≫
        (f.sheafPushforwardContinuous A J K).map
          ((coefficientEquivalence K e).unit.app ((f.sheafPullback A J K).obj G)) =
      (coefficientEquivalence J e).unit.app G ≫
        (coefficientEquivalence J e).inverse.map
          ((coefficientEquivalence J e).functor.map
            ((f.sheafAdjunctionContinuous A J K).unit.app G)) :=
    (coefficientEquivalence J e).unitIso.hom.naturality
      ((f.sheafAdjunctionContinuous A J K).unit.app G)
  have hmc : (coefficientEquivalence J e).inverse.map
        ((f.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J e.functor).obj G) ≫
          (f.sheafPushforwardContinuous B J K).map
            ((sheafPullbackCoefficientIso f J K e).inv.app G)) =
      (coefficientEquivalence J e).inverse.map
          ((f.sheafAdjunctionContinuous B J K).unit.app
            ((sheafCompose J e.functor).obj G)) ≫
        (coefficientEquivalence J e).inverse.map
          ((f.sheafPushforwardContinuous B J K).map
            ((sheafPullbackCoefficientIso f J K e).inv.app G)) :=
    (coefficientEquivalence J e).inverse.map_comp _ _
  refine (coefficientEquivalence J e).inverse.map_injective (Eq.trans ?_ hmc.symm)
  exact ((Iso.cancel_iso_hom_left ((coefficientEquivalence J e).unitIso.app G) _ _).1
    (h.trans hnat)).symm

/-- **The comparison of the two inverse images, on sections.** Pulling a section over `V` back
along the unit of the inverse image of `B`-valued sheaves and reading it through the comparison
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` of the two inverse images is the change of
coefficients applied to the pullback of that section along the unit of the inverse image of
`A`-valued sheaves. -/
public theorem unit_comp_sheafPullbackCoefficientIso_inv_app_app
    (G : Sheaf J A) (V : C) :
    ((f.sheafAdjunctionContinuous B J K).unit.app
          ((sheafCompose J e.functor).obj G)).hom.app (op V) ≫
        ((sheafPullbackCoefficientIso f J K e).inv.app G).hom.app (op (f.obj V)) =
      e.functor.map
        (((f.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op V)) := by
  have h : ((sheafCompose J e.functor).map
        ((f.sheafAdjunctionContinuous A J K).unit.app G)).hom.app (op V) =
      (((f.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J e.functor).obj G) ≫
        (f.sheafPushforwardContinuous B J K).map
          ((sheafPullbackCoefficientIso f J K e).inv.app G)).hom).app (op V) :=
    congrArg (fun m => m.hom.app (op V)) (sheafCompose_map_unit_app f J K e G)
  exact h.symm

end CategoryTheory.Sheaf

end
