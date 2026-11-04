module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeCoherence

/-!
# The unit coherences of spaces-étale base change, over all algebraic spaces

Stacks 03G2 attaches to a morphism `f : X ⟶ Y` of algebraic spaces over `S` a base-change
functor on the spaces-étale sites (part (1)) together with a composition isomorphism for it
(part (2)). This file supplies the identity datum and the two unit coherences relating it to the
composition isomorphism, on the sites and on the direct images of sheaves, and assembles them,
with the associativity coherence of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeCoherence`, into a
pseudofunctor on the category of all algebraic spaces over `S`.

On the sites, base change along an identity is identified with the identity functor through
`CategoryTheory.Over.pullbackId`, and the two coherences are the restrictions of
`CategoryTheory.Over.pullbackComp_id_comp` and `CategoryTheory.Over.pullbackComp_comp_id` to the
objects étale over the base.

## Main definitions

* `AlgebraicGeometry.Space.spacesBaseChange_id`: base change along an identity morphism of
  algebraic spaces is the identity functor of the spaces-étale site;
* `AlgebraicGeometry.Space.spacesEtaleSheafPushforwardId`: the direct image of spaces-étale
  sheaves along an identity is the identity functor;
* `AlgebraicGeometry.Space.spacesEtalePseudofunctor`: the pseudofunctor sending an algebraic
  space over `S` to the sheaves on its spaces-étale site and a morphism to its inverse image.

## Main results

* `AlgebraicGeometry.Space.spacesBaseChange_comp_id` and
  `AlgebraicGeometry.Space.spacesBaseChange_id_comp`: the two unit coherences on the sites;
* `AlgebraicGeometry.Space.spacesEtaleSheafPushforward_comp_id` and
  `AlgebraicGeometry.Space.spacesEtaleSheafPushforward_id_comp`: the two unit coherences on
  direct images of sheaves.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Base change of spaces-étale charts along `𝟙 X` is the identity functor of the spaces-étale
site of `X`. -/
noncomputable def spacesBaseChange_id (X : AlgebraicSpaces B S hS) :
    (spacesBaseChange B S hS (𝟙 X)).functor ≅ 𝟭 (SpacesEtale B S hS X) := by
  refine NatIso.ofComponents (fun V ↦ (IsEtaleOver B S hS X).isoMk
    (Over.pullbackId.app ((SpacesEtale.inclusion B S hS X).obj V))) ?_
  intro V W k
  apply ObjectProperty.hom_ext
  simp [spacesBaseChange, SpacesEtale.toSpaces, SpacesEtale.inclusion, ObjectProperty.lift]

/-- The identification of the base-change functors along two equal morphisms, read at a chart
and on the underlying slice object: it is the identification of the two base-changed charts. -/
theorem spacesBaseChange_eqToHom_app_hom {X Y : AlgebraicSpaces B S hS} {p q : X ⟶ Y}
    (e : p = q) (V : SpacesEtale B S hS Y) :
    ((eqToHom (congrArg (fun k : X ⟶ Y => (spacesBaseChange B S hS k).functor) e)).app V).hom =
      eqToHom (congrArg
        (fun k : X ⟶ Y => ((spacesBaseChange B S hS k).functor.obj V).obj) e) := by
  subst e
  simp

/-- The first unit coherence for the base-change functors of Stacks 03G2 on the spaces-étale
sites: comparing base change along `p ≫ 𝟙` with base change along `𝟙` followed by base change
along `p` is the identification of the two morphisms. -/
theorem spacesBaseChange_comp_id {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (spacesBaseChange_comp B S hS p (𝟙 Y)).inv ≫
        Functor.whiskerRight (spacesBaseChange_id B S hS Y).hom
            (spacesBaseChange B S hS p).functor ≫
          (Functor.leftUnitor (spacesBaseChange B S hS p).functor).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => (spacesBaseChange B S hS k).functor)
        (Category.comp_id p)) := by
  refine NatTrans.ext (funext fun V => ?_)
  apply ObjectProperty.hom_ext
  have key := NatTrans.congr_app (Over.pullbackComp_id_comp p) V.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToHom_app] at key
  rw [spacesBaseChange_eqToHom_app_hom B S hS (Category.comp_id p) V]
  change _ = 𝟙 _
  dsimp only [spacesBaseChange_comp, spacesBaseChange_id]
  simpa [spacesBaseChange, SpacesEtale.toSpaces, SpacesEtale.inclusion, IsEtaleOver,
    ObjectProperty.lift] using key

/-- The second unit coherence for the base-change functors of Stacks 03G2 on the spaces-étale
sites: comparing base change along `𝟙 ≫ p` with base change along `p` followed by base change
along `𝟙` is the identification of the two morphisms. -/
theorem spacesBaseChange_id_comp {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (spacesBaseChange_comp B S hS (𝟙 X) p).inv ≫
        Functor.whiskerLeft (spacesBaseChange B S hS p).functor
            (spacesBaseChange_id B S hS X).hom ≫
          (Functor.rightUnitor (spacesBaseChange B S hS p).functor).hom =
      eqToHom (congrArg (fun k : X ⟶ Y => (spacesBaseChange B S hS k).functor)
        (Category.id_comp p)) := by
  refine NatTrans.ext (funext fun V => ?_)
  apply ObjectProperty.hom_ext
  have key := NatTrans.congr_app (Over.pullbackComp_comp_id p) V.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, eqToHom_app] at key
  rw [spacesBaseChange_eqToHom_app_hom B S hS (Category.id_comp p) V]
  change _ = 𝟙 _
  dsimp only [spacesBaseChange_comp, spacesBaseChange_id]
  simpa [spacesBaseChange, SpacesEtale.toSpaces, SpacesEtale.inclusion, IsEtaleOver,
    ObjectProperty.lift] using key

/-- The direct image of spaces-étale sheaves along an identity morphism of algebraic spaces is
the identity functor. -/
noncomputable def spacesEtaleSheafPushforwardId (X : AlgebraicSpaces B S hS) :
    spacesEtaleSheafPushforward B S hS (𝟙 X) ≅ 𝟭 (spacesEtaleSheafCat B S hS X) := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS (𝟙 X)).isContinuous
  exact Functor.sheafPushforwardContinuousId' (spacesBaseChange_id B S hS X)
    (Type (u + 1)) (SpacesEtale.topology B S hS X)

/-- The inverse of the identity comparison on direct images is precomposition with the
site-level identity comparison. -/
theorem spacesEtaleSheafPushforwardId_inv_app_hom_app (X : AlgebraicSpaces B S hS)
    (M : spacesEtaleSheafCat B S hS X) (V : (SpacesEtale B S hS X)ᵒᵖ) :
    ((spacesEtaleSheafPushforwardId B S hS X).inv.app M).hom.app V =
      M.obj.map ((spacesBaseChange_id B S hS X).hom.app V.unop).op :=
  rfl

/-- The sections of the direct image of a sheaf along `p` over a chart are the sections of the
sheaf over the base change of that chart. -/
theorem spacesEtaleSheafPushforward_obj_obj_obj {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (M : spacesEtaleSheafCat B S hS X) (V : (SpacesEtale B S hS Y)ᵒᵖ) :
    ((spacesEtaleSheafPushforward B S hS p).obj M).obj.obj V =
      M.obj.obj (Opposite.op ((spacesBaseChange B S hS p).functor.obj V.unop)) :=
  rfl

/-- The direct image of a sheaf along `p` acts on charts by base change along `p`. -/
theorem spacesEtaleSheafPushforward_obj_obj_map {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (M : spacesEtaleSheafCat B S hS X) {V W : (SpacesEtale B S hS Y)ᵒᵖ} (t : V ⟶ W) :
    ((spacesEtaleSheafPushforward B S hS p).obj M).obj.map t =
      M.obj.map ((spacesBaseChange B S hS p).functor.map t.unop).op :=
  rfl

/-- The first unit coherence on direct images of spaces-étale sheaves, relating
`spacesEtaleSheafPushforwardId` at `Y` to `spacesEtaleSheafPushforwardComp` for `p` and `𝟙 Y`. -/
theorem spacesEtaleSheafPushforward_comp_id {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (Functor.rightUnitor (spacesEtaleSheafPushforward B S hS p)).inv ≫
        Functor.whiskerLeft (spacesEtaleSheafPushforward B S hS p)
            (spacesEtaleSheafPushforwardId B S hS Y).inv ≫
          (spacesEtaleSheafPushforwardComp B S hS p (𝟙 Y)).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => spacesEtaleSheafPushforward B S hS k)
        (Category.comp_id p).symm) := by
  refine NatTrans.ext (funext fun M => ?_)
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have key := NatTrans.congr_app (spacesBaseChange_comp_id B S hS p) V.unop
  have h2 := (congrArg (fun t => M.obj.map (Quiver.Hom.op t)) key).trans (M.obj.map_id _)
  simpa [-Iso.symm_inv, spacesEtaleSheafPushforwardId_inv_app_hom_app,
    spacesEtaleSheafPushforward_obj_obj_map, spacesEtaleSheafPushforward_obj_obj_obj,
    spacesBaseChange_pushforward_comp_inv_app_hom_app] using h2

/-- The second unit coherence on direct images of spaces-étale sheaves, relating
`spacesEtaleSheafPushforwardId` at `X` to `spacesEtaleSheafPushforwardComp` for `𝟙 X` and `p`. -/
theorem spacesEtaleSheafPushforward_id_comp {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) :
    (Functor.leftUnitor (spacesEtaleSheafPushforward B S hS p)).inv ≫
        Functor.whiskerRight (spacesEtaleSheafPushforwardId B S hS X).inv
            (spacesEtaleSheafPushforward B S hS p) ≫
          (spacesEtaleSheafPushforwardComp B S hS (𝟙 X) p).inv =
      eqToHom (congrArg (fun k : X ⟶ Y => spacesEtaleSheafPushforward B S hS k)
        (Category.id_comp p).symm) := by
  refine NatTrans.ext (funext fun M => ?_)
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have key := NatTrans.congr_app (spacesBaseChange_id_comp B S hS p) V.unop
  have h2 := (congrArg (fun t => M.obj.map (Quiver.Hom.op t)) key).trans (M.obj.map_id _)
  simpa [-Iso.symm_inv, spacesEtaleSheafPushforwardId_inv_app_hom_app,
    spacesEtaleSheafPushforward_obj_obj_map, spacesEtaleSheafPushforward_obj_obj_obj,
    spacesBaseChange_pushforward_comp_inv_app_hom_app] using h2

/-- **The pseudofunctor of spaces-étale inverse images**, over the category of all algebraic
spaces over `S`: it sends an algebraic space to the category of sheaves of sets on its
spaces-étale site and a morphism to the inverse image of Stacks 03G2 part (3), both on the
nose. -/
noncomputable def spacesEtalePseudofunctor :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctorOfLeftAdjoints (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun {_ _} f => spacesEtaleSheafPushforward B S hS f)
    (fun {_ _} f => spacesEtaleAdjunction B S hS f)
    (fun X => spacesEtaleSheafPushforwardId B S hS X)
    (fun {_ _ _} f g => spacesEtaleSheafPushforwardComp B S hS f g)
    (fun {_ _ _ _} f g h => spacesBaseChange_pushforward_comp_assoc B S hS f g h)
    (fun {_ _} p => spacesEtaleSheafPushforward_comp_id B S hS p)
    (fun {_ _} p => spacesEtaleSheafPushforward_id_comp B S hS p)

end AlgebraicGeometry.Space

end
