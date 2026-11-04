module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleInverseImageUnitors
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp

/-!
# Stacks 03LQ is compatible with identities

Let `U` be an algebraic space over a scheme `S` contained in a big fppf site `B`. Stacks 03LQ
identifies the inverse image of the morphism of spaces-étale topoi attached to an étale
morphism with restriction along postcomposition. Both sides carry an identity comparison: on
the inverse images it is the adjoint mate of the identity comparison for the direct images,
and on the restriction functors it is the strict comparison attached to the isomorphism
between postcomposition with `𝟙 U` and the identity functor. This file proves that the
resulting triangle commutes.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtalePostcompId`: postcomposition with `𝟙 U` is the identity
  functor of the spaces-étale site of `U`;
* `AlgebraicGeometry.Space.spacesEtalePostcompSheafId`: the resulting strict comparison of the
  restriction functor with the identity functor on sheaves.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompId`: on the sites, the adjoint
  mate of `AlgebraicGeometry.Space.spacesEtalePostcompId` is the identity isomorphism of
  Stacks 03G2 for base change along `𝟙 U`;
* `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafId`: the same on sheaves;
* `AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso_id`: **Stacks 03LQ is
  compatible with identities.**

## Implementation notes

This is the identity analogue of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp`, and the three
steps are the same, with `CategoryTheory.Adjunction.id` in place of
`CategoryTheory.Adjunction.comp`. On the sites both comparisons are restrictions along the
inclusion of the objects étale over the base of `CategoryTheory.Over.mapId` and
`CategoryTheory.Over.pullbackId`, and the latter is by definition the adjoint mate of the
former, so `CategoryTheory.conjugateEquiv_of_counit_comm_app` transfers the identity across
the restriction. Passing to sheaves is
`CategoryTheory.conjugateEquiv_sheafPushforwardContinuousNatTrans` together with
`CategoryTheory.Adjunction.sheafPushforwardContinuous_id`. The last step is uniqueness of a
left adjoint, through `Stacks.CategoryTheory.leftAdjointUniq_naturality` and
`CategoryTheory.Adjunction.leftAdjointUniq_refl`.

The étaleness witness for `𝟙 U` is carried as an explicit argument rather than produced here,
so that the statements apply verbatim to the witness supplied by whatever consumer needs them;
`AlgebraicGeometry.Space.IsEtale` is a proposition, so no two such witnesses differ.

Nothing here is tagged. Stacks 03LQ itself is registered in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage`; the compatibility of
that identification with identities is a coherence the source does not state.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}

/-- **Postcomposition with an identity is the identity.** On the spaces-étale site of `U`,
postcomposition with `𝟙 U` is the identity functor. This is `CategoryTheory.Over.mapId`
restricted to the objects étale over the base. -/
noncomputable def spacesEtalePostcompId (hu : IsEtale B S hS (𝟙 U : U ⟶ U).hom) :
    spacesEtalePostcomp B S hS (𝟙 U) hu ≅ 𝟭 (SpacesEtale B S hS U) :=
  NatIso.ofComponents
    (fun T ↦ (IsEtaleOver B S hS U).isoMk
      ((Over.mapId U).app ((SpacesEtale.inclusion B S hS U).obj T)))
    (fun f ↦ ObjectProperty.hom_ext _ (by
      simp [spacesEtalePostcomp, SpacesEtale.inclusion]))

/-- **On the sites, the adjoint mate of the identity comparison for postcomposition is the one
for base change.** The mate of `AlgebraicGeometry.Space.spacesEtalePostcompId` with respect to
the adjunctions of Stacks 03LP is the identity isomorphism of Stacks 03G2 for base change
along `𝟙 U`. -/
theorem conjugateEquiv_spacesEtalePostcompId (hu : IsEtale B S hS (𝟙 U : U ⟶ U).hom) :
    conjugateEquiv (spacesEtalePostcompBaseChangeAdjunction B S hS (𝟙 U) hu)
        (Adjunction.id (C := SpacesEtale B S hS U))
        (spacesEtalePostcompId B S hS hu).inv =
      (spacesBaseChange_id B S hS U).hom := by
  refine NatTrans.ext (funext fun T ↦ ObjectProperty.hom_ext _ ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (𝟙 U))
    (Adjunction.id (C := Over U))
    (spacesEtalePostcompBaseChangeAdjunction B S hS (𝟙 U) hu)
    (Adjunction.id (C := SpacesEtale B S hS U))
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (Iso.refl _) (Iso.refl _)
    (counit_comm_restrictFullyFaithful _ _ _ _ _)
    (fun Y => by simp)
    (Over.mapId U).inv (spacesEtalePostcompId B S hS hu).inv
    (fun X ↦ by
      simp [spacesEtalePostcompId, ObjectProperty.liftCompιIso,
        ObjectProperty.isoMk, ObjectProperty.homMk, spacesEtalePostcomp,
        ObjectProperty.lift]) T
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, ObjectProperty.ι_obj_lift_obj] at key
  exact (Category.id_comp _).symm.trans (key.trans (Category.comp_id _))

/-- **The strict identity comparison of the restriction functor on sheaves.** Restriction
along postcomposition with `𝟙 U` is the identity functor on spaces-étale sheaves of `U`. -/
noncomputable def spacesEtalePostcompSheafId (hu : IsEtale B S hS (𝟙 U : U ⟶ U).hom) :
    (spacesEtalePostcomp B S hS (𝟙 U) hu).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS U) ≅
      𝟭 (Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1))) :=
  Functor.sheafPushforwardContinuousId' (spacesEtalePostcompId B S hS hu)
    (Type (u + 1)) (SpacesEtale.topology B S hS U)

/-- **On sheaves, the adjoint mate of the strict identity comparison of the restriction
functor is the identity comparison of the direct images.** -/
theorem conjugateEquiv_spacesEtalePostcompSheafId
    (hu : IsEtale B S hS (𝟙 U : U ⟶ U).hom) :
    conjugateEquiv (Adjunction.id (C := spacesEtaleSheafCat B S hS U))
        (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) (𝟙 U) hu)
        (spacesEtalePostcompSheafId B S hS hu).hom =
      (spacesEtaleSheafPushforwardId B S hS U).inv := by
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    (Adjunction.id (C := SpacesEtale B S hS U))
    (spacesEtalePostcompBaseChangeAdjunction B S hS (𝟙 U) hu)
    (Type (u + 1)) (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS U)
    (spacesEtalePostcompId B S hS hu).inv
  rw [conjugateEquiv_spacesEtalePostcompId B S hS hu,
    Adjunction.sheafPushforwardContinuous_id] at ht
  have h1 : (spacesEtalePostcompSheafId B S hS hu).hom =
      Functor.sheafPushforwardContinuousNatTrans (spacesEtalePostcompId B S hS hu).inv
        (Type (u + 1)) (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS U) :=
    Category.comp_id _
  have h2 : (spacesEtaleSheafPushforwardId B S hS U).inv =
      Functor.sheafPushforwardContinuousNatTrans (spacesBaseChange_id B S hS U).hom
        (Type (u + 1)) (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS U) :=
    Category.id_comp _
  rw [h1, h2]
  exact ht

/-- **Stacks 03LQ is compatible with identities.** For an algebraic space `U`, the
identification of the inverse image with restriction along postcomposition carries the
identity comparison of the inverse images — the adjoint mate of the one for the direct
images — to the strict identity comparison of the restriction functor. -/
theorem spacesToposMorphism_inverseImageIso_id (hu : IsEtale B S hS (𝟙 U : U ⟶ U).hom) :
    (spacesEtaleInverseImage_id B S hS U).hom =
      (spacesToposMorphism_inverseImageIso B S hS (𝟙 U) hu).hom ≫
        (spacesEtalePostcompSheafId B S hS hu).hom := by
  have hA : conjugateEquiv (Adjunction.id (C := spacesEtaleSheafCat B S hS U))
      (spacesEtaleAdjunction B S hS (𝟙 U))
      (spacesEtaleInverseImage_id B S hS U).hom =
      (spacesEtaleSheafPushforwardId B S hS U).inv := Equiv.apply_symm_apply _ _
  have hnat := _root_.Stacks.CategoryTheory.leftAdjointUniq_naturality
    (spacesEtaleAdjunction B S hS (𝟙 U))
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) (𝟙 U) hu)
    (Adjunction.id (C := spacesEtaleSheafCat B S hS U))
    (Adjunction.id (C := spacesEtaleSheafCat B S hS U))
    (spacesEtaleInverseImage_id B S hS U).hom
    (spacesEtalePostcompSheafId B S hS hu).hom
    (hA.trans (conjugateEquiv_spacesEtalePostcompSheafId B S hS hu).symm)
  rw [Adjunction.leftAdjointUniq_refl] at hnat
  exact (Category.comp_id _).symm.trans hnat

end AlgebraicGeometry.Space

end
