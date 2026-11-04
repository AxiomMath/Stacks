module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeCoherence
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.RestrictMates
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates

/-!
# The inverse image along an étale morphism of algebraic spaces and composition

Let `h : U ⟶ V` and `k : V ⟶ W` be étale morphisms of algebraic spaces over a scheme `S`
contained in a big fppf site `B`. The inverse image of the morphism of spaces-étale topoi attached
to an étale morphism is identified with restriction along postcomposition. Both sides of that
identification carry a composition comparison: on the inverse images it is the adjoint mate of the
composition comparison for the direct images, and on the restriction functors it is the strict
comparison of `CategoryTheory.Functor.sheafPushforwardContinuousComp'` attached to the
isomorphism of the two postcomposition functors. The identification carries the first comparison
to the second.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtalePostcompComp`: postcomposition with `h` followed by
  postcomposition with `k` is postcomposition with `h ≫ k`, on the spaces-étale sites;
* `AlgebraicGeometry.Space.spacesEtalePostcompSheafComp`: the resulting strict comparison of
  the restriction functors on sheaves.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompComp`: on the sites, the adjoint
  mate of `AlgebraicGeometry.Space.spacesEtalePostcompComp` is the composition comparison for
  base change;
* `AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafComp`: the same on sheaves;
* `AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso_comp`: the identification of the
  inverse image with restriction along postcomposition is compatible with composition.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V W : AlgebraicSpaces B S hS}

/-- **Postcomposition is compatible with composition.** On the spaces-étale sites,
postcomposition with `h : U ⟶ V` followed by postcomposition with `k : V ⟶ W` is
postcomposition with `h ≫ k`. This is `CategoryTheory.Over.mapComp` restricted to the objects
étale over the base. -/
noncomputable def spacesEtalePostcompComp (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (k : V ⟶ W) (hk : IsEtale B S hS k.hom) :
    spacesEtalePostcomp B S hS h hh ⋙ spacesEtalePostcomp B S hS k hk ≅
      spacesEtalePostcomp B S hS (h ≫ k) (isEtale_comp B S hS hh hk) :=
  NatIso.ofComponents
    (fun T ↦ (IsEtaleOver B S hS W).isoMk
      ((Over.mapComp h k).symm.app ((SpacesEtale.inclusion B S hS U).obj T)))
    (fun f ↦ ObjectProperty.hom_ext _ (by
      simpa [spacesEtalePostcomp, SpacesEtale.inclusion, IsEtaleOver] using
        (Over.mapComp h k).symm.hom.naturality
          ((SpacesEtale.inclusion B S hS U).map f)))

/-- **On the sites, the adjoint mate of the composition comparison for postcomposition is the
one for base change.** The mate of `AlgebraicGeometry.Space.spacesEtalePostcompComp` with
respect to the adjunctions between postcomposition and base change is the inverse of the
composition isomorphism `AlgebraicGeometry.Space.spacesBaseChange_comp`. -/
theorem conjugateEquiv_spacesEtalePostcompComp (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (k : V ⟶ W) (hk : IsEtale B S hS k.hom) :
    conjugateEquiv (spacesEtalePostcompBaseChangeAdjunction B S hS (h ≫ k)
          (isEtale_comp B S hS hh hk))
        ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).comp
          (spacesEtalePostcompBaseChangeAdjunction B S hS k hk))
        (spacesEtalePostcompComp B S hS h hh k hk).hom =
      (spacesBaseChange_comp B S hS h k).inv := by
  refine NatTrans.ext (funext fun T ↦ ObjectProperty.hom_ext _ ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (h ≫ k))
    ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj k))
    (spacesEtalePostcompBaseChangeAdjunction B S hS (h ≫ k) (isEtale_comp B S hS hh hk))
    ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).comp
      (spacesEtalePostcompBaseChangeAdjunction B S hS k hk))
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (commIsoComp (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm)
    (commIsoComp (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm)
    (counit_comm_restrictFullyFaithful _ _ _ _ _)
    (counit_comm_comp _ _ _ _ _ _ _ _
      (counit_comm_restrictFullyFaithful _ _ _ _ _)
      (counit_comm_restrictFullyFaithful _ _ _ _ _))
    (Over.mapComp h k).inv (spacesEtalePostcompComp B S hS h hh k hk).hom
    (fun X ↦ by
      simp [spacesEtalePostcompComp, commIsoComp, ObjectProperty.liftCompιIso, Iso.app,
        ObjectProperty.isoMk, ObjectProperty.homMk, spacesEtalePostcomp,
        ObjectProperty.lift]) T
  simp only [ObjectProperty.liftCompιIso, commIsoComp, Iso.app, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.trans_hom,
    Functor.comp_obj, ObjectProperty.ι_obj_lift_obj] at key
  have aux : ∀ {X Y : Over U} (f : X ⟶ Y) (u v : Y ⟶ Y), u = 𝟙 Y → v = 𝟙 Y →
      f ≫ u ≫ v = f := by
    rintro X Y f u v rfl rfl
    simp
  exact ((Category.id_comp _).symm.trans key).trans
    (aux _ _ _ (CategoryTheory.Functor.map_id _ _) rfl)

/-- **The strict composition comparison of the restriction functors on sheaves.** Restriction
along postcomposition with `k` followed by restriction along postcomposition with `h` is
restriction along postcomposition with `h ≫ k`. -/
noncomputable def spacesEtalePostcompSheafComp (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (k : V ⟶ W) (hk : IsEtale B S hS k.hom) :
    (spacesEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS W) ⋙
      (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V) ≅
      (spacesEtalePostcomp B S hS (h ≫ k) (isEtale_comp B S hS hh hk)
        ).sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS W) :=
  Functor.sheafPushforwardContinuousComp' (spacesEtalePostcompComp B S hS h hh k hk)
    (Type (u + 1)) (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V)
    (SpacesEtale.topology B S hS W)

/-- **On sheaves, the adjoint mate of the strict composition comparison of the restriction
functors is the composition comparison of the direct images.** -/
theorem conjugateEquiv_spacesEtalePostcompSheafComp (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (k : V ⟶ W) (hk : IsEtale B S hS k.hom) :
    conjugateEquiv
        ((spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) k hk).comp
          (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) h hh))
        (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) (h ≫ k)
          (isEtale_comp B S hS hh hk))
        (spacesEtalePostcompSheafComp B S hS h hh k hk).inv =
      (spacesEtaleSheafPushforwardComp B S hS h k).inv := by
  have := Functor.isContinuous_comp (spacesEtalePostcomp B S hS h hh)
    (spacesEtalePostcomp B S hS k hk) (SpacesEtale.topology B S hS U)
    (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS W)
  have := Functor.isContinuous_comp (spacesBaseChange B S hS k).functor
    (spacesBaseChange B S hS h).functor (SpacesEtale.topology B S hS W)
    (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U)
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).comp
      (spacesEtalePostcompBaseChangeAdjunction B S hS k hk))
    (spacesEtalePostcompBaseChangeAdjunction B S hS (h ≫ k) (isEtale_comp B S hS hh hk))
    (Type (u + 1)) (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS W)
    (spacesEtalePostcompComp B S hS h hh k hk).hom
  rw [conjugateEquiv_spacesEtalePostcompComp B S hS h hh k hk,
    Adjunction.sheafPushforwardContinuous_comp
      (spacesEtalePostcompBaseChangeAdjunction B S hS h hh)
      (spacesEtalePostcompBaseChangeAdjunction B S hS k hk) (Type (u + 1))
      (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V)
      (SpacesEtale.topology B S hS W)] at ht
  have h1 : (spacesEtalePostcompSheafComp B S hS h hh k hk).inv =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesEtalePostcompComp B S hS h hh k hk).hom (Type (u + 1))
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS W) :=
    Category.comp_id _
  have h2 : (spacesEtaleSheafPushforwardComp B S hS h k).inv =
      Functor.sheafPushforwardContinuousNatTrans (spacesBaseChange_comp B S hS h k).inv
        (Type (u + 1)) (SpacesEtale.topology B S hS W) (SpacesEtale.topology B S hS U) :=
    Category.id_comp _
  rwa [h1, h2]

/-- **The inverse image along an étale morphism is compatible with composition.** For étale
morphisms `h : U ⟶ V` and `k : V ⟶ W` of algebraic spaces, the identification of the inverse
image with restriction along postcomposition carries the composition comparison of the inverse
images — the adjoint mate of the one for the direct images — to the strict composition
comparison of the restriction functors. -/
theorem spacesToposMorphism_inverseImageIso_comp (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (k : V ⟶ W) (hk : IsEtale B S hS k.hom) :
    (spacesEtaleInverseImage_comp B S hS h k).hom ≫
        (Functor.whiskerRight (spacesToposMorphism_inverseImageIso B S hS k hk).hom
            (spacesEtaleInverseImage B S hS h) ≫
          Functor.whiskerLeft
            ((spacesEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS W))
            (spacesToposMorphism_inverseImageIso B S hS h hh).hom) =
      (spacesToposMorphism_inverseImageIso B S hS (h ≫ k)
          (isEtale_comp B S hS hh hk)).hom ≫
        (spacesEtalePostcompSheafComp B S hS h hh k hk).inv := by
  have hA : conjugateEquiv
      ((spacesEtaleAdjunction B S hS k).comp (spacesEtaleAdjunction B S hS h))
      (spacesEtaleAdjunction B S hS (h ≫ k))
      (spacesEtaleInverseImage_comp B S hS h k).hom =
      (spacesEtaleSheafPushforwardComp B S hS h k).inv := Equiv.apply_symm_apply _ _
  have hnat := _root_.Stacks.CategoryTheory.leftAdjointUniq_naturality
    (spacesEtaleAdjunction B S hS (h ≫ k))
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) (h ≫ k)
      (isEtale_comp B S hS hh hk))
    ((spacesEtaleAdjunction B S hS k).comp (spacesEtaleAdjunction B S hS h))
    ((spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) k hk).comp
      (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) h hh))
    (spacesEtaleInverseImage_comp B S hS h k).hom
    (spacesEtalePostcompSheafComp B S hS h hh k hk).inv
    (hA.trans (conjugateEquiv_spacesEtalePostcompSheafComp B S hS h hh k hk).symm)
  rwa [Adjunction.leftAdjointUniq_comp] at hnat

end AlgebraicGeometry.Space

end
