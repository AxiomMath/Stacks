module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.RestrictMates
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates

/-!
# Inverse image along an étale morphism is restriction, coherently

Let `B` be a big étale site. For an étale morphism `f : T' ⟶ T` of its underlying category the
inverse image of small étale sheaves along `f` is restriction along composition with `f`
(`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward`, Stacks 03S3): both functors are
left adjoint to the direct image along `f`. Both sides of that identification carry an identity
and a composition comparison. On the inverse images they are the adjoint mates of those of the
direct images, which are the comparisons the pseudofunctor of small étale sheaves
`AlgebraicGeometry.smallEtaleSheafPullbackSystemGeneral` is built from; on the restriction
functors they are the strict comparisons attached to the identification of composition with an
identity, and of two successive compositions with one composition. This file proves that the
identification is compatible with both.

## Main definitions

* `AlgebraicGeometry.smallEtalePostcomposeId` and `AlgebraicGeometry.smallEtalePostcomposeComp`:
  composition with an identity is the identity, and composition with `h` followed by composition
  with `k` is composition with `h ≫ k`, on the small étale sites;
* `AlgebraicGeometry.smallEtalePostcomposeSheafId` and
  `AlgebraicGeometry.smallEtalePostcomposeSheafComp`: the resulting strict comparisons of the
  restriction functors on sheaves.

## Main results

* `AlgebraicGeometry.conjugateEquiv_smallEtalePostcomposeId` and
  `AlgebraicGeometry.conjugateEquiv_smallEtalePostcomposeComp`: on the sites, the adjoint mates of
  those comparisons are the identity and composition comparisons of base change;
* `AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward_id` and
  `AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward_comp`: **the identification of the
  inverse image along an étale morphism with restriction is compatible with identities and with
  composition.**

## Implementation notes

The argument is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp`, for the bounded
small étale sites of schemes. On the sites both comparisons are restrictions of
`CategoryTheory.Over.mapComp` and `CategoryTheory.Over.pullbackComp` (respectively of
`CategoryTheory.Over.mapId` and `CategoryTheory.Over.pullbackId`), the second being by definition
the adjoint mate of the first, so `CategoryTheory.conjugateEquiv_of_counit_comm_app` transfers the
identity across the restriction. Passing to sheaves is
`CategoryTheory.conjugateEquiv_sheafPushforwardContinuousNatTrans`, and the last step is
uniqueness of a left adjoint, natural in a parameter by
`Stacks.CategoryTheory.leftAdjointUniq_naturality` and compatible with composition by
`CategoryTheory.Adjunction.leftAdjointUniq_comp`.

Nothing here is tagged: the compatibility of Stacks 03S3 with identities and composition is a
coherence the source does not state.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- A composite of morphisms of a big étale site that are étale as morphisms of schemes is étale
as a morphism of schemes. -/
public instance etale_inclusion_map_comp {T'' T' T : B.Scheme} (h : T'' ⟶ T') (k : T' ⟶ T)
    [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)] :
    Etale (B.inclusion.map (h ≫ k)) := by
  rw [Functor.map_comp]
  infer_instance

/-! ### The comparisons on the sites -/

/-- **Composition with an identity is the identity**, on the small étale site of `T`. This is
`CategoryTheory.Over.mapId` restricted to the étale objects. -/
public def smallEtalePostcomposeId (T : B.Scheme) :
    smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B (𝟙 T)) ≅
      𝟭 (SmallEtale B T.1 T.property) :=
  NatIso.ofComponents
    (fun V ↦ (BigEtaleOver.IsEtaleOver B T.1 T.property).isoMk
      ((Over.mapId T).app ((SmallEtale.inclusion B T.1 T.property).obj V)))
    (fun f ↦ ObjectProperty.hom_ext _ (by
      simp [smallEtalePostcompose, SmallEtale.inclusion]))

/-- **Composition with `h` followed by composition with `k` is composition with `h ≫ k`**, on
the small étale sites. This is `CategoryTheory.Over.mapComp` restricted to the étale objects. -/
public def smallEtalePostcomposeComp {T'' T' T : B.Scheme} (h : T'' ⟶ T') (k : T' ⟶ T)
    [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)] :
    smallEtalePostcompose B T'.1 T'.property (SmallEtale.ofEtaleHom B h) ⋙
        smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k) ≅
      smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B (h ≫ k)) :=
  NatIso.ofComponents
    (fun V ↦ (BigEtaleOver.IsEtaleOver B T.1 T.property).isoMk
      ((Over.mapComp h k).symm.app ((SmallEtale.inclusion B T''.1 T''.property).obj V)))
    (fun f ↦ ObjectProperty.hom_ext _ (by
      simpa [smallEtalePostcompose, SmallEtale.inclusion] using
        (Over.mapComp h k).symm.hom.naturality
          ((SmallEtale.inclusion B T''.1 T''.property).map f)))

section

-- Base change is defined by lifting slice pullback along a full subcategory inclusion, so
-- recognizing a base-changed object as the corresponding slice pullback is a round trip through
-- structure projections, which instance-level definitional unfolding has to see through.
attribute [local implicit_reducible] smallEtaleBaseChange

/-- **On the sites, the adjoint mate of the identity comparison for composition is the identity
comparison for base change.** -/
public theorem conjugateEquiv_smallEtalePostcomposeId (T : B.Scheme) :
    conjugateEquiv (smallEtalePostcomposeBaseChangeAdjunction B (𝟙 T))
        (Adjunction.id (C := SmallEtale B T.1 T.property))
        (smallEtalePostcomposeId B T).inv =
      (smallEtaleBaseChange_idIso B T).hom := by
  refine NatTrans.ext (funext fun V ↦
    (SmallEtale.inclusion B T.1 T.property).map_injective ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (𝟙 T))
    (Adjunction.id (C := Over T))
    (smallEtalePostcomposeBaseChangeAdjunction B (𝟙 T))
    (Adjunction.id (C := SmallEtale B T.1 T.property))
    (eqToIso (smallEtalePostcompose_comp_inclusion B T.1 T.property
      (SmallEtale.ofEtaleHom B (𝟙 T))).symm)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B (𝟙 T)).symm)
    (Iso.refl _) (Iso.refl _)
    (counit_comm_restrictFullyFaithful _ _ _ _ _ )
    (fun Y ↦ by simp)
    (Over.mapId T).inv (smallEtalePostcomposeId B T).inv
    (fun X ↦ by
      simp [smallEtalePostcomposeId, ObjectProperty.isoMk, ObjectProperty.homMk,
        smallEtalePostcompose, ObjectProperty.lift]
      exact Category.comp_id _) V
  have hpb : conjugateEquiv (Over.mapPullbackAdj (𝟙 T)) (Adjunction.id (C := Over T))
      (Over.mapId T).inv = (Over.pullbackId (X := T)).hom := rfl
  rw [hpb] at key
  have hid : (SmallEtale.inclusion B T.1 T.property).map
      ((smallEtaleBaseChange_idIso B T).hom.app V) = Over.pullbackId.hom.app V.obj := by
    simp only [smallEtaleBaseChange_idIso, Functor.fullyFaithfulCancelRight]
    simp
    exact (SmallEtale.inclusion B T.1 T.property).map_preimage _
  exact (Category.id_comp _).symm.trans (key.trans ((Category.comp_id _).trans hid.symm))

end

/-- **On the sites, the adjoint mate of the composition comparison for composition is the
composition comparison for base change.** -/
public theorem conjugateEquiv_smallEtalePostcomposeComp {T'' T' T : B.Scheme} (h : T'' ⟶ T')
    (k : T' ⟶ T) [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)] :
    conjugateEquiv (smallEtalePostcomposeBaseChangeAdjunction B (h ≫ k))
        ((smallEtalePostcomposeBaseChangeAdjunction B h).comp
          (smallEtalePostcomposeBaseChangeAdjunction B k))
        (smallEtalePostcomposeComp B h k).hom =
      (smallEtaleBaseChange_compIso B T'' T' T h k).val.inv := by
  refine NatTrans.ext (funext fun V ↦
    (SmallEtale.inclusion B T''.1 T''.property).map_injective ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (h ≫ k))
    ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj k))
    (smallEtalePostcomposeBaseChangeAdjunction B (h ≫ k))
    ((smallEtalePostcomposeBaseChangeAdjunction B h).comp
      (smallEtalePostcomposeBaseChangeAdjunction B k))
    (eqToIso (smallEtalePostcompose_comp_inclusion B T.1 T.property
      (SmallEtale.ofEtaleHom B (h ≫ k))).symm)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B (h ≫ k)).symm)
    (commIsoComp (eqToIso (smallEtalePostcompose_comp_inclusion B T'.1 T'.property
        (SmallEtale.ofEtaleHom B h)).symm)
      (eqToIso (smallEtalePostcompose_comp_inclusion B T.1 T.property
        (SmallEtale.ofEtaleHom B k)).symm))
    (commIsoComp (eqToIso (smallEtaleBaseChange_comp_inclusion B k).symm)
      (eqToIso (smallEtaleBaseChange_comp_inclusion B h).symm))
    (counit_comm_restrictFullyFaithful _ _ _ _ _)
    (counit_comm_comp _ _ _ _ _ _ _ _
      (counit_comm_restrictFullyFaithful _ _ _ _ _)
      (counit_comm_restrictFullyFaithful _ _ _ _ _))
    (Over.mapComp h k).inv (smallEtalePostcomposeComp B h k).hom
    (fun X ↦ by
      simp [smallEtalePostcomposeComp, commIsoComp, ObjectProperty.isoMk,
        ObjectProperty.homMk, smallEtalePostcompose, ObjectProperty.lift]
      exact Category.comp_id _) V
  have hpb : conjugateEquiv (Over.mapPullbackAdj (h ≫ k))
      ((Over.mapPullbackAdj h).comp (Over.mapPullbackAdj k))
      (Over.mapComp h k).inv = (Over.pullbackComp h k).hom := rfl
  rw [hpb] at key
  have hc : (SmallEtale.inclusion B T''.1 T''.property).map
      ((smallEtaleBaseChange_compIso B T'' T' T h k).val.inv.app V) =
      (Over.pullbackComp h k).hom.app V.obj := by
    have hh : (SmallEtale.inclusion B T''.1 T''.property).mapIso
        ((smallEtaleBaseChange_compIso B T'' T' T h k).val.app V) =
        (Over.pullbackComp h k).symm.app V.obj :=
      Iso.ext (smallEtaleBaseChange_compIso_app B T'' T' T h k V)
    exact congrArg Iso.inv hh
  simp only [commIsoComp_hom_app, Functor.comp_obj, eqToIso.hom] at key
  refine (Category.id_comp _).symm.trans (key.trans ?_)
  refine Eq.trans ?_ hc.symm
  refine (congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)
  exact (congrArg (· ≫ _) ((congrArg (Over.pullback h).map (rfl : _ = 𝟙 _)).trans
    ((Over.pullback h).map_id _))).trans (Category.id_comp _)

/-! ### The comparisons on sheaves -/

/-- Base change along an étale morphism `f : T' ⟶ T` is continuous, with its target written as
the small étale site of the source of `SmallEtale.ofEtaleHom B f`. This is the spelling in which
base change occurs in the type of `AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction`,
and instance search does not identify it with `T'`. -/
public instance isContinuous_smallEtaleBaseChange_ofEtaleHom_source {T' T : B.Scheme}
    (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    Functor.IsContinuous (C := SmallEtale B T.1 T.property) (D := SmallEtale B T'.1 T'.property)
      (@smallEtaleBaseChange B T (SmallEtale.ofEtaleHom B f).obj.left f)
      (SmallEtale.topology B T.1 T.property) (SmallEtale.topology B T'.1 T'.property) :=
  smallEtaleBaseChange_isContinuous B f

/-- Composition with an étale morphism `f : T' ⟶ T` is continuous, with its source written as the
small étale site of `T'` rather than of the source of `SmallEtale.ofEtaleHom B f`. The two are the
same site and not the same term, and instance search does not identify them: this is the spelling
in which the source arises when composition with `f` is composed with another functor of sites,
as in `AlgebraicGeometry.smallEtalePostcomposeSheafComp`. -/
public instance isContinuous_smallEtalePostcompose_ofEtaleHom_source {T' T : B.Scheme}
    (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    Functor.IsContinuous (C := SmallEtale B T'.1 T'.property)
      (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f))
      (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property) :=
  isContinuous_smallEtalePostcompose_ofEtaleHom B f

variable (A : Type*) [Category A]

/-- **The strict identity comparison of the restriction functor on sheaves.** Restriction along
composition with `𝟙 T` is the identity functor on small étale sheaves of `T`. -/
public def smallEtalePostcomposeSheafId (T : B.Scheme) :
    (smallEtalePostcompose B T.1 T.property
        (SmallEtale.ofEtaleHom B (𝟙 T))).sheafPushforwardContinuous A
        (SmallEtale.topology B T.1 T.property) (SmallEtale.topology B T.1 T.property) ≅
      𝟭 (Sheaf (SmallEtale.topology B T.1 T.property) A) :=
  Functor.sheafPushforwardContinuousId' (smallEtalePostcomposeId B T) A
    (SmallEtale.topology B T.1 T.property)

/-- **The strict composition comparison of the restriction functors on sheaves.** Restriction
along composition with `k` followed by restriction along composition with `h` is restriction
along composition with `h ≫ k`. -/
public def smallEtalePostcomposeSheafComp {T'' T' T : B.Scheme} (h : T'' ⟶ T') (k : T' ⟶ T)
    [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)] :
    (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous
        A (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property) ⋙
      (smallEtalePostcompose B T'.1 T'.property
        (SmallEtale.ofEtaleHom B h)).sheafPushforwardContinuous
        A (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T'.1 T'.property) ≅
      (smallEtalePostcompose B T.1 T.property
        (SmallEtale.ofEtaleHom B (h ≫ k))).sheafPushforwardContinuous
        A (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T.1 T.property) :=
  Functor.sheafPushforwardContinuousComp' (smallEtalePostcomposeComp B h k) A
    (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T'.1 T'.property)
    (SmallEtale.topology B T.1 T.property)

/-- **On sheaves, the adjoint mate of the strict identity comparison of the restriction functor
is the identity comparison of the direct images.** -/
public theorem conjugateEquiv_smallEtalePostcomposeSheafId (T : B.Scheme) :
    conjugateEquiv (Adjunction.id (C := Sheaf (SmallEtale.topology B T.1 T.property) A))
        (smallEtalePostcomposePushforwardAdjunction B (𝟙 T) A)
        (smallEtalePostcomposeSheafId B A T).hom =
      (Functor.sheafPushforwardContinuousId' (C := SmallEtale B T.1 T.property)
        (smallEtaleBaseChange_idIso B T) A (SmallEtale.topology B T.1 T.property)).inv := by
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    (C := SmallEtale B T.1 T.property) (D := SmallEtale B T.1 T.property)
    (Adjunction.id (C := SmallEtale B T.1 T.property))
    (smallEtalePostcomposeBaseChangeAdjunction B (𝟙 T))
    A (SmallEtale.topology B T.1 T.property) (SmallEtale.topology B T.1 T.property)
    (smallEtalePostcomposeId B T).inv
  rw [conjugateEquiv_smallEtalePostcomposeId B T,
    Adjunction.sheafPushforwardContinuous_id] at ht
  exact (congrArg _ (Category.comp_id _)).trans (ht.trans (Category.id_comp _).symm)

/-- **On sheaves, the adjoint mate of the strict composition comparison of the restriction
functors is the composition comparison of the direct images.** -/
public theorem conjugateEquiv_smallEtalePostcomposeSheafComp {T'' T' T : B.Scheme}
    (h : T'' ⟶ T') (k : T' ⟶ T) [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)] :
    conjugateEquiv
        ((smallEtalePostcomposePushforwardAdjunction B k A).comp
          (smallEtalePostcomposePushforwardAdjunction B h A))
        (smallEtalePostcomposePushforwardAdjunction B (h ≫ k) A)
        (smallEtalePostcomposeSheafComp B A h k).inv =
      (smallEtaleSheafPushforwardCompIso B T'' T' T h k A).hom := by
  have := Functor.isContinuous_comp
    (smallEtalePostcompose B T'.1 T'.property (SmallEtale.ofEtaleHom B h))
    (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B k))
    (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T'.1 T'.property)
    (SmallEtale.topology B T.1 T.property)
  have := Functor.isContinuous_comp (smallEtaleBaseChange B k) (smallEtaleBaseChange B h)
    (SmallEtale.topology B T.1 T.property) (SmallEtale.topology B T'.1 T'.property)
    (SmallEtale.topology B T''.1 T''.property)
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    (C := SmallEtale B T''.1 T''.property) (D := SmallEtale B T.1 T.property)
    ((smallEtalePostcomposeBaseChangeAdjunction B h).comp
      (smallEtalePostcomposeBaseChangeAdjunction B k))
    (smallEtalePostcomposeBaseChangeAdjunction B (h ≫ k))
    A (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T.1 T.property)
    (smallEtalePostcomposeComp B h k).hom
  rw [conjugateEquiv_smallEtalePostcomposeComp B h k,
    Adjunction.sheafPushforwardContinuous_comp (C := SmallEtale B T''.1 T''.property)
      (D := SmallEtale B T'.1 T'.property) (E := SmallEtale B T.1 T.property)
      (smallEtalePostcomposeBaseChangeAdjunction B h)
      (smallEtalePostcomposeBaseChangeAdjunction B k) A
      (SmallEtale.topology B T''.1 T''.property) (SmallEtale.topology B T'.1 T'.property)
      (SmallEtale.topology B T.1 T.property)] at ht
  exact (congrArg _ (Category.comp_id _)).trans (ht.trans (Category.id_comp _).symm)

/-! ### Compatibility of the identification with identities and composition -/

/-- **The identification of the inverse image along an étale morphism with restriction is
compatible with identities.** The identity comparison of the inverse image along `𝟙 T` — the
adjoint mate of the identity comparison of the direct image — is the identification with
restriction along composition with `𝟙 T`, followed by the strict identity comparison of that
restriction functor. -/
public theorem smallInverseImageIsoPostcomposePushforward_id (T : B.Scheme)
    [((smallEtaleBaseChange B (𝟙 T)).sheafPushforwardContinuous A
      (SmallEtale.topology B T.1 T.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint] :
    (Adjunction.leftAdjointIdIso (B.smallPullbackAdjunction (𝟙 T) A)
        (Functor.sheafPushforwardContinuousId' (C := SmallEtale B T.1 T.property)
          (smallEtaleBaseChange_idIso B T) A (SmallEtale.topology B T.1 T.property))).hom =
      (smallInverseImageIsoPostcomposePushforward B (𝟙 T) A).hom ≫
        (smallEtalePostcomposeSheafId B A T).hom := by
  have hA := Adjunction.conjugateEquiv_leftAdjointIdIso_hom (B.smallPullbackAdjunction (𝟙 T) A)
    (Functor.sheafPushforwardContinuousId' (C := SmallEtale B T.1 T.property)
      (smallEtaleBaseChange_idIso B T) A (SmallEtale.topology B T.1 T.property))
  have hnat := Stacks.CategoryTheory.leftAdjointUniq_naturality
    (B.smallPullbackAdjunction (𝟙 T) A) (smallEtalePostcomposePushforwardAdjunction B (𝟙 T) A)
    (Adjunction.id (C := Sheaf (SmallEtale.topology B T.1 T.property) A))
    (Adjunction.id (C := Sheaf (SmallEtale.topology B T.1 T.property) A))
    _ (smallEtalePostcomposeSheafId B A T).hom
    (hA.trans (conjugateEquiv_smallEtalePostcomposeSheafId B A T).symm)
  rw [Adjunction.leftAdjointUniq_refl] at hnat
  exact (Category.comp_id _).symm.trans hnat

/-- **The identification of the inverse image along an étale morphism with restriction is
compatible with composition.** For étale `h : T'' ⟶ T'` and `k : T' ⟶ T`, the composition
comparison of the inverse images — the adjoint mate of the one of the direct images — is carried
by the identifications with restriction to the strict composition comparison of the restriction
functors. -/
public theorem smallInverseImageIsoPostcomposePushforward_comp {T'' T' T : B.Scheme}
    (h : T'' ⟶ T') (k : T' ⟶ T) [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)]
    [((smallEtaleBaseChange B h).sheafPushforwardContinuous A
      (SmallEtale.topology B T'.1 T'.property)
      (SmallEtale.topology B T''.1 T''.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B k).sheafPushforwardContinuous A
      (SmallEtale.topology B T.1 T.property)
      (SmallEtale.topology B T'.1 T'.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B (h ≫ k)).sheafPushforwardContinuous A
      (SmallEtale.topology B T.1 T.property)
      (SmallEtale.topology B T''.1 T''.property)).IsRightAdjoint] :
    (Adjunction.leftAdjointCompIso (B.smallPullbackAdjunction k A)
        (B.smallPullbackAdjunction h A) (B.smallPullbackAdjunction (h ≫ k) A)
        (smallEtaleSheafPushforwardCompIso B T'' T' T h k A)).inv ≫
        (Functor.whiskerRight (smallInverseImageIsoPostcomposePushforward B k A).hom
            (B.smallInverseImage h A) ≫
          Functor.whiskerLeft
            ((smallEtalePostcompose B T.1 T.property
              (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous A
              (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property))
            (smallInverseImageIsoPostcomposePushforward B h A).hom) =
      (smallInverseImageIsoPostcomposePushforward B (h ≫ k) A).hom ≫
        (smallEtalePostcomposeSheafComp B A h k).inv := by
  have hA := Adjunction.conjugateEquiv_leftAdjointCompIso_inv (B.smallPullbackAdjunction k A)
    (B.smallPullbackAdjunction h A) (B.smallPullbackAdjunction (h ≫ k) A)
    (smallEtaleSheafPushforwardCompIso B T'' T' T h k A)
  have hnat := Stacks.CategoryTheory.leftAdjointUniq_naturality
    (B.smallPullbackAdjunction (h ≫ k) A)
    (smallEtalePostcomposePushforwardAdjunction B (h ≫ k) A)
    ((B.smallPullbackAdjunction k A).comp (B.smallPullbackAdjunction h A))
    ((smallEtalePostcomposePushforwardAdjunction B k A).comp
      (smallEtalePostcomposePushforwardAdjunction B h A))
    _ (smallEtalePostcomposeSheafComp B A h k).inv
    (hA.trans (conjugateEquiv_smallEtalePostcomposeSheafComp B A h k).symm)
  rwa [Adjunction.leftAdjointUniq_comp] at hnat

end AlgebraicGeometry

end
