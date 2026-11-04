module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Pseudofunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.RestrictMates
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp
public import StacksFrontier.CategoryTheory.Sites.ContinuousPushforwardMates
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Coherence
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent

/-!
# Inverse image along an étale morphism is restriction, compatibly with composition

For an étale morphism `f : T' ⟶ T` of a big étale site, inverse image of small étale sheaves
along `f` is restriction along composition with `f`
(`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward`, Stacks 03S3): both functors
are left adjoint to the direct image. Both sides carry an identity and a composition comparison:
on the inverse images they are the adjoint mates of those of the direct images, and on the
restriction functors they are the strict comparisons induced by
`CategoryTheory.Over.mapId` and `CategoryTheory.Over.mapComp`. This file proves that the
identification is compatible with them.

The argument is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp` for algebraic
spaces: on the sites the comparisons for base change are by definition the adjoint mates of
those for composition, restriction of sheaves commutes with mates, and uniqueness of
left adjoints is natural.

## Main definitions

* `AlgebraicGeometry.SmallEtaleGluing.post` — composition with an étale morphism, on small étale
  sites.
* `AlgebraicGeometry.SmallEtaleGluing.postCompIso`, `AlgebraicGeometry.SmallEtaleGluing.postIdIso`
  — its composition and identity comparisons.
* `AlgebraicGeometry.SmallEtaleGluing.pullbackIsoRestriction` — inverse image along an étale
  morphism is restriction along composition with it.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.pullbackIsoRestriction_comp` — compatibility with
  composition.
* `AlgebraicGeometry.SmallEtaleGluing.pullbackIsoRestriction_id` — compatibility with
  identities.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

namespace SmallEtaleGluing

variable (B : BigEtaleSite.{u})

/-- Composition with an étale morphism `f : T' ⟶ T` of `B`, as a functor between the small étale
sites of `T'` and of `T`. -/
public abbrev post {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    SmallEtale B T'.1 T'.property ⥤ SmallEtale B T.1 T.property :=
  smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)

/-- A composite of étale morphisms of `B` is étale. -/
public instance etale_inclusion_map_comp {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] :
    Etale (B.inclusion.map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

/-- An identity morphism of `B` is étale. -/
public instance etale_inclusion_map_id (X : B.Scheme) : Etale (B.inclusion.map (𝟙 X)) := by
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- Composition with an étale morphism is continuous. -/
public instance post_isContinuous {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    (post B f).IsContinuous (SmallEtale.topology B T'.1 T'.property)
      (SmallEtale.topology B T.1 T.property) :=
  isContinuous_smallEtalePostcompose_ofEtaleHom B f

/-- The adjunction between composition with an étale morphism and base change along it: the
restriction of `CategoryTheory.Over.mapPullbackAdj` to the étale objects. -/
public def postAdj {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    post B f ⊣ smallEtaleBaseChange B f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- **Composition with étale morphisms is compatible with composition.** -/
public def postCompIso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))] :
    post B f ⋙ post B g ≅ post B (f ≫ g) :=
  NatIso.ofComponents
    (fun T ↦ (BigEtaleOver.IsEtaleOver B Z.1 Z.property).isoMk
      ((Over.mapComp f g).symm.app ((SmallEtale.inclusion B X.1 X.property).obj T)))
    (fun a ↦ ObjectProperty.hom_ext _
      ((Over.mapComp f g).symm.hom.naturality ((SmallEtale.inclusion B X.1 X.property).map a)))

/-- **On the sites, the adjoint mate of the composition comparison for composition is the one
for base change.** -/
public theorem conjugateEquiv_postCompIso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))] :
    conjugateEquiv (postAdj B (f ≫ g)) ((postAdj B f).comp (postAdj B g))
        (postCompIso B f g).hom =
      (smallEtaleBaseChange_compIso B X Y Z f g).val.inv := by
  refine NatTrans.ext (funext fun T ↦ ObjectProperty.hom_ext _ ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (postAdj B (f ≫ g))
    ((postAdj B f).comp (postAdj B g))
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (commIsoComp (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm)
    (commIsoComp (ObjectProperty.liftCompιIso _ _ _).symm
      (ObjectProperty.liftCompιIso _ _ _).symm)
    (counit_comm_restrictFullyFaithful _ _ _ _ _)
    (counit_comm_comp _ _ _ _ _ _ _ _
      (counit_comm_restrictFullyFaithful _ _ _ _ _)
      (counit_comm_restrictFullyFaithful _ _ _ _ _))
    (Over.mapComp f g).inv (postCompIso B f g).hom
    (fun X ↦ by
      simp [postCompIso, commIsoComp, ObjectProperty.liftCompιIso, Iso.app,
        ObjectProperty.isoMk, ObjectProperty.homMk, ObjectProperty.lift]
      rfl) T
  simp only [ObjectProperty.liftCompιIso, commIsoComp, Iso.app, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.trans_hom,
    Functor.comp_obj, ObjectProperty.ι_obj_lift_obj] at key
  have aux : ∀ {P Q : Over (B.obj X.1 X.property)} (a : P ⟶ Q) (b c : Q ⟶ Q), b = 𝟙 Q →
      c = 𝟙 Q → a ≫ b ≫ c = a := by
    rintro P Q a b c rfl rfl
    simp
  have h2 := baseChangeComp_inv B f g T
  refine ((Category.id_comp _).symm.trans key).trans
    ((aux _ _ _ (CategoryTheory.Functor.map_id _ _) rfl).trans ?_)
  exact h2.symm

/-- **Composition with an identity is the identity.** -/
public def postIdIso (X : B.Scheme) [Etale (B.inclusion.map (𝟙 X))] :
    post B (𝟙 X) ≅ 𝟭 (SmallEtale B X.1 X.property) :=
  NatIso.ofComponents
    (fun T ↦ (BigEtaleOver.IsEtaleOver B X.1 X.property).isoMk
      ((Over.mapId _).app ((SmallEtale.inclusion B X.1 X.property).obj T)))
    (fun a ↦ ObjectProperty.hom_ext _
      ((Over.mapId _).hom.naturality ((SmallEtale.inclusion B X.1 X.property).map a)))

/-- **On the sites, the adjoint mate of the identity comparison for composition is the one for
base change.** -/
public theorem conjugateEquiv_postIdIso (X : B.Scheme) [Etale (B.inclusion.map (𝟙 X))] :
    conjugateEquiv (postAdj B (𝟙 X)) (Adjunction.id (C := SmallEtale B X.1 X.property))
        (postIdIso B X).inv =
      (smallEtaleBaseChange_idIso B X).hom := by
  refine NatTrans.ext (funext fun T ↦ ObjectProperty.hom_ext _ ?_)
  have key := conjugateEquiv_of_counit_comm_app
    (Over.mapPullbackAdj (𝟙 (B.obj X.1 X.property)))
    (Adjunction.id (C := Over (B.obj X.1 X.property)))
    (postAdj B (𝟙 X))
    (Adjunction.id (C := SmallEtale B X.1 X.property))
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm
    (Iso.refl _) (Iso.refl _)
    (counit_comm_restrictFullyFaithful _ _ _ _ _)
    (fun Y => by simp)
    (Over.mapId _).inv (postIdIso B X).inv
    (fun X ↦ by
      simp [postIdIso, ObjectProperty.liftCompιIso,
        ObjectProperty.isoMk, ObjectProperty.homMk, ObjectProperty.lift]
      rfl) T
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, ObjectProperty.ι_obj_lift_obj] at key
  refine ((Category.id_comp _).symm.trans (key.trans (Category.comp_id _))).trans ?_
  exact (smallEtaleBaseChange_idIso_hom_inclusion B X T).symm

variable (A : Type t) [Category.{v} A]

/-- The adjunction between restriction along composition with an étale morphism and the direct
image along it. -/
public abbrev postSheafAdj {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    (post B f).sheafPushforwardContinuous A (SmallEtale.topology B T'.1 T'.property)
        (SmallEtale.topology B T.1 T.property) ⊣ pushforward B A f :=
  (postAdj B f).sheafPushforwardContinuous (E := A) (SmallEtale.topology B T'.1 T'.property)
    (SmallEtale.topology B T.1 T.property)

/-- The strict composition comparison of restriction along composition with étale morphisms. -/
public def postSheafCompIso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))] :
    (post B g).sheafPushforwardContinuous A (SmallEtale.topology B Y.1 Y.property)
        (SmallEtale.topology B Z.1 Z.property) ⋙
      (post B f).sheafPushforwardContinuous A (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Y.1 Y.property) ≅
      (post B (f ≫ g)).sheafPushforwardContinuous A (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B Z.1 Z.property) :=
  Functor.sheafPushforwardContinuousComp' (postCompIso B f g) A _ _ _

/-- **On sheaves, the adjoint mate of the strict composition comparison of the restriction
functors is the composition comparison of the direct images.** -/
public theorem conjugateEquiv_postSheafCompIso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))] :
    conjugateEquiv ((postSheafAdj B A g).comp (postSheafAdj B A f)) (postSheafAdj B A (f ≫ g))
        (postSheafCompIso B A f g).inv =
      (pushforwardComp B A f g).inv := by
  have := Functor.isContinuous_comp (post B f) (post B g)
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B Z.1 Z.property)
  have := Functor.isContinuous_comp (smallEtaleBaseChange B g) (smallEtaleBaseChange B f)
    (SmallEtale.topology B Z.1 Z.property) (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    ((postAdj B f).comp (postAdj B g)) (postAdj B (f ≫ g)) A
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Z.1 Z.property)
    (postCompIso B f g).hom
  rw [conjugateEquiv_postCompIso B f g,
    Adjunction.sheafPushforwardContinuous_comp (postAdj B f) (postAdj B g) A
      (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B Y.1 Y.property)
      (SmallEtale.topology B Z.1 Z.property)] at ht
  exact (congrArg _ (Category.comp_id _)).trans (ht.trans (Category.id_comp _).symm)

/-- The strict identity comparison of restriction along composition with an identity. -/
public def postSheafIdIso (X : B.Scheme) [Etale (B.inclusion.map (𝟙 X))] :
    (post B (𝟙 X)).sheafPushforwardContinuous A (SmallEtale.topology B X.1 X.property)
        (SmallEtale.topology B X.1 X.property) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (postIdIso B X) A _

/-- **On sheaves, the adjoint mate of the strict identity comparison of the restriction functor
is the identity comparison of the direct images.** -/
public theorem conjugateEquiv_postSheafIdIso (X : B.Scheme) [Etale (B.inclusion.map (𝟙 X))] :
    conjugateEquiv (Adjunction.id (C := Sheaf (SmallEtale.topology B X.1 X.property) A))
        (postSheafAdj B A (𝟙 X)) (postSheafIdIso B A X).hom =
      (pushforwardId B A X).inv := by
  have ht := conjugateEquiv_sheafPushforwardContinuousNatTrans
    (Adjunction.id (C := SmallEtale B X.1 X.property)) (postAdj B (𝟙 X)) A
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B X.1 X.property)
    (postIdIso B X).inv
  rw [conjugateEquiv_postIdIso B X, Adjunction.sheafPushforwardContinuous_id] at ht
  exact (congrArg _ (Category.comp_id _)).trans (ht.trans (Category.id_comp _).symm)

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Inverse image along an étale morphism is restriction along composition with it**: both
are left adjoint to the direct image. -/
public def pullbackIsoRestriction {T' T : B.Scheme} (f : T' ⟶ T) [Etale (B.inclusion.map f)] :
    smallEtaleSheafPullback B A f ≅
      (post B f).sheafPushforwardContinuous A (SmallEtale.topology B T'.1 T'.property)
        (SmallEtale.topology B T.1 T.property) :=
  Adjunction.leftAdjointUniq ((smallEtaleBaseChange B f).sheafAdjunctionContinuous A _ _)
    (postSheafAdj B A f)

/-- **The identification of inverse image with restriction is compatible with composition.** -/
public theorem pullbackIsoRestriction_comp {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))] :
    (smallEtaleSheafPullbackCompIso B X Y Z f g A).inv ≫
        (Functor.whiskerRight (pullbackIsoRestriction B A g).hom (smallEtaleSheafPullback B A f) ≫
          Functor.whiskerLeft ((post B g).sheafPushforwardContinuous A
              (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B Z.1 Z.property))
            (pullbackIsoRestriction B A f).hom) =
      (pullbackIsoRestriction B A (f ≫ g)).hom ≫ (postSheafCompIso B A f g).inv := by
  have hA : conjugateEquiv
      (((smallEtaleBaseChange B g).sheafAdjunctionContinuous A _ _).comp
        ((smallEtaleBaseChange B f).sheafAdjunctionContinuous A _ _))
      ((smallEtaleBaseChange B (f ≫ g)).sheafAdjunctionContinuous A _ _)
      (smallEtaleSheafPullbackCompIso B X Y Z f g A).inv =
      (pushforwardComp B A f g).inv :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hnat := Stacks.CategoryTheory.leftAdjointUniq_naturality
    ((smallEtaleBaseChange B (f ≫ g)).sheafAdjunctionContinuous A _ _)
    (postSheafAdj B A (f ≫ g))
    (((smallEtaleBaseChange B g).sheafAdjunctionContinuous A _ _).comp
        ((smallEtaleBaseChange B f).sheafAdjunctionContinuous A _ _))
    ((postSheafAdj B A g).comp (postSheafAdj B A f))
    (smallEtaleSheafPullbackCompIso B X Y Z f g A).inv
    (postSheafCompIso B A f g).inv
    (hA.trans (conjugateEquiv_postSheafCompIso B A f g).symm)
  rw [Adjunction.leftAdjointUniq_comp] at hnat
  exact hnat

/-- **The identification of inverse image with restriction is compatible with identities.** -/
public theorem pullbackIsoRestriction_id (X : B.Scheme) [Etale (B.inclusion.map (𝟙 X))] :
    (conjugateEquiv Adjunction.id
        ((smallEtaleBaseChange B (𝟙 X)).sheafAdjunctionContinuous A _ _)).symm
        (pushforwardId B A X).inv =
      (pullbackIsoRestriction B A (𝟙 X)).hom ≫ (postSheafIdIso B A X).hom := by
  have hnat := Stacks.CategoryTheory.leftAdjointUniq_naturality
    ((smallEtaleBaseChange B (𝟙 X)).sheafAdjunctionContinuous A _ _)
    (postSheafAdj B A (𝟙 X))
    (Adjunction.id (C := Sheaf (SmallEtale.topology B X.1 X.property) A))
    (Adjunction.id (C := Sheaf (SmallEtale.topology B X.1 X.property) A))
    ((conjugateEquiv Adjunction.id
        ((smallEtaleBaseChange B (𝟙 X)).sheafAdjunctionContinuous A _ _)).symm
        (pushforwardId B A X).inv)
    (postSheafIdIso B A X).hom
    ((Equiv.apply_symm_apply _ _).trans (conjugateEquiv_postSheafIdIso B A X).symm)
  rw [Adjunction.leftAdjointUniq_refl] at hnat
  exact (Category.comp_id _).symm.trans hnat

end SmallEtaleGluing

end AlgebraicGeometry

end
