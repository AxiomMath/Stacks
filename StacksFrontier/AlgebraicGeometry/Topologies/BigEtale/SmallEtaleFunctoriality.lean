module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Inverse and direct image of small étale sheaves

Let `B` be a big étale site. Base change along a morphism `f : T ⟶ S` of its underlying category
is a continuous functor between the small étale sites of `S` and of `T`, so it induces a direct
image on sheaves and — the pushforward having a left adjoint — an inverse image as well. This
file names those two functors and their adjunction at an arbitrary coefficient category, and
adds the two further pieces of functoriality that the comparison of big and small étale sheaves
needs:

* the direct-image comparison for a composite, at arbitrary coefficients;
* for an *étale* morphism `f`, the left adjoint of base change on sites, namely composition
  with `f`, and hence the identification of inverse image along `f` with a direct image.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.smallInverseImage` and
  `AlgebraicGeometry.BigEtaleSite.smallPushforward` — inverse and direct image of small étale
  sheaves along base change, with `AlgebraicGeometry.BigEtaleSite.smallPullbackAdjunction` the
  adjunction between them.
* `AlgebraicGeometry.smallEtaleSheafPushforwardCompIso` — the direct-image comparison for a
  composite of morphisms.
* `AlgebraicGeometry.SmallEtale.ofEtaleHom` — an étale morphism of the site, viewed as an object
  of the small étale site of its target.
* `AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction` — composition with an étale
  morphism is left adjoint to base change along it.

## Main results

* `AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward` — for an étale morphism `f`,
  inverse image along `f` is the direct image of composition with `f`.
* `AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction_unit_app` identifies the unit of
  that adjunction on the nose, which is what computes the preceding isomorphism on sections, and
  `AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward_inv_app_comp` reads a morphism
  out of an inverse image off its adjoint.

## Implementation notes

The coefficient category is a parameter throughout. The existing comparison
`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso` of direct images is the special case
of `AlgebraicGeometry.smallEtaleSheafPushforwardCompIso` at coefficients `Type (u + 1)`, in the
same way as `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` generalises
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`.

The adjunction between composition with an étale morphism and base change along it is
transported from `CategoryTheory.Over.mapPullbackAdj` through the two fully faithful inclusions
of the small étale sites, using that both legs commute with those inclusions on the nose.

## References

* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

namespace BigEtaleSite

/-- Inverse image of small étale sheaves along base change in a big étale site: the chosen left
adjoint of the direct image `AlgebraicGeometry.BigEtaleSite.smallPushforward`. -/
public abbrev smallInverseImage {S T : B.Scheme} (f : T ⟶ S) (A : Type u₁) [Category.{v₁} A]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint] :
    Sheaf (SmallEtale.topology B S.1 S.property) A ⥤
      Sheaf (SmallEtale.topology B T.1 T.property) A :=
  (smallEtaleBaseChange B f).sheafPullback A
    (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property)

/-- Direct image of small étale sheaves along base change in a big étale site: restriction of a
sheaf on the small étale site of `T` along base change, which is continuous. -/
public abbrev smallPushforward {S T : B.Scheme} (f : T ⟶ S) (A : Type u₁) [Category.{v₁} A] :
    Sheaf (SmallEtale.topology B T.1 T.property) A ⥤
      Sheaf (SmallEtale.topology B S.1 S.property) A :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property)

/-- Inverse image of small étale sheaves is left adjoint to direct image. -/
public def smallPullbackAdjunction {S T : B.Scheme} (f : T ⟶ S) (A : Type u₁) [Category.{v₁} A]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint] :
    smallInverseImage B f A ⊣ smallPushforward B f A :=
  (smallEtaleBaseChange B f).sheafAdjunctionContinuous A
    (SmallEtale.topology B S.1 S.property) (SmallEtale.topology B T.1 T.property)

end BigEtaleSite

/-- **Stacks 021J.** Direct image along a composite of morphisms of a big étale site is the
composite of the direct images, for any coefficient category. -/
public def smallEtaleSheafPushforwardCompIso (X Y Z : B.Scheme) (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u₁) [Category.{v₁} A] :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property) ⋙
      (smallEtaleBaseChange B g).sheafPushforwardContinuous A
        (SmallEtale.topology B Z.1 Z.property) (SmallEtale.topology B Y.1 Y.property) ≅
    (smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.1 Z.property) (SmallEtale.topology B X.1 X.property) :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_compIso B X Y Z f g).val A
    (SmallEtale.topology B Z.1 Z.property) (SmallEtale.topology B Y.1 Y.property)
    (SmallEtale.topology B X.1 X.property)

/-- Direct image along base change acts on sections by restriction along base change, with no
further identification. -/
public theorem smallPushforward_map_hom_app {S T : B.Scheme} (f : T ⟶ S)
    {F G : Sheaf (SmallEtale.topology B T.1 T.property) (Type u₁)} (η : F ⟶ G)
    (U : SmallEtale B S.1 S.property) :
    ((B.smallPushforward f (Type u₁)).map η).hom.app (op U) =
      η.hom.app (op ((smallEtaleBaseChange B f).obj U)) := rfl

/-- An étale morphism of a big étale site, viewed as an object of the small étale site of its
target. -/
public abbrev SmallEtale.ofEtaleHom {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] : SmallEtale B T.1 T.property :=
  ⟨Over.mk f, inferInstanceAs (Etale (B.inclusion.map f))⟩

/-- **Stacks 03S3.** Composition with an étale morphism of a big étale site is a continuous
functor between the corresponding small étale sites. This is the continuity of composition with
a small étale object, indexed by the morphism instead of by the object. -/
public instance isContinuous_smallEtalePostcompose_ofEtaleHom {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] :
    (smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).IsContinuous
      (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property) :=
  smallEtalePostcompose_isContinuous B T.1 T.property (SmallEtale.ofEtaleHom B f)

/-- **Stacks 03S3.** Composition with an étale morphism `f : T' ⟶ T` of a big étale site is left
adjoint to base change along `f`, as functors between the corresponding small étale sites. -/
public def smallEtalePostcomposeBaseChangeAdjunction {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] :
    smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f) ⊣
      smallEtaleBaseChange B f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B T'.1 T'.property))
    (ObjectProperty.fullyFaithfulι (BigEtaleOver.IsEtaleOver B T.1 T.property))
    (eqToIso (smallEtalePostcompose_comp_inclusion B T.1 T.property
      (SmallEtale.ofEtaleHom B f)).symm)
    (eqToIso (smallEtaleBaseChange_comp_inclusion B f).symm)

/-- The lift of an object of the small étale site of `T'` through base change along `f`, given a
morphism of schemes over `T`. This is the morphism into the fibre product with `T'`. -/
public def smallEtaleBaseChangeLift {S T : B.Scheme} (f : T ⟶ S)
    (U : SmallEtale B S.1 S.property) (V : SmallEtale B T.1 T.property)
    (k : V.obj.left ⟶ U.obj.left) (hk : k ≫ U.obj.hom = V.obj.hom ≫ f) :
    V ⟶ (smallEtaleBaseChange B f).obj U :=
  ObjectProperty.homMk (Over.homMk (pullback.lift k V.obj.hom hk) (pullback.lift_snd _ _ _))

/-- The unit of the adjunction between composition with an étale morphism and base change along
it is the canonical lift with identity first component. -/
public theorem smallEtalePostcomposeBaseChangeAdjunction_unit_app {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] (U : SmallEtale B T'.1 T'.property) :
    (smallEtalePostcomposeBaseChangeAdjunction B f).unit.app U =
      smallEtaleBaseChangeLift B f
        ((smallEtalePostcompose B T.1 T.property (SmallEtale.ofEtaleHom B f)).obj U) U (𝟙 _)
        (by simp [smallEtalePostcompose]) := by
  apply (BigEtaleOver.IsEtaleOver B T'.1 T'.property).ι.map_injective
  dsimp only [smallEtalePostcomposeBaseChangeAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app,
    show (eqToIso (smallEtalePostcompose_comp_inclusion B T.1 T.property
      (SmallEtale.ofEtaleHom B f)).symm).hom = 𝟙 _ from rfl,
    show (eqToIso (smallEtaleBaseChange_comp_inclusion B f).symm).hom = 𝟙 _ from rfl]
  simp only [NatTrans.id_app]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [ObjectProperty.ι_obj, Functor.id_obj, smallEtalePostcompose, Over.mk_left,
      Over.mk_hom, ObjectProperty.lift_obj_obj, Functor.comp_obj, Over.map_obj_left,
      Over.map_obj_hom, smallEtaleBaseChange, Over.mapPullbackAdj_unit_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Over.homMk_left, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, smallEtaleBaseChangeLift, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [ObjectProperty.ι_obj, Functor.id_obj, Over.mk_left, smallEtalePostcompose,
      Over.mk_hom, ObjectProperty.lift_obj_obj, Functor.comp_obj, Over.map_obj_left,
      Over.map_obj_hom, smallEtaleBaseChange, Over.mapPullbackAdj_unit_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Over.homMk_left, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, smallEtaleBaseChangeLift, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom]
    exact (pullback.lift_snd _ _ _).symm

/-- The adjunction of direct images on sheaves induced by the adjunction between composition
with an étale morphism and base change along it. -/
public def smallEtalePostcomposePushforwardAdjunction {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] (A : Type u₁) [Category.{v₁} A] :
    (smallEtalePostcompose B T.1 T.property
        (SmallEtale.ofEtaleHom B f)).sheafPushforwardContinuous A
          (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property) ⊣
      B.smallPushforward f A := by
  haveI : (smallEtaleBaseChange B f).IsContinuous
      (SmallEtale.topology B T.1 T.property) (SmallEtale.topology B T'.1 T'.property) :=
    inferInstance
  exact (smallEtalePostcomposeBaseChangeAdjunction B f).sheafPushforwardContinuous
    (E := A) (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property)

/-- **Stacks 03S3.** For an étale morphism `f`, inverse image of small étale sheaves along `f`
is the direct image of composition with `f`: the two are left adjoints of the same functor. -/
public def smallInverseImageIsoPostcomposePushforward {T' T : B.Scheme} (f : T' ⟶ T)
    [Etale (B.inclusion.map f)] (A : Type u₁) [Category.{v₁} A]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B T.1 T.property)
      (SmallEtale.topology B T'.1 T'.property)).IsRightAdjoint] :
    B.smallInverseImage f A ≅
      (smallEtalePostcompose B T.1 T.property
        (SmallEtale.ofEtaleHom B f)).sheafPushforwardContinuous A
          (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property) :=
  Adjunction.leftAdjointUniq (B.smallPullbackAdjunction f A)
    (smallEtalePostcomposePushforwardAdjunction B f A)

/-- The counit of the adjunction of direct images acts on sections by restriction along the unit
of the adjunction between composition with an étale morphism and base change along it. -/
public theorem smallEtalePostcomposePushforwardAdjunction_counit_app {T' T : B.Scheme}
    (f : T' ⟶ T) [Etale (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B T'.1 T'.property) (Type u₁))
    (U : SmallEtale B T'.1 T'.property) :
    ((smallEtalePostcomposePushforwardAdjunction B f (Type u₁)).counit.app F).hom.app (op U) =
      F.obj.map ((smallEtalePostcomposeBaseChangeAdjunction B f).unit.app U).op := rfl

/-- **The transition maps of a small étale sheaf, read off from their adjoints.** For an étale
morphism `f`, a morphism out of the inverse image of a sheaf is computed, on sections over `U`,
from its adjoint by restricting along the unit of the postcomposition adjunction at `U`. -/
public theorem smallInverseImageIsoPostcomposePushforward_inv_app_comp {T' T : B.Scheme}
    (f : T' ⟶ T) [Etale (B.inclusion.map f)]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type u₁)
      (SmallEtale.topology B T.1 T.property)
      (SmallEtale.topology B T'.1 T'.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type u₁))
    (G : Sheaf (SmallEtale.topology B T'.1 T'.property) (Type u₁))
    (c : (B.smallInverseImage f (Type u₁)).obj F ⟶ G)
    (U : SmallEtale B T'.1 T'.property) :
    ((smallInverseImageIsoPostcomposePushforward B f (Type u₁)).inv.app F).hom.app (op U) ≫
        c.hom.app (op U) =
      ((B.smallPullbackAdjunction f (Type u₁)).homEquiv _ _ c).hom.app
          (op ((smallEtalePostcompose B T.1 T.property
            (SmallEtale.ofEtaleHom B f)).obj U)) ≫
        G.obj.map ((smallEtalePostcomposeBaseChangeAdjunction B f).unit.app U).op := by
  let adj := smallEtalePostcomposePushforwardAdjunction B f (Type u₁)
  have he : (smallInverseImageIsoPostcomposePushforward B f (Type u₁)).inv.app F ≫ c =
      (adj.homEquiv _ _).symm
        ((B.smallPullbackAdjunction f (Type u₁)).homEquiv _ _ c) := by
    rw [Equiv.eq_symm_apply]
    change adj.homEquiv _ _
      ((Adjunction.leftAdjointUniq (B.smallPullbackAdjunction f (Type u₁)) adj).inv.app _ ≫ _) = _
    rw [Adjunction.leftAdjointUniq_inv_app]
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app_comp adj
      (B.smallPullbackAdjunction f (Type u₁)) _
  rw [Adjunction.homEquiv_symm_apply] at he
  exact congrArg (fun a => a.hom.app (op U)) he

/-- The comparison of the two composite direct images acts on sections by restriction along the
comparison of the two composite base-change functors. -/
theorem smallEtaleSheafPushforwardCompIso_inv_app_hom_app
    (B : BigEtaleSite.{u}) (W T S : B.Scheme) (k : W ⟶ T) (l : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B W.obj W.property) (Type (u + 1)))
    (U : SmallEtale B S.obj S.property) :
    ((smallEtaleSheafPushforwardCompIso B W T S k l (Type (u + 1))).inv.app F).hom.app (op U) =
      F.obj.map ((smallEtaleBaseChange_compIso B W T S k l).val.hom.app U).op :=
  rfl

end AlgebraicGeometry

end
