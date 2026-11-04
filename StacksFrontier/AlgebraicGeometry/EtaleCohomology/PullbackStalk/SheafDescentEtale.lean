module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Descent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleGlobalDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Equiv
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleInverseImageCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Bicategory.Functor.Cat.Transport
public import StacksFrontier.CategoryTheory.Equivalence.CounitCancel
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Small étale sheaves form a stack for the étale topology

Let `B` be a big étale site. The pseudofunctor
`AlgebraicGeometry.smallEtaleSheafPullbackSystemGeneral` sends a scheme `X` of `B` to the category
`Sh(X_étale)` of sheaves of sets on its small étale site and a morphism to the inverse image along
it. This file proves that it is a stack for the étale topology of `B`: for a family
`{f i : X i ⟶ S}` of étale morphisms which are jointly surjective, sheaves on the small étale site
of `S` are the same thing as descent data for small étale sheaves with respect to `{f i}`. In
particular, being Zariski coverings, open coverings have effective descent: small étale sheaves
glue along open coverings.

The source does not state this separately; the proof of Stacks 0GF5 gives condition (1) of
Stacks 0EX9 as "we have glueing for sheaves (and Zariski coverings are étale coverings)", citing
Stacks 04TR, and the proof of Stacks 0GF2 ends with "using that the problem is local on `Y`". Both
are this statement.

## The argument

The members of an étale covering of `S` are objects of the small étale site of `S`, and the
covering is a covering of the final object of that site, so Stacks 04TS
(`CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`) says that
sheaves on the slice of the small étale site of `S` at its final object are glueing data for the
covering, with values in the sheaf categories of the slices at the members. Three identifications
turn this into the statement:

* the slice of the small étale site of `S` at an object `V` is the small étale site of the scheme
  `V` (`AlgebraicGeometry.smallEtaleEquivalenceOver`, as an equivalence of sites), and moving the
  fibres of the pseudofunctor of slices along these equivalences
  (`CategoryTheory.Pseudofunctor.transport`) does not change effective descent;
* the transported pseudofunctor is the restriction of the pseudofunctor of small étale sheaves to
  the small étale site of `S`: their fibres agree, and the slice pullback along `φ : V' ⟶ V`, read
  through the slice equivalences, is the inverse image along the underlying morphism of schemes.
  That is Stacks 03S3 (`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward`), and its
  compatibility with identities and composition
  (`AlgebraicGeometry.smallInverseImageIsoPostcomposePushforward_id` and `_comp`) is what makes the
  identification a strong transformation,
  `AlgebraicGeometry.smallEtaleSliceSheafSystemStrongTrans`;
* descent data for a family of the small étale site, in the restricted pseudofunctor, are descent
  data for its image in `B`
  (`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves`).

The construction follows the one of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleGlobalDescent` for the spaces-étale
sites of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.smallEtaleSliceSheafSystem`: the pseudofunctor on the small étale site of `S`
  whose fibre over `V` is the category of sheaves on the small étale site of the scheme `V`,
  transported from the pseudofunctor of slices.
* `AlgebraicGeometry.smallEtaleSliceSheafSystemStrongTrans`: its identification with the
  restriction of `AlgebraicGeometry.smallEtaleSheafPullbackSystemGeneral`.

## Main results

* `AlgebraicGeometry.isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale`:
  effective descent for small étale sheaves along a jointly surjective family of étale morphisms.
* `AlgebraicGeometry.smallEtaleSheafPullbackSystem_isStack`: the pseudofunctor of small étale
  sheaves is a stack for the topology on `B` generated by the étale coverings.
* `AlgebraicGeometry.isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale_sections`:
  descent is effective along any family which admits sections over the members of an étale
  covering of its target.

## References

* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0GF5](https://stacks.math.columbia.edu/tag/0GF5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe t u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-- The morphism of schemes underlying a morphism of the small étale site of `S` is étale. -/
public instance etale_inclusion_map_hom_left {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    Etale (B.inclusion.map φ.hom.left) :=
  B.etale_map_of_postcomp φ.hom.left V.obj.hom V'.obj.hom V'.property V.property (Over.w φ.hom)

/-- The forgetful functor from the small étale site preserves fibre products. -/
public instance preservesPullbacks_smallEtaleForget :
    PreservesLimitsOfShape WalkingCospan
      (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S) := by
  dsimp only [_root_.AlgebraicGeometry.SmallEtaleGluing.forget]
  infer_instance

/-- The equivalence of sheaf categories induced by the slice equivalence
`AlgebraicGeometry.smallEtaleEquivalenceOver`: sheaves on the slice of the small étale site of `S`
at `V` are sheaves on the small étale site of the scheme `V`. Its inverse is restriction along the
inverse of the slice equivalence. -/
public abbrev smallEtaleSliceSheafEquiv (V : SmallEtale B S.1 S.property) :
    Sheaf ((SmallEtale.topology B S.1 S.property).over V) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1)) :=
  ((smallEtaleEquivalenceOver B S.1 S.property V).sheafCongr
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    ((SmallEtale.topology B S.1 S.property).over V) (Type (u + 1))).symm

/-- **The pseudofunctor of small étale sheaves of the objects of the small étale site of `S`,
transported from the pseudofunctor of slices.** Its fibre over `V` is the category of sheaves of
sets on the small étale site of the scheme `V`; it is the transport of
`CategoryTheory.GrothendieckTopology.pseudofunctorOver` along the equivalences
`AlgebraicGeometry.smallEtaleSliceSheafEquiv`. -/
public abbrev smallEtaleSliceSheafSystem :
    Pseudofunctor (LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) Cat :=
  Pseudofunctor.transport
    ((SmallEtale.topology B S.1 S.property).pseudofunctorOver (Type (u + 1)))
    (fun a => ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.restrict
      (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S)).obj a)
    (fun a => smallEtaleSliceSheafEquiv B S (unop a.as))

/-! ### The slice pullback is the inverse image -/

/-- The slice of the small étale site of `S` at `V'`, read as the small étale site of the scheme
`V'` and then composed into the small étale site of the scheme `V` along the morphism underlying
`φ : V' ⟶ V`. -/
public abbrev smallEtaleSlicePostcompose {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    Over V' ⥤ SmallEtale B V.obj.left.1 V.obj.left.property :=
  (smallEtaleEquivalenceOver B S.1 S.property V').inverse ⋙
    smallEtalePostcompose B V.obj.left.1 V.obj.left.property (SmallEtale.ofEtaleHom B φ.hom.left)

/-- `AlgebraicGeometry.smallEtaleSlicePostcompose` is continuous, being a composite of two
continuous functors of sites. -/
public instance isContinuous_smallEtaleSlicePostcompose {V' V : SmallEtale B S.1 S.property}
    (φ : V' ⟶ V) :
    (smallEtaleSlicePostcompose B S φ).IsContinuous ((SmallEtale.topology B S.1 S.property).over V')
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property) _

/-- The first half of `AlgebraicGeometry.smallEtaleSliceOverMapPullbackIso`: the slice pullback
along `φ`, read through the slice equivalence at the target, is restriction along
`AlgebraicGeometry.smallEtaleSlicePostcompose`. -/
public def smallEtaleSliceOverMapIso {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    (smallEtaleSliceSheafEquiv B S V).inverse ⋙
        (SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ ≅
      (smallEtaleSlicePostcompose B S φ).sheafPushforwardContinuous (Type (u + 1))
        ((SmallEtale.topology B S.1 S.property).over V')
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property) :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Iso.refl _ : Over.map φ ⋙ (smallEtaleEquivalenceOver B S.1 S.property V).inverse ≅
      smallEtaleSlicePostcompose B S φ)
    (Type (u + 1)) _
    ((SmallEtale.topology B S.1 S.property).over V')
    ((SmallEtale.topology B S.1 S.property).over V)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property) _ _
    (isContinuous_smallEtaleSlicePostcompose B S φ)

/-- The second half of `AlgebraicGeometry.smallEtaleSliceOverMapPullbackIso`: restriction along
composition with the morphism underlying `φ`, read through the slice equivalence at the source,
is restriction along `AlgebraicGeometry.smallEtaleSlicePostcompose`. -/
public def smallEtaleSlicePostcomposeIso {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    (smallEtalePostcompose B V.obj.left.1 V.obj.left.property
        (SmallEtale.ofEtaleHom B φ.hom.left)).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property)
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property) ⋙
        (smallEtaleSliceSheafEquiv B S V').inverse ≅
      (smallEtaleSlicePostcompose B S φ).sheafPushforwardContinuous (Type (u + 1))
        ((SmallEtale.topology B S.1 S.property).over V')
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property) :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Iso.refl _ : (smallEtaleEquivalenceOver B S.1 S.property V').inverse ⋙
        smallEtalePostcompose B V.obj.left.1 V.obj.left.property
          (SmallEtale.ofEtaleHom B φ.hom.left) ≅ smallEtaleSlicePostcompose B S φ)
    (Type (u + 1)) _
    ((SmallEtale.topology B S.1 S.property).over V')
    (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property) _
    (isContinuous_smallEtalePostcompose_ofEtaleHom_source B φ.hom.left)
    (isContinuous_smallEtaleSlicePostcompose B S φ)

/-- The comparison of the slice pullback with restriction along composition, with the
identification of Stacks 03S3 removed: the composite of the two halves above. -/
public def smallEtaleSliceMate {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    (smallEtaleSliceSheafEquiv B S V).inverse ⋙
        (SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ ⟶
      (smallEtalePostcompose B V.obj.left.1 V.obj.left.property
          (SmallEtale.ofEtaleHom B φ.hom.left)).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property)
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property) ⋙
        (smallEtaleSliceSheafEquiv B S V').inverse :=
  (smallEtaleSliceOverMapIso B S φ).hom ≫ (smallEtaleSlicePostcomposeIso B S φ).inv

/-- **The slice pullback is the inverse image.** For a morphism `φ : V' ⟶ V` of the small étale
site of `S`, the slice pullback along `φ` and the inverse image along the morphism of schemes
underlying `φ` agree through the slice equivalences at `V` and at `V'`: by Stacks 03S3 the inverse
image is restriction along composition, and both sides are restriction along
`AlgebraicGeometry.smallEtaleSlicePostcompose`. -/
@[sga "4 VII 1.6"]
public def smallEtaleOverMapPullbackInverseImageIso {V' V : SmallEtale B S.1 S.property}
    (φ : V' ⟶ V) :
    (smallEtaleSliceSheafEquiv B S V).inverse ⋙
        (SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ ≅
      B.smallInverseImage φ.hom.left (Type (u + 1)) ⋙ (smallEtaleSliceSheafEquiv B S V').inverse :=
  smallEtaleSliceOverMapIso B S φ ≪≫
    (Functor.isoWhiskerRight (smallInverseImageIsoPostcomposePushforward B φ.hom.left
        (Type (u + 1))) (smallEtaleSliceSheafEquiv B S V').inverse ≪≫
      smallEtaleSlicePostcomposeIso B S φ).symm

/-- The comparison of the slice pullback with the inverse image is the composite of its two halves
and the identification of Stacks 03S3. -/
public theorem overMapPullbackInverseImageIso_hom_app {V' V : SmallEtale B S.1 S.property}
    (φ : V' ⟶ V)
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1))) :
    (smallEtaleOverMapPullbackInverseImageIso B S φ).hom.app M =
      (smallEtaleSliceMate B S φ).app M ≫
        (smallEtaleSliceSheafEquiv B S V').inverse.map
          ((smallInverseImageIsoPostcomposePushforward B φ.hom.left (Type (u + 1))).inv.app M) :=
  rfl

/-- **The slice pullback is the inverse image**, as an isomorphism onto the inverse image itself:
the transition functor of `AlgebraicGeometry.smallEtaleSliceSheafSystem` along `φ` is the inverse
image along the morphism of schemes underlying `φ`. -/
public def smallEtaleSliceOverMapPullbackIso {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) :
    (smallEtaleSliceSheafEquiv B S V).inverse ⋙
        (SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ ⋙
        (smallEtaleSliceSheafEquiv B S V').functor ≅
      B.smallInverseImage φ.hom.left (Type (u + 1)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleOverMapPullbackInverseImageIso B S φ)
      (smallEtaleSliceSheafEquiv B S V').functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (B.smallInverseImage φ.hom.left (Type (u + 1)))
      (smallEtaleSliceSheafEquiv B S V').counitIso ≪≫
    Functor.rightUnitor _

/-- The comparison `AlgebraicGeometry.smallEtaleSliceOverMapPullbackIso`, at a sheaf. -/
public theorem smallEtaleSliceOverMapPullbackIso_hom_app {V' V : SmallEtale B S.1 S.property}
    (φ : V' ⟶ V)
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1))) :
    (smallEtaleSliceOverMapPullbackIso B S φ).hom.app M =
      (smallEtaleSliceSheafEquiv B S V').functor.map
          ((smallEtaleOverMapPullbackInverseImageIso B S φ).hom.app M) ≫
        (smallEtaleSliceSheafEquiv B S V').counitIso.hom.app
          ((B.smallInverseImage φ.hom.left (Type (u + 1))).obj M) := by
  simp [smallEtaleSliceOverMapPullbackIso]


/-- `AlgebraicGeometry.smallEtaleSliceMate` is the identity on sections: the two functors of sites
it compares are equal on the nose. -/
public theorem smallEtaleSliceMate_app_hom_app {V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V)
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1)))
    (T : (Over V')ᵒᵖ) :
    ((smallEtaleSliceMate B S φ).app M).hom.app T = 𝟙 _ := by
  have h : ((smallEtaleSliceMate B S φ).app M).hom.app T =
      ((smallEtaleSliceOverMapIso B S φ).hom.app M).hom.app T ≫
        ((smallEtaleSlicePostcomposeIso B S φ).inv.app M).hom.app T := rfl
  have h1 : ((smallEtaleSliceOverMapIso B S φ).hom.app M).hom.app T = M.obj.map (𝟙 _) := rfl
  have h2 : ((smallEtaleSlicePostcomposeIso B S φ).inv.app M).hom.app T = M.obj.map (𝟙 _) := rfl
  rw [h, h1, h2, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-! ### The identity coherence -/

/-- **The comparison with restriction along composition is compatible with identities.** At the
identity of an object of the small étale site of `S`, the composite of
`AlgebraicGeometry.smallEtaleSliceMate` with the strict identity comparison of the restriction
functor is the identity comparison of the slice pullback. -/
public theorem smallEtaleSliceMate_id (V : SmallEtale B S.1 S.property) :
    (smallEtaleSliceOverMapIso B S (𝟙 V)).hom ≫ (smallEtaleSlicePostcomposeIso B S (𝟙 V)).inv ≫
        Functor.whiskerRight (smallEtalePostcomposeSheafId B (Type (u + 1)) V.obj.left).hom
          (smallEtaleSliceSheafEquiv B S V).inverse =
      Functor.whiskerLeft (smallEtaleSliceSheafEquiv B S V).inverse
        ((SmallEtale.topology B S.1 S.property).overMapPullbackId (Type (u + 1)) V).hom := by
  refine NatTrans.ext (funext fun M ↦ Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_)))
  have h3 : (((smallEtaleSliceSheafEquiv B S V).inverse.map
        ((smallEtalePostcomposeSheafId B (Type (u + 1)) V.obj.left).hom.app M)).hom.app T) =
      M.obj.map ((smallEtalePostcomposeId B V.obj.left).inv.app
        ((smallEtaleEquivalenceOver B S.1 S.property V).inverse.obj (unop T))).op ≫ 𝟙 _ := rfl
  have hsite : (smallEtalePostcomposeId B V.obj.left).inv.app
        ((smallEtaleEquivalenceOver B S.1 S.property V).inverse.obj (unop T)) =
      (smallEtaleEquivalenceOver B S.1 S.property V).inverse.map
        ((Over.mapId V).inv.app (unop T)) := rfl
  have hm := smallEtaleSliceMate_app_hom_app B S (𝟙 V) M T
  simp only [smallEtaleSliceMate, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
    at hm
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, h3,
    Category.comp_id, GrothendieckTopology.overMapPullbackId_hom_app_hom_app]
  erw [reassoc_of% hm, Category.id_comp]
  exact congrArg (fun z ↦ M.obj.map (Quiver.Hom.op z)) hsite

/-- **The identification of the slice pullback with the inverse image is compatible with
identities.** -/
public theorem overMapPullbackInverseImageIso_id (V : SmallEtale B S.1 S.property) :
    (smallEtaleOverMapPullbackInverseImageIso B S (𝟙 V)).hom ≫
        Functor.whiskerRight
          (Adjunction.leftAdjointIdIso (B.smallPullbackAdjunction (𝟙 V.obj.left) (Type (u + 1)))
            (Functor.sheafPushforwardContinuousId'
              (C := SmallEtale B V.obj.left.1 V.obj.left.property)
              (smallEtaleBaseChange_idIso B V.obj.left) (Type (u + 1))
              (SmallEtale.topology B V.obj.left.1 V.obj.left.property))).hom
          (smallEtaleSliceSheafEquiv B S V).inverse =
      Functor.whiskerLeft (smallEtaleSliceSheafEquiv B S V).inverse
        ((SmallEtale.topology B S.1 S.property).overMapPullbackId (Type (u + 1)) V).hom := by
  rw [smallInverseImageIsoPostcomposePushforward_id B (Type (u + 1)) V.obj.left,
    Functor.whiskerRight_comp]
  have he : (smallEtaleOverMapPullbackInverseImageIso B S (𝟙 V)).hom =
      (smallEtaleSliceOverMapIso B S (𝟙 V)).hom ≫ (smallEtaleSlicePostcomposeIso B S (𝟙 V)).inv ≫
        (Functor.isoWhiskerRight (smallInverseImageIsoPostcomposePushforward B (𝟙 V.obj.left)
          (Type (u + 1))) (smallEtaleSliceSheafEquiv B S V).inverse).inv := rfl
  rw [he]
  simp only [Category.assoc]
  have hc : (Functor.isoWhiskerRight (smallInverseImageIsoPostcomposePushforward B
        (𝟙 V.obj.left) (Type (u + 1))) (smallEtaleSliceSheafEquiv B S V).inverse).inv ≫
        Functor.whiskerRight (smallInverseImageIsoPostcomposePushforward B (𝟙 V.obj.left)
          (Type (u + 1))).hom (smallEtaleSliceSheafEquiv B S V).inverse = 𝟙 _ :=
    (Functor.isoWhiskerRight (smallInverseImageIsoPostcomposePushforward B
        (𝟙 V.obj.left) (Type (u + 1))) (smallEtaleSliceSheafEquiv B S V).inverse).inv_hom_id
  rw [reassoc_of% hc]
  exact smallEtaleSliceMate_id B S V


/-! ### The composition coherence -/

/-- **The comparison with restriction along composition is compatible with composition.** This is
the composition coherence with the identification of Stacks 03S3 removed; it holds because the
underlying functors of sites agree on the nose. -/
public theorem smallEtaleSliceMate_comp {V'' V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V)
    (ψ : V'' ⟶ V')
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1))) :
    (smallEtaleSliceMate B S (ψ ≫ φ)).app M ≫
        (smallEtaleSliceSheafEquiv B S V'').inverse.map
          ((smallEtalePostcomposeSheafComp B (Type (u + 1)) ψ.hom.left φ.hom.left).inv.app M) =
      ((SmallEtale.topology B S.1 S.property).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
          ((smallEtaleSliceSheafEquiv B S V).inverse.obj M) ≫
        ((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) ψ).map
            ((smallEtaleSliceMate B S φ).app M) ≫
          (smallEtaleSliceMate B S ψ).app
            ((smallEtalePostcompose B V.obj.left.1 V.obj.left.property
                (SmallEtale.ofEtaleHom B φ.hom.left)).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property)
              (SmallEtale.topology B V.obj.left.1 V.obj.left.property) |>.obj M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hL1 : ((smallEtaleSliceMate B S (ψ ≫ φ)).app M).hom.app T = 𝟙 _ :=
    smallEtaleSliceMate_app_hom_app B S _ M T
  have hL2 : (((smallEtaleSliceSheafEquiv B S V'').inverse.map
        ((smallEtalePostcomposeSheafComp B (Type (u + 1)) ψ.hom.left φ.hom.left).inv.app
          M)).hom.app T) =
      M.obj.map ((smallEtalePostcomposeComp B ψ.hom.left φ.hom.left).hom.app
        ((smallEtaleEquivalenceOver B S.1 S.property V'').inverse.obj (unop T))).op := rfl
  have hR1 : ((((SmallEtale.topology B S.1 S.property).overMapPullbackComp (Type (u + 1))
        ψ φ).inv.app ((smallEtaleSliceSheafEquiv B S V).inverse.obj M)).hom.app T) =
      M.obj.map ((smallEtaleEquivalenceOver B S.1 S.property V).inverse.map
        ((Over.mapComp ψ φ).inv.app (unop T))).op := rfl
  have hR2 : ((((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) ψ).map
        ((smallEtaleSliceMate B S φ).app M)).hom.app T) = 𝟙 _ :=
    smallEtaleSliceMate_app_hom_app B S φ M _
  have hR3 : ((smallEtaleSliceMate B S ψ).app
        ((smallEtalePostcompose B V.obj.left.1 V.obj.left.property
            (SmallEtale.ofEtaleHom B φ.hom.left)).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B V'.obj.left.1 V'.obj.left.property)
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property) |>.obj M)).hom.app T =
      𝟙 _ := smallEtaleSliceMate_app_hom_app B S ψ _ T
  have hsite : (smallEtalePostcomposeComp B ψ.hom.left φ.hom.left).hom.app
        ((smallEtaleEquivalenceOver B S.1 S.property V'').inverse.obj (unop T)) =
      (smallEtaleEquivalenceOver B S.1 S.property V).inverse.map
        ((Over.mapComp ψ φ).inv.app (unop T)) := rfl
  rw [hL1, hL2, hR1, hR2, hR3, hsite]
  exact (Category.id_comp _).trans
    ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _)).symm

/-- **Stacks 03S3 is compatible with composition**, in the form needed for the composition
coherence: the identification of the inverse image with restriction along composition, inverted
and composed with the composition comparison of the inverse images, is the composition
comparison of the restriction functors followed by the two inverted identifications. -/
public theorem smallInverseImageIsoPostcomposePushforward_inv_comp {T'' T' T : B.Scheme}
    (h : T'' ⟶ T') (k : T' ⟶ T) [Etale (B.inclusion.map h)] [Etale (B.inclusion.map k)]
    (M : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1))) :
    (smallInverseImageIsoPostcomposePushforward B (h ≫ k) (Type (u + 1))).inv.app M ≫
        (smallEtaleMorphism_comp_inverseImageIso B T'' T' T h k).inv.app M =
      (smallEtalePostcomposeSheafComp B (Type (u + 1)) h k).inv.app M ≫
        (smallInverseImageIsoPostcomposePushforward B h (Type (u + 1))).inv.app
          ((smallEtalePostcompose B T.1 T.property
              (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property)
              |>.obj M) ≫
          (B.smallInverseImage h (Type (u + 1))).map
            ((smallInverseImageIsoPostcomposePushforward B k (Type (u + 1))).inv.app M) := by
  have hSB0 := NatTrans.congr_app
    (smallInverseImageIsoPostcomposePushforward_comp B (Type (u + 1)) h k) M
  have hSB : (smallEtaleMorphism_comp_inverseImageIso B T'' T' T h k).inv.app M ≫
        ((B.smallInverseImage h (Type (u + 1))).map
            ((smallInverseImageIsoPostcomposePushforward B k (Type (u + 1))).hom.app M) ≫
          (smallInverseImageIsoPostcomposePushforward B h (Type (u + 1))).hom.app
            ((smallEtalePostcompose B T.1 T.property
                (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property)
                |>.obj M)) =
      (smallInverseImageIsoPostcomposePushforward B (h ≫ k) (Type (u + 1))).hom.app M ≫
        (smallEtalePostcomposeSheafComp B (Type (u + 1)) h k).inv.app M := hSB0
  have hcancel : (smallEtaleMorphism_comp_inverseImageIso B T'' T' T h k).inv.app M =
      ((smallInverseImageIsoPostcomposePushforward B (h ≫ k) (Type (u + 1))).hom.app M ≫
        (smallEtalePostcomposeSheafComp B (Type (u + 1)) h k).inv.app M) ≫
        (smallInverseImageIsoPostcomposePushforward B h (Type (u + 1))).inv.app
          ((smallEtalePostcompose B T.1 T.property
              (SmallEtale.ofEtaleHom B k)).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B T'.1 T'.property) (SmallEtale.topology B T.1 T.property)
              |>.obj M) ≫
          (B.smallInverseImage h (Type (u + 1))).map
            ((smallInverseImageIsoPostcomposePushforward B k (Type (u + 1))).inv.app M) := by
    rw [← hSB]
    simp
  rw [hcancel]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]

/-- **The identification of the slice pullback with the inverse image is compatible with
composition.** -/
public theorem overMapPullbackInverseImageIso_comp {V'' V' V : SmallEtale B S.1 S.property}
    (φ : V' ⟶ V) (ψ : V'' ⟶ V')
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1))) :
    (smallEtaleOverMapPullbackInverseImageIso B S (ψ ≫ φ)).hom.app M ≫
        (smallEtaleSliceSheafEquiv B S V'').inverse.map
          ((smallEtaleMorphism_comp_inverseImageIso B _ _ _ ψ.hom.left φ.hom.left).inv.app M) =
      ((SmallEtale.topology B S.1 S.property).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
          ((smallEtaleSliceSheafEquiv B S V).inverse.obj M) ≫
        ((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) ψ).map
            ((smallEtaleOverMapPullbackInverseImageIso B S φ).hom.app M) ≫
          (smallEtaleOverMapPullbackInverseImageIso B S ψ).hom.app
            ((B.smallInverseImage φ.hom.left (Type (u + 1))).obj M) := by
  have hnat1 := (smallEtaleSliceMate B S ψ).naturality
    ((smallInverseImageIsoPostcomposePushforward B φ.hom.left (Type (u + 1))).inv.app M)
  have hnat2 := (smallInverseImageIsoPostcomposePushforward B ψ.hom.left
      (Type (u + 1))).inv.naturality
    ((smallInverseImageIsoPostcomposePushforward B φ.hom.left (Type (u + 1))).inv.app M)
  dsimp only [Functor.comp_map] at hnat1 hnat2
  rw [overMapPullbackInverseImageIso_hom_app B S (ψ ≫ φ) M,
    overMapPullbackInverseImageIso_hom_app B S φ M,
    overMapPullbackInverseImageIso_hom_app B S ψ
      ((B.smallInverseImage φ.hom.left (Type (u + 1))).obj M),
    Category.assoc, ← Functor.map_comp]
  have hic : (smallInverseImageIsoPostcomposePushforward B (ψ ≫ φ).hom.left (Type (u + 1))).inv.app
        M ≫ (smallEtaleMorphism_comp_inverseImageIso B _ _ _ ψ.hom.left φ.hom.left).inv.app M =
      _ := smallInverseImageIsoPostcomposePushforward_inv_comp B ψ.hom.left φ.hom.left M
  rw [hic]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  slice_rhs 3 4 => rw [hnat1]
  slice_rhs 4 5 => rw [← Functor.map_comp, hnat2, CategoryTheory.Functor.map_comp]
  rw [reassoc_of% (smallEtaleSliceMate_comp B S φ ψ M)]


/-- The identity constraint of the restricted pseudofunctor of small étale sheaves, read on
sheaves, is the identity comparison of the inverse image. -/
public theorem smallEtaleSheafPullbackSystem_restrict_mapId_hom_app
    (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ)
    (M : Sheaf (SmallEtale.topology B (unop a.as).obj.left.1 (unop a.as).obj.left.property)
      (Type (u + 1))) :
    (((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.restrict
        (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S)).mapId a).hom.toNatTrans.app M =
      (Adjunction.leftAdjointIdIso (B.smallPullbackAdjunction (𝟙 (unop a.as).obj.left)
        (Type (u + 1))) (Functor.sheafPushforwardContinuousId'
          (C := SmallEtale B (unop a.as).obj.left.1 (unop a.as).obj.left.property)
          (smallEtaleBaseChange_idIso B (unop a.as).obj.left) (Type (u + 1))
          (SmallEtale.topology B (unop a.as).obj.left.1
            (unop a.as).obj.left.property))).hom.app M := rfl

/-- The composition constraint of the restricted pseudofunctor of small étale sheaves, read on
sheaves, is the inverse of `AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. -/
public theorem smallEtaleSheafPullbackSystem_restrict_mapComp_hom_app
    {a b c : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : Sheaf (SmallEtale.topology B (unop a.as).obj.left.1 (unop a.as).obj.left.property)
      (Type (u + 1))) :
    (((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.restrict
        (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S)).mapComp f g).hom.toNatTrans.app M =
      (smallEtaleMorphism_comp_inverseImageIso B _ _ _ g.as.unop.hom.left
        f.as.unop.hom.left).inv.app M := rfl

/-- The identity coherence of `AlgebraicGeometry.smallEtaleSliceSheafSystemStrongTrans`, at a
sheaf. -/
public theorem smallEtaleSliceSheafSystemStrongTrans_naturality_id_app
    (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ)
    (M : Sheaf (SmallEtale.topology B (unop a.as).obj.left.1 (unop a.as).obj.left.property)
      (Type (u + 1))) :
    (smallEtaleSliceOverMapPullbackIso B S (𝟙 (unop a.as))).hom.app M ≫
        (Adjunction.leftAdjointIdIso
          (B.smallPullbackAdjunction (𝟙 (unop a.as).obj.left) (Type (u + 1)))
          (Functor.sheafPushforwardContinuousId'
            (C := SmallEtale B (unop a.as).obj.left.1 (unop a.as).obj.left.property)
            (smallEtaleBaseChange_idIso B (unop a.as).obj.left) (Type (u + 1))
            (SmallEtale.topology B (unop a.as).obj.left.1
              (unop a.as).obj.left.property))).hom.app M =
      (smallEtaleSliceSheafEquiv B S (unop a.as)).functor.map
          (((SmallEtale.topology B S.1 S.property).overMapPullbackId (Type (u + 1))
            (unop a.as)).hom.app ((smallEtaleSliceSheafEquiv B S (unop a.as)).inverse.obj M)) ≫
        (smallEtaleSliceSheafEquiv B S (unop a.as)).counitIso.hom.app M :=
  glueCounit (smallEtaleSliceSheafEquiv B S (unop a.as))
    ((smallEtaleOverMapPullbackInverseImageIso B S (𝟙 (unop a.as))).hom.app M) _ _
    (NatTrans.congr_app (overMapPullbackInverseImageIso_id B S (unop a.as)) M)

/-- The composition coherence of `AlgebraicGeometry.smallEtaleSliceSheafSystemStrongTrans`, at a
sheaf. -/
public theorem smallEtaleSliceSheafSystemStrongTrans_naturality_comp_app
    {V'' V' V : SmallEtale B S.1 S.property} (φ : V' ⟶ V) (ψ : V'' ⟶ V')
    (M : Sheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property) (Type (u + 1))) :
    (smallEtaleSliceOverMapPullbackIso B S (ψ ≫ φ)).hom.app M ≫
        (smallEtaleMorphism_comp_inverseImageIso B _ _ _ ψ.hom.left φ.hom.left).inv.app M =
      (smallEtaleSliceSheafEquiv B S V'').functor.map
          (((SmallEtale.topology B S.1 S.property).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
            ((smallEtaleSliceSheafEquiv B S V).inverse.obj M)) ≫
        (smallEtaleSliceSheafEquiv B S V'').functor.map
          (((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) ψ).map
            ((smallEtaleSliceSheafEquiv B S V').unitIso.hom.app
              (((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ).obj
                ((smallEtaleSliceSheafEquiv B S V).inverse.obj M)))) ≫
        ((smallEtaleSliceSheafEquiv B S V'').functor.map
            ((smallEtaleOverMapPullbackInverseImageIso B S ψ).hom.app
              ((smallEtaleSliceSheafEquiv B S V').functor.obj
                (((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ).obj
                  ((smallEtaleSliceSheafEquiv B S V).inverse.obj M)))) ≫
          (smallEtaleSliceSheafEquiv B S V'').counitIso.hom.app
            (((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
                ψ.hom.left.op.toLoc).toFunctor.obj
              ((smallEtaleSliceSheafEquiv B S V').functor.obj
                (((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) φ).obj
                  ((smallEtaleSliceSheafEquiv B S V).inverse.obj M))))) ≫
        ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
            ψ.hom.left.op.toLoc).toFunctor.map
          ((smallEtaleSliceSheafEquiv B S V').functor.map
              ((smallEtaleOverMapPullbackInverseImageIso B S φ).hom.app M) ≫
            (smallEtaleSliceSheafEquiv B S V').counitIso.hom.app
              (((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
                φ.hom.left.op.toLoc).toFunctor.obj M)) :=
  (glueCounit (smallEtaleSliceSheafEquiv B S V'')
      ((smallEtaleOverMapPullbackInverseImageIso B S (ψ ≫ φ)).hom.app M)
      ((smallEtaleMorphism_comp_inverseImageIso B _ _ _ ψ.hom.left φ.hom.left).inv.app M) _
      (overMapPullbackInverseImageIso_comp B S φ ψ M)).trans
    (glueComp (smallEtaleSliceSheafEquiv B S V') (smallEtaleSliceSheafEquiv B S V'')
      ((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1)) ψ)
      (B.smallInverseImage ψ.hom.left (Type (u + 1)))
      (smallEtaleOverMapPullbackInverseImageIso B S ψ)
      ((smallEtaleOverMapPullbackInverseImageIso B S φ).hom.app M)
      (((SmallEtale.topology B S.1 S.property).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
        ((smallEtaleSliceSheafEquiv B S V).inverse.obj M))).symm

/-! ### The strong transformation -/

/-- **The transported pseudofunctor of slices is the restriction of the pseudofunctor of small
étale sheaves.** The two pseudofunctors on the small étale site of `S` have the same fibres, and
the strong naturality constraint identifying their transition functors is the comparison of the
slice pullback with the inverse image. -/
public def smallEtaleSliceSheafSystemStrongTrans :
    Pseudofunctor.StrongTrans (smallEtaleSliceSheafSystem B S)
      ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.restrict
        (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S)) where
  app a := 𝟙 _
  naturality {a b} φ := Cat.Hom.isoMk (smallEtaleSliceOverMapPullbackIso B S φ.as.unop)
  naturality_naturality := by
    intro a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    rw [Pseudofunctor.map₂_eq_eqToHom (smallEtaleSliceSheafSystem B S),
      Pseudofunctor.map₂_eq_eqToHom ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.restrict
        (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S))]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  naturality_id := by
    intro a
    ext M
    exact smallEtaleSliceSheafSystemStrongTrans_naturality_id_app B S a M
  naturality_comp := by
    intro a b c f g
    ext M
    refine Eq.trans ?_ ((smallEtaleSliceSheafSystemStrongTrans_naturality_comp_app B S
      f.as.unop g.as.unop M).trans ?_)
    · rfl
    · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
        Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      change _ = (((SmallEtale.topology B S.1 S.property).pseudofunctorOver
            (Type (u + 1))).transportMapComp
            (fun a ↦ (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.obj
              { as := op ((_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S).obj (unop a.as)) })
            (fun a ↦ smallEtaleSliceSheafEquiv B S (unop a.as)) f g).hom.toNatTrans.app M ≫
          (smallEtaleSliceOverMapPullbackIso B S g.as.unop).hom.app
            ((smallEtaleSliceSheafEquiv B S (unop b.as)).functor.obj
              (((SmallEtale.topology B S.1 S.property).overMapPullback (Type (u + 1))
                f.as.unop).obj ((smallEtaleSliceSheafEquiv B S (unop a.as)).inverse.obj M))) ≫
          ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.map
              g.as.unop.hom.left.op.toLoc).toFunctor.map
            ((smallEtaleSliceOverMapPullbackIso B S f.as.unop).hom.app M)
      simp only [smallEtaleSliceOverMapPullbackIso_hom_app]
      simp only [smallEtaleSliceOverMapPullbackIso_hom_app B S f.as.unop M]
      exact (Category.assoc _ _ _).symm

/-- The components of `AlgebraicGeometry.smallEtaleSliceSheafSystemStrongTrans` are equivalences,
being identities. -/
public instance isEquivalence_smallEtaleSliceSheafSystemStrongTrans_app
    (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) :
    ((smallEtaleSliceSheafSystemStrongTrans B S).app a).toFunctor.IsEquivalence :=
  Functor.isEquivalence_refl


/-! ### Effective descent along étale coverings -/

/-- **Effective descent for small étale sheaves along a jointly surjective family of étale
morphisms.** Let `{f i : X i ⟶ S}` be a family of morphisms of a big étale site which are étale
and jointly surjective. Then the canonical functor from sheaves on the small étale site of `S` to
descent data for small étale sheaves with respect to `{f i}` is an equivalence of categories. -/
public theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale
    {I : Type t} {X : I → B.Scheme} (f : ∀ i, X i ⟶ S) [∀ i, Etale (B.inclusion.map (f i))]
    (hsurj : ∀ s : B.inclusion.obj S, ∃ i, s ∈ Set.range (B.inclusion.map (f i))) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData f).IsEquivalence := by
  let U : I → SmallEtale B S.1 S.property := fun i ↦ SmallEtale.ofEtaleHom B (f i)
  let p : ∀ i, U i ⟶ SmallEtale.final B S.1 S.property := fun i ↦
    ObjectProperty.homMk (Over.homMk (f i))
  have hcov : Sieve.ofArrows U p ∈
      SmallEtale.topology B S.1 S.property (SmallEtale.final B S.1 S.property) :=
    SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S.1 S.property U p hsurj
  have h1 : ((smallEtaleSliceSheafSystem B S).toDescentData p).IsEquivalence :=
    (Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ p).mp
      (GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver
        (SmallEtale.topology B S.1 S.property) (Type (u + 1)) p hcov)
  have h2 := ((smallEtaleSliceSheafSystemStrongTrans B S).isEquivalence_toDescentData_iff p
    (isEquivalence_smallEtaleSliceSheafSystemStrongTrans_app B S)).mp h1
  exact (Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves
    (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor
    (_root_.AlgebraicGeometry.SmallEtaleGluing.forget B S) p).mp h2


/-- **The pseudofunctor of small étale sheaves is a stack for the étale topology** on the
underlying category of a big étale site, the topology generated by the families of morphisms which
are étale and jointly surjective as families of morphisms of schemes. -/
public theorem smallEtaleSheafPullbackSystem_isStack :
    (smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.IsStack
      (Scheme.etalePrecoverage.comap B.inclusion).toGrothendieck := by
  let P : MorphismProperty Scheme.{u} := @Etale
  have : Scheme.etalePrecoverage.HasIsos := (inferInstance : (Scheme.precoverage P).HasIsos)
  have : Scheme.etalePrecoverage.IsStableUnderComposition :=
    (inferInstance : (Scheme.precoverage P).IsStableUnderComposition)
  have : Scheme.etalePrecoverage.IsStableUnderBaseChange :=
    (inferInstance : (Scheme.precoverage P).IsStableUnderBaseChange)
  refine Pseudofunctor.IsStack.of_precoverage fun S R hR ↦ ?_
  obtain ⟨ι, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  have hR' := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hR
  have : ∀ i, Etale (B.inclusion.map (f i)) := hR'.2
  exact isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale B S f hR'.1

/-- **Effective descent for small étale sheaves along a family with sections étale locally on the
target.** Descent is effective along a family `h i : X i ⟶ Z` of morphisms of a big étale site as
soon as there is a jointly surjective family of étale morphisms `j c : W c ⟶ Z` each member of
which factors through some member of the family. -/
public theorem isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale_sections
    {I : Type t} {X : I → B.Scheme} {Z : B.Scheme} (h : ∀ i, X i ⟶ Z) {K : Type*}
    (W : K → B.Scheme) (j : ∀ c, W c ⟶ Z) (hétale : ∀ c, Etale (B.inclusion.map (j c)))
    (hsurj : ∀ z : B.inclusion.obj Z, ∃ c, z ∈ Set.range (B.inclusion.map (j c)))
    (hsec : ∀ c, ∃ i, ∃ s : W c ⟶ X i, s ≫ h i = j c) :
    ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData h).IsEquivalence := by
  have := smallEtaleSheafPullbackSystem_isStack B
  have : ((smallEtaleSheafPullbackSystemGeneral B).pseudofunctor.toDescentData j).IsEquivalence :=
    isEquivalence_toDescentData_smallEtaleSheafPullbackSystem_of_etale B Z j hsurj
  refine Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le (f' := j)
    (J := (Scheme.etalePrecoverage.comap B.inclusion).toGrothendieck) _ ?_ ?_
  · apply Precoverage.generate_mem_toGrothendieck
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨hsurj, hétale⟩
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨c⟩
    obtain ⟨i, s, hs⟩ := hsec c
    exact ⟨_, s, h i, ⟨i⟩, hs⟩

end AlgebraicGeometry

end
