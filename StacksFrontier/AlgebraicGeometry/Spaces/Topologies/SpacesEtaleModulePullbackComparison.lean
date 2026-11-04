module

public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalencesComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePushforwardComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseShrink
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.CoverDenseSmallSections
public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence

/-!
# `ι` commutes with inverse images

Let `f : Y ⟶ X` be a morphism of algebraic spaces and `ι` the transport of `𝒪_X`-modules from
the small étale site `X_étale` to the spaces-étale site `X_{spaces,étale}`
(`AlgebraicGeometry.Space.toSpacesEtaleModules`). The direct images commute with `ι`
(`AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso`), and so do the inverse
images: the mate `f_{small}^*(ι𝓕) ⟶ ι(f^*𝓕)` of that isomorphism is an isomorphism, compatibly
with composition.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPullbackHom`: the comparison
  `ι_X ⋙ f_{small}^* ⟶ f^* ⋙ ι_Y`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleRingedSiteHomPullbackCompIso`: the composition
  comparison `f_{small}^* ⋙ h_{small}^* ≅ (h ≫ f)_{small}^*`.

## Main results

* `AlgebraicGeometry.Space.small_toSpacesEtaleModules_obj`: the sections of `ι𝓕` are `u`-small.
* `AlgebraicGeometry.Space.mem_essImage_toSpacesEtaleModules`: a module on
  `X_{spaces,étale}` with sections in `Type u`, lifted to `Type (u + 1)`, is in the essential
  image of `ι`.
* `AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage`: `ι` is fully faithful
  and its essential image is exactly the modules on `X_{spaces,étale}` whose sections are
  `u`-small.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_toSpacesEtaleModulesPullbackHom`: **the comparison
  is an isomorphism**.
* `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPullbackHom_comp_app`: the comparison
  is compatible with composition.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections of the transport `ι𝓕` are `u`-small. -/
theorem small_toSpacesEtaleModules_obj (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : (SpacesEtale B S hS X)ᵒᵖ) :
    Small.{u} (((toSpacesEtaleModules B S hS X).obj F).val.obj V) := by
  let N := (toSpacesEtaleModules B S hS X).obj F
  let P : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) :=
    (sheafCompose _ (forget AddCommGrpCat.{u + 1})).obj
      ((SheafOfModules.toSheaf _).obj N)
  have h : ∀ W : SmallEtale B S hS X.1,
      Small.{u} (P.obj.obj (op ((comparisonFunctor B S hS X).obj W))) := fun W => by
    let e := (comparisonModuleEquivalence B S hS X).counitIso.app
      ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2)).obj F)
    let e' := ((PresheafOfModules.evaluation _ (op W)).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv.toEquiv
    exact @small_map _ _ (small_ulift _ : Small.{u} (ULift.{u + 1} (F.val.obj (op W)))) e'
  have : (comparisonFunctor B S hS X).IsCoverDense (SpacesEtale.topology B S hS X) :=
    Functor.IsDenseSubsite.isCoverDense' (J := SmallEtale.topology B S hS X.1)
  exact Functor.IsCoverDense.small_obj_of_small_obj_map (comparisonFunctor B S hS X) P h V.unop

/-- The universe lift of an `𝒪`-module on `X_{spaces,étale}` with sections in `Type u` is in the
essential image of the transport `ι`. -/
theorem mem_essImage_toSpacesEtaleModules (X : AlgebraicSpaces B S hS)
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :
    (toSpacesEtaleModules B S hS X).essImage
      ((SheafOfModules.uliftFunctor.{_, _, _, _, u + 1}).obj N) := by
  let E := comparisonModuleEquivalence B S hS X
  let G := E.functor.obj ((SheafOfModules.uliftFunctor.{_, _, _, _, u + 1}).obj N)
  have : ∀ V, Small.{u} (G.val.obj V) := fun V =>
    (small_ulift _ : Small.{u} (ULift.{u + 1}
      (N.val.obj (op ((comparisonFunctor B S hS X).obj V.unop)))))
  obtain ⟨M, ⟨i⟩⟩ := Stacks.SheafOfModules.CoherentLift.mem_essImage_liftModuleFunctor
    (smallEtaleRingedSite B S hS X.1 X.2) G
  exact ⟨M, ⟨E.inverse.mapIso i ≪≫ (E.unitIso.app _).symm⟩⟩

/-- **`ι` identifies the `𝒪_X`-modules of `X_étale` with the `u`-small modules of
`X_{spaces,étale}`.** The transport `ι` is fully faithful, and a module on `X_{spaces,étale}` is
in its essential image exactly when all its sections are `u`-small. -/
theorem toSpacesEtaleModules_full_faithful_essImage (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleModules B S hS X).Full ∧ (toSpacesEtaleModules B S hS X).Faithful ∧
      ∀ N : SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O),
        (toSpacesEtaleModules B S hS X).essImage N ↔ ∀ V, Small.{u} (N.val.obj V) := by
  refine ⟨(fullyFaithfulToSpacesEtaleModules B S hS X).full,
    (fullyFaithfulToSpacesEtaleModules B S hS X).faithful, fun N ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨F, ⟨e⟩⟩ V
    exact @small_map _ _ (small_toSpacesEtaleModules_obj B S hS X F V)
      ((PresheafOfModules.evaluation _ V).mapIso
        ((SheafOfModules.forget _).mapIso e)).toLinearEquiv.toEquiv.symm
  · let E := comparisonModuleEquivalence B S hS X
    let G := E.functor.obj N
    have : ∀ V, Small.{u} (G.val.obj V) := fun V ↦
      h (op ((comparisonFunctor B S hS X).obj V.unop))
    obtain ⟨M, ⟨i⟩⟩ := Stacks.SheafOfModules.CoherentLift.mem_essImage_liftModuleFunctor
      (smallEtaleRingedSite B S hS X.1 X.2) G
    exact ⟨M, ⟨E.inverse.mapIso i ≪≫ (E.unitIso.app _).symm⟩⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- Sheafification of presheaves of abelian groups in the universe of the structure rings, on
the spaces-étale site. -/
theorem hasSheafify_spacesEtale_addCommGrp (Z : T.Spaces) :
    HasSheafify (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u + 1, u, u + 1, u + 1, u} _ _

/-- The comma categories of a small model of the spaces-étale site have limits of abelian
groups in `Type u`. -/
theorem hasLimitsOfShape_structuredArrow_equivSmallModel (Z : T.Spaces)
    (W : (Space.SpacesEtale T.fppfSite S T.fppf_mem Z)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (equivSmallModel.{u}
      (Space.SpacesEtale T.fppfSite S T.fppf_mem Z)).inverse.op) AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall _ _

attribute [local instance] hasLimitsOfShape_structuredArrow_equivSmallModel

/-- Local isomorphisms of presheaves of abelian groups in `Type u` on the spaces-étale site are
the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_spacesEtale_addCommGrp (Z : T.Spaces) :
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  .ofEssentiallySmall.{u + 1, u, u + 1, u + 1, u, u, u} _

/-- The rings of sections of the structure sheaf of the spaces-étale site are `u`-small. -/
theorem small_spacesEtaleRingSheaf_obj (Z : T.Spaces)
    (V : (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).Cᵒᵖ) :
    Small.{u} (((sheafToPresheaf (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).J
      RingCat).obj (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).O)).obj V) :=
  Space.small_globalFunctions T.fppfSite S T.fppf_mem _

/-- The rings of sections of the structure sheaf of the spaces-étale site are `u`-small, stated
for the underlying presheaf of the ring sheaf. -/
theorem small_spacesEtaleRingSheaf_obj' (Z : T.Spaces)
    (V : (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).Cᵒᵖ) :
    Small.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z).O).obj.obj V) :=
  Space.small_globalFunctions T.fppfSite S T.fppf_mem _

attribute [local instance] small_spacesEtaleRingSheaf_obj'

attribute [local instance] hasSheafify_spacesEtale_addCommGrp
  wEqualsLocallyBijective_spacesEtale_addCommGrp small_spacesEtaleRingSheaf_obj

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- The pushforward of presheaves of modules with sections in `Type u` along `f_{small}` has a
left adjoint. -/
theorem isRightAdjoint_presheafPushforward_smallEtaleRingedSiteHom :
    (PresheafOfModules.pushforward.{u}
      (smallEtaleRingedSiteHom T f).fSharpRing.hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{u}
    (smallEtaleRingedSiteHom T f).fSharpRing.hom

/-- The base change functor underlying `f_{small}` is continuous, at the spelling of the
spaces-étale ringed topoi. -/
theorem isContinuous_smallEtaleRingedSiteHom_u : (smallEtaleRingedSiteHom T f).u.IsContinuous
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).J
    (Space.spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y).J :=
  (smallEtaleRingedSiteHom T f).isContinuous

attribute [local instance] isRightAdjoint_presheafPushforward_smallEtaleRingedSiteHom
  isContinuous_smallEtaleRingedSiteHom_u

/-- **Inverse images commute with `ι`**: the comparison `f_{small}^*(ι𝓕) ⟶ ι(f^*𝓕)`, the mate
of `AlgebraicGeometry.BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso`. -/
def toSpacesEtaleModulesPullbackHom :
    Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X ⋙
        (smallEtaleRingedSiteHom T f).pullbackTopos ⟶
      Space.modulePullback T.fppfSite S T.fppf_mem f ⋙
        Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y :=
  Adjunction.mateOfRightIso (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
    (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos
    (toSpacesEtaleModulesPushforwardIso T f)

/-- The inverse image of `ι𝓕` along `f_{small}` is in the essential image of `ι`. -/
theorem mem_essImage_pullbackTopos_toSpacesEtaleModules
    (F : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :
    (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).essImage
      ((smallEtaleRingedSiteHom T f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj F)) := by
  let G := (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj F
  have : ∀ V, Small.{u} (G.val.obj V) :=
    Space.small_toSpacesEtaleModules_obj T.fppfSite S T.fppf_mem X F
  let M := SheafOfModules.shrinkSame.{u, u + 1} G
  have hM := SheafOfModules.isIso_pullbackULiftHom_app.{u, u + 1}
    (smallEtaleRingedSiteHom T f).fSharpRing M
  have i₁ : (smallEtaleRingedSiteHom T f).pullbackTopos.obj G ≅
      (SheafOfModules.uliftFunctor.{_, _, _, _, u + 1}).obj
        ((SheafOfModules.pullback.{u} (smallEtaleRingedSiteHom T f).fSharpRing).obj M) :=
    (smallEtaleRingedSiteHom T f).pullbackTopos.mapIso
        (SheafOfModules.uliftShrinkIso.{u, u + 1} G).symm ≪≫
      @asIso _ _ _ _ ((SheafOfModules.pullbackULiftHom.{u, u + 1}
        (smallEtaleRingedSiteHom T f).fSharpRing).app M) hM
  exact (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Y).essImage.prop_of_iso i₁.symm
    (Space.mem_essImage_toSpacesEtaleModules T.fppfSite S T.fppf_mem Y _)

/-- **`f_{small}^*(ι𝓕) ≅ ι(f^*𝓕)`**: the comparison of inverse images through `ι` is an
isomorphism. -/
instance isIso_toSpacesEtaleModulesPullbackHom : IsIso (toSpacesEtaleModulesPullbackHom T f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun F => Adjunction.isIso_mateOfRightIso_app_of_mem_essImage _ _ _
    (Space.fullyFaithfulToSpacesEtaleModules T.fppfSite S T.fppf_mem X)
    (Space.fullyFaithfulToSpacesEtaleModules T.fppfSite S T.fppf_mem Y)
    (mem_essImage_pullbackTopos_toSpacesEtaleModules T f F)

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)

attribute [local instance] isContinuous_smallEtaleRingedSiteHom_u

/-- The composition comparison `f_{small}^* ⋙ h_{small}^* ≅ (h ≫ f)_{small}^*` of inverse images of
modules on the spaces-étale sites: the left adjoint form of the composition comparison of direct
images. -/
noncomputable def smallEtaleRingedSiteHomPullbackCompIso :
    (smallEtaleRingedSiteHom T f).pullbackTopos ⋙ (smallEtaleRingedSiteHom T h).pullbackTopos ≅
      (smallEtaleRingedSiteHom T (h ≫ f)).pullbackTopos :=
  CategoryTheory.Adjunction.leftAdjointCompIso
    (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T h).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T (h ≫ f)).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHomPushforwardCompIso T h f)

/-- **The comparison `f_{small}^*(ι𝓕) ⟶ ι(f^*𝓕)` is compatible with composition.** For
`h : Z ⟶ Y` and `f : Y ⟶ X`, the comparison for `h ≫ f` after the composition comparison of
spaces-étale inverse images is `h_{small}^*` of the comparison for `f`, then the comparison for
`h`, then `ι` of the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso`. -/
theorem toSpacesEtaleModulesPullbackHom_comp_app
    (N : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :
    (smallEtaleRingedSiteHomPullbackCompIso T h f).hom.app
        ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj N) ≫
      (toSpacesEtaleModulesPullbackHom T (h ≫ f)).app N =
    (smallEtaleRingedSiteHom T h).pullbackTopos.map ((toSpacesEtaleModulesPullbackHom T f).app N) ≫
      (toSpacesEtaleModulesPullbackHom T h).app
        ((Space.modulePullback T.fppfSite S T.fppf_mem f).obj N) ≫
      (Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem Z).map
        ((Space.modulePullbackCompIso T.fppfSite S T.fppf_mem h f).hom.app N) := by
  have key := CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem h)
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem (h ≫ f))
    (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T h).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom T (h ≫ f)).pullbackPushforwardAdjunctionTopos
    (toSpacesEtaleModulesPushforwardIso T f) (toSpacesEtaleModulesPushforwardIso T h)
    (toSpacesEtaleModulesPushforwardIso T (h ≫ f))
    (Space.modulePushforwardCompIso T.fppfSite S T.fppf_mem h f)
    (smallEtaleRingedSiteHomPushforwardCompIso T h f)
    (toSpacesEtaleModulesPushforwardIso_comp_hom_app T h f)
    (Space.modulePullbackCompIso T.fppfSite S T.fppf_mem h f)
    (Space.modulePullbackCompIso_eq_leftAdjointCompIso T.fppfSite S T.fppf_mem h f) N
  have t1 : toSpacesEtaleModulesPullbackHom T (h ≫ f) = CategoryTheory.Adjunction.mateOfRightIso
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem (h ≫ f))
    (smallEtaleRingedSiteHom T (h ≫ f)).pullbackPushforwardAdjunctionTopos
    (toSpacesEtaleModulesPushforwardIso T (h ≫ f)) := rfl
  have t2 : toSpacesEtaleModulesPullbackHom T h = CategoryTheory.Adjunction.mateOfRightIso
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem h)
    (smallEtaleRingedSiteHom T h).pullbackPushforwardAdjunctionTopos
    (toSpacesEtaleModulesPushforwardIso T h) := rfl
  have t3 : toSpacesEtaleModulesPullbackHom T f = CategoryTheory.Adjunction.mateOfRightIso
    (Space.modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
    (smallEtaleRingedSiteHom T f).pullbackPushforwardAdjunctionTopos
    (toSpacesEtaleModulesPushforwardIso T f) := rfl
  rw [t1, t2, t3]
  exact key

end AlgebraicGeometry.BigEtaleSpaceSite
