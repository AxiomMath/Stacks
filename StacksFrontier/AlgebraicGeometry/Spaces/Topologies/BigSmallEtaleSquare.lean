module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp

/-!
# The square of big and small étale topoi (Stacks 0DF6)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism
of its objects. Then:

* (1) the small-to-big morphism `i_f` of Tag 0DF2 factors as `i_Y` followed by the big étale
  morphism `f_big` of Tag 0DF5;
* (2) base change along `f` is a morphism of sites of the spaces-étale sites, hence induces a
  morphism `f_small` of the spaces-étale topoi;
* (3) the square formed by `f_small`, `f_big` and the two big-to-small morphisms of Tag 0DF3
  commutes on direct images;
* (4) consequently `f_small` factors through either big topos.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleMorphism` is `f_small`: **Stacks 0DF6**,
  part (2).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBig_comp_big_pushforwardIso`: **Stacks 0DF6**,
  part (1).
* `AlgebraicGeometry.BigEtaleSpaceSite.smallBaseChange_comp_inclusionIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtale_pushforwardCommIso`: **Stacks 0DF6**,
  part (3), at the level of site functors and of topoi.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtale_pushforwardIsoBigFactorization` and
  `AlgebraicGeometry.BigEtaleSpaceSite.smallEtale_pushforwardIsoDirectFactorization`:
  **Stacks 0DF6**, part (4), with the two coherence statements identifying them.

## Implementation notes

Part (1) is an equality of site functors: `inclusionFunctor T f` is literally
`inclusionFunctor T (𝟙 Y) ⋙ Over.map f` after `Over.mapId_eq`, so the factorization of direct
images is the general composition isomorphism for cocontinuous pushforwards.

Part (3) rests on the commuting square of site functors
`AlgebraicGeometry.BigEtaleSpaceSite.smallBaseChange_comp_inclusionIso`: the base change of an
étale chart `U` of `X`, included into the big étale site of `Y`, is the fibre product
`U ×_X Y` in the slice, and the comparison is the canonical isomorphism of two cartesian
squares over the same cospan. Its naturality is uniqueness of maps into a fibre product, and
its underlying map to `U` is the cartesian projection of the base change. Passing to direct
images gives the commuting square of topoi, after identifying the direct image along
`Over.pullback f` with the one along `Over.map f` by
`CategoryTheory.StacksRelocalization.sheafPushforwardOverMapIso`.

Part (4) composes part (3) with the retraction identity of Tag 0DF3 at `Y`; the direct
factorization is then obtained from part (1). Both coherence statements are the definitional
unfoldings of those composites.

## References

* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

add_to_stacks 0DF6 "part (2), direct-image section formula"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

/-- **Stacks 0DF6, part (2).** The morphism of spaces-étale topoi induced by cartesian base
change along `f`. -/
@[stacks 0DF6 "part (2), morphism of small étale topoi"]
noncomputable def smallEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)))
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :=
  (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).morphismOfTopoi

/-- **Stacks 0DF6, part (1).** The small-to-big morphism `i_f` agrees with the composite of
`i_Y` and the big étale morphism along `f`. -/
@[stacks 0DF6 "part (1), factorization of the small-to-big morphism"]
noncomputable def smallToBig_comp_big_pushforwardIso :
    (smallToBigEtaleMorphism T f).pushforward ≅
      (smallToBigEtaleMorphism T (𝟙 Y)).pushforward ⋙ (bigEtaleMorphism T f).pushforward := by
  have hsite : inclusionFunctor T f = inclusionFunctor T (𝟙 Y) ⋙ Over.map f := by
    simp only [inclusionFunctor, Over.mapId_eq, Functor.comp_id]
  letI := CategoryTheory.isCocontinuous_comp (inclusionFunctor T (𝟙 Y)) (Over.map f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology Y)
    (L := (T.bigEtaleTopology X))
  dsimp only [smallToBigEtaleMorphism, bigEtaleMorphism]
  simp only [hsite]
  exact sheafPushforwardCocontinuousCompIso
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology Y) (T.bigEtaleTopology X)
    (inclusionFunctor T (𝟙 Y)) (Over.map f)

/-- The comparison of the two cartesian squares over `U.1.hom` and `f` at a single étale chart
`U`: the base change of `U` along `f`, included into the big étale site of `Y`, is the fibre
product `U ×_X Y` in the slice over `X`. -/
noncomputable def smallBaseChange_comp_inclusionIsoApp
    (b : Space.SpacesBaseChange T.fppfSite S T.fppf_mem f)
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X) :
    (b.functor ⋙ Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).obj U ≅
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X ⋙ Over.pullback f).obj U :=
  Over.isoMk ((b.isPullback U).isoIsPullback _ _ (IsPullback.of_hasPullback U.1.hom f))
    ((b.isPullback U).isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback U.1.hom f))

/-- Naturality of the comparison of the two cartesian squares over `U.1.hom` and `f`: the two
maps into the fibre product `U ×_X Y` agree because a map into a fibre product is determined
by its two components. -/
theorem smallBaseChange_comp_inclusionIso_naturality
    (b : Space.SpacesBaseChange T.fppfSite S T.fppf_mem f)
    {U V : Space.SpacesEtale T.fppfSite S T.fppf_mem X} (g : U ⟶ V) :
    (b.functor ⋙ Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).map g ≫
        (smallBaseChange_comp_inclusionIsoApp T f b V).hom =
      (smallBaseChange_comp_inclusionIsoApp T f b U).hom ≫
        (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X ⋙ Over.pullback f).map g := by
  let eu := (b.isPullback U).isoIsPullback _ _ (IsPullback.of_hasPullback U.1.hom f)
  let ev := (b.isPullback V).isoIsPullback _ _ (IsPullback.of_hasPullback V.1.hom f)
  apply Over.OverMorphism.ext
  change (Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).map (b.functor.map g) ≫
      ev.hom = eu.hom ≫ ((Over.pullback f).map
        ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).map g)).left
  apply (IsPullback.of_hasPullback V.1.hom f).hom_ext
  · have := b.projection.naturality g
    simp_all [eu, ev, Over.pullback_map_left, Space.SpacesEtale.toSpaces]
  · simp [eu, ev, Over.pullback_map_left, Space.SpacesEtale.toSpaces]

/-- **Stacks 0DF6, part (3).** The inclusion of the étale objects commutes with base change in
the big slice site, up to the canonical isomorphism of cartesian squares. -/
@[stacks 0DF6 "part (3), commutative square of site functors"]
noncomputable def smallBaseChange_comp_inclusionIso :
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor ⋙
        Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y ≅
      Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X ⋙ Over.pullback f :=
  NatIso.ofComponents
    (fun U ↦ smallBaseChange_comp_inclusionIsoApp T f
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f) U)
    (fun {_ _} g ↦ smallBaseChange_comp_inclusionIso_naturality T f _ g)

/-- **Stacks 0DF6, part (3).** The site-square comparison is the cartesian comparison: its
underlying map to the original chart is the projection defining base change. -/
@[stacks 0DF6 "part (3), cartesian projection coherence"]
theorem smallBaseChange_comp_inclusionIso_projection
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X) :
    ((smallBaseChange_comp_inclusionIso T f).hom.app U).left ≫ pullback.fst U.1.hom f =
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app U := by
  simp [smallBaseChange_comp_inclusionIso, smallBaseChange_comp_inclusionIsoApp]

/-- **Stacks 0DF6, part (3).** The square of big and small étale morphisms commutes on direct
images. -/
@[stacks 0DF6 "part (3), commutative square of topoi"]
noncomputable def bigSmallEtale_pushforwardCommIso :
    ((smallEtaleMorphism T f).comp (bigToSmallEtaleMorphism T Y)).pushforward ≅
      ((bigToSmallEtaleMorphism T X).comp (bigEtaleMorphism T f)).pushforward := by
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f).isContinuous
  letI := (inclusion_isMorphismOfSites T Y).isContinuous
  letI := (inclusion_isMorphismOfSites T X).isContinuous
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  letI := Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology Y)
  letI := Functor.isContinuous_comp
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  exact
    Functor.sheafPushforwardContinuousComp
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Type (u + 1))
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      (T.bigEtaleTopology Y) ≪≫
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comp_inclusionIso T f)
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
      (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (T.bigEtaleTopology X) (T.bigEtaleTopology Y)).symm ≪≫
    Functor.isoWhiskerRight
      (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).symm
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X))

/-- **Stacks 0DF6, part (4).** The small étale direct image factors through the big étale
topoi of both `Y` and `X`. -/
@[stacks 0DF6 "part (4), factorization through both big topoi"]
noncomputable def smallEtale_pushforwardIsoBigFactorization :
    (smallEtaleMorphism T f).pushforward ≅
      ((bigToSmallEtaleMorphism T X).comp
        ((bigEtaleMorphism T f).comp (smallToBigEtaleMorphism T (𝟙 Y)))).pushforward :=
  Functor.isoWhiskerRight (bigToSmall_comp_smallToBig_pushforwardIso T Y).symm
      (smallEtaleMorphism T f).pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (smallToBigEtaleMorphism T (𝟙 Y)).pushforward
      (bigSmallEtale_pushforwardCommIso T f) ≪≫
    (Functor.associator _ _ _).symm

/-- **Stacks 0DF6, part (4).** The small étale direct image factors directly through `i_f`. -/
@[stacks 0DF6 "part (4), direct factorization through the big topos"]
noncomputable def smallEtale_pushforwardIsoDirectFactorization :
    (smallEtaleMorphism T f).pushforward ≅
      ((bigToSmallEtaleMorphism T X).comp (smallToBigEtaleMorphism T f)).pushforward :=
  smallEtale_pushforwardIsoBigFactorization T f ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (smallToBig_comp_big_pushforwardIso T f).symm
      (bigToSmallEtaleMorphism T X).pushforward

private theorem functor_map_symm_hom_cancel_app
    {C : Type u} [Category C] {D : Type u} [Category D] {E : Type u} [Category E]
    {F G : C ⥤ D} (α : F ≅ G) (H : D ⥤ E) (c : C) :
    H.map (α.symm.hom.app c) ≫ H.map (α.hom.app c) = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id_app]
  exact H.map_id _

/-- **Stacks 0DF6, part (4).** The factorization through both big topoi is the topos square
after inserting the small/big retraction at `Y`. -/
@[stacks 0DF6 "part (4), coherence with the topos square"]
theorem smallEtale_pushforwardIsoBigFactorization_coherence
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1))) :
    (smallEtaleMorphism T f).pushforward.map
        ((bigToSmall_comp_smallToBig_pushforwardIso T Y).inv.app F) ≫
      (bigSmallEtale_pushforwardCommIso T f).hom.app
        ((smallToBigEtaleMorphism T (𝟙 Y)).pushforward.obj F) =
    (smallEtale_pushforwardIsoBigFactorization T f).hom.app F :=
  rfl

/-- **Stacks 0DF6, part (4).** The direct factorization and the factorization through `i_Y`
are identified by the canonical comparison `i_f ≅ f_big ∘ i_Y` of part (1). -/
@[stacks 0DF6 "part (4), coherence of the two factorizations"]
theorem smallEtale_pushforwardIsoDirectFactorization_coherence
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1))) :
    (smallEtale_pushforwardIsoDirectFactorization T f).hom.app F ≫
      (bigToSmallEtaleMorphism T X).pushforward.map
        ((smallToBig_comp_big_pushforwardIso T f).hom.app F) =
    (smallEtale_pushforwardIsoBigFactorization T f).hom.app F := by
  change ((smallEtale_pushforwardIsoBigFactorization T f).hom.app F ≫
      (Functor.associator (smallToBigEtaleMorphism T (𝟙 Y)).pushforward
        (bigEtaleMorphism T f).pushforward
        (bigToSmallEtaleMorphism T X).pushforward).hom.app F ≫
      (Functor.isoWhiskerRight (smallToBig_comp_big_pushforwardIso T f).symm
        (bigToSmallEtaleMorphism T X).pushforward).hom.app F) ≫
    (bigToSmallEtaleMorphism T X).pushforward.map
      ((smallToBig_comp_big_pushforwardIso T f).hom.app F) =
    (smallEtale_pushforwardIsoBigFactorization T f).hom.app F
  simp only [Functor.associator_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  dsimp only [MorphismOfTopoi.comp, smallEtale_pushforwardIsoBigFactorization] at ⊢
  simp only [Functor.comp_obj, Category.id_comp]
  rw [Category.assoc, functor_map_symm_hom_cancel_app]
  simp

end AlgebraicGeometry.BigEtaleSpaceSite

end
