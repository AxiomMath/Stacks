module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtalePushforwardModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp

/-!
# Composition and base change for the big and small étale topoi of algebraic spaces

Let `T` be a big étale site of algebraic spaces over a scheme `S`. The morphisms of big and
small étale topoi induced by a morphism of algebraic spaces (Stacks 0DF5, 0DF2 and 0DF6) are
functorial in two senses: they compose, and they commute with base change across a cartesian
square of algebraic spaces.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleMorphism_comp_pushforwardIso` and
  `.bigEtaleMorphism_comp_inverseImageIso`: **Stacks 0DF7** for the big étale topoi.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleMorphism_comp_inverseImageIso`:
  **Stacks 0DF7** for the small étale topoi; the direct images are
  `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtalePushforwardBaseChangeIso` and
  `.bigEtalePushforwardBaseChangeIso`: **Stacks 0DF8**, the base-change comparisons from big
  étale sheaves on `Y` to small, respectively big, étale sheaves on `X'`.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleModulePushforwardBaseChangeIso`:
  **Stacks 0DF8 for sheaves of `𝒪`-modules**, the same square on `𝒪`-modules.
* `AlgebraicGeometry.BigEtaleSpaceSite.sharpCommSqBaseChange`: the four structure maps are
  compatible with the comparison `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleCartesianIndexIso`
  of the two composite site functors.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleCartesianIndexIso_projection`: the projection
  coherence of that comparison.

## Implementation notes

The source writes equalities of geometric morphisms. Their direct-image functors are
canonically isomorphic, and the inverse-image comparisons are the adjunction mates, so these
record the corresponding identities without identifying chosen fibre products or chosen
sheafifications on the nose. For the small étale direct image under composition, the existing
composition comparison for spaces-étale base change is already the direct-image comparison of
`AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleMorphism`, so nothing new is constructed.

For base change the square is an arbitrary cartesian square, not a chosen fibre product.

## References

* [Stacks Project, Tag 0DF7](https://stacks.math.columbia.edu/tag/0DF7)
* [Stacks Project, Tag 0DF8](https://stacks.math.columbia.edu/tag/0DF8)
* [Stacks Project, Tag 0DG9](https://stacks.math.columbia.edu/tag/0DG9), the `g = 𝟙` case of the
  `𝒪`-module square
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9), the structure maps
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

add_to_stacks 0DF7 "small étale direct images" Space.spacesBaseChange_pushforward_comp

section Comp

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y Z : T.Spaces} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The direct images of composable morphisms of big étale topoi agree canonically with the direct
image of the composite. -/
@[stacks 0DF7 "big étale direct images"]
def bigEtaleMorphism_comp_pushforwardIso :
    ((bigEtaleMorphism T g).comp (bigEtaleMorphism T f)).pushforward ≅
      (bigEtaleMorphism T (f ≫ g)).pushforward := by
  dsimp only [bigEtaleMorphism, MorphismOfTopoi.comp]
  simpa only [Over.mapComp_eq] using (sheafPushforwardCocontinuousCompIso
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y) (T.bigEtaleTopology Z)
    (Over.map f) (Over.map g)).symm

/-- The inverse-image comparison for the big étale topoi is the adjunction mate of the direct-image
comparison. -/
@[stacks 0DF7 "big étale inverse images"]
def bigEtaleMorphism_comp_inverseImageIso :
    ((bigEtaleMorphism T g).comp (bigEtaleMorphism T f)).inverseImage ≅
      (bigEtaleMorphism T (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso (bigEtaleMorphism T g).adj (bigEtaleMorphism T f).adj
    (bigEtaleMorphism T (f ≫ g)).adj (bigEtaleMorphism_comp_pushforwardIso T f g)

/-- The inverse-image comparison for the small étale topoi is the adjunction mate of the canonical
composition comparison for cartesian base change on the spaces-étale sites. -/
@[stacks 0DF7 "small étale inverse images"]
def smallEtaleMorphism_comp_inverseImageIso :
    ((smallEtaleMorphism T g).comp (smallEtaleMorphism T f)).inverseImage ≅
      (smallEtaleMorphism T (f ≫ g)).inverseImage :=
  Adjunction.leftAdjointCompIso (smallEtaleMorphism T g).adj (smallEtaleMorphism T f).adj
    (smallEtaleMorphism T (f ≫ g)).adj
    (Space.spacesBaseChange_pushforward_comp T.fppfSite S T.fppf_mem f g)

end Comp

section BaseChange

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {Y' Y X' X : T.Spaces}
  (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (g : X' ⟶ X) (h : IsPullback g' f' f g)

/-- The comparison of the two descriptions of the small étale site of `X'` inside the big
étale site of `Y`: including an étale object of `X'` and then base changing along `f` agrees
with base changing along `f'` and then including into the big étale site of `Y`. -/
def smallEtaleCartesianIndexIso :
    inclusionFunctor T g ⋙ Over.pullback f ≅
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor ⋙
        inclusionFunctor T g' := by
  letI := inclusionFunctor_isContinuous T g
  letI := inclusionFunctor_isContinuous T g'
  letI := (Space.spacesBaseChange_isMorphismOfSites
    T.fppfSite S T.fppf_mem f').isContinuous
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  let incX' := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X'
  let incY' := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y'
  let b := Space.spacesBaseChange T.fppfSite S T.fppf_mem f'
  calc
    inclusionFunctor T g ⋙ Over.pullback f ≅
        incX' ⋙ (Over.map g ⋙ Over.pullback f) := by
      dsimp [inclusionFunctor]
      exact (Functor.associator incX' (Over.map g) (Over.pullback f)).symm
    _ ≅ incX' ⋙ (Over.pullback f' ⋙ Over.map g') :=
      Functor.isoWhiskerLeft incX' (overPullbackBaseChangeIso g' f' f g h)
    _ ≅ (incX' ⋙ Over.pullback f') ⋙ Over.map g' :=
      (Functor.associator incX' (Over.pullback f') (Over.map g')).symm
    _ ≅ (b.functor ⋙ incY') ⋙ Over.map g' :=
      Functor.isoWhiskerRight (smallBaseChange_comp_inclusionIso T f').symm (Over.map g')
    _ ≅ b.functor ⋙ (incY' ⋙ Over.map g') :=
      Functor.associator b.functor incY' (Over.map g')
    _ = b.functor ⋙ inclusionFunctor T g' := rfl

/-- Restriction to the small étale site commutes canonically with big étale direct image across a
cartesian square of algebraic spaces. -/
@[stacks 0DF8 "small-site base change"]
def smallEtalePushforwardBaseChangeIso :
    (bigEtaleMorphism T f).pushforward ⋙ (smallToBigEtaleMorphism T g).inverseImage ≅
      (smallToBigEtaleMorphism T g').inverseImage ⋙ (smallEtaleMorphism T f').pushforward := by
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  letI := (Space.spacesBaseChange_isMorphismOfSites
    T.fppfSite S T.fppf_mem f').isContinuous
  letI := Functor.isContinuous_comp (inclusionFunctor T g) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  letI := Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor (inclusionFunctor T g')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
    (T.bigEtaleTopology Y)
  calc
    _ ≅ (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X) (T.bigEtaleTopology Y) ⋙
        (inclusionFunctor T g).sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
          (T.bigEtaleTopology X) := by
      dsimp only [bigEtaleMorphism, smallToBigEtaleMorphism]
      exact Functor.isoWhiskerRight
        (StacksRelocalization.sheafPushforwardOverMapIso T.topology f) _
    _ ≅ (inclusionFunctor T g ⋙ Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
          (T.bigEtaleTopology Y) :=
      Functor.sheafPushforwardContinuousComp (inclusionFunctor T g) (Over.pullback f)
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
    _ ≅ ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor ⋙
          inclusionFunctor T g').sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
          (T.bigEtaleTopology Y) :=
      Functor.sheafPushforwardContinuousIso
        (smallEtaleCartesianIndexIso T g' f' f g h) (Type (u + 1))
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (T.bigEtaleTopology Y)
    _ ≅ (inclusionFunctor T g').sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
          (T.bigEtaleTopology Y) ⋙
        Functor.sheafPushforwardContinuous
          (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') :=
      (Functor.sheafPushforwardContinuousComp
        (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor (inclusionFunctor T g')
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
        (T.bigEtaleTopology Y)).symm
    _ ≅ (smallToBigEtaleMorphism T g').inverseImage ⋙
          (smallEtaleMorphism T f').pushforward := by
      dsimp only [smallToBigEtaleMorphism, smallEtaleMorphism,
        Space.spacesBaseChange_isMorphismOfSites]
      rfl

/-- Big étale inverse image commutes canonically with big étale direct image across a cartesian
square of algebraic spaces. -/
@[stacks 0DF8 "big-site base change"]
def bigEtalePushforwardBaseChangeIso :
    (bigEtaleMorphism T f).pushforward ⋙ (bigEtaleMorphism T g).inverseImage ≅
      (bigEtaleMorphism T g').inverseImage ⋙ (bigEtaleMorphism T f').pushforward := by
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous
  letI := (StacksRelocalization.isMorphismOfSites_overPullback T.topology f').isContinuous
  letI := (Over.map g).IsContinuous (T.bigEtaleTopology X') (T.bigEtaleTopology X)
  letI := (Over.map g').IsContinuous (T.bigEtaleTopology Y') (T.bigEtaleTopology Y)
  letI := Functor.isContinuous_comp (Over.map g) (Over.pullback f)
    (T.bigEtaleTopology X') (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  letI := Functor.isContinuous_comp (Over.pullback f') (Over.map g')
    (T.bigEtaleTopology X') (T.bigEtaleTopology Y') (T.bigEtaleTopology Y)
  calc
    _ ≅ (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X) (T.bigEtaleTopology Y) ⋙
        (Over.map g).sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X') (T.bigEtaleTopology X) := by
      dsimp only [bigEtaleMorphism]
      exact Functor.isoWhiskerRight
        (StacksRelocalization.sheafPushforwardOverMapIso T.topology f) _
    _ ≅ (Over.map g ⋙ Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X') (T.bigEtaleTopology Y) :=
      Functor.sheafPushforwardContinuousComp (Over.map g) (Over.pullback f) (Type (u + 1))
        (T.bigEtaleTopology X') (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
    _ ≅ (Over.pullback f' ⋙ Over.map g').sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X') (T.bigEtaleTopology Y) :=
      Functor.sheafPushforwardContinuousIso (overPullbackBaseChangeIso g' f' f g h)
        (Type (u + 1)) (T.bigEtaleTopology X') (T.bigEtaleTopology Y)
    _ ≅ (Over.map g').sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology Y') (T.bigEtaleTopology Y) ⋙
        (Over.pullback f').sheafPushforwardContinuous (Type (u + 1))
          (T.bigEtaleTopology X') (T.bigEtaleTopology Y') :=
      (Functor.sheafPushforwardContinuousComp (Over.pullback f') (Over.map g')
        (Type (u + 1)) (T.bigEtaleTopology X') (T.bigEtaleTopology Y')
        (T.bigEtaleTopology Y)).symm
    _ ≅ (bigEtaleMorphism T g').inverseImage ⋙ (bigEtaleMorphism T f').pushforward := by
      dsimp only [bigEtaleMorphism]
      exact Functor.isoWhiskerLeft _
        (StacksRelocalization.sheafPushforwardOverMapIso T.topology f').symm

end BaseChange

section BaseChangeModules

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- **Stacks 0DF9, item (3), along a morphism.** The structure map of the comparison morphism
`i_g` from the big étale site of `X` to the spaces-étale site of `X'` attached to
`g : X' ⟶ X`: the sections of the direct image of the big étale structure sheaf of `X` over an
algebraic space étale over `X'` are its own global regular functions, so the structure map is
the identity. This is `AlgebraicGeometry.BigEtaleSpaceSite.restrictSharp` along `g`. -/
def restrictAlongSharp {X X' : T.Spaces} (g : X' ⟶ X) :
    spacesEtaleRingSheaf T X' ⟶
      ((inclusionFunctor T g).sheafPushforwardContinuous RingCat.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (T.bigEtaleTopology X)).obj (bigEtaleRingSheaf T X) :=
  𝟙 _

/-- Restriction of a sheaf of `𝒪`-modules from the big étale site of `X` to the spaces-étale
site of `X'` along `g : X' ⟶ X`, that is, the inverse image `i_g^*` of Tag 0DF2 on sheaves of
`𝒪`-modules. For `g = 𝟙 X` this is
`AlgebraicGeometry.BigEtaleSpaceSite.restrictModules`. -/
abbrev restrictModulesAlong {X X' : T.Spaces} (g : X' ⟶ X) :
    BigEtaleModules.{u, u + 1} T X ⥤ SpacesEtaleModules.{u, u + 1} T X' :=
  SheafOfModules.pushforward.{u + 1} (restrictAlongSharp T g)

variable {Y' Y X' X : T.Spaces} (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (g : X' ⟶ X)
  (h : IsPullback g' f' f g)

/-- Base change of the spaces-étale sites along `f'` is continuous. -/
instance isContinuous_spacesBaseChangeFunctor :
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor.IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') :=
  (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f').isContinuous

/-- Including an algebraic space étale over `X'` into the big étale site of `X` and then base
changing along `f` is continuous. -/
instance isContinuous_inclusionFunctor_comp_overPullback :
    (inclusionFunctor T g ⋙ Over.pullback f).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (T.bigEtaleTopology Y) :=
  Functor.isContinuous_comp (inclusionFunctor T g) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)

/-- Base changing an algebraic space étale over `X'` along `f'` and then including it into the
big étale site of `Y` is continuous. -/
instance isContinuous_spacesBaseChange_comp_inclusionFunctor :
    ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor ⋙
        inclusionFunctor T g').IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (T.bigEtaleTopology Y) :=
  Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor (inclusionFunctor T g')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
    (T.bigEtaleTopology Y)

/-- The comparison of the two descriptions of the small étale site of `X'` inside the big étale
site of `Y`, read on components: it is the base-change comparison of the big slice sites
followed by the comparison of the two cartesian squares over the small site. -/
private theorem smallEtaleCartesianIndexIso_inv_app
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X') :
    (smallEtaleCartesianIndexIso T g' f' f g h).inv.app U =
      (Over.map g').map ((smallBaseChange_comp_inclusionIso T f').hom.app U) ≫
        (overPullbackBaseChangeIso g' f' f g h).inv.app
          ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X').obj U) :=
  rfl

/-- The base-change comparison of the big slice sites is the cartesian comparison: composed with
the projection of the fibre product over `X` it is the projection of the fibre product
over `X'`. -/
private theorem overPullbackBaseChangeIso_inv_app_left_fst (W : Over X') :
    ((overPullbackBaseChangeIso g' f' f g h).inv.app W).left ≫
        pullback.fst (W.hom ≫ g) f = pullback.fst W.hom f' := by
  simp [overPullbackBaseChangeIso]

/-- **Projection coherence.** The comparison of the two descriptions of the small étale site of
`X'` inside the big étale site of `Y` is the cartesian comparison: its underlying map, followed by
the projection of the fibre product with `f`, is the projection defining the base change along
`f'`. This is `AlgebraicGeometry.BigEtaleSpaceSite.smallBaseChange_comp_inclusionIso_projection`
across the whole cartesian square. -/
@[stacks 0DF8 "projection coherence of the index comparison"]
theorem smallEtaleCartesianIndexIso_projection
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X') :
    ((smallEtaleCartesianIndexIso T g' f' f g h).inv.app U).left ≫
        pullback.fst ((inclusionFunctor T g).obj U).hom f =
      (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').projection.app U := by
  rw [smallEtaleCartesianIndexIso_inv_app T g' f' f g h U]
  change ((smallBaseChange_comp_inclusionIso T f').hom.app U).left ≫
      ((overPullbackBaseChangeIso g' f' f g h).inv.app
          ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X').obj U)).left ≫
        pullback.fst
          (((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X').obj U).hom ≫ g) f = _
  rw [overPullbackBaseChangeIso_inv_app_left_fst T g' f' f g h
    ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X').obj U)]
  exact smallBaseChange_comp_inclusionIso_projection T f' U

/-- **Structure-map coherence.** The structure maps of `i_g`, `f_big`, `i_{g'}` and `f'_small` are
compatible with the comparison of the two composite site functors over the cartesian square: both
composite structure maps are pullback of global regular functions along the cartesian projection of
the base change. This is `AlgebraicGeometry.BigEtaleSpaceSite.sharpCommSq` across the whole square.
-/
@[stacks 0DF8 "structure-map coherence over the cartesian square"]
theorem sharpCommSqBaseChange :
    (restrictAlongSharp T g ≫
        ((inclusionFunctor T g).sheafPushforwardContinuous RingCat.{u + 1}
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
          (T.bigEtaleTopology X)).map (bigPullbackSharp T f)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (smallEtaleCartesianIndexIso T g' f' f g h).symm.hom RingCat.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (T.bigEtaleTopology Y)).app (bigEtaleRingSheaf T Y) =
    smallBaseChangeSharp T f' ≫
      ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor.sheafPushforwardContinuous
        RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')).map
        (restrictAlongSharp T g') := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  change (globalRingPresheaf T).map ((pullback.fst ((inclusionFunctor T g).obj U.unop).hom f).op) ≫
      (globalRingPresheaf T).map
        (((smallEtaleCartesianIndexIso T g' f' f g h).inv.app U.unop).left.op) =
    (globalRingPresheaf T).map
      (((Space.spacesBaseChange T.fppfSite S T.fppf_mem f').projection.app U.unop).op)
  rw [← Functor.map_comp, ← op_comp, smallEtaleCartesianIndexIso_projection]

/-- Restriction to the small étale site commutes canonically with big étale direct image of sheaves
of `𝒪`-modules across a cartesian square of algebraic spaces:
`i_g^*(f_{big,*}F) = f'_{small,*}(i_{g'}^*F)`.

This is the `𝒪`-module form of
`AlgebraicGeometry.BigEtaleSpaceSite.smallEtalePushforwardBaseChangeIso`, which states the same
square for sheaves of sets. -/
@[stacks 0DF8 "the sheaf-of-modules form over a cartesian square"]
def smallEtaleModulePushforwardBaseChangeIso :
    bigEtaleModulePushforward.{u, u + 1} T f ⋙ restrictModulesAlong T g ≅
      restrictModulesAlong T g' ⋙ smallEtaleModulePushforward.{u, u + 1} T f' :=
  SheafOfModules.pushforwardComp.{u + 1} (restrictAlongSharp T g) (bigPullbackSharp T f) ≪≫
    SheafOfModules.pushforwardCongr₂.{u + 1} _
      (smallEtaleCartesianIndexIso T g' f' f g h).symm
      (sharpCommSqBaseChange T g' f' f g h) ≪≫
    (SheafOfModules.pushforwardComp.{u + 1} (smallBaseChangeSharp T f')
      (restrictAlongSharp T g')).symm

end BaseChangeModules

end AlgebraicGeometry.BigEtaleSpaceSite

end
