module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Restricting a big étale direct image to the small étale site

Let `f : Y ⟶ X` be a morphism of algebraic spaces of a big étale site. Restriction of a big
étale sheaf to the spaces-étale site is the direct image along the comparison morphism
`π_X : (Spaces/X)_étale ⟶ X_{spaces,étale}`, and the square formed by `π_X`, `π_Y`, the big
étale direct image `f_big` and the small étale direct image `f_small` commutes. Hence
`(f_{big,*}F)|_{X_étale} = f_{small,*}(F|_{Y_étale})` for a sheaf `F` on `(Spaces/Y)_étale`,
and the same comparison is an isomorphism of `𝒪_X`-modules on `X_étale` when `F` is a sheaf of
`𝒪`-modules.

Both sites carry the structure sheaf of global regular functions, and all three structure maps
involved are pullback of regular functions: the one of `π_X` is the identity, the one of `f_big`
is pullback along the projection of a fibre product in the slice, and the one of `f_small` is
pullback along the cartesian projection of a base change of étale objects.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleRingedSite`: the big étale site of an algebraic
  space with its sheaf of global regular functions.  The spaces-étale site of an algebraic space
  with its sheaf of global regular functions is
  `AlgebraicGeometry.Space.spacesEtaleRingedSite`.
* `AlgebraicGeometry.BigEtaleSpaceSite.restrictSharp`,
  `AlgebraicGeometry.BigEtaleSpaceSite.bigPullbackSharp` and
  `AlgebraicGeometry.BigEtaleSpaceSite.smallBaseChangeSharp`: the structure maps of `π_X`,
  `f_big` and `f_small`.
* `AlgebraicGeometry.BigEtaleSpaceSite.restrictModules`,
  `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleModulePushforward` and
  `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleModulePushforward`: restriction to the
  spaces-étale site, `f_{big,*}` and `f_{small,*}` on sheaves of modules.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtale_restrictPushforwardIso`: **Stacks 0DG9**
  for sheaves of sets.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtale_restrictPushforwardModulesIso`:
  **Stacks 0DG9** for sheaves of `𝒪`-modules.
* `AlgebraicGeometry.BigEtaleSpaceSite.sharpCommSq`: the three structure maps are compatible
  with the commuting square of site functors of Tag 0DF6.

## Implementation notes

The displayed equation of the source is delivered as a pinned natural isomorphism of composite
direct-image functors; that is the categorical form of an equality of sheaves functorial in the
sheaf, and the inverse-image statement is its mate.

For sheaves of sets the comparison is the square of Tag 0DF6 read through the definition of a
composite of morphisms of topoi, which identifies the direct image of a composite with the
composite of the direct images on the nose.

For sheaves of modules the comparison is not transported from the sheaf-level one: both sides
are direct images along a *continuous functor of sites* together with a map of structure
sheaves, and for those the two composites are literally direct images along the two composite
site functors, so the whole content is the compatibility `sharpCommSq` of the three structure
maps with the comparison isomorphism of the two composite functors. That compatibility is
`AlgebraicGeometry.BigEtaleSpaceSite.smallBaseChange_comp_inclusionIso_projection`: the
comparison of the two cartesian squares is compatible with the projections, and pullback of
global regular functions is functorial.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 09W9](https://stacks.math.columbia.edu/tag/09W9)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 0DG9](https://stacks.math.columbia.edu/tag/0DG9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### The two ringed sites -/

/-- The big étale site of an algebraic space `X` of the site, together with its sheaf of global
regular functions, as a ringed site. -/
abbrev bigEtaleRingedSite (X : T.Spaces) : RingedSite.{u + 1, u + 1, u + 1} where
  C := Over X
  J := T.bigEtaleTopology X
  O := T.structureSheaf X

/-- Forgetting commutativity of rings preserves sheaves on the big étale site of `X`. -/
instance hasSheafCompose_bigEtale (X : T.Spaces) :
    (T.bigEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (bigEtaleRingedSite T X).hasSheafCompose_forget₂_ringCat

/-- Forgetting commutativity of rings preserves sheaves on the spaces-étale site of `X`. -/
instance hasSheafCompose_spacesEtale (X : T.Spaces) :
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (Space.spacesEtaleRingedSite T.fppfSite S T.fppf_mem X).hasSheafCompose_forget₂_ringCat

/-- The presheaf of rings of global regular functions on the algebraic spaces of the site: the
presheaf of commutative rings of global regular functions with its commutativity forgotten. -/
abbrev globalRingPresheaf : T.Spacesᵒᵖ ⥤ RingCat.{u + 1} :=
  Space.globalFunctionsPresheaf T.fppfSite S T.fppf_mem ⋙
    forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The sheaf of rings of global regular functions on the big étale site of `X`. -/
abbrev bigEtaleRingSheaf (X : T.Spaces) : Sheaf (T.bigEtaleTopology X) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleRingedSite T X).O)

/-- The sheaf of rings of global regular functions on the spaces-étale site of `X`. -/
abbrev spacesEtaleRingSheaf (X : T.Spaces) :
    Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (Space.spacesEtaleRingedSite T.fppfSite S T.fppf_mem X).O)

/-- Sheaves of `𝒪_X`-modules on the big étale site of `X`. -/
abbrev BigEtaleModules (X : T.Spaces) := SheafOfModules.{m} (bigEtaleRingSheaf T X)

/-- Sheaves of `𝒪_X`-modules on the spaces-étale site of `X`. -/
abbrev SpacesEtaleModules (X : T.Spaces) := SheafOfModules.{m} (spacesEtaleRingSheaf T X)

/-! ### Continuity of the four site functors -/

variable {X Y : T.Spaces}

/-- Base change along `f : Y ⟶ X` is continuous for the big étale topologies of `X` and `Y`. -/
instance isContinuous_overPullback (f : Y ⟶ X) :
    (Over.pullback f).IsContinuous (T.bigEtaleTopology X) (T.bigEtaleTopology Y) :=
  (StacksRelocalization.isMorphismOfSites_overPullback T.topology f).isContinuous

/-- Base change along `f : Y ⟶ X` from the spaces-étale site of `X` to that of `Y`, followed by
the inclusion into the big étale site of `Y`, is continuous. -/
instance isContinuous_spacesBaseChange_comp_inclusion (f : Y ⟶ X) :
    ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor ⋙
        Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology Y) :=
  Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology Y)

/-- The inclusion of the spaces-étale site of `X` into its big étale site, followed by base change
along `f : Y ⟶ X`, is continuous for the big étale topology of `Y`. -/
instance isContinuous_inclusion_comp_overPullback (f : Y ⟶ X) :
    ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) ⋙ Over.pullback f).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology Y) :=
  Functor.isContinuous_comp
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)

/-! ### The three structure maps -/

/-- The projection of the base change in the slice over `X`: the fibre product `V ×_X Y` of an
algebraic space `V` over `X` with `f`, mapped to `V`. -/
def overPullbackProjection (f : Y ⟶ X) :
    Over.pullback f ⋙ Over.forget Y ⟶ Over.forget X where
  app V := pullback.fst V.hom f
  naturality _ _ _ := by simp

/-- **Stacks 0DF9, item (3).** The structure map of the comparison morphism `π_X`: the sections
of the direct image of the big étale structure sheaf over an algebraic space étale over `X` are
its own global regular functions, so the structure map is the identity. -/
@[stacks 0DF9 "item (3), the structure map of the comparison morphism π_X"]
def restrictSharp (X : T.Spaces) :
    spacesEtaleRingSheaf T X ⟶
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X)).obj (bigEtaleRingSheaf T X) :=
  𝟙 _

/-- **Stacks 0DF9, item (5).** The structure map of the big étale morphism `f_big`: pullback of
global regular functions along the projection of the fibre product `V ×_X Y` to `V`. -/
@[stacks 0DF9 "item (5), the structure map of the big étale morphism f_big"]
def bigPullbackSharp (f : Y ⟶ X) :
    bigEtaleRingSheaf T X ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u + 1}
        (T.bigEtaleTopology X) (T.bigEtaleTopology Y)).obj (bigEtaleRingSheaf T Y) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op (overPullbackProjection T f)) (globalRingPresheaf T))

/-- **Stacks 0DF9, item (4).** The structure map of the small étale morphism `f_small`:
pullback of global regular functions along the cartesian projection of the base change of an
algebraic space étale over `X`. -/
@[stacks 0DF9 "item (4), the structure map of the small étale morphism f_small"]
def smallBaseChangeSharp (f : Y ⟶ X) :
    spacesEtaleRingSheaf T X ⟶
      ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)).obj
        (spacesEtaleRingSheaf T Y) :=
  ObjectProperty.homMk
    (Functor.whiskerRight
      (NatTrans.op (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).projection)
      (globalRingPresheaf T))

/-! ### The direct images on sheaves of modules -/

/-- Restriction of a sheaf of `𝒪`-modules on the big étale site of `X` to the spaces-étale site
of `X`, that is, the direct image of `𝒪`-modules along the comparison morphism `π_X`. -/
abbrev restrictModules (X : T.Spaces) :
    BigEtaleModules.{u, m} T X ⥤ SpacesEtaleModules.{u, m} T X :=
  SheafOfModules.pushforward.{m} (restrictSharp T X)

/-- The direct image of sheaves of `𝒪`-modules along the big étale morphism `f_big`. -/
abbrev bigEtaleModulePushforward (f : Y ⟶ X) :
    BigEtaleModules.{u, m} T Y ⥤ BigEtaleModules.{u, m} T X :=
  SheafOfModules.pushforward.{m} (bigPullbackSharp T f)

/-- The direct image of sheaves of `𝒪`-modules along the small étale morphism `f_small`. -/
abbrev smallEtaleModulePushforward (f : Y ⟶ X) :
    SpacesEtaleModules.{u, m} T Y ⥤ SpacesEtaleModules.{u, m} T X :=
  SheafOfModules.pushforward.{m} (smallBaseChangeSharp T f)

/-! ### The comparison -/

/-- The structure maps of `π_X`, `f_big`, `π_Y` and `f_small` are compatible with the comparison
isomorphism of Tag 0DF6 between the two composite site functors: both composite structure maps
are pullback of global regular functions along the cartesian projection of the base change. -/
theorem sharpCommSq (f : Y ⟶ X) :
    (restrictSharp T X ≫
        ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
          RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
          (T.bigEtaleTopology X)).map (bigPullbackSharp T f)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (smallBaseChange_comp_inclusionIso T f).hom RingCat.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology Y)).app (bigEtaleRingSheaf T Y) =
    smallBaseChangeSharp T f ≫
      ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor.sheafPushforwardContinuous
        RingCat.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)).map (restrictSharp T Y) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  change (globalRingPresheaf T).map ((pullback.fst U.unop.obj.hom f).op) ≫
      (globalRingPresheaf T).map
        (((smallBaseChange_comp_inclusionIso T f).hom.app U.unop).left.op) =
    (globalRingPresheaf T).map
      (((Space.spacesBaseChange T.fppfSite S T.fppf_mem f).projection.app U.unop).op)
  rw [← Functor.map_comp, ← op_comp, smallBaseChange_comp_inclusionIso_projection]

/-- **Stacks 0DG9.** The restriction to the spaces-étale site of `X` of the big étale direct
image along `f` is the small étale direct image along `f` of the restriction to the
spaces-étale site of `Y`. -/
@[stacks 0DG9 "the comparison for sheaves of sets"]
def bigSmallEtale_restrictPushforwardIso (f : Y ⟶ X) :
    (bigEtaleMorphism T f).pushforward ⋙ (bigToSmallEtaleMorphism T X).pushforward ≅
      (bigToSmallEtaleMorphism T Y).pushforward ⋙ (smallEtaleMorphism T f).pushforward :=
  (bigSmallEtale_pushforwardCommIso T f).symm

/-- **Stacks 0DG9.** For a sheaf of `𝒪`-modules the comparison of the previous isomorphism is
an isomorphism of `𝒪_X`-modules on the spaces-étale site of `X`. -/
@[stacks 0DG9 "the comparison for sheaves of modules"]
def bigSmallEtale_restrictPushforwardModulesIso (f : Y ⟶ X) :
    bigEtaleModulePushforward.{u, m} T f ⋙ restrictModules.{u, m} T X ≅
      restrictModules.{u, m} T Y ⋙ smallEtaleModulePushforward.{u, m} T f :=
  SheafOfModules.pushforwardComp.{m} (restrictSharp T X) (bigPullbackSharp T f) ≪≫
    SheafOfModules.pushforwardCongr₂.{m} _ (smallBaseChange_comp_inclusionIso T f)
      (sharpCommSq T f) ≪≫
    (SheafOfModules.pushforwardComp.{m} (smallBaseChangeSharp T f) (restrictSharp T Y)).symm

/-- **Stacks 0DG9.** On sections over an algebraic space étale over `X`, the comparison of
sheaves of modules is restriction along the comparison isomorphism of the two cartesian squares
of Tag 0DF6. -/
@[stacks 0DG9 "the comparison for sheaves of modules, on sections"]
theorem bigSmallEtale_restrictPushforwardModulesIso_hom_app_val_app (f : Y ⟶ X)
    (M : BigEtaleModules.{u, m} T Y)
    (U : (Space.SpacesEtale T.fppfSite S T.fppf_mem X)ᵒᵖ) (x) :
    ((bigSmallEtale_restrictPushforwardModulesIso.{u, m} T f).hom.app M).val.app U x =
      M.val.map ((smallBaseChange_comp_inclusionIso T f).hom.app U.unop).op x :=
  rfl

end AlgebraicGeometry.BigEtaleSpaceSite

end
