module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallToBigEtale
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The small étale topos at the bottom of the big étale topos (Stacks 0DF3)

For an algebraic space `X` of a big étale site of algebraic spaces, the spaces-étale site of
`X` is the full subsite of the big étale site of `X` on the objects étale over `X`. That
inclusion is a morphism of sites in the reverse direction, so it determines a morphism of
topoi from the big étale topos of `X` to its small étale topos, and that morphism is a
retraction of the small-to-big morphism `i_X` of Tag 0DF2 for `f = 𝟙 X`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleMorphism` is the morphism of topoi
  induced by the inclusion of the small étale site: **Stacks 0DF3**.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigEtaleMorphism T (𝟙 X)` is the morphism
  denoted `i_X` in the source.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.inclusion_isMorphismOfSites`: the inclusion is a
  morphism of sites.
* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctorIdIso` identifies the inclusion with
  the functor of Tag 0DF2 for `f = 𝟙 X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_comp_smallToBig_pushforwardIso`: the
  composite of the two morphisms of topoi is the identity on the small étale topos.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBig_inverseImageIso_bigToSmall_pushforward`:
  the inverse image of `i_X` is the direct image of the big-to-small morphism — both restrict
  a big sheaf to the objects étale over `X`.
* `CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj` is the section rule for
  that restriction.

## Implementation notes

An equality of morphisms of topoi is expressed by a natural isomorphism of their direct-image
functors; this is the categorical form of equality of geometric morphisms, and the
corresponding inverse-image isomorphism is its mate.

The inclusion of the spaces-étale site of `X` into the big étale site of `X` is the functor of
Tag 0DF2 for `f = 𝟙 X` up to the canonical isomorphism `Over.mapId`, so its continuity and
cocontinuity are the identity-morphism case of Tag 0DF2 transported along that isomorphism.
Being a morphism of sites needs in addition that the inclusion preserve the final object and
fibre products, which it does, so
`CategoryTheory.Functor.isMorphismOfSites_of_isTerminal` applies.

The retraction identity is uniqueness of right adjoints: the inverse image of `i_X` and the
direct image of the inclusion are both right adjoint to the sheafified left adjoint of the
inclusion, so they agree, and the counit of the continuous adjunction is then an isomorphism.

## References

* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)

/-- **Stacks 0DF3.** The full inclusion of the spaces-étale site of `X` into the big étale
site of `X` is a morphism of sites in the reverse direction. -/
@[stacks 0DF3 "the morphism of sites"]
theorem inclusion_isMorphismOfSites :
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).IsMorphismOfSites
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X) :=
  let : (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X) :=
    Functor.isContinuous_of_iso
      (Functor.isoWhiskerLeft
        (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.mapId X))
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)
  Functor.isMorphismOfSites_of_isTerminal _
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)
    (Space.SpacesEtale.final_isTerminal T.fppfSite S T.fppf_mem X) Over.mkIdTerminal

/-- The inclusion of the spaces-étale site of `X` into the big étale site of `X` is
continuous, being half of the morphism of sites it induces. -/
instance spacesEtaleInclusion_isContinuous :
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X) :=
  (inclusion_isMorphismOfSites T X).isContinuous

/-- **Stacks 0DF3.** The inclusion of the spaces-étale site of `X` is canonically the functor
of Tag 0DF2 for the identity morphism of `X`. -/
@[stacks 0DF3 "identification with the identity case of 0DF2"]
noncomputable def inclusionFunctorIdIso :
    inclusionFunctor T (𝟙 X) ≅ Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X :=
  Functor.isoWhiskerLeft
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) (Over.mapId X)

/-- **Stacks 0DF3.** The morphism of topoi from the big étale topos of `X` to its small étale
topos, induced by the inclusion of the spaces-étale site as a morphism of sites. -/
@[stacks 0DF3 "the morphism of topoi",
  stacks 0DF4 "its pushforward is the restriction to the small étale site"]
noncomputable def bigToSmallEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (T.bigEtaleTopology X) (Type (u + 1)))
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :=
  (inclusion_isMorphismOfSites T X).morphismOfTopoi

/-- **Stacks 0DF3.** Composing the morphism of topoi induced by the inclusion with the
small-to-big morphism `i_X` gives the identity on the small étale topos, canonically up to
natural isomorphism. -/
@[stacks 0DF3 "the retraction identity"]
noncomputable def bigToSmall_comp_smallToBig_pushforwardIso :
    ((bigToSmallEtaleMorphism T X).comp (smallToBigEtaleMorphism T (𝟙 X))).pushforward ≅
      𝟭 (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :=
  letI J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  letI K := T.bigEtaleTopology X
  letI v := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  letI e := inclusionFunctorIdIso T X
  letI : v.IsCocontinuous J K := Functor.IsCocontinuous.of_iso e
  letI : v.IsContinuous J K := Functor.isContinuous_of_iso e J K
  letI adjW := (inclusionFunctor T (𝟙 X)).sheafAdjunctionCocontinuous (Type (u + 1)) J K
  letI adjV := v.sheafAdjunctionCocontinuous (Type (u + 1)) J K
  letI adjV' := adjV.ofNatIsoLeft
    (Functor.sheafPushforwardContinuousIso e (Type (u + 1)) J K).symm
  Functor.isoWhiskerRight (Adjunction.rightAdjointUniq adjW adjV')
      (v.sheafPushforwardContinuous (Type (u + 1)) J K) ≪≫
    asIso adjV.counit

/-- **Stacks 0DF3.** The inverse image of the small-to-big morphism `i_X` is the direct image
of the big-to-small morphism of sites: both restrict a big étale sheaf to the objects étale
over `X`. -/
@[stacks 0DF3 "the inverse-image identification"]
noncomputable def smallToBig_inverseImageIso_bigToSmall_pushforward :
    (smallToBigEtaleMorphism T (𝟙 X)).inverseImage ≅
      (bigToSmallEtaleMorphism T X).pushforward :=
  letI J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  letI K := T.bigEtaleTopology X
  letI : (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).IsContinuous J K :=
    (inclusion_isMorphismOfSites T X).isContinuous
  Functor.sheafPushforwardContinuousIso (inclusionFunctorIdIso T X) (Type (u + 1)) J K

add_to_stacks 0DF3 "the section rule for inverse image"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj

end AlgebraicGeometry.BigEtaleSpaceSite

end
