module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The commutative-ring counit of a closed immersion is invertible

For a closed immersion `i : Z ⟶ X` of algebraic spaces, Stacks 04E5, part (1) says that the
direct image of sheaves of *sets* along the morphism of small étale topoi is fully faithful, so
the counit `i⁻¹i_*G ⟶ G` is an isomorphism
(`AlgebraicGeometry.Space.smallEtalePullbackPushforwardCounitIso`).  This file carries that
across to sheaves of *commutative rings*, which is the form a computation with derivations needs:
the derivation API is stated over presheaves of `CommRingCat`.

## Main results

* `AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion`: the counit of
  `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` at a closed immersion is an
  isomorphism on every sheaf of commutative rings.
* `AlgebraicGeometry.Space.commRingCounitIso`: that isomorphism, `i⁻¹i_*𝒜 ≅ 𝒜`.  On underlying
  sheaves of sets it is the counit of `i⁻¹ ⊣ i_*`, which is
  `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forget` and is not restated
  here.

## Implementation notes

The argument is the one
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor_isEquivalence` runs on the unit and
the counit together: the counit is an isomorphism because it is one on underlying sheaves of
sets, by `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forget`, and
`CategoryTheory.sheafCompose _ (forget CommRingCat)` reflects isomorphisms.  That lemma is *not*
reused here, because it asks for the direct image to be an equivalence: along a closed immersion
the direct image is fully faithful and not essentially surjective, so only the counit half is
available and only the counit half is wanted.

The set-level input is taken through
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion` rather than
through `AlgebraicGeometry.Space.smallEtalePullbackPushforwardCounitIso` itself, because what is
needed is invertibility of the counit *at one object* and the latter packages invertibility of
the whole natural transformation; the two `have`s below are the ones that definition is built
from.

The morphism of topoi is `AlgebraicGeometry.Space.smallToposMorphismTypeU`, which is
`(smallEtaleRingedToposHom B S hS i).toToposHom` by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_toToposHom`; so this is the counit of the
adjunction the structure map of `i` is adjunct across, and not that of some other morphism of
topoi.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X : AlgebraicSpaces B S hS}

/-- **The commutative-ring counit of a closed immersion is invertible.**  For a closed immersion
`i : Z ⟶ X` of algebraic spaces and a sheaf of commutative rings `𝒜` on the small étale site of
`Z`, the counit `i⁻¹i_*𝒜 ⟶ 𝒜` of
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction` is an isomorphism.

It is one on underlying sheaves of sets by Stacks 04E5, part (1), and
`CategoryTheory.sheafCompose _ (forget CommRingCat)` reflects isomorphisms. -/
theorem isIso_commRingCounit_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (A : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    IsIso ((commRingImageAdjunction (smallToposMorphismTypeU B S hS i)).counit.app A) := by
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi).full
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi).faithful
  have ht : IsIso ((smallToposMorphismTypeU B S hS i).adj.counit.app
      ((sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).obj A)) :=
    inferInstance
  have hm : IsIso ((sheafCompose (SmallEtale.topology B S hS Z.1)
      (forget CommRingCat.{u})).map
        ((commRingImageAdjunction (smallToposMorphismTypeU B S hS i)).counit.app A)) :=
    (commRingImageAdjunction_counit_forget (smallToposMorphismTypeU B S hS i) A).symm ▸ ht
  exact isIso_of_reflects_iso
    ((commRingImageAdjunction (smallToposMorphismTypeU B S hS i)).counit.app A)
    (sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u}))

/-- **`i⁻¹i_*𝒜 ≅ 𝒜` for a closed immersion**, as sheaves of commutative rings on the small étale
site of `Z`: the counit of `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, which is
invertible by `AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion`. -/
noncomputable def commRingCounitIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (A : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (inverseImageCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
        ((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj A) ≅ A :=
  have := isIso_commRingCounit_of_isClosedImmersion B S hS i hi A
  asIso ((commRingImageAdjunction (smallToposMorphismTypeU B S hS i)).counit.app A)

end AlgebraicGeometry.Space

end
