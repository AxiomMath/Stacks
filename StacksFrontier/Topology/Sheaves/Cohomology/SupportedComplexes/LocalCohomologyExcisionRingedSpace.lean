module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetRestrictionOpenImmersion
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsOpenImmersion

/-!
# Degreewise excision for sections with support, at ringed-space level

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an open immersion of ringed spaces, let `Z ⊆ X` be closed
and let `Z' = f^{-1}(Z)`.  The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on
`Z` of [Stacks, Tag 0G6N] commutes with pullback along `f`:

`H_Z(ℱ)|_{Z'} ≅ H_{Z'}(f^*ℱ)`,

naturally in the `𝒪_X`-module `ℱ`.  Here `(-)|_{Z'}` is pullback along the restriction
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` of `f`, which is itself an open immersion by
`isOpenImmersion_closedSubsetRestriction`.

## Main definitions

* `closedSubsetPullbackPushforwardIso`: `i^* i_* ≅ 𝟭` for the inclusion `i` of a closed subset,
  the counit of `i^* ⊣ i_*` ([Stacks, Tag 08KS]).
* `closedSubsetRestrictionPullbackSquareIso`: `i^* ⋙ (f|_{Z'})^* ≅ f^* ⋙ (i')^*`, pullback read
  along the two sides of the commuting square of the restriction ([Stacks, Tag 0097] part (2)),
  for every morphism of ringed spaces.
* `supportedSectionsOnClosedPullbackNatIso`: degreewise excision for `H_Z`,
  `H_Z(ℱ)|_{Z'} ≅ H_{Z'}(f^*ℱ)`.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Lemma 17.6.3 (Tag 0097)](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

/-! ### The counit of `i^* ⊣ i_*` for a closed subset -/

/-- The isomorphism `i^* i_* ≅ 𝟭` for the inclusion `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` of a closed
subset, given by the counit of the adjunction `i^* ⊣ i_*` of [Stacks, Tag 0096]. -/
def closedSubsetPullbackPushforwardIso (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    modulePushforward (closedSubsetInclusion X Z) ⋙
        modulePullback (closedSubsetInclusion X Z) ≅
      𝟭 (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))) :=
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).full
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  asIso (modulePullbackPushforwardAdjunction (closedSubsetInclusion X Z)).counit

/-! ### Pullback along the square of the restriction -/

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) (Z : Set X.carrier)

/-- Pullback read along the two sides of the square `f|_{Z'} ≫ i = i' ≫ f` of the restriction,
`i^* ⋙ (f|_{Z'})^* ≅ f^* ⋙ (i')^*`, by pseudofunctoriality of pullback
([Stacks, Tag 0097] part (2)). -/
def closedSubsetRestrictionPullbackSquareIso :
    modulePullback (closedSubsetInclusion X Z) ⋙
        modulePullback (closedSubsetRestriction f Z) ≅
      modulePullback f ⋙
        modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z)) :=
  (pullbackCompIso (closedSubsetRestriction f Z) (closedSubsetInclusion X Z)).symm ≪≫
    eqToIso (congrArg (fun k : closedSubsetRingedSpace X' (closedSubsetPreimage f Z) ⟶ X =>
        modulePullback k)
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)) ≪≫
    pullbackCompIso (closedSubsetInclusion X' (closedSubsetPreimage f Z)) f

/-! ### Degreewise excision -/

/-- Degreewise excision for sections with support: for an open immersion of ringed spaces
`f : X' ⟶ X`, a closed `Z ⊆ X` and `Z' = f^{-1}(Z)`,

`H_Z(ℱ)|_{Z'} ≅ H_{Z'}(f^*ℱ)`,

naturally in the `𝒪_X`-module `ℱ`; that is, the functor `H_Z` of [Stacks, Tag 0G6N] commutes
with pullback along `f`, the left-hand side being pullback along the restriction
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)`. -/
def supportedSectionsOnClosedPullbackNatIso [SheafedSpace.IsOpenImmersion f] (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z)) :
    supportedSectionsOnClosedFunctor X Z hZ ⋙ modulePullback (closedSubsetRestriction f Z) ≅
      modulePullback f ⋙
        supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ' :=
  let A := supportedSectionsOnClosedFunctor X Z hZ
  let A' := supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ'
  let P := modulePushforward (closedSubsetInclusion X Z)
  let P' := modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))
  let Q := modulePullback (closedSubsetInclusion X Z)
  let Q' := modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))
  let S := supportedSectionsFunctor X Z
  let S' := supportedSectionsFunctor X' (closedSubsetPreimage f Z)
  let F := modulePullback f
  let G := modulePullback (closedSubsetRestriction f Z)
  let ρ : A ⋙ P ≅ S := supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ
  let ρ' : A' ⋙ P' ≅ S' :=
    supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
      (closedSubsetPreimage f Z) hZ'
  let κ : P ⋙ Q ≅ 𝟭 _ := closedSubsetPullbackPushforwardIso X Z hZ
  let κ' : P' ⋙ Q' ≅ 𝟭 _ :=
    closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ'
  let β : Q ⋙ G ≅ F ⋙ Q' := closedSubsetRestrictionPullbackSquareIso f Z
  let α : S ⋙ F ≅ F ⋙ S' := supportedSectionsPullbackNatIso f Z
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft A κ ≪≫ A.rightUnitor).symm G ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight ρ Q) G ≪≫
    Functor.isoWhiskerLeft S β ≪≫
    Functor.isoWhiskerRight α Q' ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight ρ'.symm Q') ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft A' κ' ≪≫ A'.rightUnitor)

end Stacks.Cohomology.SupportedComplexes

end
