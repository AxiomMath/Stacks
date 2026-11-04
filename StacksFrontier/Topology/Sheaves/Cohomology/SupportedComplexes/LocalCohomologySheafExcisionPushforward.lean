module

public import
    StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision

/-!
# Underived base change for the direct image from a closed subset

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be an **open immersion** of ringed spaces, let `Z ⊆ X` be a
subset and let `Z' = f^{-1}(Z)`. Write `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` and
`i' : (Z', 𝒪_{X'}|_{Z'}) ⟶ (X', 𝒪_{X'})` for the two inclusions and
`f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` for the restriction of `f`, so that

```
(Z', 𝒪_{X'}|_{Z'}) --i'--> (X', 𝒪_{X'})
      |                          |
   f|_{Z'}                       f
      v                          v
(Z, 𝒪_X|_Z)  ------i----> (X, 𝒪_X)
```

is Cartesian by `isPullback_closedSubsetRestriction`. For sheaves of modules, and with no
derived categories involved, there is a natural isomorphism

`i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*`,

that is `f^*(i_*ℳ) ≅ i'_*(ℳ|_{Z'})`, naturally in the `𝒪_X|_Z`-module `ℳ`. For `Z` and `Z'`
closed and every degree `n` there is a natural isomorphism

`(ℋ ⁿ_Z ⋙ i_*) ⋙ f^* ≅ f^* ⋙ (ℋ ⁿ_{Z'} ⋙ i'_*)`,

excision for `ℋ ⁿ_Z` with both sides sheaves of modules on the ambient space.

## Main results

* `closedSubsetPushforwardPullbackNatIso`: **the underived base change
  `i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*`** for the Cartesian square of the restriction of an open
  immersion to a subset `Z`, which need not be closed.
* `closedSubsetPushforwardPullbackNatIso_hom`: that isomorphism is the canonical base-change
  map of the square.
* `localCohomologySheafPushforwardPullbackNatIso`: **excision for the local cohomology sheaves
  with the direct image from the closed subset folded in**, in every degree.

## References

* [Stacks Project, Lemma 20.32.4 (Tag 08FE)](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.SupportedComplexes

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### The underived base change for the direct image from the closed subset -/

/-- **The underived base change `i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*`** for the Cartesian square of
the restriction of an open immersion `f : X' ⟶ X` to a subset `Z ⊆ X` with preimage
`Z' = f^{-1}(Z)`: for an `𝒪_X|_Z`-module `ℳ`,

`f^*(i_*ℳ) ≅ i'_*(ℳ|_{Z'})`,

naturally in `ℳ`. The subset `Z` need not be closed. -/
def closedSubsetPushforwardPullbackNatIso :
    modulePushforward (closedSubsetInclusion X Z) ⋙ modulePullback f ≅
      modulePullback (closedSubsetRestriction f Z) ⋙
        modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)) :=
  haveI := pushforwardRestrictMap_isIso (closedSubsetInclusion X Z)
    (closedSubsetRestriction f Z) f (closedSubsetInclusion X' (closedSubsetPreimage f Z))
    (isPullback_closedSubsetRestriction f Z)
  asIso (pushforwardRestrictMap (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
    (closedSubsetInclusion X' (closedSubsetPreimage f Z))
    (isPullback_closedSubsetRestriction f Z).w)

/-- The forward direction of `closedSubsetPushforwardPullbackNatIso` is the canonical base-change
map `pushforwardRestrictMap` of the square: the adjoint transpose under `f^* ⊣ f_*` of `i_*`
applied to the unit of `(f|_{Z'})^* ⊣ (f|_{Z'})_*`, followed by the identification
`i_*(f|_{Z'})_* ≅ f_* i'_*`. -/
theorem closedSubsetPushforwardPullbackNatIso_hom :
    (closedSubsetPushforwardPullbackNatIso f Z).hom =
      pushforwardRestrictMap (closedSubsetInclusion X Z) (closedSubsetRestriction f Z) f
        (closedSubsetInclusion X' (closedSubsetPreimage f Z))
        (isPullback_closedSubsetRestriction f Z).w :=
  rfl

/-! ### Excision with the direct image folded in -/

/-- **Excision for the local cohomology sheaves with the direct image from the closed subset
folded in.** For an open immersion of ringed spaces `f : X' ⟶ X`, a closed `Z ⊆ X`,
`Z' = f^{-1}(Z)` and a degree `n`,

`(ℋ ⁿ_Z(ℱ) pushed to X)|_{X'} ≅ ℋ ⁿ_{Z'}(f^*ℱ) pushed to X'`,

naturally in the `𝒪_X`-module `ℱ`; that is, the functor `ℋ ⁿ_Z ⋙ i_*` commutes with pullback
along `f`, both sides being sheaves of modules on the ambient spaces. -/
def localCohomologySheafPushforwardPullbackNatIso (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z)) (n : ℕ) :
    (localCohomologySheafFunctor X Z hZ n ⋙
          modulePushforward (closedSubsetInclusion X Z)) ⋙ modulePullback f ≅
      modulePullback f ⋙
        (localCohomologySheafFunctor X' (closedSubsetPreimage f Z) hZ' n ⋙
          modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) :=
  let L := localCohomologySheafFunctor X Z hZ n
  let L' := localCohomologySheafFunctor X' (closedSubsetPreimage f Z) hZ' n
  let P := modulePushforward (closedSubsetInclusion X Z)
  let P' := modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))
  let F := modulePullback f
  let G := modulePullback (closedSubsetRestriction f Z)
  let θ : P ⋙ F ≅ G ⋙ P' := closedSubsetPushforwardPullbackNatIso f Z
  let ε : L ⋙ G ≅ F ⋙ L' := localCohomologySheafPullbackNatIso f Z hZ hZ' n
  Functor.associator L P F ≪≫
    Functor.isoWhiskerLeft L θ ≪≫
    (Functor.associator L G P').symm ≪≫
    Functor.isoWhiskerRight ε P' ≪≫
    Functor.associator F L' P'

end Stacks.Cohomology.SupportedComplexes

end
