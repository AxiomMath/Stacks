module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change for a derived tensor product and a derived internal hom

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes, `K` an object of `D(𝒪_X)`, `K'` an object of `D(𝒪_{X'})`
and `φ : L(g')^*K ⟶ K'`.  For an object `E` of `D(𝒪_X)` the datum `(K, K', φ)` propagates to
the two comparison maps

`L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'`  and
`L(g')^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(L(g')^*E, K')`,

each the comparison for the derived pullback itself followed by the map induced by `φ`.  This
module computes the pointwise base-change map of Stacks 0DJ7 on each of them: it is the
base-change map of that first factor, followed by the stalkwise cohomology of the map induced
by `φ`.  So when `φ` is invertible the pointwise condition of Stacks 0DJ8 (1) holds for a
comparison map as soon as it holds for the derived pullback alone, a statement in which neither
`K'` nor `φ` occurs.

## Main results

* `AlgebraicGeometry.baseChangeCohomologyMap_baseChangeTensorComparison` and
  `AlgebraicGeometry.baseChangeCohomologyMap_baseChangeSheafHomComparison`: the two
  factorizations of the base-change map.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison` and
  `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison`: the
  invertibility of the pointwise base-change map transports along an invertible `φ`, from the
  comparison for the derived pullback to the comparison for `K'`.

## Implementation notes

Both factorizations are instances of `AlgebraicGeometry.baseChangeCohomologyMap_comp`, the
naturality of the map of Stacks 0DJ7 in the target of the given morphism: the two comparison
maps are by construction a composite whose first factor already has the derived pullback of
`E ⊗^L_{𝒪_X} K`, respectively of `R𝓗om_{𝒪_X}(E, K)`, as its source, so only the target varies.

Nothing here asks `E` to be perfect or pseudo-coherent, and nothing asks the square to be
cartesian: the two equations below are naturality statements, true for any commutative square
and any `E`.  For a cartesian square, the conclusion for an arbitrary `φ` satisfying condition (1)
of Stacks 0DJ8 is Stacks 0DJA (1),
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedBaseChangeComparison
  (baseChangeTensorComparison baseChangeSheafHomComparison)
open Stacks.Cohomology.DerivedInternalHomPullback (derivedPullbackSheafHomMap)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackTensorIso)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.SheafOfModules (derivedSheafHom)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g) (E K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
  (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')

/-- **The base-change map on the comparison for a derived tensor product.** The map of
Stacks 0DJ7 at `L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'` is the map of Stacks 0DJ7 at
the monoidality isomorphism of Tag 079U, followed by the stalkwise cohomology of
`L(g')^*E ⊗^L_{𝒪_{X'}} φ`.

This is the factorization the proof of Stacks 0DJA (1) computes with. Conclusion (1) itself is
`AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeTensorComparison_of_isPullback`. -/
theorem baseChangeCohomologyMap_baseChangeTensorComparison (x' : X') (n : ℤ) :
    baseChangeCohomologyMap f g f' g' w
        (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
        (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj K')
        (baseChangeTensorComparison g'.toLRSHom.toShHom E K K' φ) x' n =
      baseChangeCohomologyMap f g f' g' w
          (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
          (((derivedTensorProductFunctor X'.sheaf).obj
            ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
            ((derivedPullback g'.toLRSHom.toShHom).obj K))
          ((derivedPullbackTensorIso g'.toLRSHom.toShHom).hom.app (E, K)) x' n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X'.presheaf.stalk x')) n).map
          ((derivedStalkFunctor x').map
            (((derivedTensorProductFunctor X'.sheaf).obj
              ((derivedPullback g'.toLRSHom.toShHom).obj E)).map φ)) := by
  dsimp only [baseChangeTensorComparison]
  exact baseChangeCohomologyMap_comp f g f' g' w _ _ _ _ _ x' n

/-- **The base-change map on the comparison for a derived internal hom.** The map of
Stacks 0DJ7 at `L(g')^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(L(g')^*E, K')` is the map of
Stacks 0DJ7 at the map of Tag 08I3, followed by the stalkwise cohomology of
`R𝓗om_{𝒪_{X'}}(L(g')^*E, φ)`.

This is the factorization through `R𝓗om(L(g')^*E, L(g')^*K)` that the proof of Stacks 0DJA (2)
and (3) performs. Conclusions (2) and (3) themselves are
`isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect` and
`isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_hasTorAmplitude`. -/
theorem baseChangeCohomologyMap_baseChangeSheafHomComparison (x' : X') (n : ℤ) :
    baseChangeCohomologyMap f g f' g' w
        (((derivedSheafHom X.sheaf).obj (op E)).obj K)
        (((derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
        (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ) x' n =
      baseChangeCohomologyMap f g f' g' w
          (((derivedSheafHom X.sheaf).obj (op E)).obj K)
          (((derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj
            ((derivedPullback g'.toLRSHom.toShHom).obj K))
          (derivedPullbackSheafHomMap g'.toLRSHom.toShHom E K) x' n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X'.presheaf.stalk x')) n).map
          ((derivedStalkFunctor x').map
            (((derivedSheafHom X'.sheaf).obj
              (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).map φ)) := by
  dsimp only [baseChangeSheafHomComparison]
  exact baseChangeCohomologyMap_comp f g f' g' w _ _ _ _ _ x' n

/-- **Transport of the pointwise condition along an invertible `φ`, for a derived tensor
product.** For an invertible `φ` the pointwise base-change map of Stacks 0DJ7 at
`L(g')^*(E ⊗^L_{𝒪_X} K) ⟶ L(g')^*E ⊗^L_{𝒪_{X'}} K'` is invertible exactly when the one at the
monoidality isomorphism of Tag 079U is, the two differing by an isomorphism; the implication
from the latter to the former is the statement below. Conclusion (1) of Stacks 0DJA has a
different hypothesis, the pointwise condition for `(K, K', φ)` itself. -/
theorem isIso_baseChangeCohomologyMap_baseChangeTensorComparison (hφ : IsIso φ)
    (hE : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj K))
      ((derivedPullbackTensorIso g'.toLRSHom.toShHom).hom.app (E, K)) x' n)) :
    ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w
      (((derivedTensorProductFunctor X.sheaf).obj E).obj K)
      (((derivedTensorProductFunctor X'.sheaf).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj K')
      (baseChangeTensorComparison g'.toLRSHom.toShHom E K K' φ) x' n) := by
  intro x' n
  rw [baseChangeCohomologyMap_baseChangeTensorComparison f g f' g' w E K K' φ x' n]
  exact IsIso.comp_isIso' (hE x' n)
    (Functor.isIso_map_of_isIso _ _
      (Functor.isIso_map_of_isIso _ _ (Functor.isIso_map_of_isIso _ _ hφ)))

/-- **Transport of the pointwise condition along an invertible `φ`, for a derived internal
hom.** For an invertible `φ` the pointwise base-change map of Stacks 0DJ7 at
`L(g')^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(L(g')^*E, K')` is invertible exactly when the one at
the map of Tag 08I3 is, the two differing by an isomorphism; the implication from the latter to
the former is the statement below. Conclusions (2) and (3) of Stacks 0DJA have a different
hypothesis, the pointwise condition for `(K, K', φ)` itself. -/
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison (hφ : IsIso φ)
    (hE : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w
      (((derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj
        ((derivedPullback g'.toLRSHom.toShHom).obj K))
      (derivedPullbackSheafHomMap g'.toLRSHom.toShHom E K) x' n)) :
    ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w
      (((derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ) x' n) := by
  intro x' n
  rw [baseChangeCohomologyMap_baseChangeSheafHomComparison f g f' g' w E K K' φ x' n]
  exact IsIso.comp_isIso' (hE x' n)
    (Functor.isIso_map_of_isIso _ _
      (Functor.isIso_map_of_isIso _ _ (Functor.isIso_map_of_isIso _ _ hφ)))

end AlgebraicGeometry

end
