module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetRestrictionOpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the comparison map of Tag 0G78

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, let `Z ⊆ X` be closed and let
`Z' = f^{-1}(Z)`. For `K` in `D(𝒪_X)` the canonical map of [Stacks, Tag 0G78] is

`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^* K)`,

namely `Stacks.Cohomology.SupportedComplexes.supportedPullbackMap`. This file reduces its
invertibility to one invertibility statement about the adjunction map of [Stacks, Tag 0A3B].

## Main results

* `Stacks.Cohomology.SupportedComplexes.supportedPullbackMap_eq_unit_comp`: the canonical map,
  written out as the unit of the adjunction `i'_* ⊣ R𝓗_{Z'}` followed by `R𝓗_{Z'}` of the
  displayed composite. This is the definition of the map unfolded through
  `CategoryTheory.Adjunction.homEquiv_unit`, and it is what makes its invertibility readable off
  the factors.
* `Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_isIso_map_counit`: **the
  reduction.** The canonical map is invertible as soon as

  `R𝓗_{Z'}(Lf^*(ε_K))` is invertible, where `ε_K : i_* R𝓗_Z(K) ⟶ K`

  is the adjunction map of [Stacks, Tag 0A3B]. Three of the four factors of the displayed
  composite are invertible for free: the unit of `i'_* ⊣ R𝓗_{Z'}` by [Stacks, Tag 0A3B] part
  (2), the base-change transformation by `isIso_supportedPullbackBaseChangeMap`, and the two
  comparisons of [Stacks, Tag 0E2K] because they are isomorphisms of functors.
* `Stacks.Cohomology.SupportedComplexes.isIso_derivedSupportedSectionsOnClosed_map_counit`: the
  same statement one space down, which is where the reduction is *not* circular: `R𝓗_Z(ε_K)` is
  invertible for every morphism of ringed spaces and every `K`, by the triangle identity, since
  the unit of `i_* ⊣ R𝓗_Z` is invertible. The content of the remaining hypothesis is therefore
  exactly that `R𝓗_{Z'} ∘ Lf^*` sees `ε_K` the way `R𝓗_Z` does.
* `Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_natIso`: the reduction in
  the form a comparison of functors discharges it. A natural isomorphism
  `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}` — *any* one, with no compatibility with the canonical
  map asked for — makes the canonical map invertible, by naturality at `ε_K` together with the
  previous item.
* `Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_cohomologySupportedOn`:
  **the case the library already settles.** When every cohomology sheaf of `K` is supported on
  `Z`, the canonical map of [Stacks, Tag 0G78] *is* an isomorphism: the adjunction map `ε_K` is
  then invertible by [Stacks, Tag 0AEF] part (2). No hypothesis on `f` is used at all, so this
  holds for every morphism of ringed spaces.

## Implementation notes

**Why no identification of the comparison is needed.** The last item is the point of the file.
Invertibility of the canonical map of Tag 0G78 would normally be proved by identifying it with
some independently constructed isomorphism, which for a map pinned down only by an adjunction
equation (`supportedPullbackMap_unique`) is a substantial computation. It is not needed:
`R𝓗_Z(ε_K)` is invertible unconditionally, so a natural isomorphism between the two composite
functors transports that invertibility to `R𝓗_{Z'}(Lf^*(ε_K))`, and the reduction then gives the
canonical map. So a successor may build the comparison of functors by any route — the
uniqueness of right derived functors, say — without ever comparing it to Tag 0G78's map.

That comparison *is* now identified with Tag 0G78's map, by
`Stacks.Cohomology.SupportedComplexes`
`.supportedPullbackNatTrans_eq_derivedSupportedSectionsOnClosedPullbackNatIso`
(`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedPullbackComparison.lean`),
which is a theorem about the comparison built downstream and not an input to anything here: the
reduction below still needs no identification, which is why it, and not that theorem, is what
`isIso_supportedPullbackMap_of_isOpenImmersion` runs on.

**What is not proved here.** No natural isomorphism `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}` is
constructed in this file, so apart from the supported case this file does *not* conclude that
the map of Tag 0G78 is an isomorphism. For an **open immersion** `f` that isomorphism is
supplied downstream by
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso`, and the
canonical map of Tag 0G78 is then unconditionally invertible by
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackMap_of_isOpenImmersion`. For a
general morphism of ringed spaces nothing beyond the supported case below is known here.

The route taken downstream is this. Both composites are right derived functors of isomorphic
degreewise functors, so the uniqueness of right derived functors supplies the comparison:

* `R𝓗_Z ⋙ L(f|_{Z'})^*` derives `H_Z ⋙ (f|_{Z'})^*`, because `L(f|_{Z'})^*` is the functor
  induced by the exact `modulePullback (f|_{Z'})` — `f|_{Z'}` is an open immersion by
  `isOpenImmersion_closedSubsetRestriction`, so
  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` applies — and
  post-composing a right derived functor with any functor derives the composite.
* `Lf^* ⋙ R𝓗_{Z'}` derives `f^* ⋙ H_{Z'}`, by the unbounded form of [Stacks, Tag 015Z]:
  `modulePullback f` is exact and carries K-injective complexes to K-injective complexes.
* the degreewise comparison `H_Z ⋙ (f|_{Z'})^* ≅ f^* ⋙ H_{Z'}`, which is excision for sections
  supported on a closed subset along an open immersion of ringed spaces, in degree zero. That
  is `Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso`, and it is
  where the mathematics is.

The obstruction to the third piece used to be that `H_Z` takes values on the inverse-image
ringed space `closedSubsetRingedSpace X Z`, for which there was no open-immersion theory. There
is now: `isOpenImmersion_closedSubsetRestriction`. Even so the comparison is proved by pulling
back rather than by pushing forward, which is what avoids the base-change isomorphism
`i'_*(f|_{Z'})^* ≅ f^* i_*`: the counit `i^* i_* ≅ 𝟭` is invertible because `i_*` is fully
faithful, which replaces `H_Z` by the subsheaf-valued `supportedSectionsFunctor`, for which the
sectionwise engine
`Stacks.SheafOfModules.SupportedSections.mem_supportedSectionsSheafι_range_iff` applies on the
nose.

**Where the base-change transformation comes in.** The canonical map of Tag 0G78 is built in
`Stacks.Cohomology.SupportedComplexes.supportedPullbackMap` from the invertibility of the
base-change transformation of [Stacks, Tag 08HY], which for a closed `Z` is
`isIso_supportedPullbackBaseChangeMap` and for an open immersion and an arbitrary `Z` is
`isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`. It is therefore not a hypothesis of
anything below.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.2 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The adjunction map seen by `R𝓗_Z` -/

/-- **`R𝓗_Z` inverts the adjunction map `ε_K : i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0A3B].** This
holds for every ringed space, every closed subset and every `K`: the unit of the adjunction
`i_* ⊣ R𝓗_Z` is invertible by [Stacks, Tag 0A3B] part (2), and the triangle identity
`η_{R𝓗_Z(K)} ≫ R𝓗_Z(ε_K) = 𝟙` then exhibits `R𝓗_Z(ε_K)` as its inverse. -/
theorem isIso_derivedSupportedSectionsOnClosed_map_counit (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    IsIso ((derivedSupportedSectionsOnClosed X Z hZ).map
      ((derivedPushforwardAdjunction X Z hZ).counit.app K)) := by
  let := pushforward_preservesFiniteLimits X Z
  let := pushforward_preservesFiniteColimits X Z hZ
  have htri := (derivedPushforwardAdjunction X Z hZ).right_triangle_components (Y := K)
  have : IsIso ((derivedPushforwardAdjunction X Z hZ).unit.app
      ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) := inferInstance
  rw [← IsIso.inv_eq_of_hom_inv_id htri]
  infer_instance

/-! ### The canonical map of Tag 0G78, factor by factor -/

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) (Z : Set X.carrier) (hZ : IsClosed Z)
  [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]

/-- **The canonical map of [Stacks, Tag 0G78] written out.** It is the adjoint transpose of
`supportedPullbackMateMap`, so by `CategoryTheory.Adjunction.homEquiv_unit` it is the unit of the
adjunction `i'_* ⊣ R𝓗_{Z'}` of [Stacks, Tag 0A3B] followed by `R𝓗_{Z'}` applied to that
composite. -/
theorem supportedPullbackMap_eq_unit_comp (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    supportedPullbackMap f Z hZ hZ' K =
      (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ').unit.app
          ((derivedPullback (closedSubsetRestriction f Z)).obj
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          (supportedPullbackMateMap f Z hZ K) :=
  Adjunction.homEquiv_unit (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z) hZ') _ _ _

/-- **The reduction.** The canonical map of [Stacks, Tag 0G78] is an isomorphism as soon as
`R𝓗_{Z'}` inverts the derived pullback along `f` of the adjunction map
`ε_K : i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0A3B].

The other three factors of the displayed composite are invertible with no further hypothesis:
the unit of `i'_* ⊣ R𝓗_{Z'}` by [Stacks, Tag 0A3B] part (2), the base-change transformation by
`isIso_supportedPullbackBaseChangeMap`, and the two comparisons of [Stacks, Tag 0E2K] because
they are components of isomorphisms of functors. -/
theorem isIso_supportedPullbackMap_of_isIso_map_counit
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (h : IsIso ((derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
      ((derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K)))) :
    IsIso (supportedPullbackMap f Z hZ hZ' K) := by
  have := h
  have := isIso_supportedPullbackBaseChangeMap f Z hZ
    ((derivedSupportedSectionsOnClosed X Z hZ).obj K)
  rw [supportedPullbackMap_eq_unit_comp, supportedPullbackMateMap]
  simp only [Functor.map_comp]
  infer_instance

/-- **The reduction in the form a comparison of functors discharges it.** Let

`e : R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}`

be *any* natural isomorphism — nothing is asked about its relation to the canonical map of
[Stacks, Tag 0G78]. Then the canonical map is an isomorphism.

Naturality of `e` at the adjunction map `ε_K : i_* R𝓗_Z(K) ⟶ K` reads

`L(f|_{Z'})^*(R𝓗_Z(ε_K)) ≫ e_K = e_{i_* R𝓗_Z(K)} ≫ R𝓗_{Z'}(Lf^*(ε_K))`,

whose left-hand side is invertible by `isIso_derivedSupportedSectionsOnClosed_map_counit`; so the
hypothesis of `isIso_supportedPullbackMap_of_isIso_map_counit` holds. -/
theorem isIso_supportedPullbackMap_of_natIso
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    (e : derivedSupportedSectionsOnClosed X Z hZ ⋙
        derivedPullback (closedSubsetRestriction f Z) ≅
      derivedPullback f ⋙ derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (supportedPullbackMap f Z hZ hZ' K) := by
  refine isIso_supportedPullbackMap_of_isIso_map_counit f Z hZ hZ' K ?_
  have hleft : IsIso ((derivedSupportedSectionsOnClosed X Z hZ ⋙
      derivedPullback (closedSubsetRestriction f Z)).map
        ((derivedPushforwardAdjunction X Z hZ).counit.app K)) := by
    have := isIso_derivedSupportedSectionsOnClosed_map_counit X Z hZ K
    exact (derivedPullback (closedSubsetRestriction f Z)).map_isIso _
  exact (NatIso.isIso_map_iff e ((derivedPushforwardAdjunction X Z hZ).counit.app K)).mp hleft

/-- **The canonical map of [Stacks, Tag 0G78] is an isomorphism at a complex supported on `Z`.**
If every cohomology sheaf of `K` is supported on `Z` then the adjunction map
`ε_K : i_* R𝓗_Z(K) ⟶ K` is itself an isomorphism, by [Stacks, Tag 0AEF] part (2), so the
hypothesis of `isIso_supportedPullbackMap_of_isIso_map_counit` is immediate.

No hypothesis on `f` is used. This is the special case of the invertibility of Tag 0G78 that
the library's Tag 0AEF already supplies, for an arbitrary morphism of ringed spaces; for an open
immersion and an arbitrary `K` see `isIso_supportedPullbackMap_of_isOpenImmersion`. -/
@[stacks 0G78 "the canonical map is an isomorphism when K has cohomology sheaves supported on \
  Z, for an arbitrary morphism of ringed spaces"]
theorem isIso_supportedPullbackMap_of_cohomologySupportedOn
    (hZ' : IsClosed (closedSubsetPreimage f Z))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K) :
    IsIso (supportedPullbackMap f Z hZ hZ' K) := by
  refine isIso_supportedPullbackMap_of_isIso_map_counit f Z hZ hZ' K ?_
  have := isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ K hK
  exact (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map_isIso
    ((derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K))

end Stacks.Cohomology.SupportedComplexes

end
