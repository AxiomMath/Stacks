module

public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Saturation of the supported perfect derived category

For a closed subscheme `Z` of a scheme `X`, the subcategory `D_{Z, perf}(O_X)` of perfect
objects of `D(O_X)` whose cohomology sheaves are set-theoretically supported on `Z` is
*saturated*, or *thick*: a direct summand of one of its objects is again one of its objects.
This is the one adjective of [Stacks, Tag 0FDN] that
`StacksFrontier/AlgebraicGeometry/Perfect/KGroups/Basic.lean` leaves open.

## Main results

* `AlgebraicGeometry.isSaturated_supportedPerfect`: the supported perfect objects form a
  saturated subcategory of `D(O_X)`.

## Implementation notes

The condition is a conjunction and each half is saturated for its own reason.

Perfectness is saturated by [Stacks, Tag 08CS], proved unconditionally as
`Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`, which is applied directly.

The support condition is saturated because a direct summand is a retract, cohomology is a
functor and so carries the retraction to the module category, and the support of a retract is
contained in the support of the object it retracts off
(`SheafOfModules.supp_subset_of_retract`). No property of the closed subset is used — not
closedness, not that it is the image of a morphism — so this half holds for the cohomology
support condition attached to an arbitrary subset.

`ObjectProperty.IsSaturated` is a condition on the isomorphism closure of the property; the
supported perfect objects are closed under isomorphisms
(`AlgebraicGeometry.isClosedUnderIsomorphisms_supportedPerfect`), so the closure is the
property itself and `ObjectProperty.isoClosure_eq_self` removes it from both sides.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 05RB](https://stacks.math.columbia.edu/tag/05RB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry

/-- **Perfect complexes supported on a closed subscheme form a saturated subcategory** of
`D(O_X)`: if a binary biproduct is perfect with all its cohomology sheaves supported on `Z`,
then so is each of its two summands.

Together with `AlgebraicGeometry.isClosedUnderIsomorphisms_supportedPerfect` and
`AlgebraicGeometry.isTriangulated_supportedPerfect` this gives all three adjectives the source
attaches to `D_{Z, perf}(O_X)`: strictly full, saturated, triangulated. -/
@[stacks 0FDN "saturation of the supported perfect subcategory -- the adjective `saturated` of \
  the source, which is closure under direct summands (Tag 05RB). The two other adjectives, \
  strict fullness and triangulatedness, and the definition of the subcategory itself, are in \
  `StacksFrontier/AlgebraicGeometry/Perfect/KGroups/Basic.lean`. The multiplication on \
  `K_0(D_{Z, perf}(O_X))` is in `StacksFrontier/AlgebraicGeometry/Perfect/KGroups/Ring.lean` \
  and the absence of a unit in general \
  in `StacksFrontier/AlgebraicGeometry/Perfect/KGroups/NoUnit.lean`"]
instance isSaturated_supportedPerfect {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    ObjectProperty.IsSaturated
      (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
              Set.range i.base) where
  isoClosure_of_biprod_left {K L} _ h := by
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
    refine ⟨(Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod K L h.1).1, fun n => ?_⟩
    refine subset_trans (SheafOfModules.supp_subset_of_retract
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).map biprod.inl)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).map biprod.fst)
      (by rw [← CategoryTheory.Functor.map_comp, biprod.inl_fst,
        CategoryTheory.Functor.map_id])) (h.2 n)
  isoClosure_of_biprod_right {K L} _ h := by
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
    refine ⟨(Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod K L h.1).2, fun n => ?_⟩
    refine subset_trans (SheafOfModules.supp_subset_of_retract
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).map biprod.inr)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).map biprod.snd)
      (by rw [← CategoryTheory.Functor.map_comp, biprod.inr_snd,
        CategoryTheory.Functor.map_id])) (h.2 n)

end AlgebraicGeometry

end
