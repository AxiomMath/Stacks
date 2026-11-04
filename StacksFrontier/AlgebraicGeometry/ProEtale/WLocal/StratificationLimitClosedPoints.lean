module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitSpecialization
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed points of the limiting stratification scheme

Let `A` be a commutative ring, let `X_w = Spec A_w` be the inverse limit of the finite vanishing
stratifications of `Spec A`, and let `Z ⊆ X_w` be the inverse limit of the finite closed strata.
Then `Z` is exactly the set of closed points of `X_w`, every point of `X_w` specializes to a
unique point of `Z`, and `X_w` is a w-local space.

## Main results

* `AlgebraicGeometry.ProEtale.range_inclusion_eq_closedPoints`: the image of `Z` is the set of
  closed points of `X_w`.
* `AlgebraicGeometry.ProEtale.existsUnique_specializes_closedScheme`: every point of `X_w`
  specializes to exactly one point of `Z`.
* `AlgebraicGeometry.ProEtale.stratificationLimitScheme_wLocal`: `X_w` is w-local.
* `AlgebraicGeometry.ProEtale.range_stratificationLimitInclusion_eq_closedPoints`,
  `AlgebraicGeometry.ProEtale.existsUnique_specializes_stratificationLimitClosedScheme`: the
  first two statements for the canonical limiting data, with no bundle to supply.

## Implementation notes

The first two results hold for an arbitrary bundle of limiting data `L : StratificationLimit A`;
the canonical bundle `stratificationLimit` is one, so the statements about `Z = lim Z_E` itself
are the special cases recorded afterwards.
Uniqueness is recorded as uniqueness of a point of `Z` rather than of its image in `X_w`, which
is the stronger form, and is deduced from uniqueness of the image using that the inclusion of `Z`
is a closed immersion and hence injective.

W-locality is registered as an instance on the canonical limiting scheme, so that later results
about it are available by typeclass inference. Spectrality of `X_w` is automatic, being the
spectrum of a ring; the two remaining conditions are the two results above.

## References

* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-- The limiting closed subscheme `Z` of `X_w` has as its underlying set exactly the closed
points of `X_w`. -/
@[stacks 0975 "closed_points"]
theorem range_inclusion_eq_closedPoints (L : StratificationLimit A) :
    Set.range L.inclusion.base = closedPoints (stratificationLimitScheme (A := A)) := by
  refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · refine mem_closedPoints_iff.mpr
      (closure_eq_iff_isClosed.mp (Set.Subset.antisymm ?_ subset_closure))
    intro y hy
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    obtain ⟨z, hyz⟩ := exists_specializes_to_closedScheme L y
    obtain rfl := eq_of_specializes_to_closedScheme L hx ⟨z, rfl⟩ (specializes_refl x)
      (hxy.trans hyz)
    exact Set.mem_singleton_iff.mpr (hxy.antisymm hyz).eq.symm
  · obtain ⟨z, hxz⟩ := exists_specializes_to_closedScheme L x
    exact ⟨z, Set.mem_singleton_iff.mp
      (hxz.mem_closed (mem_closedPoints_iff.mp hx) (Set.mem_singleton x))⟩

/-- Every point of `X_w` specializes to exactly one point of its limiting closed subscheme
`Z`. -/
@[stacks 0975 "unique_closed_specialization"]
theorem existsUnique_specializes_closedScheme (L : StratificationLimit A)
    (x : stratificationLimitScheme (A := A)) :
    ∃! z : L.closedScheme, x ⤳ L.inclusion.base z := by
  obtain ⟨z, hz⟩ := exists_specializes_to_closedScheme L x
  exact ⟨z, hz, fun z' hz' => L.isClosedImmersion.isClosedEmbedding.injective
    (eq_of_specializes_to_closedScheme L ⟨z', rfl⟩ ⟨z, rfl⟩ hz' hz)⟩

/-- The limiting scheme `X_w` of the finite vanishing stratifications of `Spec A` is w-local. -/
@[stacks 0975 "w_locality"]
instance stratificationLimitScheme_wLocal :
    WLocalSpace (stratificationLimitScheme (A := A)) := by
  have : SpectralSpace (stratificationLimitScheme (A := A)) :=
    inferInstanceAs (SpectralSpace (PrimeSpectrum (stratificationColimitRing (A := A))))
  have hrange := range_inclusion_eq_closedPoints (stratificationLimit (A := A))
  refine ⟨?_, ?_⟩
  · intro x c c' hc hc' hxc hxc'
    refine eq_of_specializes_to_closedScheme (stratificationLimit (A := A)) ?_ ?_ hxc hxc'
    · rw [hrange]
      exact mem_closedPoints_iff.mpr hc
    · rw [hrange]
      exact mem_closedPoints_iff.mpr hc'
  · rw [← hrange]
    exact (stratificationLimit (A := A)).isClosedImmersion.isClosedEmbedding.isClosed_range

/-- **Stacks 0975**, part (3): the limiting closed subscheme `Z` of `X_w` is exactly the set of
closed points of `X_w`. -/
@[stacks 0975 "closed_points"]
theorem range_stratificationLimitInclusion_eq_closedPoints :
    Set.range (stratificationLimitInclusion (A := A)).base =
      closedPoints (stratificationLimitScheme (A := A)) :=
  range_inclusion_eq_closedPoints (stratificationLimit (A := A))

/-- **Stacks 0975**, part (5): every point of `X_w` specializes to exactly one point of the
limiting closed subscheme `Z`. -/
@[stacks 0975 "unique_closed_specialization"]
theorem existsUnique_specializes_stratificationLimitClosedScheme
    (x : stratificationLimitScheme (A := A)) :
    ∃! z : stratificationLimitClosedScheme (A := A),
      x ⤳ (stratificationLimitInclusion (A := A)).base z :=
  existsUnique_specializes_closedScheme (stratificationLimit (A := A)) x

end AlgebraicGeometry.ProEtale

end
