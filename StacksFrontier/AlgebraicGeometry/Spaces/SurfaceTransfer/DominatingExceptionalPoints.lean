module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SingularPointNeighborhoods

/-!
# The points over which a proper birational morphism of surfaces is not an isomorphism

Let `X` be a decent algebraic space over a scheme `S` of dimension at most two with locally
Noetherian étale charts, and let `U ⊆ X` be an open subspace containing every point whose local
ring has dimension at most one — in the proof of Stacks 0BHM, the open over which a proper
birational morphism of normal spaces is an isomorphism, which contains those points by
Stacks 0BBQ. Then the complement `T` of `U` is a finite set of closed points: "there is a finite
set of closed points `T ⊆ |X|` such that `f` is an isomorphism over `X ∖ T`".

## Main results

* `AlgebraicGeometry.Space.isClosed_singleton_of_one_lt_localRingDimension`: a point of local
  dimension at least two is closed.
* `AlgebraicGeometry.Space.finite_and_isClosed_of_compl_range`: the statement above.
* `AlgebraicGeometry.Space.isIso_pullback_snd_of_range_subset`: an isomorphism over an open
  subspace is one over every smaller open subspace.

## References

* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
* [Stacks Project, Tag 0BBQ](https://stacks.math.columbia.edu/tag/0BBQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A point of local dimension at least two on a space of dimension at most two is closed**: a
proper specialization of it lifts to an étale chart (Stacks 03K2), where the point above it has
a local ring of dimension at least two in a scheme of dimension at most two, so has none. -/
theorem isClosed_singleton_of_one_lt_localRingDimension {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hXdim : dimension B S hS X hX ≤ 2) (y : points B S hS X)
    (hy : 1 < localRingDimension B S hS y) : IsClosed ({y} : Set (points B S hS X)) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hyz : y ⤳ z := specializes_iff_mem_closure.mpr hz
  obtain ⟨U, a, has, hae⟩ := hX.exists_atlas
  obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp has z
  have hfin := hasFiniteChartFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers B S hS X
    ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).mp hdec)
  obtain ⟨w', hw'w, hw'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX hyz
    (fun V hV ψ hψ => hfin y V hV ψ hψ) U a hae w hw
  have h2 : 2 ≤ ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
      (pointsToScheme B S hS U w')) := by
    have hc := chartPoint_pointsToScheme B S hS U a w'
    rw [hw'] at hc
    rw [← localRingDimension_eq_of_chartPoint B S hS hX U a hae _ y hc]
    have h22 : (2 : ℕ∞) ≤ localRingDimension B S hS y := by
      simpa [one_add_one_eq_two] using Order.add_one_le_of_lt hy
    exact (WithBot.coe_le_coe.mpr h22 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)
  have hclosed := AlgebraicGeometry.isClosed_singleton_of_two_le_ringKrullDim_stalk _
    ((topologicalKrullDim_le_dimension_of_etale B S hS hX U a hae).trans hXdim) _ h2
  have hsp : pointsToScheme B S hS U w' ⤳ pointsToScheme B S hS U w :=
    hw'w.map (schemePointsHomeomorph B S hS U).continuous
  have heq : pointsToScheme B S hS U w = pointsToScheme B S hS U w' :=
    hclosed.closure_subset (specializes_iff_mem_closure.mp hsp)
  rw [← hw, ← hw', injective_pointsToScheme B S hS U heq]
  rfl

/-- **The complement of an open containing the points of codimension at most one.** In a
decent, quasi-compact algebraic space of dimension at most two with locally Noetherian étale
charts, the complement of an open subspace containing every point of local dimension at most
one is a finite set of closed points. -/
theorem finite_and_isClosed_of_compl_range {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXdim : dimension B S hS X hX ≤ 2) (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (h1 : ∀ x : points B S hS X, localRingDimension B S hS x ≤ 1 →
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ.Finite ∧
      ∀ x ∈ (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ,
        IsClosed ({x} : Set (points B S hS X)) := by
  have hlt : ∀ x ∈ (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ,
      1 < localRingDimension B S hS x := fun x hx => lt_of_not_ge fun h => hx (h1 x h)
  have hopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
    rw [← openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩]
    exact (openSubspacesOrderIso B S hS X hX ⟨U, hU⟩).isOpen
  exact ⟨finite_of_isClosed_of_one_lt_localRingDimension B S hS hX hXqc hXnoeth hXdim _
      hopen.isClosed_compl hlt,
    fun x hx => isClosed_singleton_of_one_lt_localRingDimension hX hdec hXdim x (hlt x hx)⟩

/-- **An isomorphism over an open subspace is one over every smaller open subspace**: the
smaller open factors through the larger one. -/
theorem isIso_pullback_snd_of_range_subset {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (l : Y ⟶ X) {U V : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hiso : IsIso (pullback.snd l U.ι))
    (hsub : Set.range (pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    IsIso (pullback.snd l V.ι) := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hV.1 U hU V.ι).2 hsub
  exact isIso_pullback_snd_of_factor l g hg hiso

end AlgebraicGeometry.Space

end
