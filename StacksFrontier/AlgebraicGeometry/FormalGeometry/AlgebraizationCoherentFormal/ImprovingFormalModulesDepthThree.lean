module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSublevel
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwo

/-!
# Improving a coherent formal module to depth three against the distance function

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`.  Running the depth-two improvement of [Stacks, Tag 0EJF] on `U` with
`T = {y ∈ U ∩ Y : δ^Y_Z(y) ≤ 2}` and `T' = {y ∈ U ∩ Y : δ^Y_Z(y) ≤ 1}` produces a system
`(ℱ''ₙ)` with a canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` and
`depth(ℱ''_{n, y}) + δ^Y_Z(y) ≥ 3` at every point `y` of `U ∩ Y`.

The bound is a three-way case split against the distance, and it is the point at which the
geometry of `U` enters: a point of `U ∩ Y` is at distance at least one from `Z`, because it is
not a point of `Z`.  So at distance one the depth-two bound along `T'` gives `2 + 1`, at
distance two the depth-one bound along `T` gives `1 + 2`, and at distance three or more the
distance alone already exceeds the bound.

## Main definitions

* `Stacks.Algebraization.AlgebraizationSituation.distanceToZSublevel`: the locus
  `{y ∈ U ∩ Y : δ^Y_Z(y) ≤ k}` inside `U`, which is `T` for `k = 2` and `T'` for `k = 1`.

## Main results

* `Stacks.Algebraization.AlgebraizationSituation.one_le_distanceToZ`: a point of `U ∩ Y` is at
  distance at least one from `Z`.
* `Stacks.Algebraization.AlgebraizationSituation.stableUnderSpecialization_distanceToZSublevel`:
  each of these loci is stable under specialization, so it is admissible as the subset `T` of
  the depth-two improvement.
* `Stacks.Algebraization.AlgebraizationSituation.three_le_add_distanceToZ`: the three-way case
  split, as a statement about one extended natural number.

## Implementation notes

A point of `U ∩ Y` is given by a point `y` of `U` together with a point `z` of `Y` having the
same image in `X`, as in `Stacks.Algebraization.SatisfiesDepthInequalities`; the distance is
evaluated at `z` and the depth at `y`.  The sublevel loci are accordingly subsets of `U`, cut
out by the existence of such a `z`.

Specialization stability transports along the two immersions: `U ⟶ X` is continuous, the range
of `Y ⟶ X` is closed and hence stable under specialization, and `Y ⟶ X` is an embedding, so a
specialization inside `U` of a point of `U ∩ Y` again lies in `U ∩ Y` and is a specialization
inside `Y`.  There `Stacks.Algebraization.distanceFunction_sublevel_stableUnderSpecialization`
applies.

The depth bounds are taken at the level of `ℕ∞`, which is where both the depth and the distance
live; the infinite values are retained, and the source's inequality holds rather than being
truncated when either is infinite.

The statements below are for an inverse system of coherent `𝒪_U`-modules, which is the shape in
which `StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizationCoherentFormal/ImprovingFormalModulesDepthTwo.lean` carries Tag 0EJF; an object of
`Coh(U, I𝒪_U)` has such an underlying system, so this covers the source's hypothesis on
`(ℱₙ)`.

[Stacks, Tag 0EJG] itself, with all four of its conclusions, is
`Stacks.Algebraization.exists_proIso_coherentAdicSystem_depthThreeImprovedSystem` in
`ImprovingFormalModulesDepthThreeCarrier.lean`; this file supplies the loci `T`, `T'` and the
case split it uses.

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

namespace AlgebraizationSituation

variable (S : AlgebraizationSituation.{u})

/-- The open `U = X ∖ V(𝔞)` of an algebraization situation is a Noetherian scheme: it is an
open subscheme of the Noetherian `X = Spec(A)`, hence locally Noetherian, and its underlying
space is a subspace of a Noetherian space, hence quasi-compact. -/
@[ega "I 10.4.4" "special case"]
public instance isNoetherian_U_toScheme : IsNoetherian S.U.toScheme := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have : CompactSpace S.U :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (S.U : Set S.X))
  exact (isNoetherian_iff S.U.toScheme).2 ⟨inferInstance, inferInstance⟩

/-- The locus `{y ∈ U ∩ Y : δ^Y_Z(y) ≤ k}` of points of `U ∩ Y` at distance at most `k` from
`Z`, as a subset of `U`.  A point of `U ∩ Y` is a point `y` of `U` together with a point `z` of
`Y` having the same image in `X`, and the distance is evaluated at `z`. -/
public def distanceToZSublevel (k : ℕ∞) : Set S.U.toScheme :=
  {y | ∃ z : S.Y, S.U.ι.base y = S.Yι.base z ∧ S.distanceToZ z ≤ k}

public theorem mem_distanceToZSublevel {k : ℕ∞} {y : S.U.toScheme} :
    y ∈ S.distanceToZSublevel k ↔
      ∃ z : S.Y, S.U.ι.base y = S.Yι.base z ∧ S.distanceToZ z ≤ k :=
  Iff.rfl

/-- A point of `U ∩ Y` is at distance at least one from `Z`: it is a point of `U`, so it is not
a point of `Z`, and only the points of `Z` are at distance zero. -/
public theorem one_le_distanceToZ (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) : 1 ≤ S.distanceToZ z := by
  refine Order.one_le_iff_ne_zero.mpr fun hzero => ?_
  have hmem : z ∈ (S.closedSubsetZ : Set S.Y) :=
    (distanceFunction_eq_zero_iff_mem S.Y S.closedSubsetZ z).1 hzero
  have hmemz : ((S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) : Set (S.A ⧸ S.I)) ⊆
      ((z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal : Set (S.A ⧸ S.I)) := hmem
  have hax : (S.a : Set S.A) ⊆
      ((S.U.ι.base y : PrimeSpectrum S.A).asIdeal : Set S.A) := by
    intro a ha
    have h1 : Ideal.Quotient.mk S.I a ∈ S.a.map (Ideal.Quotient.mk S.I) :=
      Ideal.mem_map_of_mem _ ha
    have h2 : Ideal.Quotient.mk S.I a ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal := hmemz h1
    change a ∈ (S.U.ι.base y : PrimeSpectrum S.A).asIdeal
    rw [hyz]
    exact h2
  have hyU : S.U.ι.base y ∈ (S.U : Set S.X) := by
    rw [← Scheme.Opens.range_ι S.U]
    exact Set.mem_range_self y
  have hnot : (S.U.ι.base y : PrimeSpectrum S.A) ∉
      PrimeSpectrum.zeroLocus (S.a : Set S.A) := hyU
  exact hnot hax

/-- Each locus `{y ∈ U ∩ Y : δ^Y_Z(y) ≤ k}` is stable under specialization inside `U`.  A
specialization of a point of `U ∩ Y` again lies in `U ∩ Y`, because the range of `Y ⟶ X` is
closed, and it is a specialization inside `Y`, because `Y ⟶ X` is an embedding; the sublevel
sets of the distance function on `Y` are stable under specialization. -/
public theorem stableUnderSpecialization_distanceToZSublevel (k : ℕ∞) :
    StableUnderSpecialization (S.distanceToZSublevel k) := by
  rintro y y' hspec ⟨z, hyz, hz⟩
  have hXspec : S.U.ι.base y ⤳ S.U.ι.base y' := hspec.map S.U.ι.continuous
  have hemb : Topology.IsClosedEmbedding S.Yι.base := S.Yι.isClosedEmbedding
  have hrange : S.U.ι.base y' ∈ Set.range S.Yι.base :=
    hemb.isClosed_range.stableUnderSpecialization hXspec ⟨z, hyz.symm⟩
  obtain ⟨z', hz'⟩ := hrange
  have hzz' : z ⤳ z' := by
    refine hemb.isInducing.specializes_iff.mp ?_
    rw [← hyz, hz']
    exact hXspec
  exact ⟨z', hz'.symm,
    distanceFunction_sublevel_stableUnderSpecialization S.Y S.closedSubsetZ k hzz' hz⟩

/-- The three-way case split against the distance from `Z`, for a single extended natural
number in place of the depth.  At a point of `U ∩ Y` the distance is at least one, so a bound
of two on the loci where the distance is at most one and a bound of one on the loci where it is
at most two together force the sum to be at least three. -/
public theorem three_le_add_distanceToZ (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) (dep : ℕ∞)
    (h1 : y ∈ S.distanceToZSublevel 2 → 1 ≤ dep)
    (h2 : y ∈ S.distanceToZSublevel 1 → 2 ≤ dep) :
    3 ≤ dep + S.distanceToZ z := by
  have hone : 1 ≤ S.distanceToZ z := S.one_le_distanceToZ y z hyz
  have succ_le : ∀ n : ℕ∞, ¬ S.distanceToZ z ≤ n → n + 1 ≤ S.distanceToZ z := fun n h =>
    Order.add_one_le_of_lt (not_le.mp h)
  by_cases hb1 : S.distanceToZ z ≤ 1
  · exact le_trans (by norm_num) (add_le_add (h2 ⟨z, hyz, hb1⟩) hone)
  by_cases hb2 : S.distanceToZ z ≤ 2
  · exact le_trans (by norm_num) (add_le_add (h1 ⟨z, hyz, hb2⟩) (succ_le 1 hb1))
  exact (succ_le 2 hb2).trans le_add_self

end AlgebraizationSituation

end Stacks.Algebraization

end
