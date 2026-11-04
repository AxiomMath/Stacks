module

public import StacksFrontier.RingTheory.Rig.ClosedPoint.RigPointCriterion
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RelativeCriterion
public import StacksFrontier.RingTheory.Rig.ClosedPoint.LiftingAndCompletedAway

/-!
# Rig-closed points of Noetherian adic rings

Let `A` be a Noetherian adic topological ring.  A prime `q` of `A` is a *rig point*, or a
*rig-closed point*, when it is maximal among the primes that do not contain an ideal of
definition — equivalently, when the corresponding point of `Spec A` is closed in the
complement of the vanishing locus of an ideal of definition, the "rigid-analytic" open
subspace.  `rigPoint_tfae` collects the eight equivalent descriptions of this condition, the
last of which is purely algebraic: `A ⧸ q` is a complete one-dimensional Noetherian local
domain whose maximal ideal is the radical of every extended ideal of definition.

The rest of the file studies how rig points behave along a morphism.  For an adic,
topologically finite type morphism `φ : A →+* B` of Noetherian weakly admissible rings and a
rig point `q` of `B`, three conditions are equivalent: finiteness of the residue field of
`B ⧸ q` over the reduction of `A`, rig-closedness of `q.comap φ`, and finiteness of the
induced map `A ⧸ q.comap φ → B ⧸ q`.  Rig-closedness descends to `q.comap φ` unconditionally
when a reduction of `A` is Jacobson, and a rig point of `A` lifts to one of `B` along a flat
such morphism exactly when the closed point of its quotient is hit on special fibres.

The last section treats the completed principal localization `A[1/f]^` of an `I`-adically
complete Noetherian ring.  When `f` is a unit modulo a prime `p`, the extension of `p` to
`A[1/f]^` is again prime with the same quotient `A ⧸ p`, and that extension is described both
as a scalar extension and as a completion of the localized ideal.

## Main definitions

* `Rig.Ideal.IsMaximalAmongPrimesAvoiding` — a prime is maximal among the primes not
  containing a fixed ideal.
* `Rig.Ideal.IsClosedPointAwayFrom` — the point of `Spec A` cut out by a prime is closed in
  the complement of a vanishing locus.
* `Rig.Ideal.IsRigPointLocalCondition` — the complete one-dimensional local domain
  description of the quotient.
* `Rig.CompletedAway` — the adic completion of a principal localization.
* `Rig.extendedIdeal` — the extension of an ideal to that completed localization.

## Main results

* `Rig.isIdealOfDefinition_iff_isAdic` — in a pre-adic topological ring the ideals of
  definition are exactly the ideals defining the adic topology.
* `Rig.rigPoint_tfae` — the eight equivalent descriptions of a rig point.
* `Rig.exists_residueFieldMap_finiteType_of_rigPoint` — the residue field at a rig point is
  of finite type over the reduction of the source.
* `Rig.rigPoint_relative_tfae` — the relative criterion for rig-closedness.
* `Rig.isRigPointLocalCondition_comap_of_isJacobsonRing_quotient` — rig-closedness descends
  over a Jacobson reduction.
* `Rig.rigPoint_lifts_iff_maximalIdeal_mem_specialFibre_image` — the lifting criterion along
  a flat morphism, with `Rig.rigPoint_residueFieldMap_finite_of_lift` and
  `Rig.rigPoint_quotientMap_finite_of_lift` the relative finiteness statements at a lift.
* `Rig.extendedIdeal_isPrime` and `Rig.quotient_extendedIdeal_equiv` — primality of the
  extended ideal in a completed principal localization, and the identification of its
  quotient.

## Implementation notes

An ideal of definition is `TopologicalRing.IsIdealOfDefinition`;
`isIdealOfDefinition_iff_isAdic` identifies it with Mathlib's `IsAdic` in a pre-adic topology.
A quotient ring carries the quotient topology, so nontriviality of the induced topology means
that this topology is not discrete, and completeness is expressed through the canonical
uniformity of the additive topological group.  A closed point of the open complement is stated
intrinsically, as a closed singleton in the corresponding subtype.  The entries of the two
`List.TFAE`s occur in the order of the source.

## References

* [Stacks Project, Tag 0GG8](https://stacks.math.columbia.edu/tag/0GG8)
* [Stacks Project, Tag 0GGA](https://stacks.math.columbia.edu/tag/0GGA)
* [Stacks Project, Tag 0GGB](https://stacks.math.columbia.edu/tag/0GGB)
* [Stacks Project, Tag 0GGC](https://stacks.math.columbia.edu/tag/0GGC)
* [Stacks Project, Tag 0GGD](https://stacks.math.columbia.edu/tag/0GGD)
* [Stacks Project, Tag 0GGF](https://stacks.math.columbia.edu/tag/0GGF)
-/
