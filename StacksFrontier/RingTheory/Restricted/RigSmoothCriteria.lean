module

public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.Conditions
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.Equivalences
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.JacobianChartPointwise

/-!
# Criteria for rig-smoothness of an adic algebra

For a completed polynomial presentation of an adically finite type algebra over a Noetherian
ring, rig-smoothness is equivalent to a cohomological condition on the two cohomology modules
of the completed naive cotangent complex, to a factorization of a power of the ideal of
definition through its differential, and to the existence of a finite Jacobian cover away from
that ideal.

## Main definitions

* `Rig.HasCotangentCohomologyCondition`: the annihilation and relative-projectivity condition
  on the two cohomology modules.
* `Rig.HasCotangentFactorization`: the factorization condition for the differential.
* `Rig.cotangentFactorizationIdeal`: the ideal of scalars which factor through a linear map,
  in terms of which condition (3) reads `I ^ c ⊆ (…).comap (algebraMap A B)`.
* `Rig.HasJacobianCover`: the finite Jacobian-cover condition.

## Main results

* `Rig.isRigSmooth_iff_cotangentCohomologyCondition`: conditions (1) and (2) agree.
* `Rig.isRigSmooth_iff_cotangentFactorization`: conditions (1) and (3) agree.
* `Rig.isRigSmooth_iff_hasJacobianCover`: conditions (1) and (4) agree.
* `Rig.isElementPowerTorsion_hneg_of_jacobianChart`: on one chart of a Jacobian cover,
  `H⁻¹(NL^∧_{B/A})` is `b`-power torsion.
* `Rig.free_localized_hzero_of_jacobianChart`: on one chart of a Jacobian cover,
  `H⁰(NL^∧_{B/A})` becomes finite free after inverting `b`.

The last section of the file reads the same characterisation *pointwise*, at a single prime
away from the ideal of definition, which is the form in which the source's proof of
Stacks 0GH6 consumes Stacks 0GAJ:

* `Rig.subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth`: for a rig-smooth `B`
  and a prime `𝔮` of `B` not containing `I B`, the localization of `H⁻¹(NL^∧_{B/A})` at `𝔮`
  vanishes and the localization of `H⁰(NL^∧_{B/A})` at `𝔮` is free.
* `Rig.isRigSmooth_of_forall_prime`: the converse, for a fixed presentation.
* `Rig.exists_jacobian_chart_away_prime_of_isRigSmooth`: for a rig-smooth `B` and such a `𝔮`, a
  Jacobian chart of the presentation whose distinguished element is a unit at `𝔮`.
* `Rig.subsingleton_and_free_of_flat_isLocalHom`: along a flat local homomorphism of local
  rings, vanishing and freeness of a finite module descend from the target to the source.

## Implementation notes

Condition (2) is expressed using the cohomological condition among the six equivalent
conditions of Stacks 0G9K. In condition (4), elements of `B` are represented by lifts to the
completed polynomial algebra, which makes the relation `bJ ⊆ (f₁, …, fₘ) + J²` literal; the
choice of lift does not affect that inclusion. An injection `Fin m ↪ Fin n` records a subset
of variables of cardinality `m`.

*The pointwise reading.* The forward direction goes through condition (4) together with the two
chart-level conclusions `Rig.isElementPowerTorsion_hneg_of_jacobianChart` and
`Rig.free_localized_hzero_of_jacobianChart`: given `𝔮` not containing `I B`, the cover
condition `I B ⊆ √(b₁, …, b_s)` produces an index `l` with `b_l ∉ 𝔮`, and the two chart
conclusions at that `l` give the two pointwise conclusions. The converse does not have to
manufacture a Jacobian cover, which is why it is available at all: it goes through condition
(2), reached from the localized condition of Stacks 0G9K, since a finite generating family of
`I B` already covers the complement of `V(I B)` by principal opens. Condition (2) is stated on
`DerivedCategory.homologyFunctor` while the pointwise hypothesis is stated on the kernel and
cokernel `Rig.CompletedNaiveCotangentComplex.Hneg` and `…Hzero`; the two presentations are
matched by `Rig.derivedHnegEquivHneg` and `Rig.derivedHzeroEquivHzero`, which compute the
homology of the complex from its strict bracketing. Freeness at `𝔮` is read through
`Module.freeLocus` in both directions.

## References

* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/
