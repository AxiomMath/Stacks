module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.AdicCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.DegreeZero
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.InductiveSteps
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.NormalizedProjections

/-!
# The completion unit on local cohomology

Let `I` and `J` be ideals of a Noetherian ring `A` and let `M` be an `A`-module. Write
`RΓ_J(M)` for local cohomology with support in `V(J)` and `(-)^∧` for derived `I`-adic
completion, the reflection of `D(A)` onto the derived `I`-complete objects. This file collects
what is needed about the unit

`η : RΓ_J(M) ⟶ RΓ_J(M)^∧`

of that reflection in order to run the induction of Stacks 0EFL: formal criteria for the unit to
be invertible on cohomology in a given degree, criteria for `RΓ_J(M)` to be already derived
complete, and the degree-zero statement that for a sufficiently small support ideal the unit is
invertible on `H⁰`.

## Main definitions

* `Stacks.Algebraization.adicCompletionFunctor` — derived `I`-adic completion as an endofunctor of
  `D(A)`, namely `Dualizing.derivedCompletion` followed by the inclusion of the derived
  `I`-complete objects.
* `Stacks.Algebraization.adicCompletionUnit` — the unit of that reflection.
* `Stacks.Algebraization.localCohomologyAdicQuotientLeg` — the map
  `RΓ_J(M) ⟶ RΓ_J(M/IⁿM)` induced by `M ↠ M/IⁿM`.
* `Stacks.Algebraization.completedLocalCohomologyNormalizedProjection` — the unique maps
  `RΓ_J(M)^∧ ⟶ RΓ_J(M/IⁿM)` whose composite with the completion unit is the previous one.

## Main results

* `Stacks.Algebraization.completionUnit_localCohomology_isIso_of_regular_annihilator` — the
  inductive step of Stacks 0EFL in its formal form: given a nonzerodivisor annihilating both
  sides in degree `j`, invertibility in degree `j - 1` for `M` and for `M/aM` gives
  invertibility in degree `j` for `M`.
* `Stacks.Algebraization.completionUnit_localCohomology_isIso_of_shortExact` — the reduction
  along a short exact sequence whose sub is already derived complete.
* `Stacks.Algebraization.isIso_homology_completionUnit_localCohomology_zero` — the degree-zero
  statement, from Stacks 0EEX.
* `Stacks.Algebraization.isIso_completionFunctor_map_localCohomologyComparison` — completion
  inverts the comparison `RΓ_{J}(K) ⟶ RΓ_{J'}(K)` attached to a shrinking with the same trace
  on `V(I)`.
* `Stacks.Algebraization.isDerivedComplete_adicQuotientLocalCohomologySystem_obj` — every term
  of the tower of Stacks 0EEW is already derived `I`-complete.
* `Stacks.Algebraization.map_completionUnit_comp_completedLocalCohomologyToLimit` — the
  comparison map of Stacks 0EEW part (2) for the normalized projections, precomposed with `Hʳ`
  of the completion unit, is the canonical map `Hʳ_J(M) ⟶ lim Hʳ_J(M/IⁿM)` induced by the
  quotient maps `M ↠ M/IⁿM`.

## Implementation notes

The module universe is the ring universe, which is where `Dualizing.completedLocalCohomology`
lives.

The degree-zero statement is where Stacks 0EEX enters. The library's form of that tag identifies
`H⁰(RΓ_J(M)^∧)` with the submodule `⨆ Γ_{J'}(M)` of `M` only up to the choice of a derived-limit
structure on the completion, so it is not directly a statement about the map induced by the
counit `RΓ_J(M) ⟶ M`. What is proved here instead is that the map

`u : H⁰(RΓ_J(M)^∧) ⟶ M`

obtained from the completion of that counit lands in `⨆ Γ_{J'}(M)` — because its composite with
each projection `M ⟶ M/IⁿM` factors through `H⁰_J(M/IⁿM)`, the terms of the tower being derived
complete — and that it is injective, by Orzech's theorem applied to the surjection onto
`Γ_J(M)` that it becomes once the supremum has been collapsed. Only the existence of an abstract
isomorphism `H⁰(RΓ_J(M)^∧) ≅ ⨆ Γ_{J'}(M)` is taken from the tag.

The same derived completeness of the terms of the tower gives the *normalized* projections
`RΓ_J(M)^∧ ⟶ RΓ_J(M/IⁿM)`: the unit is invertible on each term, so the maps induced by
`M ↠ M/IⁿM` factor through the completion uniquely. These projections form a cone, and the
comparison map of Stacks 0EEW part (2) built from them is, after precomposition with the unit,
the canonical map into the limit — unconditionally, that map being the canonical map into the
limit determined by any cone of projections. What is *not* available here is that the normalized
projections exhibit `RΓ_J(M)^∧` as a *derived limit* of the tower: that is part (1) of
Stacks 0EEW in the form that specifies the projections, and it does not follow from
`Dualizing.isDerivedLimit_completedLocalCohomology`, which asserts only that some defining
triangle exists. It is what the Milnor sequence and the invertibility statements need, so those
are not yet available for the normalized projections.

## References

* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EEX](https://stacks.math.columbia.edu/tag/0EEX)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
-/
