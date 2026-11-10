module

public import StacksCore.Tactic.StacksAttribute
public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSeparablyClosedFiberRestriction

/-!
# The erratum to Tag 0EZV

This file records the erratum to
[Stacks, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV), and registers the refutation of
the statement as printed next to the corrected theorem.

## The statement as printed

Let `f : X ⟶ S` be a morphism of schemes, `x̄` a geometric point of `X` with image `s̄` in `S`,
`k : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` with `K` separably closed, `ℱ` an abelian sheaf on `Spec K`
and `q ≥ 0`. The tag asserts that the following are equivalent:

1. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_S Spec K, ℱ) = H^q(Spec(𝒪^{sh}_{S,s̄}) ×_S Spec K, ℱ)`;
2. `H^q(Spec(𝒪^{sh}_{X,x̄}) ×_{Spec(𝒪^{sh}_{S,s̄}), k} Spec K, ℱ) = H^q(Spec K, ℱ)`,

each equality read as bijectivity of the restriction map.

## What fails

`(1) ⇒ (2)` holds, but `(2) ⇒ (1)` does not. Condition (2) only sees the fibre over the given
point `k`, while condition (1) sees the fibres over every lift `k'` of the composite
`Spec K ⟶ S` to `Spec(𝒪^{sh}_{S,s̄})`. The printed proof identifies each summand of the limit
with the fibre over `k`, although that summand lies over its own lift.

## The counterexample

`S` is the nodal cubic `y² = x²(1 + x)` over an algebraic closure of `ℚ`, `s̄` its geometric point
at the node, and `X = Spec(𝒪^{sh}_{S,s̄}/(y - x √(1 + x)))` one branch of the node. `K` is an
algebraically closed field with two `K`-points `κ` (on the branch) and `τ` (off it) of
`Spec(𝒪^{sh}_{S,s̄})` over the same point of `S`. Take `k = κ`, `ℱ = ℤ` and `q = 0`. The fibre of
`X` over `κ` is `Spec K`, so (2) holds. The fibre over `τ` is empty, so the class of the constant
function `1` on a clopen neighbourhood of `τ` restricts to `0`, and (1) fails.

## The corrected statement

Condition (1) holds if and only if condition (2) holds for every lift
`k' : Spec K ⟶ Spec(𝒪^{sh}_{S,s̄})` of the composite `Spec K ⟶ S`.

## Lean names

All of them live in the namespace `Stacks.EtaleCohomology`, in the directory
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/`.

* `bijective_strictHenselizationFiberCohomologyPullback_iff`, in
  `StrictHenselizationSeparablyClosedFiberCohomology.lean`: the corrected statement, registered
  under Tag 0EZV. Its maps `strictHenselizationFiberCohomologyPullback` (condition (1)) and
  `strictHenselizationPointCohomologyPullback` (condition (2)) are defined in the same file.
* `exists_bijective_pointRestriction_and_not_bijective_fiberRestriction`, in the same file: the
  counterexample above, for those maps.
* `not_forall_bijective_strictHenselizationFiberRestriction_iff`, in
  `StrictHenselizationSeparablyClosedFiberRestriction.lean`: the negation of the statement as
  printed, for the restriction maps `strictHenselizationFiberRestriction` and
  `strictHenselizationPointRestriction` of
  `StrictHenselizationSeparablyClosedFiber.lean`. It is registered below.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

add_to_stacks 0EZV "erratum: the statement as printed is false; condition (2)
  at the given point does not imply condition (1). This is the negation of the printed equivalence,
  for the restriction maps of its statement, at the nodal cubic. The corrected statement, (1) iff
  (2) for every lift `k'` of `Spec K ⟶ S` to the strict henselization, is
  `Stacks.EtaleCohomology.bijective_strictHenselizationFiberCohomologyPullback_iff`."
  Stacks.EtaleCohomology.not_forall_bijective_strictHenselizationFiberRestriction_iff
