module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PurelyInseparablePullback.PrimeRingTheta
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PurelyInseparablePullback.DifferentialComponents
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PurelyInseparablePullback.HomotopyInverse

/-!
# Pulling back along a purely inseparable map

Let `(B, J, γ)` be a divided power ring which is an algebra over `ℤ_(p)` for a prime `p`, and let
`λ ∈ B`.  Writing the ring of the first display of the proof of Tag 07N1 in the equivalent form

`B[z]⟨ξ⟩/(ξ - (z^p - λ)) = B⟨ξ⟩[z]/(z^p - ξ - λ)`,

this file constructs that ring, exhibits the free `B`-module basis `z^i ξ^[n]` with `0 ≤ i < p`
and `n ≥ 0` of the source, and builds the operator `θ` of the proof of Tag 07N1 on that basis.
Here `z` is an *ordinary* polynomial variable and `ξ` is a *divided power* variable, so that
`B⟨ξ⟩` is free as a `B`-module on the divided power monomials `ξ^[n]` rather than on the
ordinary powers `ξ^n`.

Instantiating at the `p`-adically completed divided power envelope `(D, J̄, γ̄)` of equation
(07J8) in Situation 07MD, the `p`-adic completion of this ring is the ring `D'` of Tag 07N1.

## Main definitions

* `Crystalline.PthRootExtension.primeRing` — the ring `B[z]⟨ξ⟩/(ξ - (z^p - λ))`.
* `Crystalline.PthRootExtension.basisZXi` — its free `B`-module basis `z^i ξ^[n]`.
* `Crystalline.PthRootExtension.theta` — the `B`-linear operator `θ` of the proof of Tag 07N1,
  given on the basis by `θ(z^j) = p z^{j+1}/(j+1)`, `θ(z^{p-1} ξ^[m]) = ξ^[m+1]` and
  `θ(z^j ξ^[m]) = (p z^{j+1} ξ^[m] - θ(p λ z^j ξ^[m-1]))/(j + 1 + pm)`.
* `Crystalline.PthRootExtension.PartialZValues` — the three values of `∂_z` on the basis
  computed in the proof of Tag 07N1 from `ξ = z^p - λ` and `ξ ξ^[n-1] = n ξ^[n]`.
* `Crystalline.PthRootExtension.IsDpowDifferential` — the first display of the proof of
  Tag 07N1: the differential of `Ω'` satisfies `d(ξ^[n+1]) = ξ^[n] d ξ`, which is what holds
  when `Ω'` is the module of divided power differentials and `ξ` lies in the divided power
  ideal.
* `Crystalline.PthRootExtension.epsilon` — the `B`-valued remainder `p f - θ(∂_z f)`, which is
  `p` on `1`, `-p λ` on `ξ` and zero on every other basis vector.
* `Crystalline.PthRootExtension.DOneValues` — the two values of `d₁` on the basis, computed in
  the proof of Tag 07N1 from `ξ = z^p - λ`.
* `Crystalline.PthRootExtension.epsilonPrimeMap` — the remainder
  `ε'(f) = (θ ⊗ 1)(d₁ f) - d₁(θ f)`, as a `B`-linear map.

## Main results

* `Crystalline.PthRootExtension.universallyInjective_toPrimeRing` — assumption (07Q4) of
  Lemma 07Q7 for this extension: `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))` is universally injective,
  because the basis splits it.
* `Crystalline.PthRootExtension.partialZ_theta` — assumption (07Q3): `∂_z ∘ θ` is
  multiplication by `p`.
* `Crystalline.PthRootExtension.smul_sub_theta_partialZ` — assumption (07Q5) in the sharp form
  of the footnote of Tag 07N1: `p f - θ(∂_z f)` is the image of `epsilon f ∈ B`.
* `Crystalline.PthRootExtension.dOne_remainder_mem` — assumption (07Q6) in the sharp form of
  the footnote of Tag 07N1: `(θ ⊗ 1)(d₁ f) - d₁(θ f)` lies in `Ω`, being zero on every basis
  vector except `z^{p-1} ξ`, where it is `-λ dλ`.
* `Crystalline.targetD_natCast` — assumption (07Q0) for `a` the image of an integer.
* `Crystalline.targetD_ringInverse` — the de Rham differential annihilates the inverse of a unit
  it annihilates, hence kills the scalars `p/(i + 1 + pn)` occurring in `θ`.
* `Crystalline.DzDecomposition.partialZLinear` — `∂_z` is `B`-linear, so it is determined by its
  values on the basis `z^i ξ^[n]`.
* `Crystalline.DzDecomposition.dOne_smul` — the twisted Leibniz rule `d₁(b f) = b d₁(f) + f ⊗ db`
  for `b ∈ B`, which is why `d₁` is merely additive while `ε'` is `B`-linear.
* `Crystalline.DzDecomposition.partialZ_mul` and `Crystalline.DzDecomposition.dOne_mul` — the
  Leibniz rules for the two components of the differential, which the `B'`-linearity of the
  decomposition gives.
* `Crystalline.PthRootExtension.xiElt_one_mul_xiElt` — the divided power identity
  `ξ ξ^[n] = (n + 1) ξ^[n+1]` in the extension.
* `Crystalline.PthRootExtension.partialZValues_of_isDpowDifferential` and
  `Crystalline.PthRootExtension.dOneValues_of_isDpowDifferential` — the two tables of values on
  the basis `z^i ξ^[n]` displayed in the proof of Tag 07N1, derived from
  `d(ξ^[n+1]) = ξ^[n] d ξ`, `ξ = z^p - λ` and `ξ ξ^[n-1] = n ξ^[n]` rather than assumed.
* `Crystalline.exists_homotopyInverse_pthRootExtension` — **the conclusion of Tag 07N1** for the
  uncompleted extension: Lemma 07Q7 at `a = p`, with assumptions (07Q0), (07Q2), (07Q3),
  (07Q4), (07Q5) and (07Q6) discharged.

## Implementation notes

Two things the source proves are hypotheses of
`exists_homotopyInverse_pthRootExtension`, so the tag on it carries the corresponding
description.

The first is the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz` of assumption (07Q1).  In the source it
comes from identifying `B[z]⟨ξ⟩/(ξ - (z^p - λ))` with the divided power envelope of the ideal
generated by `z^p - λ` in `B[z]` (Lemma 07HC, whose instance for this relation is
`Crystalline.ker_presentation_pthRootRelation`) and then applying Lemma 07HW.  Carrying that out
needs the divided power structure on `J B' + (ξ)` extending `γ`, and then a comparison between
the base change of the *Kähler* differentials that
`Crystalline.dividedPowerEnvelopeDifferentialsEquiv` produces and the divided power
differentials of `B`; neither is assembled in this tree.

The second is `PthRootExtension.IsDpowDifferential`, the statement `d(ξ^[n+1]) = ξ^[n] d ξ`.
This holds whenever `Ω'` is the module of divided power differentials of `B'` with `ξ` in the
divided power ideal, so it comes from the same construction; it is isolated as a hypothesis
because everything else about the two components of the differential follows from it.  The two
structures `PthRootExtension.PartialZValues` and `PthRootExtension.DOneValues`, which record the
values of `∂_z` and `d₁` on the basis `z^i ξ^[n]`, are *proved* from it rather than assumed.

Finally the statement here is for the uncompleted extension `B[z]⟨ξ⟩/(ξ - (z^p - λ))`, whereas
Tag 07N1 is stated for its `p`-adic completion `D'` in Situation 07MD, with `Ω_{D'}` the `p`-adic
completion of the divided power differentials.  The `p`-adic completion half is proved
elsewhere: Tag 07N1 in Situation 07MD is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation` of
`StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedSituation`, and the
completed clause of Tag 07LD is clause 2 of `Crystalline.DividedPowerPolynomial.stacks07LD`.

The recursion defining `θ` is used in the cleared form
`(i + 1 + pn) • θ(z^i ξ^[n]) = p • z^{i+1} ξ^[n] - (p λ) • θ(z^i ξ^[n-1])`, valid for all `n`
through `PthRootExtension.thetaBasisPred`, which is `0` at `n = 0`; this is what makes the
induction for (07Q6) a single step rather than two.

## References

* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Tag 07HC](https://stacks.math.columbia.edu/tag/07HC)
* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Tag 07H5](https://stacks.math.columbia.edu/tag/07H5)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

