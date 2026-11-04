module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.MittagLeffler
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.LimitTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InverseSystems.AdicQuotientSystems.StableImages

/-!
# Inverse systems of sheaves of modules with adic quotients

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it, `I ⊆ Γ(C, O)` an ideal and
`… → F₂ → F₁ → F₀` an inverse system of sheaves of `O`-modules with
`Fₙ = Fₙ₊₁/I^(n+1)Fₙ₊₁`.  The term `Fₙ` of the system stands for the source's `F₍ₙ₊₁₎`, so the
`n`-th homogeneous piece `IⁿFₙ` is the source's `IⁿF₍ₙ₊₁₎` and the grading starts at zero.

Three consequences of an ascending chain condition on the graded object
`⨁ₙ Hᵖ(C, IⁿFₙ)` are proved.  Stacks 0GYQ: if the chain condition holds one degree up, in
`⨁ₙ H^(p+1)(C, IⁿFₙ)`, then the inverse system `n ↦ Hᵖ(C, Fₙ)` satisfies the Mittag-Leffler
condition, with a shift `c` uniform in the degree.  Stacks 0GYR sharpens this: the chain
condition is needed only on the graded submodule `⨁ₙ Nₙ` of stable images
`Nₙ = ⋂_{m ≥ n} Im(H^(p+1)(C, IⁿF_m) → H^(p+1)(C, IⁿFₙ))`, which already contains the images of
all the boundary maps.  Stacks 0GYS: if it holds in degree `p`
itself, then the limit topology on `lim Hᵖ(C, Fₙ)` is the `I`-adic topology.

All three arguments run through the boundary maps of the short exact sequences
`0 → I^(n+1)Fₘ → Fₘ → Fₙ → 0`, which the quotient hypothesis supplies for every `m ≥ n + 1`
(`IsAdicQuotientSystem.shortExact`), and through the *canonical graded action*: multiplication
by `a ∈ Iᵐ` on `Fₙ` lifts through the quotients to a map `Fₙ ⟶ Fₙ₊ₘ` (`mulLift`), which
restricts to the ideal-power subsheaves (`act`).  For 0GYQ the graded submodules of
`⨁ₙ H^(p+1)(C, IⁿFₙ)` are the families closed under that action (`GradedSubmodule`), and the
chain condition is well-foundedness of their strict reverse order; the proof takes the images
under the boundary maps of the classes vanishing `c` stages earlier, which increase with `c` and
exhaust the whole boundary image, so that stabilisation gives a uniform lifting bound.  For
0GYS the chain condition is Noetherianity of `⨁ₙ Hᵖ(C, IⁿFₙ)` as a module over
`⨁ₙ Iⁿ/Iⁿ⁺¹` for the canonical action, and the proof produces, by
`AssociatedGraded.exists_eventual_degree_one_generators`, one finite family of elements of `I`
with which every element of `Ker(M → Hᵖ(C, Fₙ₊₁))` can be successively approximated; summing
the approximations in the complete inverse limit gives `Ker(M → Hᵖ(C, F_{c+k})) ⊆ IᵏM`.

## Main definitions

* `Stacks.Cohomology.AdicInverseSystems.towerMap`: the transition map `Fₘ ⟶ Fₙ` of an inverse
  system indexed by `ℕ`.
* `Stacks.Cohomology.AdicInverseSystems.vanishingSubmodule`: the classes of an inverse system of
  modules vanishing at every stage at least `c` steps earlier.
* `Stacks.Cohomology.AdicInverseSystems.gradedPiece`: the subsheaf `IⁿFₙ`.
* `Stacks.Cohomology.AdicInverseSystems.IsAdicQuotientSystem`: the hypothesis
  `Fₙ = Fₙ₊₁/I^(n+1)Fₙ₊₁`.
* `Stacks.Cohomology.AdicInverseSystems.mulLift` and `act`: the canonical graded action of `Iᵐ`
  on the system and on its ideal-power subsheaves.
* `Stacks.Cohomology.AdicInverseSystems.cohomologyBoundary`: the boundary map
  `Hᵖ(C, Fₙ) ⟶ H^(p+1)(C, I^(n+1)Fₙ₊₁)`.
* `Stacks.Cohomology.AdicInverseSystems.GradedSubmodule`: a graded submodule of
  `⨁ₙ H^(p+1)(C, IⁿFₙ)`.
* `Stacks.Cohomology.AdicInverseSystems.StableGradedSubmodule`: a graded submodule of the
  graded object `⨁ₙ Nₙ` of stable images of Stacks 0GYR.
* `Stacks.Cohomology.AdicInverseSystems.CohomologySum`, `IsCanonicalAction` and
  `HasGradedACC`: the graded module `⨁ₙ Hᵖ(C, IⁿFₙ)`, the specification of the canonical action
  on it, and the ascending chain condition of Stacks 0GYS.
* `Stacks.Cohomology.AdicInverseSystems.cohomologyLimit`: the inverse limit
  `lim Hᵖ(C, Fₙ)`.
* `Stacks.Cohomology.AdicInverseSystems.stableImage`: the stable image in `Hᵖ(C, IⁿFₙ)` of the
  classes coming from `Hᵖ(C, IⁿFₘ)` for every `m ≥ n`.
* `Stacks.Cohomology.AdicInverseSystems.StableCohomologySum`, `IsCanonicalActionOnStable` and
  `HasStableGradedACC`: the graded module `⨁ₙ Nₙ`, the specification of the canonical action on
  it, and the ascending chain condition of Stacks 0GYT.

## Main results

* `Stacks.Cohomology.AdicInverseSystems.isMittagLefflerCategorical_cohomology` and
  `exists_uniform_stable_image`: Stacks 0GYQ and its footnote.
* `Stacks.Cohomology.AdicInverseSystems.isMittagLefflerCategorical_cohomology_of_stableImages`
  and `exists_uniform_stable_image_of_stableImages`: Stacks 0GYR and its footnote.
* `Stacks.Cohomology.AdicInverseSystems.cohomologyBoundary_mem_stableImage` and
  `map_act_mem_stableImage`: the two verifications of Stacks 0GYR, that `⨁ₙ Nₙ` is a graded
  submodule and that it contains the images of the boundary maps.
* `Stacks.Cohomology.AdicInverseSystems.limitTopology_eq_adicModuleTopology`: Stacks 0GYS.
* `Stacks.Cohomology.AdicInverseSystems.IsAdicQuotientSystem.shortExact`: the short exact
  sequences `0 → I^(n+1)Fₘ → Fₘ → Fₙ → 0` for every `m ≥ n + 1`.
* `Stacks.Cohomology.AdicInverseSystems.exists_approx`: the successive approximation that
  replaces the appeal to the open mapping lemma in the source of 0GYS.
* `Stacks.Cohomology.AdicInverseSystems.limitTopology_eq_adicModuleTopology_of_stableImages`
  and `exists_approx_of_stableImages`: Stacks 0GYT and the successive approximation it rests on.

## Implementation notes

The source states the chain condition for `⨁ H^{p+1}(C, IⁿF₍ₙ₊₁₎)` as a graded
`⨁ Iⁿ/Iⁿ⁺¹`-module and leaves the module structure implicit ("details omitted").  The two
tags are rendered differently here because they use the hypothesis differently.  Stacks 0GYQ
needs only that the boundary images form a graded submodule and that these stabilise, so the
hypothesis is well-foundedness of the order on the families of submodules closed under the
canonical action: no graded module structure has to be constructed.  Stacks 0GYS needs finite
generation in degree one, which is a statement about the honest graded module, so there the
hypothesis asserts the existence of a `⨁ Iⁿ/Iⁿ⁺¹`-module structure on `⨁ₙ Hᵖ(C, IⁿFₙ)` whose
action is the canonical one and which is Noetherian.  For an `ℕ`-graded module Noetherianity is
equivalent to the ascending chain condition on graded submodules, so both renderings are
faithful.  Stacks 0GYR follows 0GYQ: a graded submodule of `⨁ₙ Nₙ` is a family of submodules of
`⨁ₙ H^(p+1)(C, IⁿFₙ)` closed under the canonical action with its degree `n` part inside `Nₙ`,
which is the right notion because `Nₙ` is itself closed under that action.

Stacks 0GYT sharpens 0GYS in the same way and is rendered like it: the hypothesis asserts the
existence of a `⨁ Iⁿ/Iⁿ⁺¹`-module structure on `⨁ₙ Nₙ` whose action is the canonical one and
which is Noetherian.  This is weaker than the hypothesis of 0GYS because the graded submodule
used in the proof — the classes lifting a coordinate of the inverse limit that dies one step
earlier — consists of stable classes already, so it lies inside `⨁ₙ Nₙ`.

The structure sheaf is an arbitrary sheaf of commutative rings rather than the constant sheaf of
a ring `A`: the coefficient ring is then `Γ(C, O)` and the source's situation is the case of the
constant sheaf.

The proof of 0GYS given here does not use the open mapping lemma, and in particular does not
need `I` to be finitely generated, which the source's choice of generators of `I` tacitly
assumes.  The fixed finite family of degree-one scalars comes instead from finite generation of
`J · E`, where `J` is the ideal of degree-one classes of `⨁ Iⁿ/Iⁿ⁺¹`; see
`StacksFrontier/RingTheory/Filtration/AssociatedGradedGenerators.lean`.

## References

* [Stacks Project, Tag 0GYQ](https://stacks.math.columbia.edu/tag/0GYQ)
* [Stacks Project, Tag 0GYR](https://stacks.math.columbia.edu/tag/0GYR)
* [Stacks Project, Tag 0GYS](https://stacks.math.columbia.edu/tag/0GYS)
* [Stacks Project, Tag 0GYT](https://stacks.math.columbia.edu/tag/0GYT)

## Files

* `AdicQuotientSystems/Basic.lean`: basic theory of inverse systems with adic quotients.
* `AdicQuotientSystems/MittagLeffler.lean`: Mittag-Leffler for the cohomology.
* `AdicQuotientSystems/LimitTopology.lean`: the limit topology on the cohomology.
* `AdicQuotientSystems/StableImages.lean`: the chain condition on the stable images.
-/
