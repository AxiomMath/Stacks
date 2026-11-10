module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberZariskiRiemann
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeathOfLimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannCenterOpenBasic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.FiniteLiftsAtPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.KillsOfForallDeadAt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.FibreOpenOverEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkZeroOffClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.GermDeathSpreads
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkTransitionComp

/-!
# Stacks 0DC6 from germ death in the limit of the proper models

The Zariski–Riemann proof of Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (the last remark of
§2 there) gives the vanishing above `d_V` of Stacks 0DC6, `GabberVanishing S n`, from its
remaining inputs: germ death at a valuation ring in the limit of the proper models
(`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath`) and the stalk cocycle of the
transition maps along refinements
(`AlgebraicGeometry.Scheme.ZariskiRiemann.DeadAtStableUnderRefinement`), the latter proved
(`deadAtStableUnderRefinement`). Every other input
of `AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath_of_etaleInputs`
is proved: `refinementsCofiltered`, `germDeathSpreads`, `stalkZeroOffClosure`,
`killsOfForallDeadAt`, `fibreOpenOverEtale`, `centerOpenBasic` and `finiteLiftsAtPoint`. So
`GabberVanishing S n` rests on `CenterLimitGermDeath` alone
(`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_centerLimitGermDeath'`).

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath_of_stable`
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_centerLimitGermDeath`
* `AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_centerLimitGermDeath'`

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- **Germ death at the centres of small rank from germ death at valuation rings**, with every
étale-sheaf and scheme input proved except the stalk
cocycle `AlgebraicGeometry.Scheme.ZariskiRiemann.DeadAtStableUnderRefinement`. -/
theorem centeredGermDeath_of_valuationGermDeath_of_stable {n : ℕ}
    (hVGD : ValuationGermDeath.{u} n) (hstab : DeadAtStableUnderRefinement.{u}) :
    CenteredGermDeath.{u} n :=
  centeredGermDeath_of_valuationGermDeath_of_etaleInputs hVGD
    (fun B _ _ => refinementsCofiltered B) germDeathSpreads stalkZeroOffClosure hstab
    killsOfForallDeadAt fibreOpenOverEtale centerOpenBasic finiteLiftsAtPoint

end AlgebraicGeometry.Scheme.ZariskiRiemann

namespace AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

open ZariskiRiemann in
/-- **The vanishing above `d_V` of Stacks 0DC6 from germ death in the limit of the proper
models.** For every base `S` of Stacks 0DC6 and every `n` invertible on `S`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` and the stalk cocycle
`AlgebraicGeometry.Scheme.ZariskiRiemann.DeadAtStableUnderRefinement` give
`GabberVanishing S n`. -/
theorem gabberVanishing_of_centerLimitGermDeath {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (hlim : CenterLimitGermDeath.{u}) (hstab : DeadAtStableUnderRefinement.{u}) :
    GabberVanishing S n :=
  gabberVanishing_of_centeredGermDeath hS hn
    (centeredGermDeath_of_valuationGermDeath_of_stable
      (valuationGermDeath_of_centerLimitGermDeath hlim n) hstab)

open ZariskiRiemann in
/-- **The vanishing above `d_V` of Stacks 0DC6 from germ death in the limit of the proper models
alone.** For every base `S` of Stacks 0DC6 and every `n` invertible on `S`,
`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` gives `GabberVanishing S n`; the
stalk cocycle is `AlgebraicGeometry.Scheme.ZariskiRiemann.deadAtStableUnderRefinement`. -/
theorem gabberVanishing_of_centerLimitGermDeath' {S : Scheme.{u}}
    (hS : IsUnboundedDescentEtaleBase S) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (hlim : CenterLimitGermDeath.{u}) : GabberVanishing S n :=
  gabberVanishing_of_centerLimitGermDeath hS hn hlim deadAtStableUnderRefinement

end AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale

end
