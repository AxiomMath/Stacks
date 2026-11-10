module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLevelStalkCompatOfRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkTransitionRestrictionOfBaseChangeAgreement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLevelEventualVanishingOfLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkTransitionSepClosedExtension

/-!
# Germ death at a valuation ring from vanishing on the limit, unconditionally

This file assembles `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLimitGermDeath` (Travaux de
Gabber, Exposé XVIII-A, last remark of §2) from its three
inputs, all proved:

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelEventualVanishing` (the limit layer,
  Stacks 09YQ);
* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelStalkCompat` (germs at the centers come
  from the levels), itself from the compatibility of the stalk transition with Stacks 03Q9,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionStrictHenselizationRestriction`;
* `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionSepClosedExtension` (extending the
  field of a separably closed geometric point).

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelStalkCompat`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLimitGermDeath`

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

/-- **Germs at the centers come from the levels** (Travaux de Gabber, Exposé XVIII-A, last remark
of §2, Steps 0, 1 and 3 of the proof), unconditionally. -/
theorem centerLevelStalkCompat : CenterLevelStalkCompat.{u} :=
  centerLevelStalkCompat_of_restriction stalkTransitionStrictHenselizationRestriction

/-- **Germ death at a valuation ring from vanishing on the limit of the models**
(Travaux de Gabber, Exposé XVIII-A, last remark of §2), unconditionally. -/
theorem centerLimitGermDeath : CenterLimitGermDeath.{u} :=
  centerLimitGermDeath_of_inputs centerLevelEventualVanishing centerLevelStalkCompat
    stalkTransitionSepClosedExtension

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
