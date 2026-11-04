module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AffineAlmostBlowUpInterludeB
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ClosedImmersionAlmostBlowUp
import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ThickeningHSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusLimitHSheaf

/-!
# Stacks 0EVL: the Frobenius limit of global functions is a sheaf for the h topology

For a prime `p` and a scheme `S` over `𝔽_p`, the rule `X ↦ lim_F Γ(X, 𝒪_X)` — the limit of the
`p`-power map on global functions — is a sheaf on the big h site `(Sch/S)_h` of Stacks 0EU1.

`AlgebraicGeometry.BigHOver.isSheaf_frobeniusLimitSections_of_criterion` reduces this to two
inputs of the sufficiency direction of the h sheaf criterion: the sufficiency direction of Stacks
0EVF, which is `AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion`, and the reduction of its
condition (3) to the two shapes of Examples 0EVG and 0EVH, which is the content of the proof of
Stacks 0EVI and is `AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice`.  Both are available,
so the assembly is unconditional here.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_frobeniusLimitSections`: **Stacks 0EVL.**

## Implementation notes

The four conditions of the criterion Stacks 0EVI hold for this presheaf unconditionally and at
the source's own hypotheses: `AlgebraicGeometry.BigHOver.isZariskiSheaf_frobeniusLimitSections`,
`AlgebraicGeometry.BigHOver.isAffineFlatProperFinitePresentationSheaf_frobeniusLimitSections`,
`AlgebraicGeometry.BigHOver.isOneGeneratorAlmostBlowUpSheaf_frobeniusLimitSections` and
`AlgebraicGeometry.BigHOver.isTwoGeneratorAlmostBlowUpSheaf_frobeniusLimitSections`.

Being a scheme over `𝔽_p` is recorded as `Stacks.Frobenius.IsInCharacteristic S p`, the vanishing
of `p` in the ring of global functions of `S`; by
`Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic` that vanishing holds over every open, so the
structure sheaf is a sheaf of `𝔽_p`-algebras, which is what the source assumes.

## References

* [Stacks Project, Tag 0EVL](https://stacks.math.columbia.edu/tag/0EVL)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EVL.** Let `p` be a prime number and let `S` be a scheme over `𝔽_p`, contained in a
big h site `B`.  Then `X ↦ lim_F Γ(X, 𝒪_X)`, the limit of the `p`-power map on global functions,
is a sheaf on the big h site `(Sch/S)_h`.

The four conditions of the h sheaf criterion Stacks 0EVI hold for this presheaf; the sufficiency
direction of that criterion is `AlgebraicGeometry.affineAlmostBlowUpHSheafCriterion` together with
`AlgebraicGeometry.generatorAlmostBlowUpSquaresSuffice`. -/
@[stacks 0EVL]
public theorem isSheaf_frobeniusLimitSections
    (p : ℕ) (hp : p.Prime) (hChar : Stacks.Frobenius.IsInCharacteristic S p) :
    Presheaf.IsSheaf (BigHOver.topology B S hS) (frobeniusLimitSections B S hS p) :=
  isSheaf_frobeniusLimitSections_of_criterion B S hS affineAlmostBlowUpHSheafCriterion
    generatorAlmostBlowUpSquaresSuffice p hp hChar

end BigHOver

end AlgebraicGeometry

end
