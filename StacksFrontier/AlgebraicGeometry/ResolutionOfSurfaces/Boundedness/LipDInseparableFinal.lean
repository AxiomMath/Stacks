module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDInseparableGoUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDFrobeniusData

/-!
# Reduction to rational singularities after a purely inseparable extension of degree `p`

Let `p` be a prime, `R` a complete regular local ring of dimension two and characteristic `p`,
and `A` a Noetherian complete local normal domain, finite over `R`, whose fraction field is a
purely inseparable extension of degree `p` of that of `R`. Then reduction to rational
singularities is possible for `A`. This is [Stacks, Tag 0B4U], in the form in which the proof
of [Stacks, Tag 0BGN] uses it: there `A` is the integral closure of `R` in an inseparable
extension `L` of degree `p` of the fraction field of `R`, and the hypotheses below are what that
amounts to.

## Main results

* `AlgebraicGeometry.isReductionToRationalSingularitiesPossible_of_inseparable`:
  [Stacks, Tag 0B4U].

## Implementation notes

The source's proof goes through the trace of differential forms, Grauert–Riemenschneider and
duality ([Stacks, Tags 0AX6, 0B4T and 0B4S]). The proof here uses the Frobenius instead, and no
duality. A nonzero `c ∈ R` factors, over the punctured spectrum, through the `p`-th power map
and a Frobenius splitting of `R` (`AlgebraicGeometry.PuncturedRestriction.exists_frobeniusData`).
On a normal modification `Y` of `Spec A` finite over a normal modification `X` of `Spec R`, the
`p`-th powers of a cocycle of `𝒪_Y` form a coboundary on `X` because `H¹(X, 𝒪_X) = 0`
([Stacks, Tag 0B4Q]). So `c` kills `H¹(Y, 𝒪_Y)` over the punctured spectrum, hence everywhere
by [Stacks, Tag 0AXB] in the form of the polar lemma
(`AlgebraicGeometry.PuncturedRestriction.smul_rightDerived_pushUnit_eq_zero`). Such `Y`
dominate all normal modifications of `Spec A` ([Stacks, Tag 0B49]), and `H¹(Y, 𝒪_Y)[c]` is
bounded by [Stacks, Tag 0AXJ].

No `@[stacks]` attribute is attached: the tag is an input to [Stacks, Tag 0BHY] here.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0B4U].** Let `p` be a prime number, `R` a complete regular local ring of
dimension two and characteristic `p`, and `A` a Noetherian complete local normal domain, finite
and torsion free over `R`, whose fraction field has degree `p` and is inseparable over that of
`R`. Then reduction to rational singularities is possible for `A`. -/
theorem isReductionToRationalSingularitiesPossible_of_inseparable (p : ℕ) [Fact p.Prime]
    (R A : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [CharP R p] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A]
    (hR : ringKrullDim R = 2)
    (hins : letI := IsRegularLocalRing.isDomain R
      letI := FractionRing.liftAlgebra R (FractionRing A)
      Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) :
    IsReductionToRationalSingularitiesPossible A := by
  let := IsRegularLocalRing.isDomain R
  have : IsNormalDomain R := isNormalDomain_of_isRegularLocalRing R
  have hRN : IsNagataRing R := IsNagataRing.of_isPrecomplete_maximalIdeal
  have hAN : IsNagataRing A := IsNagataRing.of_isPrecomplete_maximalIdeal
  have : IsNagataRing R := hRN
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have : IsLocalHom (algebraMap R A) := Algebra.IsIntegral.isLocalHom R A
  have hdimA : ringKrullDim A = 2 := (Algebra.IsIntegral.ringKrullDim_eq R A).symm.trans hR
  obtain ⟨c, hc, hdata⟩ := PuncturedRestriction.exists_frobeniusData p R A hR hins
  refine isReductionToRationalSingularitiesPossible_of_forall_smul_eq_zero R A hRN hAN hR hdimA
    c hc fun X Y _ _ f g π hf hg hπ hπs hcomm x => ?_
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral Y := hg.source_isIntegral
  obtain ⟨hchar, hpow, n, b, β, θ, Θ, hΘ, hid⟩ := hdata X Y f g π hf hg hcomm
  exact smul_firstCohomology_eq_zero_of_frobenius R A hdimA f g π hg hcomm
    (isZero_hgroup_of_isModification_of_isRegularLocalRing R hR f hf) p hpow c b β θ Θ hΘ hid x

end AlgebraicGeometry

end
