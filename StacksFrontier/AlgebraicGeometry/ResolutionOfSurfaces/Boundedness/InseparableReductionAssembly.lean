module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpDomination

/-!
# Reduction to rational singularities through an inseparable extension of degree `p`

Let `p` be a prime, `A` a complete regular local ring of dimension two and characteristic `p`,
`L/K` an inseparable extension of degree `p` of the fraction field `K` of `A`, and `B` the
integral closure of `A` in `L`. Then reduction to rational singularities is possible for `B`.

This is `SeparableGoUp.isReductionToRationalSingularitiesPossible_integralClosure_of_frobenius`
with its two inputs discharged: `A` defines a rational singularity by [Stacks, Tag 0B4Q]
(`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`, a complete
Noetherian local ring being Nagata), and every normal modification of `Spec(B)` is dominated as
required by `AlgebraicGeometry.SeparableGoUp.isDominatedByFiniteOverBase`.

## Main results

* `AlgebraicGeometry.SeparableGoUp.isReductionToRationalSingularitiesPossible_integralClosure`:
  reduction to rational singularities is possible for the integral closure of a complete regular
  local ring of dimension two and characteristic `p` in an inseparable extension of degree `p` of
  its fraction field ([Stacks, Tag 0B4U]).

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.SeparableGoUp

/-- **Stacks Project, Tag 0B4U.** Let `p` be a prime number, `A` a complete regular local ring of
dimension two and characteristic `p`, `L/K` an inseparable extension of degree `p` of the
fraction field `K` of `A`, and `B ⊆ L` the integral closure of `A`. Then reduction to rational
singularities is possible for `B`. -/
@[stacks 0B4U]
theorem isReductionToRationalSingularitiesPossible_integralClosure (p : ℕ)
    (hp : p.Prime) (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p] (hdim : ringKrullDim A = 2)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] (hdeg : Module.finrank K L = p)
    (hinsep : ¬ Algebra.IsSeparable K L) :
    IsReductionToRationalSingularitiesPossible (integralClosure A L) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsNormalDomain A := isNormalDomain_of_isRegularLocalRing A
  have : IsNagataRing A := IsNagataRing.of_isPrecomplete_maximalIdeal
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hdeg ▸ hp.pos)
  let B := integralClosure A L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsNormalDomain B := ⟨inferInstance, inferInstance⟩
  have : Module.Finite A B := module_finite_integralClosure_of_isNagataRing K L ‹_›
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr fun x y h =>
    hAL (by rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply])
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalRing B :=
    (Stacks.ResolutionOfSurfaces.isNoetherianCompleteLocalRing_of_finite A B).isLocal
  exact isReductionToRationalSingularitiesPossible_integralClosure_of_frobenius p hp A hdim K L
    hdeg hinsep (definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing A hdim)
    (isDominatedByFiniteOverBase A B (by rw [← Algebra.IsIntegral.ringKrullDim_eq A B, hdim]))

end AlgebraicGeometry.SeparableGoUp

end
