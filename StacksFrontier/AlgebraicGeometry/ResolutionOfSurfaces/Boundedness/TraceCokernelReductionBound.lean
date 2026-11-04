module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelReduction
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to rational singularities in dimension two

Let `A` be a local normal Nagata domain of dimension two with a dualizing module `ω_A`. If some
nonzero `d ∈ A` annihilates the cokernel of the trace map `Γ(X, ω_X) ⟶ ω_A` for every
modification `X ⟶ Spec A` with `X` normal, then reduction to rational singularities is possible
for `A`. The uniform bound on the lengths of the cokernels of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z ⊂ X` cut
out by `d`, follows from `ringKrullDim A = 2` by
`AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`.

## Main results

* `isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero_of_dim_two`:
  reduction to rational singularities is possible for `A`, given the annihilation hypothesis on
  the trace cokernels and `ringKrullDim A = 2`.

## Implementation notes

The statement still carries a datum `D : TraceCokernelDuality A E ωA`, whose field
`matlisDualOfCokernel` is the identification that the source obtains from Grauert-Riemenschneider
vanishing together with duality and local duality.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

/-- Let `A` be a local normal Nagata domain of dimension two with a dualizing module `ω_A`. If
some nonzero `d ∈ A` annihilates the cokernel of the trace map `Γ(X, ω_X) ⟶ ω_A` for every
modification `f : X ⟶ Spec A` with `X` normal, then reduction to rational singularities is
possible for `A`. -/
public theorem isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero_of_dim_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    (hdim : ringKrullDim A = 2)
    (E : ModuleCat.{u} A) (i : Dualizing.residueFieldModule.{u, u} A ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (ωA : ModuleCat.{u} A) (hωA : Stacks.Duality.IsDualizingRingModule A ωA)
    (D : TraceCokernelDuality A E ωA) (d : A) (hd : d ≠ 0)
    (hcoker : ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      ∀ z : ↥ωA ⧸ LinearMap.range (D.trace X f).hom, d • z = 0) :
    IsReductionToRationalSingularitiesPossible A :=
  isReductionToRationalSingularitiesPossible_of_smul_traceCokernel_eq_zero A hdim E i hi ωA hωA
    D d hd hcoker
    (exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdim hd)

end Stacks.ResolutionOfSurfaces

end
