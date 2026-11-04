module

public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpDomination
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization

/-!
# [Stacks, Tag 0AXL] from the reduction step and [Stacks, Tag 0AXJ]

Let `A → B` be a finite injective local map of local normal domains whose extension of fraction
fields is separable. Granted

* the conclusion of [Stacks, Tag 0AXJ] for `B` (a uniform bound, over the normal modifications
  `Y` of `Spec B`, on the length of the cokernel of `B ⟶ H⁰(Z, 𝒪_Z)` for `Z ⊂ Y` cut out by a
  nonzero element), and
* the reduction step `IsDominatedByFiniteOverBase A B`,

reduction to rational singularities possible for `A` implies it for `B`.

The trace identity is `Stacks.Trace.exists_traceIdentity`, and the bound on the cokernels becomes
a bound on the torsion of `H¹(Y, 𝒪_Y)` by [Stacks, Tag 0AXK],
`AlgebraicGeometry.length_quotient_baseToZeroSchemeSections_eq`.

## Main results

In the namespace `AlgebraicGeometry.SeparableGoUp`:

* `isReductionToRationalSingularitiesPossible_of_isDominated`.
* `isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable`: [Stacks, Tag 0AXL].

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SeparableGoUp

/-- **[Stacks, Tag 0AXL], granted the reduction step and the conclusion of [Stacks, Tag 0AXJ]
for `B`.** Let `A → B` be a finite injective local map of local normal domains with separable
extension of fraction fields. If every normal modification of `Spec B` is dominated by one finite
over a normal modification of `Spec A`, and the cokernels of `B ⟶ H⁰(Z, 𝒪_Z)` have uniformly
bounded length for every nonzero `a ∈ B`, then reduction to rational singularities possible for
`A` implies it for `B`. -/
theorem isReductionToRationalSingularitiesPossible_of_isDominated (A B : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [CommRing B] [IsLocalRing B] [IsNormalDomain B]
    [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (hsep : letI := FractionRing.liftAlgebra A (FractionRing B)
      Algebra.IsSeparable (FractionRing A) (FractionRing B))
    (hbound : ∀ a : B, a ≠ 0 → ∃ N : ℕ, ∀ (Y : Scheme.{u}) [IsNormal Y]
      (g : Y ⟶ Spec (.of B)), IsModification g →
        Module.length B (globalSectionsAsBaseModule Y g (zeroSchemeStructureSheaf Y g a) ⧸
          LinearMap.range (baseToZeroSchemeSections Y g a)) ≤ N)
    (hdom : IsDominatedByFiniteOverBase A B)
    (hA : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B := by
  let := FractionRing.liftAlgebra A (FractionRing B)
  have := hsep
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  obtain ⟨n, b, e, d, hd, hid⟩ :=
    Stacks.Trace.exists_traceIdentity A B (FractionRing A) (FractionRing B)
  have hd' : algebraMap A B d ≠ 0 := fun h =>
    hd ((FaithfulSMul.algebraMap_injective A B) (h.trans (map_zero _).symm))
  obtain ⟨N, hN⟩ := hbound _ hd'
  refine isReductionToRationalSingularitiesPossible_of_dominated A B b e d
    (fun K L _ _ _ _ _ _ _ _ _ _ σ => hid K L σ) ⟨N, fun Y _ g hg => ?_⟩ hdom hA
  rw [← length_quotient_baseToZeroSchemeSections_eq Y g hg hd']
  exact hN Y g hg

/-- **[Stacks, Tag 0AXL], granted the reduction step.** Let `A → B` be a finite injective local
map of local normal domains, `B` Nagata of dimension two, with separable extension of fraction
fields. If every normal modification of `Spec B` is dominated by one finite over a normal
modification of `Spec A`, then reduction to rational singularities possible for `A` implies it
for `B`: the bound on the cokernels of `B ⟶ H⁰(Z, 𝒪_Z)` is [Stacks, Tag 0AXJ]
(`AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`). -/
theorem isReductionToRationalSingularitiesPossible_of_isSeparable (A B : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [CommRing B] [IsLocalRing B] [IsNormalDomain B]
    [IsNagataRing B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)] (hdimB : ringKrullDim B = 2)
    (hsep : letI := FractionRing.liftAlgebra A (FractionRing B)
      Algebra.IsSeparable (FractionRing A) (FractionRing B))
    (hdom : IsDominatedByFiniteOverBase A B)
    (hA : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B :=
  isReductionToRationalSingularitiesPossible_of_isDominated A B hsep
    (fun _ ha => exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdimB ha) hdom hA

/-- **Stacks Project, Tag 0AXL.** Let `A → B` be a finite injective local ring map of local normal
Nagata domains of dimension two such that the induced extension of fraction fields is separable.
If reduction to rational singularities is possible for `A`, then it is possible for `B`. -/
@[stacks 0AXL]
theorem isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable (A B : Type u)
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] [CommRing B]
    [IsLocalRing B] [IsNormalDomain B] [IsNagataRing B] [Algebra A B] [Module.Finite A B]
    [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] (_hdimA : ringKrullDim A = 2)
    (hdimB : ringKrullDim B = 2)
    (hsep : letI := FractionRing.liftAlgebra A (FractionRing B)
      Algebra.IsSeparable (FractionRing A) (FractionRing B))
    (hA : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B :=
  isReductionToRationalSingularitiesPossible_of_isSeparable A B hdimB hsep
    (isDominatedByFiniteOverBase A B hdimB.le) hA

end AlgebraicGeometry.SeparableGoUp

end
