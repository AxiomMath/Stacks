module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFlatteningDomination
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFiniteCase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsLength
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction to rational singularities goes up a finite separable extension

Let `A ⟶ B` be a finite injective local map of local normal Nagata domains of dimension two
whose extension of fraction fields `L/K` is separable. If reduction to rational singularities is
possible for `A`, it is possible for `B`.

The source argues as follows. Separability makes the trace pairing of `L/K` nondegenerate, so
there are `b₁, …, bₙ, e₁, …, eₙ ∈ B` and a nonzero `d ∈ A` with `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` for all
`σ ∈ L` (`Stacks.Trace.exists_traceIdentity`). A normal modification `Y ⟶ Spec B` is dominated by
a normal modification `Y'` finite over a normal modification `X'` of `Spec A`
(`AlgebraicGeometry.SeparableGoUp.exists_isFinite_dominating_of_isModification`, through
[Stacks, Tag 0B49]), and `H¹(Y, 𝒪_Y)` injects into `H¹(Y', 𝒪_{Y'})` ([Stacks, Tag 0AXF]). On `Y'`
the trace `π_*𝒪_{Y'} ⟶ 𝒪_{X'}` and the identity above bound the length of `H¹(Y', 𝒪_{Y'})` by `n`
copies of `H¹(X', 𝒪_{X'})` together with its `d`-torsion
(`AlgebraicGeometry.SeparableGoUp.length_firstCohomology_le_of_isFinite`), and the `d`-torsion is
bounded uniformly by [Stacks, Tag 0AXJ] and [Stacks, Tag 0AXK].

## Main results

* `Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable`
  is [Stacks, Tag 0AXL].

## Implementation notes

The lengths of the `d`-torsion are bounded over `B`, while the finite case measures lengths over
`A`; over the finite local map `A ⟶ B` the two differ by the factor `[κ_B : κ_A]`, which is why it
appears in the bound.

The finite dimensionality of `L` over `K` is not assumed: `B` is normal and integral over `A`, so
it is the integral closure of `A` in `L`, and `L` is the localization of `B` at the nonzero
elements of `A`.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0BIL](https://stacks.math.columbia.edu/tag/0BIL)
* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

/-- Let `A ⟶ B` be a finite injective local map of local normal
Nagata domains of dimension two, let `K` and `L` be their fraction fields and assume `L/K`
separable. If reduction to rational singularities is possible for `A`, it is possible for `B`. -/
@[stacks 0AXL]
theorem isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
    [CommRing B] [IsLocalRing B] [IsNormalDomain B] [IsNagataRing B]
    [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    (K L : Type u) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra.IsSeparable K L]
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hinj : Function.Injective (algebraMap A B))
    (hA : IsReductionToRationalSingularitiesPossible A) :
    IsReductionToRationalSingularitiesPossible B := by
  have : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed B A L
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  obtain ⟨n, b, e, d, hd0, hid⟩ := Stacks.Trace.exists_traceIdentity A B K L
  have hdB : algebraMap A B d ≠ 0 := fun h => hd0 (hinj (h.trans (map_zero _).symm))
  obtain ⟨NT, hNT⟩ := exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdimB hdB
  obtain ⟨NA, hNA⟩ := hA
  refine ⟨n * NA + NT * Module.finrank (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B), fun Y _ g hg => ?_⟩
  have : IsIntegral Y := hg.source_isIntegral
  obtain ⟨Y', X', g', f', π, q, hY', hX', hg', hf', hq, hπ, hπs, hcomm, hqg⟩ :=
    SeparableGoUp.exists_isFinite_dominating_of_isModification hdimA hdimB hinj g hg
  have : IsIntegral Y' := hg'.source_isIntegral
  have : IsIntegral X' := hf'.source_isIntegral
  have h₁ := SeparableGoUp.length_firstCohomology_le_of_isModification g q hq
  rw [hqg] at h₁
  have h₂ : Module.length B (firstCohomologyAsBaseModule Y' g') ≤
      Module.length A ((ModuleCat.restrictScalars (algebraMap A B)).obj
        (firstCohomologyAsBaseModule Y' g')) :=
    Module.length_le_length_restrictScalars A B (algebraMap A B) _
  have h₃ := SeparableGoUp.length_firstCohomology_le_of_isFinite b e d hid f' g' π
    hf'.isBirational hg'.isBirational hcomm
  have h₄ := SeparableGoUp.length_restrictScalars_torsionBy_le
    (firstCohomologyAsBaseModule Y' g') d
  have h₅ : Module.length B (Submodule.torsionBy B (firstCohomologyAsBaseModule Y' g')
      (algebraMap A B d)) ≤ NT := by
    rw [← length_quotient_baseToZeroSchemeSections_eq Y' g' hg' hdB]
    exact hNT Y' g' hg'
  refine h₁.trans (h₂.trans (h₃.trans ?_))
  rw [h₄, Module.length_eq_finrank]
  push_cast
  gcongr
  exact hNA X' f' hf'

end Stacks.ResolutionOfSurfaces

end
