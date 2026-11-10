module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OneDimensionalFibres

/-!
# Tag 0B4X: cohomology on a normal modification of a rational surface singularity

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity, `S = Spec(A)`, and a modification `f : X ⟶ S` with `X` normal — and for a
quasi-coherent `𝒪_X`-module `ℱ`, [Stacks, Tag 0B4X] asserts

1. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`, and
2. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

The source proves (1) by [Stacks, Tag 02V7] and (2) from (1) by the long exact sequence of a
presentation `⨁_{i ∈ I} 𝒪_X ⟶ ℱ` together with `H¹(X, 𝒪_X) = 0`, which holds because `A` defines
a rational singularity, and the commutation of `H¹(X, -)` with direct sums.

Both clauses are obtained here from
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/OneDimensionalFibres.lean`, which proves them
for an arbitrary proper morphism onto an affine base whose fibres have dimension at most one:
clause (1) is part (3) of [Stacks, Tag 0E7H] and clause (2) is part (4). This file is the
specialisation of those two statements to the situation, and it records precisely which of their
hypotheses the situation still owes.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.isZero_cohomology_of_one_lt`: clause (1).
* `AlgebraicGeometry.RationalSingularitySituation.isZero_cohomology_one_of_generatingSections`:
  clause (2).

## Implementation notes

Cohomology is `Hⁱ(X, ℱ) = ((moduleGlobalSections X).rightDerivedPlus i).obj ℱ`, as in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/OneDimensionalFibres.lean`; "globally
generated" is Mathlib's
`SheafOfModules.GeneratingSections`.

Situation [Stacks, Tag 0B4W] is carried by
`AlgebraicGeometry.RationalSingularitySituation` of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/Basic.lean`.

**No `@[stacks 0B4X]` attribute is attached here**: the two statements below take three inputs of
the source's proof as hypotheses. The tag itself is registered, with all three discharged, on
`…RationalSingularitySituation.isZero_cohomology_of_notMem_zero_one_unconditional` and
`…isZero_cohomology_one_of_globallyGenerated_unconditional` of
`QuasicoherentCohomologyExtra.lean` in this directory. The three are discharged as follows.

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.CohomologyVanishesAboveOne` is the residue of
  [Stacks, Tag 0E7D] at fibre dimension one, equivalently the conclusion of
  [Stacks, Tag 02V7] there. [Stacks, Tag 02V7] is proved in this development for an arbitrary
  fibre dimension, in
  `StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimension.lean`, where
  the theorem on formal functions ([Stacks, Tag 02OD]) and the coherence of the higher direct
  images of a proper morphism are both available. What `CohomologyVanishesAboveOne` asks for
  beyond it is an arbitrary — possibly non-Noetherian — affine base; the base of this situation
  is `Spec(A)` for a Noetherian local ring `A`.
* `hdim`, the bound `dim(X_y) ≤ 1` on every fibre of the modification, is
  `AlgebraicGeometry.RationalSingularitySituation.topologicalKrullDim_fiber_le_natCast_one` of
  `FibreDimension.lean`, which derives it from `dimension_two` and the birationality of `f` by
  [Stacks, Tag 0B2K] at the generic point of `X`.
* `hunit`, the vanishing `H¹(X, 𝒪_X) = 0`, is
  `AlgebraicGeometry.RationalSingularitySituation.isZero_firstCohomologyStructureSheaf` of
  `StructureSheafCohomology.lean`. The situation carries the vanishing through
  `definesRationalSingularity` applied to `f` itself, in Mathlib's `CategoryTheory.Sheaf.H` of
  the abelian sheaf underlying `𝒪_X`, and that file assembles the change of cohomology model,
  [Stacks, Tag 03FD].

## References

* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0B2K](https://stacks.math.columbia.edu/tag/0B2K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (S : RationalSingularitySituation.{u})

/-- **[Stacks, Tag 0B4X] clause (1).** In Situation [Stacks, Tag 0B4W], the cohomology of a
quasi-coherent `𝒪_X`-module vanishes outside degrees `0` and `1`.

This is part (3) of [Stacks, Tag 0E7H] at the modification `f : X ⟶ S`, whose target `Spec(A)` is
affine and which is proper by `AlgebraicGeometry.RationalSingularitySituation.isProper`. The
fibre-dimension bound and the vanishing at `d = 1` are carried as hypotheses; see the
implementation notes of this file. -/
theorem isZero_cohomology_of_one_lt (hcoh : CohomologyVanishesAboveOne.{u})
    (hdim : ∀ y : S.base, topologicalKrullDim (S.f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : S.X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : 1 < p) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus p).obj F) :=
  isZero_cohomology_of_affine_of_fiber_dimension_le_one hcoh S.f hdim F p hp

/-- **[Stacks, Tag 0B4X] clause (2).** In Situation [Stacks, Tag 0B4W], a globally generated
quasi-coherent `𝒪_X`-module has vanishing first cohomology.

This is part (4) of [Stacks, Tag 0E7H] at the modification `f : X ⟶ S`: from the presentation
`⨁_{i ∈ I} 𝒪_X ⟶ ℱ` given by the global generators, clause (1) kills `H²` of the relations and
hence makes `H¹(⨁_{i ∈ I} 𝒪_X) ⟶ H¹(ℱ)` surjective, while `H¹(X, 𝒪_X) = 0` and the commutation
of `H¹(X, -)` with direct sums kill the source.

The hypothesis `hunit` is the source's *"`H¹(X, 𝒪_X) = 0` as `S` has a rational singularity"*;
the situation supplies that vanishing in a different model of cohomology, and the comparison is
not assembled here. -/
theorem isZero_cohomology_one_of_generatingSections (hcoh : CohomologyVanishesAboveOne.{u})
    (hdim : ∀ y : S.base, topologicalKrullDim (S.f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hunit : IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj
      (SheafOfModules.unit S.X.ringCatSheaf)))
    (F : S.X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj F) :=
  isZero_cohomology_one_of_generatingSections_of_fiber_dimension_le_one hcoh S.f hdim hunit F σ

end

end AlgebraicGeometry.RationalSingularitySituation

end
