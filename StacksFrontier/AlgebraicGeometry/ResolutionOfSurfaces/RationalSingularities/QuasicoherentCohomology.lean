module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.Cohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FibreDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.StructureSheafCohomology

/-!
# Tag 0B4X: cohomology of quasi-coherent modules on a normal modification

In Situation [Stacks, Tag 0B4W] — a two-dimensional local normal Nagata domain `A` defining a
rational singularity, `S = Spec(A)`, and a modification `f : X ⟶ S` with `X` normal — and for a
quasi-coherent `𝒪_X`-module `ℱ`, [Stacks, Tag 0B4X] asserts

1. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`, and
2. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

Both clauses are proved here, from a single hypothesis.

`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/Cohomology.lean`
obtains the two clauses from three hypotheses: the vanishing of the cohomology of quasi-coherent
modules above degree one for a proper morphism onto an affine base with one-dimensional fibres,
the fibre-dimension bound `dim(X_y) ≤ 1`, and `H¹(X, 𝒪_X) = 0`. The last two are discharged in
this directory — by `…RationalSingularitySituation.topologicalKrullDim_fiber_le_natCast_one` and
`…RationalSingularitySituation.isZero_firstCohomologyStructureSheaf` — and this file supplies
them, leaving the first as the only hypothesis.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.isZero_cohomology_of_notMem_zero_one`:
  clause (1).
* `AlgebraicGeometry.RationalSingularitySituation.isZero_cohomology_one_of_globallyGenerated`:
  clause (2).

## Implementation notes

Cohomology is `Hⁱ(X, ℱ) = ((moduleGlobalSections X).rightDerivedPlus i).obj ℱ`, and "globally
generated" is Mathlib's `SheafOfModules.GeneratingSections`, whose `π` is the surjection
`⨁_{i ∈ I} 𝒪_X ⟶ ℱ` the source's proof of clause (2) starts from.

Clause (1) is stated at the source's own range `p ∉ {0, 1}` rather than only above degree one.
For an integer that range splits as `p < 0` or `1 < p`; the negative half is
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`, where the derived functor
vanishes for formal reasons, and the positive half is the substance.

**One hypothesis is carried: `h02V7`.** It is the residue of [Stacks, Tag 02V7] at fibre
dimension one, and it is a statement about *every* proper morphism onto an affine base all of
whose fibres have dimension at most one — not about `f`. It is instantiated at `f` inside the
proof. [Stacks, Tag 02V7] is a different result, genuinely absent from this development: its
proof needs Grothendieck vanishing on the fibre ([Stacks, Tag 02UZ], available as
`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`)
*together with* the theorem on formal functions ([Stacks, Tag 02OD]) and the coherence of the
higher direct images of a proper morphism ([Stacks, Tag 02O5]), neither of which is available.

## References

* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0B4X] clause (1).** In Situation [Stacks, Tag 0B4W], the cohomology of a
quasi-coherent `𝒪_X`-module vanishes in every degree outside `{0, 1}`.

Above degree one this is part (3) of [Stacks, Tag 0E7H] at the modification `f`, whose target is
affine and which is proper; the fibre-dimension bound it needs is
`topologicalKrullDim_fiber_le_natCast_one`. Below degree zero the derived functor vanishes for
formal reasons.

The hypothesis `h02V7` is the residue of [Stacks, Tag 02V7] at fibre dimension one, quantified
over all proper morphisms onto an affine base with one-dimensional fibres. -/
@[stacks 0B4X "clause (1); the residue of Tag 02V7 at fibre dimension one, quantified over all \
proper morphisms onto an affine base, is the hypothesis h02V7"]
theorem isZero_cohomology_of_notMem_zero_one (h02V7 : CohomologyVanishesAboveOne.{u})
    (F : S.X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : p ∉ ({0, 1} : Set ℤ)) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus p).obj F) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
  obtain ⟨hp0, hp1⟩ := hp
  rcases lt_or_gt_of_ne hp0 with h | h
  · exact CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg
      (moduleGlobalSections S.X) F p h
  · exact S.isZero_cohomology_of_one_lt h02V7 S.topologicalKrullDim_fiber_le_natCast_one F p
      (by omega)

/-- **[Stacks, Tag 0B4X] clause (2).** In Situation [Stacks, Tag 0B4W], a globally generated
quasi-coherent `𝒪_X`-module has vanishing first cohomology.

From the presentation `⨁_{i ∈ I} 𝒪_X ⟶ ℱ` given by the global generators, clause (1) kills `H²`
of the relations and hence makes `H¹(⨁_{i ∈ I} 𝒪_X) ⟶ H¹(ℱ)` surjective, while
`H¹(X, 𝒪_X) = 0` — which holds because `A` defines a rational singularity, by
`isZero_firstCohomologyStructureSheaf` — and the commutation of `H¹(X, -)` with direct sums kill
the source.

The hypothesis `h02V7` is as in clause (1). -/
@[stacks 0B4X "clause (2); the residue of Tag 02V7 at fibre dimension one, quantified over all \
proper morphisms onto an affine base, is the hypothesis h02V7"]
theorem isZero_cohomology_one_of_globallyGenerated (h02V7 : CohomologyVanishesAboveOne.{u})
    (F : S.X.Modules) [F.IsQuasicoherent] (σ : SheafOfModules.GeneratingSections F) :
    IsZero (((moduleGlobalSections S.X).rightDerivedPlus 1).obj F) :=
  S.isZero_cohomology_one_of_generatingSections h02V7
    S.topologicalKrullDim_fiber_le_natCast_one S.isZero_firstCohomologyStructureSheaf F σ

end AlgebraicGeometry.RationalSingularitySituation

end

end
