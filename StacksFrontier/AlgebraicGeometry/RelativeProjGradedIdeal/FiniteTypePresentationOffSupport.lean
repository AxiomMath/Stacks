module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.VanishingPresentation

/-!
# Cutting out a closed subscheme of a relative `Proj` away from a disjoint open

`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ClosedSubscheme.lean` proves Tag 0803 from
a `…RelativeProjGradedIdeal.VanishingIdealPresentation` — the relative case of Tag 0801 — carried
as an argument, because that file is upstream of the construction of the presentation:
`…RelativeProjGradedIdeal.compactSpace_proj_grading`, which it proves, is what makes a chart of a
quasi-compact relative `Proj` quasi-compact, and the construction of the presentation needs it.

This file supplies the argument. `…RelativeProjTwists.vanishingIdealPresentation` is the
presentation, built with no hypothesis beyond Tag 0803's own, so the statement below is the whole
of Tag 0803.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_presentation_supp`: **Tag
  0803.**

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0802](https://stacks.math.columbia.edu/tag/0802)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)

## Implementation notes

The conclusion of Tag 0803 names the cokernel of the inclusion `ℱ ⟶ 𝒜_d` of a submodule of a
sheaf of modules, and that inclusion lives in `SheafOfModules S.ringCatSheaf` rather than in
`AlgebraicGeometry.Scheme.Modules S`, which is the same category but a different head symbol.
Mathlib's abelian-category instance for a scheme is stated at the second spelling, so
`CategoryTheory.Limits.HasCokernel` is not synthesized at the first; `abelianSheafOfModules`
below supplies it, as a `local instance`, by transporting the one that is found.

The statement is separated from
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/VanishingPresentation.lean` because that
file needs `TopCat.Sheaf` and `CategoryTheory.sheafCompose` made `implicit_reducible` and
`AlgebraicGeometry.ProjectiveSpectrum.top` made `instance_reducible` — without which the chart
identification `…RelativeProjTwists.ChartData.chartIso` cannot be elaborated at all — and those
are not wanted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}}

/-- The category of sheaves of modules over the sheaf of rings of a scheme is abelian, at the
spelling `SheafOfModules S.ringCatSheaf` in which the inclusion of a submodule lives: this is
Mathlib's `Abelian S.Modules`, which is the same category under another head symbol. -/
local instance abelianSheafOfModules (T : Scheme.{u}) :
    Abelian (SheafOfModules.{u} T.ringCatSheaf) :=
  inferInstanceAs (Abelian T.Modules)

/-- **Stacks Project, Tag 0803.** Let `i : Z ⟶ Proj_S(𝒜)` be a closed subscheme of finite
presentation of a quasi-compact relative `Proj` over a quasi-compact quasi-separated base, let
`U` be a quasi-compact open of the base missing the image of `Z`, and let every `𝒜_n` be of
finite type. Then `Z` is the relative `Proj` of the quotient of `𝒜` by the graded ideal generated
by a quasi-coherent finite type submodule `ℱ` of a single homogeneous piece `𝒜_d` with `d > 0`,
and `ℱ` may be chosen so that the support of `𝒜_d/ℱ` is disjoint from `U`.

The relative case of Tag 0801 — the vanishing-ideal presentation that
`…RelativeProjGradedIdeal.exists_finiteType_presentation_supp_of_vanishingIdeal` consumes — is
`…RelativeProjTwists.vanishingIdealPresentation`, so the statement carries no hypothesis beyond
the tag's own. -/
@[stacks 0803]
public theorem exists_finiteType_presentation_supp (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj A).scheme) (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i)
    (hU : (U : Set S) ∩ Set.range (i ≫ (relativeProj A).toBase).base = ∅)
    (hUc : IsCompact (U : Set S))
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ))) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (U : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
              RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ ∧
            Nonempty (DegreeQuotientPresentation A i ℱ) :=
  RelativeProjGradedIdeal.exists_finiteType_presentation_supp_of_vanishingIdeal A i U hi hU hUc hA
    ⟨vanishingIdealPresentation i⟩

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
