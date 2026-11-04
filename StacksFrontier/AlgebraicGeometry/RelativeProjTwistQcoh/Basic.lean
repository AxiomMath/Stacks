module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent

/-!
# Quasi-coherence of the glued twists on a relative projective spectrum is free

Tag 01NR asks for a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, whose second field
is quasi-coherence of every homogeneous piece of the glued graded algebra. This file proves that
that field is **redundant**: it is implied by the fourth field, the chart identifications
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData`, and by nothing else.

So whoever constructs the twist data owes seven fields, not eight, and owes nothing about
presentations of the glued pieces.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`: the inverse image of an
  affine open `U` of the base, as a scheme, identified with the absolute projective spectrum
  `Proj Γ(A, U)` of the section ring — compatibly with the chart, which is the only thing the
  comparison below needs of it.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.isQuasicoherent_piece`: given a `ChartData`
  for a graded algebra on a relative Proj, every homogeneous piece of that algebra is
  quasi-coherent. No hypothesis on the base scheme, no hypothesis on the graded algebra of the
  base, and no multiplicative compatibility of the chart identifications.
* `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.opensRange_chart`: the range of a chart is the
  inverse image of its affine open, which is
  `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top` read as an `opensRange`.

## The route

Quasi-coherence is local on the base (`Stacks.Modules.isQuasicoherent_of_restrict`), and the
inverse images of the affine opens of the base cover the relative Proj
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`). Over one of
them the glued piece restricts, along the **chart**, to an absolute twist
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`, which is quasi-coherent because
`twistingSheaf` is an `associatedModuleSheaf` and Tag 01MB's
`AlgebraicGeometry.ProjectiveSpectrum.Proj.ProjGraded.associatedModuleSheaf_isQuasicoherent`
is an instance.

The one step that is not immediate is that the locality lemma is stated for restriction along
the inclusion `W.ι` of an open subscheme, while a `ChartData` gives the restriction along the
chart. The two agree because the chart is an open immersion whose range is exactly `W`
(`opensRange_chart`), so `AlgebraicGeometry.Scheme.Hom.isoOpensRange` and
`AlgebraicGeometry.Scheme.isoOfEq` build an isomorphism `W ≅ Proj Γ(A, U)` over the relative
Proj, and `AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver` compares the two
restrictions along it.

## What is not done here

Nothing about the **existence** of a `TwistData` is proved, and no `stacks` attribute is
attached in this file: Tag 01NR's existence assertion asks for the graded algebra itself, its
multiplication and unit, the chart identifications, and the homogeneous-section map with its
three compatibilities. This file removes one field from that list and leaves the other seven.
In particular the remaining obligation of
`StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean`,
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`, is untouched and is not
needed here — the argument below is about an arbitrary `ChartData` and never looks at a
transition between two charts.

The other two fields that are plausibly derivable from the chart data, `mul_comm` and the
degreewise commutativity it would need, are not derived.

## Implementation notes

Three elaboration points, all instances of the `def`-versus-`abbrev` hazard, since
`AlgebraicGeometry.Scheme.Modules` is a `def` while the pieces of a
`Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra` are typed over the ring sheaf
of a ringed site.

* `algebra.piece n` is a `CategoryTheory.SheafOfModules`, so the dot-notation `.restrict` does
  not resolve; `AlgebraicGeometry.Scheme.Modules.restrict` must be written out.
* Because its type does not mention `Scheme.Modules` syntactically, the ambient scheme is still
  a metavariable when `AlgebraicGeometry.Scheme.Modules.restrict`'s `[IsOpenImmersion]` argument
  and `restrictIsoOfIsoOver`'s are searched for, and both searches fail. The scheme is therefore
  supplied by name (`(X := _)`, `(Y := _)`), and the open-immersion instance for the chart is
  supplied as a `letI`. For the same reason `Stacks.Descent.isQuasicoherent_of_iso` is applied
  with its scheme named: without it the argument is checked against an unassigned metavariable
  at the wrong universe.
* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` is keyed on
  `P.chart U hU` with the two arguments separate, so the index of the cover is destructured
  before the chart is mentioned.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.RelativeProjTwistQcoh

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The range of the chart over an affine open `U` of the base is the inverse image of `U` under
the structure morphism of the relative Proj. -/
public theorem opensRange_chart (U : S.Opens) (hU : IsAffineOpen U) :
    ((relativeProj A).chart U hU).opensRange = (relativeProj A).toBase ⁻¹ᵁ U := by
  simpa using RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU

/-- The inverse image of an affine open `U` of the base, as a scheme, identified with the
absolute projective spectrum of the section ring over `U`. -/
public def chartIsoPreimage (U : S.Opens) (hU : IsAffineOpen U) :
    ((relativeProj A).toBase ⁻¹ᵁ U : Scheme.{u}) ≅ AlgebraicGeometry.Proj (A.grading U) :=
  ((relativeProj A).scheme.isoOfEq (opensRange_chart U hU)).symm ≪≫
    ((relativeProj A).chart U hU).isoOpensRange.symm

/-- The identification of the inverse image with the absolute projective spectrum is an
identification **over** the relative Proj: following it with the chart is the inclusion of the
inverse image. -/
public theorem chartIsoPreimage_hom_comp (U : S.Opens) (hU : IsAffineOpen U) :
    (chartIsoPreimage (A := A) U hU).hom ≫ (relativeProj A).chart U hU =
      ((relativeProj A).toBase ⁻¹ᵁ U).ι := by
  simp [chartIsoPreimage]

/-- **Quasi-coherence of the glued twists is free from the chart identifications.** If a graded
algebra on a relative Proj carries a `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` —
that is, if each of its homogeneous pieces restricts on every affine chart to the absolute twist
that chart carries — then each of its homogeneous pieces is quasi-coherent.

This is the `isQuasicoherent` field of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, derived from the `chartData` field
alone. -/
public theorem isQuasicoherent_piece
    {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (D : ChartData A algebra) (n : ℤ) : (algebra.piece n).IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict (algebra.piece n)
    (fun U : S.affineOpens => (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)) ?_
  intro i
  obtain ⟨U, hU⟩ := i
  have : IsOpenImmersion ((relativeProj A).chart U hU) :=
    RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) U hU
  have htw : (twistingSheaf (A.grading U) n).IsQuasicoherent := inferInstance
  have hqc := Stacks.Descent.isQuasicoherent_of_iso
    (X := AlgebraicGeometry.Proj (A.grading U)) (D.chartIso U hU n).symm htw
  have hqc' : (Scheme.Modules.restrict (Scheme.Modules.restrict (algebra.piece n)
      ((relativeProj A).chart U hU)) (chartIsoPreimage (A := A) U hU).hom).IsQuasicoherent := by
    have := hqc
    infer_instance
  exact Stacks.Descent.isQuasicoherent_of_iso
    (restrictIsoOfIsoOver (X := (relativeProj A).scheme)
      (Y := AlgebraicGeometry.Proj (A.grading U))
      (algebra.piece n) ((relativeProj A).chart U hU)
      ((relativeProj A).toBase ⁻¹ᵁ U)
      (chartIsoPreimage (A := A) U hU)
      (chartIsoPreimage_hom_comp U hU)) hqc'

end Stacks.AlgebraicGeometry.RelativeProjTwistQcoh

end
