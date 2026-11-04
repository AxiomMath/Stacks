module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishing

/-!
# Descent, Proposition 03DW on the small étale site of an algebraic space, from 03DX (2) alone

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Eleven places
in this tree carry, byte-identically, the uniform hypothesis in the shape of Descent,
Proposition 03DW recalled in the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech`: an epimorphism of
`𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on the sections over
every affine étale chart.

**This file reduces that hypothesis to a single input**: the essential surjectivity of
`(-)ᵃ` on the slice of the small étale site at an affine chart, asked only at the cartesian
modules — the hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`, which is the
essential-surjectivity clause of Descent, Proposition 03DX (2) read on that slice.

**That input is no longer open.**  It is
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurjFromChart.lean`, with no
hypothesis, and
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional` there is
the theorem below with `hEss` supplied.  The eleven places listed under the main result carry a
hypothesis which this theorem proves.

Two steps compose, and both of them are proved:

* the Čech route, `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_univ`,
  which discharges the uniform form of 03DW from the vanishing of the first Čech cohomology
  group of a cartesian module on the finite affine covering families of an affine chart, for
  families indexed at the universe `u` of the schemes;
* the transport of Descent, Lemma 03FJ case (a) to the small étale site of an algebraic space at
  an affine chart, `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_essSurj_at`,
  which proves that vanishing from `hEss` at the one chart and nothing else.

## Main results

* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj`: **the
  uniform form of Descent, Proposition 03DW from `hEss` alone.**

## Implementation notes

The two statements meet with no adapter because the index universe of the covering families is
the same on both sides.  That is what
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ` is for; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSurjectivityFromCech.lean` record why no
isomorphism between the Čech complex of a family and that of a reindexing of it is involved.

The affineness of the chart is spelled `IsAffine (chartScheme W)` in the second input and
`IsAffine ((SmallEtale.toOver … ⋙ BigFppfOver.toScheme …).obj W)` in the first;
`AlgebraicGeometry.Space.chartScheme` is that composite applied to `W`, so the two are the same
proposition and no transport is performed.

`hEss` is asked only of the modules that are `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`,
which is all the Čech route ever supplies it, and so is weaker than the hypothesis of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` itself.

**No `@[stacks]` attribute is claimed.**  The conclusion is Descent, Proposition 03DW and the
hypothesis is a clause of Descent, Proposition 03DX (2) on a site where that clause is not
proved, so tagging either would report an unproved tag as proved.  Tag 03DX is registered, for
the small étale site of a *scheme*, at
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`; the slice of the small
étale site of an algebraic space at a chart is not that site, and
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurj.lean` records what separates
them.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The uniform form of Descent, Proposition 03DW on the small étale site of an algebraic
space, granted the essential surjectivity of `(-)ᵃ` on the slices at affine charts and nothing
else.**

An epimorphism `q` of `𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on
the sections over every affine étale chart, granted that the restriction of every cartesian
`𝒪_F`-module to the slice at an affine chart is isomorphic to some `Mᵃ`.

The conclusion is, verbatim, the hypothesis carried at eleven sites in
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity`,
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj` and
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj`, so this discharges all
eleven from `hEss`.

Nothing else is owed: the local-character argument, the 1-cocycle and its coboundary and the two
uses of the sheaf condition are Cohomology on Sites, Lemma 03F8; the cofinality of the finite
affine covering families is Stacks 04JS; and the Čech vanishing for the coefficients `Mᵃ` is
Descent, Lemma 03FJ case (a) transported to this site. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj
    (hEss : ∀ W : SmallEtale B S hS F, IsAffine (chartScheme W) →
      ∀ K : Modules.{u, u} B S hS F hF, IsCartesianOnAffineCharts K →
        ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent)
          (hM : Presheaf.IsSheaf ((SmallEtale.topology B S hS F).over W)
            (Stacks.Sites.associatedPresheaf (chartScheme W) M
              (SmallEtale.sliceToOver B S hS F W))),
          Nonempty (SmallEtale.sliceModule B S hS F hF W K ≅
            SmallEtale.sliceAssociatedModule B S hS F hF W M hM)) :
    ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)) :=
  surjective_val_app_of_epi_of_kernel_isCartesian_univ (hF := hF)
    fun K hK W hW E hfin haff hcov =>
      SmallEtale.isZero_cechCohomology_succ_of_essSurj_at B S hS F W hW E hfin haff hcov K
        (hEss W hW K hK) 1 Nat.one_pos

end AlgebraicGeometry.Space

end
