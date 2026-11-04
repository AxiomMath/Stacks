module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.RaynaudGrusonFlattening0815

/-!
# Stacks 0815 from its affine case

[Stacks, Tag 0815] is the Raynaud–Gruson flattening theorem, stated in this development as
`AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` (for the structure sheaf) in
`StacksFrontier.AlgebraicGeometry.Flatness.RaynaudGrusonFlattening0815`. Its proof begins by
reducing to the case of affine `S` and affine `X`, by [Stacks, Tag 0814]; that reduction is
proved, as
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`,
and it leaves `AlgebraicGeometry.AffineChartFlatteningCentre` — the affine case, read on the
affine charts of the datum.

This file closes the distance from there, so that the statement of 0815 for the structure sheaf
follows from the affine case and nothing else. What it has to cross is a difference of spelling:
the
affine-chart descent is stated for the strict transform taken along `AlgebraicGeometry.blowUp`,
the relative `Proj` of the Rees algebra sheaf, and `AlgebraicGeometry.HasFlatteningBlowup` is
stated for the one taken along `Stacks.Blowup.blowUp`, the gluing of the `Proj` of the ordinary
Rees algebras. The two blowups are isomorphic over `S`, and
`StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformComparison` identifies their strict
transforms compatibly with the projections to the blowup, so the two flatness assertions are the
same assertion.

The consequence worth recording is that nothing between 0ETR and the Raynaud–Gruson induction is
missing: `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_affineChartFlatteningCentre` in
`StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification` derives Stacks 0ETR from
`AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre` alone, and
`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811` proves that
predicate from Stacks 0811.

## Main definitions

* `AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre`: the affine case of the
  flatness assertion of [Stacks, Tag 0815] for the structure sheaf, quantified over the same data
  as `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup`. This is the Raynaud–Gruson
  induction on the maximum over the base of the dimension of the support of a fibre, and it is
  the only input of 0815 that this file does not supply; it is proved as
  `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` in
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811`.

## Main results

* `AlgebraicGeometry.flat_strictTransformMap_iff_flat_strictTransformToBlowUp`: the strict
  transforms of `X` along the two constructions of the blowup are flat together.
* `AlgebraicGeometry.finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre`:
  **[Stacks, Tag 0815] for the structure sheaf, from its affine case.**

## Implementation notes

The library's morphism form of the flattening theorem,
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` ([Stacks, Tag 081R]), is *not*
what is used here, because its hypotheses are not those of 0815: it asks for `f` of finite type
and quasi-separated, while 0815 asks only for `X` quasi-compact and `f` locally of finite
presentation, and nothing makes `f` quasi-separated under the latter. So the affine-chart descent
is applied directly, and `AlgebraicGeometry.flat_strictTransformToBlowUp_iff` — which carries no
hypotheses — converts its module-level conclusion into flatness of a morphism.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData)

/-- **The two strict transforms of `X` along the two constructions of the blowup are flat
together.** `AlgebraicGeometry.strictTransformToBlowUp` is the structure morphism of the strict
transform taken along `AlgebraicGeometry.blowUpToBase`, the relative `Proj` of the Rees algebra
sheaf, and `Stacks.Blowup.strictTransformMap` is the one taken along
`Stacks.Blowup.blowUpToBase`, the gluing of the `Proj` of the ordinary Rees algebras. The two
are identified over `S` by `Stacks.Blowup.strictTransformIso`, compatibly with the projections to
the blowup through `AlgebraicGeometry.blowUpIso`, so each is the other conjugated by
isomorphisms. -/
theorem flat_strictTransformMap_iff_flat_strictTransformToBlowUp :
    Flat (Stacks.Blowup.strictTransformMap f I) ↔ Flat (strictTransformToBlowUp f I) := by
  have _ : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have key : (Stacks.Blowup.strictTransformIso f I).hom ≫ Stacks.Blowup.strictTransformMap f I =
      strictTransformToBlowUp f I ≫ (blowUpIso I).hom :=
    (Stacks.Blowup.strictTransformIso_hom_strictTransformMap f I).trans
      (Category.assoc _ _ _).symm
  rw [← MorphismProperty.cancel_left_of_respectsIso @Flat
    (Stacks.Blowup.strictTransformIso f I).hom (Stacks.Blowup.strictTransformMap f I), key,
    MorphismProperty.cancel_right_of_respectsIso @Flat (strictTransformToBlowUp f I)
      (blowUpIso I).hom]

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815] for the structure sheaf**,
quantified over the same data as `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup`
itself: for every datum `f : X ⟶ S` and `U ⊆ S` to which that statement applies, the centres
`AlgebraicGeometry.AffineChartFlatteningCentre` asks for on the affine charts of `f` exist.

This is the Raynaud–Gruson induction on the maximum over `S` of the dimension of the support of a
fibre, and it is the only input [Stacks, Tag 0815] needs beyond this file:
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre` derives
the full statement from it, and
`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811` proves it from
[Stacks, Tag 0811]. -/
def FinitePresentationHasAffineChartFlatteningCentre : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) [CompactSpace X] [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f], IsCompact (U : Set S) →
    Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) → AffineChartFlatteningCentre f X.unitModule U

/-- **Stacks 0815 from its affine case.** Granted the affine case of the flatness assertion for
the structure sheaf, `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` holds in full.

Both steps are in the library. [Stacks, Tag 0814] descends the flattening question along the
étale squares cut out by the affine charts, which is
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`;
and `AlgebraicGeometry.flat_strictTransformToBlowUp_iff` reads flatness over the blowup of the
strict transform of `𝒪_X` as flatness of the strict transform of `X`, which
`AlgebraicGeometry.flat_strictTransformMap_iff_flat_strictTransformToBlowUp` transports to the
spelling the statement of 0815 uses.

Nothing beyond the hypotheses of 0815 is assumed. In particular the quasi-compactness and
quasi-separatedness of `f` that [Stacks, Tag 081R]
(`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`) carries are not needed: that
tag's hypotheses are not those of 0815, and the descent is applied here directly. -/
theorem finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre
    (H : FinitePresentationHasAffineChartFlatteningCentre.{u}) :
    FinitePresentationHasFlatteningBlowup.{u} := by
  intro X S f U hX hS hqsS hlfp hUcpt hflat
  have _ := hX
  have _ := hS
  have _ := hqsS
  have _ := hlfp
  obtain ⟨I, hIfp, hIdisj, -, hIflat⟩ :=
    AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver f X.unitModule U
      hUcpt (@H X S f U hX hS hqsS hlfp hUcpt hflat)
  exact ⟨I, hIfp, hIdisj,
    (flat_strictTransformMap_iff_flat_strictTransformToBlowUp f I).mpr
      ((flat_strictTransformToBlowUp_iff f I).mpr hIflat)⟩

end AlgebraicGeometry

end
