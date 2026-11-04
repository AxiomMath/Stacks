module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.CurveVanishing
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveSection
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# Ampleness on a proper curve from one section with affine nonvanishing open

A section `s` of an invertible module `𝒫` on a proper curve over a field whose nonvanishing open
`X_s` is nonempty and affine makes `𝒫` ample, and therefore makes ample every invertible module
of which `𝒫` is a positive tensor power. This is the converse half of [Stacks, Tag 0B5X] once
its second paragraph has produced the section.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isAmple_of_isAffineOpen_nonvanishingOpen_of_isCurve`: **`𝒫` is ample.**
  [Stacks, Tag 0B5P] applied to the vanishing of
  `../SectionPowerCohomology/CurveVanishing.lean`.
* `isAmple_of_exists_tensorPower_section_of_isCurve`: **the same conclusion for `𝓛`** when `𝒫`
  is `𝓛^{⊗ n}` for some `n ≥ 1`, by [Stacks, Tag 01PT].
* `isAmple_iff_invertibleCurveDegree_pos`: **[Stacks, Tag 0B5X]** — on a proper curve over a
  field an invertible module is ample exactly when its degree is positive. The forward direction
  is `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isCurve` of `./CurveInputs.lean`
  and the converse is the above, fed by the source's second paragraph.

## The argument

The criterion of [Stacks, Tag 0B5P],
`AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_isZero_h1_quasicoherentIdeal`, asks for every
quasi-coherent submodule `𝒥 ⊆ 𝒪_X` a positive `n` with `H¹(X, 𝒥 ⊗ 𝒫^{⊗ n}) = 0`. On a locally
Noetherian scheme such a submodule is coherent ([Stacks, Tag 01Y1],
`Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono`, whose monomorphism the
criterion hands over as data). So
`AlgebraicGeometry.exists_isZero_cohomologyOverField_one_twist` applies and supplies the
vanishing.

Descending from `𝒫 = 𝓛^{⊗ n}` to `𝓛` is `AlgebraicGeometry.isAmple_iff_tensorPower_isAmple`,
[Stacks, Tag 01PT]: an invertible module is ample exactly when one of its positive tensor powers
is. Running the vanishing argument at `𝒫` rather than at `𝓛` is what avoids comparing
`(𝓛^{⊗ n})^{⊗ m}` with `𝓛^{⊗ nm}`, an identification this library does not have for the
integer-indexed tensor powers.

## Implementation notes

**The two invertibility classes both appear**, as they do throughout this directory:
`AlgebraicGeometry.SheafOfModules.IsInvertible` is what the tensor powers and
`AlgebraicGeometry.Scheme.Modules.IsAmple` are stated for, and
`Stacks.SheafOfModules.IsInvertible` is what the nonvanishing open and the twisted localization
are stated for. They are carried across by
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`.

**The vanishing is stated for `AlgebraicGeometry.cohomologyOverField`** and consumed as a
vanishing of `(moduleGlobalSections X).rightDerived 1`. The two have the same carrier —
restriction of scalars along the structure morphism changes neither — so the transport is the
one of `AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup`, read through
`ModuleCat.isZero_iff_subsingleton`.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingOpen nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.Cohomology.TwistedGradedModule (twist)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A section of an invertible module on a proper curve with nonempty affine nonvanishing open
makes that module ample.** This is the criterion of [Stacks, Tag 0B5P] fed by the `H¹` vanishing
of `../SectionPowerCohomology/CurveVanishing.lean`, which the section supplies for every
quasi-coherent sheaf of ideals. -/
public theorem isAmple_of_isAffineOpen_nonvanishingOpen_of_isCurve [IsCurve k f] [IsProper f]
    (P : X.Modules)
    [hP : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property P]
    (s : P.sections)
    (hne : ∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace) P s)
    (hU : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) P s)) :
    Scheme.Modules.IsAmple X P := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have _ : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property P :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ P hP
  have hdim : topologicalKrullDim X ≤ 1 := le_of_eq (IsCurve.topologicalKrullDim_eq_one f)
  refine Scheme.Modules.isAmple_of_forall_isZero_h1_quasicoherentIdeal P
    fun J ι hmono hJ => ?_
  have hJcoh : _root_.SheafOfModules.IsCoherent J :=
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) J
      (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X) hJ ι hmono
  obtain ⟨N, hN, hz⟩ :=
    exists_isZero_cohomologyOverField_one_twist k f P s hdim hU hne J hJcoh hJ
  exact ⟨N, hN, ModuleCat.isZero_iff_subsingleton.mpr
    (@ModuleCat.subsingleton_of_isZero k _
      (cohomologyOverField k f (twist X P J (N : ℤ)) 1) hz)⟩

/-- **A section of a positive tensor power with nonempty affine nonvanishing open makes the
module itself ample.** The power is ample by
`AlgebraicGeometry.isAmple_of_isAffineOpen_nonvanishingOpen_of_isCurve`, and ampleness descends
along positive tensor powers by [Stacks, Tag 01PT]. -/
public theorem isAmple_of_exists_tensorPower_section_of_isCurve [IsCurve k f] [IsProper f]
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (h : ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      (∃ x : X, x ∈ nonvanishingLocus (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) ∧
        IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    Scheme.Modules.IsAmple X L := by
  obtain ⟨n, hn, s, hne, hU⟩ := h
  refine (isAmple_iff_tensorPower_isAmple X L n hn).mpr ?_
  exact @isAmple_of_isAffineOpen_nonvanishingOpen_of_isCurve k _ X f _ _ _
    (tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s hne hU

/-- **[Stacks, Tag 0B5X].** Let `k` be a field, `X` a proper curve over `k` and `𝓛` an invertible
`𝒪_X`-module. Then `𝓛` is ample if and only if `deg(𝓛) > 0`.

The forward direction is `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple_of_isCurve` of
`./CurveInputs.lean`. The converse composes the source's second paragraph,
`AlgebraicGeometry.hasAffinePowerOfDegreePos_of_isCurve` of `./CurveSection.lean`, with its third,
which enters through `AlgebraicGeometry.isAmple_of_exists_tensorPower_section_of_isCurve` above.

`hdim` is an explicit argument because `AlgebraicGeometry.invertibleCurveDegree` takes the
dimension bound as one; on a curve it is `le_of_eq (IsCurve.topologicalKrullDim_eq_one f)`, and it
is an unused argument of that definition, so any two proofs of it give the same degree. -/
@[stacks 0B5X "both directions, for a proper curve over a field"]
public theorem isAmple_iff_invertibleCurveDegree_pos [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Scheme.Modules.IsAmple X L ↔ 0 < invertibleCurveDegree k f hdim L :=
  ⟨invertibleCurveDegree_pos_of_isAmple_of_isCurve k f hdim L,
    fun hdeg => isAmple_of_exists_tensorPower_section_of_isCurve k f L
      (hasAffinePowerOfDegreePos_of_isCurve k f hdim L hdeg)⟩

end AlgebraicGeometry

end
