module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.NonvanishingEq
public import StacksFrontier.AlgebraicGeometry.Segre.Morphism

/-!
# The Segre chart is a product of standard opens

`StacksFrontier/AlgebraicGeometry/Segre/Morphism.lean` identifies the chart of the Segre morphism
at the index `k ↔ (i, j)` with `pr₁⁻¹(ℙⁿ)_{Xᵢ} ⊓ pr₂⁻¹(ℙᵐ)_{Yⱼ}`, the two factors being the
*nonvanishing loci* of the coordinate sections of `𝒪(1)`. That identification is not usable by
itself: a nonvanishing locus is not visibly affine and its ring is not visibly a localization.
This file replaces each factor by the **standard open** `D₊(Xᵢ)`, which is both.

The replacement is the equality `(ℙⁿ)_{Xᵢ} = D₊(Xᵢ)`, which is
`Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen` at the homogeneous
coordinate ring: its degree-one covering hypothesis holds there because the standard opens of the
coordinates already cover, which is [Stacks, Tag 01NG]
(`Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top`).

## Main results

* `AlgebraicGeometry.Segre.nonvanishingOpen_coordinateSection_eq_basicOpen`: **the nonvanishing
  locus of the `i`-th coordinate section of `𝒪(1)` on `ℙⁿ_ℤ` is `D₊(Xᵢ)`**, an equality where
  `Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection` gave only `≤`.
* `AlgebraicGeometry.Segre.nonvanishingChart_segreSections_eq_inf_basicOpen`: **the Segre chart
  is `pr₁⁻¹D₊(Xᵢ) ⊓ pr₂⁻¹D₊(Yⱼ)`** — the form in which the two hypotheses of
  `AlgebraicGeometry.Segre.mono_segreMorphism_of_chart` are statements about an open of
  `D₊(Xᵢ) ×_{Spec ℤ} D₊(Yⱼ)` rather than about a locus of nonvanishing.
* `AlgebraicGeometry.Segre.segreMorphism_preimage_standardOpen_eq_inf_basicOpen`: the same for
  the preimage of the target's standard open `D₊(Z_{ij})`.

## Implementation notes

The covering hypothesis is discharged pointwise rather than as an equality of suprema
(`exists_mem_basicOpen_coordinate`): `Opens.mem_iSup` turns Tag 01NG into exactly the existential
the general lemma asks for, and the coordinate is in degree one by
`Stacks.ProjectiveChart.X_mem_degree_one`.

One instance has to be introduced as a local hypothesis rather than left to synthesis, and it is
the wall recorded in `Segre/Morphism.lean`: instance search does not see
`projectiveSpaceAtUniverse n = Proj (coordinateGrading n)`, so the invertibility of `𝒪(1)`
registered at the former spelling is not found at the latter, which is the one the general lemma's
instance argument is stated in. A `have` of that instance at the `Proj` spelling, whose body is the
registered instance and elaborates at default transparency, is the cure; it is the same one that
`iSup_nonvanishingOpen_coordinateSection_eq_top` uses.

No `@[stacks ...]` attribute is attached. The equality of the first result is used inside the
source's proofs of Tag 01N8 and Tag 01NE but is the statement of no tag; the chart identifications
are statements about this repository's `segreMorphism` and not about any tag either.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open CategoryTheory Opposite Limits TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace AlgebraicGeometry.Segre

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every point of `ℙⁿ_ℤ` lies in the standard open of some degree-one element: the standard
opens of the coordinates already cover, by [Stacks, Tag 01NG]. -/
theorem exists_mem_basicOpen_coordinate (n : ℕ)
    (x : ProjectiveSpectrum.top (coordinateGrading.{u} n)) :
    ∃ g, g ∈ coordinateGrading.{u} n 1 ∧
      x ∈ ProjectiveSpectrum.basicOpen (coordinateGrading.{u} n) g := by
  have h := Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n
  have hx : x ∈ (⨆ i : Fin (n + 1),
      Proj.basicOpen (coordinateGrading.{u} n) (MvPolynomial.X i)) := by
    rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨MvPolynomial.X i, Stacks.ProjectiveChart.X_mem_degree_one _ i, hi⟩

/-- **The nonvanishing locus of the `i`-th coordinate section of `𝒪(1)` on `ℙⁿ_ℤ` is the standard
open `D₊(Xᵢ)`.** This is the equality of which
`Stacks.ProjTwistSection.basicOpen_le_nonvanishingOpen_homogeneousSection` is one half; the other
half needs the degree-one covering hypothesis, which on projective space is [Stacks, Tag 01NG]. -/
theorem nonvanishingOpen_coordinateSection_eq_basicOpen (n : ℕ) (i : Fin (n + 1)) :
    Stacks.SheafOfModules.nonvanishingOpen
        (X := (projectiveSpaceAtUniverse.{u} n).toRingedSpace)
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n 1) (coordinateSection.{u} n i)
      = Proj.basicOpen (coordinateGrading.{u} n) (MvPolynomial.X i) := by
  have hinv : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (coordinateGrading.{u} n)).toRingedSpace).property
      (Stacks.ProjTwistSection.twistingModule (coordinateGrading.{u} n) 1) :=
    isInvertible_projectiveSpaceAtUniverseTwistingSheaf_one.{u} n
  exact Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen
    (coordinateGrading.{u} n) _ (Stacks.ProjectiveChart.X_mem_degree_one _ i)
    (exists_mem_basicOpen_coordinate.{u} n)

/-- **The nonvanishing locus of the Segre section `XᵢYⱼ` is `pr₁⁻¹D₊(Xᵢ) ⊓ pr₂⁻¹D₊(Yⱼ)`**: the
identification with a product of nonvanishing loci, with each factor replaced by its
standard open. -/
theorem nonvanishingOpen_segreSection_eq_inf_basicOpen (n m : ℕ) (i : Fin (n + 1))
    (j : Fin (m + 1)) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (segreProduct.{u} n m).toRingedSpace)
        (segreModule.{u} n m) (segreSection.{u} n m i j)
      = (segreFst.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} n) (MvPolynomial.X i))
        ⊓ (segreSnd.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} m)
            (MvPolynomial.X j)) := by
  rw [nonvanishingOpen_segreSection.{u} n m i j,
    nonvanishingOpen_coordinateSection_eq_basicOpen.{u} n i,
    nonvanishingOpen_coordinateSection_eq_basicOpen.{u} m j]

/-- **The `k`-th Segre chart is `pr₁⁻¹D₊(Xᵢ) ⊓ pr₂⁻¹D₊(Yⱼ)`.** This is the chart whose
affineness and whose ring are the two hypotheses of
`AlgebraicGeometry.Segre.mono_segreMorphism_of_chart`. -/
theorem nonvanishingChart_segreSections_eq_inf_basicOpen (n m : ℕ)
    (k : Fin (n * m + n + m + 1)) :
    Stacks.ProjectiveSpaceSections.nonvanishingChart (segreModule.{u} n m)
        (segreSections.{u} n m k)
      = (segreFst.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} n)
            (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).1))
        ⊓ (segreSnd.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} m)
            (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).2)) :=
  nonvanishingOpen_segreSection_eq_inf_basicOpen.{u} n m _ _

/-- **The Segre morphism pulls the standard open `D₊(Z_{ij})` back to
`pr₁⁻¹D₊(Xᵢ) ⊓ pr₂⁻¹D₊(Yⱼ)`**, both factors now standard opens. -/
theorem segreMorphism_preimage_standardOpen_eq_inf_basicOpen (n m : ℕ)
    (k : Fin (n * m + n + m + 1)) :
    segreMorphism.{u} n m ⁻¹ᵁ
        Stacks.ProjectiveSpaceSections.standardOpen.{u} (n * m + n + m) k
      = (segreFst.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} n)
            (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).1))
        ⊓ (segreSnd.{u} n m ⁻¹ᵁ Proj.basicOpen (coordinateGrading.{u} m)
            (MvPolynomial.X (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).2)) := by
  rw [segreMorphism_preimage_standardOpen.{u} n m k,
    ← nonvanishingOpen_segreSection.{u} n m]
  exact nonvanishingOpen_segreSection_eq_inf_basicOpen.{u} n m _ _

end AlgebraicGeometry.Segre

end
