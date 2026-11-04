module

public import StacksFrontier.AlgebraicGeometry.TwistDataFromChart.MapSection
public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents

/-!
# Reading the absolute degree-one section of a Proj chart on the relative twist

On the chart over an affine open `B` of the base, the glued twist `𝒪(n)` of relative Proj is
identified with the absolute twist of `Proj Γ(B, A)`
(`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chartIso`), and the identification acts on
sections by `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.mapSection`. The library stated
the identification of sections at two places only: at the whole chart, by
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart`, and in the direction out of the
glued twist, by `Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_chartPull`. Each of the two
assertions proved here moves one of those onto an *arbitrary* open of the chart, using the
compatibilities of `StacksFrontier.AlgebraicGeometry.TwistDataFromChart.MapSection`.

Together they say that over a small enough open the comparison turns the equation
"`t` is an `𝒪`-multiple of the degree-one section of `a`" on the chart into the same equation on
relative Proj, which is what local generation of `𝒪(1)` by the sections of Stacks 01OB comes down
to.

## Main results

* `Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_res_chartPull`: a section of the glued
  twist over `U`, pulled onto the chart and restricted to an open `V` of the chart lying over `U`,
  is carried back by the comparison to the restriction of the section to the image of `V`.
* `Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_degreeOneSection`: the comparison carries
  the absolute degree-one section of a homogeneous section `b` of degree one, read over any open
  `V` of the chart inside the standard open where it is defined, to the restriction of the
  homogeneous-section map's value `ψ₁(b)` — the section of Stacks 01OB attached to `b`.

## Implementation notes

**The degree index is spelled `(1 : ℤ)` here and `((1 : ℕ) : ℤ)` by the twist datum.**
`TwistData.ψ_chart` takes a natural-number degree and states the comparison at its coercion; the
two indices are definitionally equal, but `rw` does not see through the coercion, so `ψ_chart` is
consumed by `exact` against a `have` stated at the index this file uses. The same point, for the
index `(1 : ℤ) * ((1 : ℕ) : ℤ)` of
`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection`, is recorded in the implementation
notes of that file.

**Two restriction maps between the same pair of opens are the same map**, because a morphism of
`TopologicalSpace.Opens` between fixed opens is unique; this is what lets the composite restriction
produced by the two compatibilities be presented at whatever proof of the inequality the caller
holds. `piece_map_map` and `piece_map_eqRec` are the two forms of that collapse used below.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistDataFromChart

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}
  {algebra : SchemeGradedAlgebra (relativeProj A).scheme}

/-! ### Collapsing successive restrictions of a homogeneous piece -/

/-- Two successive restrictions of a section of a homogeneous piece are the restriction to the
smaller open. -/
public theorem piece_map_map (n : ℤ) {U V Z : (relativeProj A).scheme.Opens} (h₁ : V ≤ U)
    (h₂ : Z ≤ V) (x : (algebra.piece n).val.obj (op U)) :
    (algebra.piece n).val.map (homOfLE h₂).op ((algebra.piece n).val.map (homOfLE h₁).op x) =
      (algebra.piece n).val.map (homOfLE (h₂.trans h₁)).op x := by
  rw [Stacks.SectionsComponents.val_map_map,
    Subsingleton.elim (homOfLE h₂ ≫ homOfLE h₁) (homOfLE (h₂.trans h₁))]

/-- Restricting a section transported along an equality of opens is restricting the section
itself. -/
public theorem piece_map_eqRec (n : ℤ) {U U' : (relativeProj A).scheme.Opens} (h : U = U')
    (x : (algebra.piece n).val.obj (op U)) {V : (relativeProj A).scheme.Opens} (hV : V ≤ U') :
    (algebra.piece n).val.map (homOfLE hV).op (h ▸ x) =
      (algebra.piece n).val.map (homOfLE (hV.trans h.ge)).op x := by
  subst h; rfl

/-! ### The comparison on an arbitrary open of the chart -/

/-- **The chart comparison undoes the chart pull on any open of the chart over `U`.** This is
`Stacks.AlgebraicGeometry.TwistDataFromChart.mapSection_chartPull` with the open of the chart
allowed to be smaller than the whole preimage of `U`. -/
public theorem mapSection_res_chartPull (D : ChartData A algebra) (B : S.Opens)
    (hB : IsAffineOpen B) [IsOpenImmersion ((relativeProj A).chart B hB)] (n : ℤ)
    (U : (relativeProj A).scheme.Opens) (t : (algebra.piece n).val.obj (op U))
    (V : (AlgebraicGeometry.Proj (A.grading B)).Opens)
    (hV : V ≤ (relativeProj A).chart B hB ⁻¹ᵁ U)
    (hVU : (relativeProj A).chart B hB ''ᵁ V ≤ U) :
    D.mapSection B hB n V
        ((twistingSheaf (A.grading B) n).val.map (homOfLE hV).op (chartPull D B hB n U t)) =
      (algebra.piece n).val.map (homOfLE hVU).op t := by
  rw [mapSection_res D B hB n hV, mapSection_chartPull,
    piece_map_map n (((relativeProj A).chart B hB).image_preimage_le U)
      (Scheme.Hom.image_mono ((relativeProj A).chart B hB) hV)]

/-- **The comparison carries the absolute degree-one section to the Stacks 01OB section.** For a
homogeneous section `b` of degree one over an affine open `B` of the base, the absolute degree-one
section of `b` on a standard open of the chart is carried by the chart comparison to the
restriction of `ψ₁(b)`, the value of the twist datum's homogeneous-section map.

This is `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart` with the open of the chart
allowed to be any open on which the absolute section is defined, rather than the whole chart. -/
public theorem mapSection_degreeOneSection (D : TwistData A) (B : S.Opens) (hB : IsAffineOpen B)
    [IsOpenImmersion ((relativeProj A).chart B hB)]
    (b : A.sectionPieces B 1) {f : A.sectionRing B} (hf : f ∈ A.grading B 1)
    (hbf : DirectSum.of (A.sectionPieces B) 1 b = f)
    {V : (AlgebraicGeometry.Proj (A.grading B)).Opens}
    (hV : V ≤ ProjectiveSpectrum.basicOpen (A.grading B) f)
    (hVB : (relativeProj A).chart B hB ''ᵁ V ≤ (relativeProj A).toBase ⁻¹ᵁ B) :
    D.chartData.mapSection B hB 1 V
        (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection (A.grading B) hf hV) =
      (D.algebra.piece 1).val.map (homOfLE hVB).op ((D.ψ 1).val.app (op B) b) := by
  have hψ : D.chartData.mapSection B hB 1 ⊤ (degreeSection (A.grading B) 1 ⟨f, hf⟩) =
      (D.chartData.chart_range B hB).symm ▸ ((D.ψ 1).val.app (op B) b) := by
    rw [show (⟨f, hf⟩ : { x // x ∈ A.grading B 1 }) =
        ⟨DirectSum.of (A.sectionPieces B) 1 b, A.of_mem_grading B b⟩ from Subtype.ext hbf.symm]
    exact D.ψ_chart B hB 1 b
  refine Eq.trans (mapSection_res D.chartData B hB 1 (le_top (a := V))
    (degreeSection (A.grading B) 1 ⟨f, hf⟩)) ?_
  rw [hψ]
  exact piece_map_eqRec 1 (D.chartData.chart_range B hB).symm _ _

end Stacks.AlgebraicGeometry.TwistDataFromChart

end
