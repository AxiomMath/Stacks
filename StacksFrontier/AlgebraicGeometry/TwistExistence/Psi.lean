module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Mul

/-!
# The chart comparison of two twist data commutes with the homogeneous-section maps

The comparison `Stacks.AlgebraicGeometry.TwistExistence.cmp` of two sets of twist data over an
affine chart carries the image of the first datum's homogeneous-section map to the image of the
second's. This is the content of each datum's `ψ_chart` field: under the chart identification the
section map becomes the *absolute* section map of Tag 01MP, which mentions neither datum, so the
two identifications send the two section maps to one and the same thing.

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.chartLoc_psi`: **the chart identification of a twist
  datum carries the image of its homogeneous-section map to the restriction of the absolute
  homogeneous section.** The right-hand side does not mention the datum, which is the whole
  point.
* `Stacks.AlgebraicGeometry.TwistExistence.cmp_psi`: **the chart comparison commutes with the
  homogeneous-section maps.**

## Implementation notes

`ψ_chart` is stated on the sections over the *whole* chart, with the image of the chart
identified with the inverse image of the affine open by a transport along
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData.chart_range`; the comparison is read on
the sections over the inverse image of the affine open, whose preimage in the chart is the whole
chart only up to `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`. So three opens of the relative
Proj occur — the inverse image of the affine open, the image of the chart, and the image of the
preimage of the inverse image — and they are pairwise **equal**.

That is the only difficulty, and it is discharged structurally rather than by transporting:
every map in sight between those three opens is a restriction map of one presheaf, a transport
along an equality of opens is such a restriction map (`PresheafOfModules.rec_eq_map`), and any
two composites of restriction maps between the same pair of opens are the same map, the lattice
of opens being a partial order (`PresheafOfModules.map_map_eq_map`). No `eqToHom` is cancelled by
hand and no motive is ever elaborated.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace PresheafOfModules

/-- **A transport of a section along an equality of opens is a restriction map.** Proved by
substituting the equality away, after which the restriction map is the identity. -/
public theorem rec_eq_map {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} 𝒪) {W W' : Opens X} (h : W = W') (z : M.obj (op W)) :
    (h ▸ z : M.obj (op W')) = M.map (eqToHom h.symm).op z := by
  subst h
  exact (congr($(M.presheaf.map_id (op W)) z)).symm

/-- **Any two composites of restriction maps between the same pair of opens are the same map.**
The lattice of opens of a space is a partial order, so the morphisms involved are unique and the
composite of the first two is the third. -/
public theorem map_map_eq_map {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} 𝒪) {P Q T : Opens X} (i : op P ⟶ op Q) (j : op Q ⟶ op T)
    (k : op P ⟶ op T) (z : M.obj (op P)) : M.map j (M.map i z) = M.map k z := by
  rw [← M.map_comp_apply, Subsingleton.elim (i ≫ j) k]

/-- Two restriction maps between the same pair of opens are the same map. -/
public theorem map_eq_map {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} 𝒪) {P Q : Opens X} (i j : op P ⟶ op Q) (z : M.obj (op P)) :
    M.map i z = M.map j z := by
  rw [Subsingleton.elim i j]

end PresheafOfModules

namespace Stacks.AlgebraicGeometry.TwistExistence

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **The chart identification of a twist datum carries the image of its homogeneous-section map
to the restriction of the absolute homogeneous section of Tag 01MP.** The right-hand side
mentions no twist datum. -/
public theorem chartLoc_psi (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (k : ℕ)
    (a : A.sectionPieces U k) :
    (chartLoc D U hU (k : ℤ)).app ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
        ((D.ψ k).val.app (op U) a) =
      (twistingSheaf (A.grading U) (k : ℤ)).val.map
        (homOfLE (le_top :
          (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤)).op
        (degreeSection (A.grading U) k
          ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩) := by
  have hVle : (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤ := le_top
  refine TwistRigidity.mapSection_injective D.chartData U hU (k : ℤ)
    ((relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) ?_
  have h1 := mapSection_chartLoc D U hU (k : ℤ) ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
    ((D.ψ k).val.app (op U) a)
  have h2 := PresheafOfModules.naturality_apply
    (D.chartData.chartIso U hU (k : ℤ)).inv.val (homOfLE hVle).op
    (degreeSection (A.grading U) k
      ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)
  have h3 := D.ψ_chart U hU k a
  have h4 := PresheafOfModules.rec_eq_map (D.algebra.piece (k : ℤ)).val
    (D.chartData.chart_range U hU).symm ((D.ψ k).val.app (op U) a)
  have h5 := PresheafOfModules.map_map_eq_map (D.algebra.piece (k : ℤ)).val
    (eqToHom (D.chartData.chart_range U hU)).op
    (homOfLE (((relativeProj A).chart U hU).image_mono hVle)).op
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le
      ((relativeProj A).toBase ⁻¹ᵁ U))).op ((D.ψ k).val.app (op U) a)
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine Eq.trans ?_ (congrArg
    ((Scheme.Modules.restrict (D.algebra.piece (k : ℤ))
      ((relativeProj A).chart U hU)).val.map (homOfLE hVle).op) (h3.trans h4)).symm
  exact h5.symm

/-- **The chart comparison of two twist data commutes with the homogeneous-section maps**, on the
sections over the inverse image of the affine open. -/
public theorem cmp_psi (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (k : ℕ)
    (a : A.sectionPieces U k) :
    (cmp D E U hU (k : ℤ)).app ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
        ((D.ψ k).val.app (op U) a) = (E.ψ k).val.app (op U) a :=
  cmp_eq_of_chartLoc_eq D E U hU (k : ℤ) ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
    ((chartLoc_psi E U hU k a).trans (chartLoc_psi D U hU k a).symm)

end Stacks.AlgebraicGeometry.TwistExistence

end
