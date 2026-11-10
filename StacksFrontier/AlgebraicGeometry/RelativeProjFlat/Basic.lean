module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic

/-!
# Flatness of a relative projective spectrum

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra. If the homogeneous piece `A_n`
is a flat `𝒪_S`-module for all sufficiently large `n`, the structure morphism
`p : Proj_S(A) ⟶ S` is flat.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjFlat.chartCover`: the charts of a relative `Proj` over the
  affine opens of the base, as an open cover.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFlat.flat_projInclusionToOpen`: the chart structure
  morphism over an affine open of the base is flat under eventual flatness of the homogeneous
  pieces.
* `Stacks.AlgebraicGeometry.RelativeProjFlat.flat_toBase`: the structure morphism of a relative
  `Proj` is flat under eventual flatness of the homogeneous pieces.

## Implementation notes

Flatness of a homogeneous piece as an `𝒪_S`-module is `AlgebraicGeometry.IsFlatOver` along the
identity morphism of the base.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFlat

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The chart structure morphisms of a relative `Proj`, as an open cover of it: the chart over an
affine open `U` of the base is an open immersion with image the inverse image of `U`, and the
affine opens of the base cover the base. -/
public def chartCover (P : RelativeProjData A) : P.scheme.OpenCover :=
  Scheme.Cover.mkOfCovers S.affineOpens (fun U ↦ AlgebraicGeometry.Proj (A.grading U.1))
    (fun U ↦ P.chart U.1 U.2) (by
      intro x
      obtain ⟨U, hU, hxU, -⟩ :=
        exists_isAffineOpen_mem_and_subset (X := S) (x := P.toBase x) (U := ⊤) (by trivial)
      refine ⟨⟨U, hU⟩, ?_⟩
      have hx : x ∈ P.toBase ⁻¹ᵁ U := hxU
      rw [← chart_image_top P U hU, Scheme.Hom.image_top_eq_opensRange] at hx
      exact hx)
    fun U ↦ isOpenImmersion_chart P U.1 U.2

/-- Flatness of morphisms of schemes is local on the source. -/
private theorem isZariskiLocalAtSource_flat : IsZariskiLocalAtSource @Flat :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)

/-- The chart structure morphism of a relative `Proj` over an affine open of the base is flat
when the homogeneous pieces of the graded algebra of large enough degree are flat
`𝒪_S`-modules. -/
public theorem flat_projInclusionToOpen (N : ℕ)
    (hflat : ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ)))
    (U : S.Opens) (hU : IsAffineOpen U) :
    Flat (projInclusionToOpen A U hU) := by
  have := isZariskiLocalAtSource_flat.toRespects
  have hdef : projInclusionToOpen A U hU =
      Proj.toSpecZero (A.grading U) ≫
        Spec.map (A.toGradedAlgebra.strZero ⟨U, hU⟩) ≫ hU.isoSpec.inv := rfl
  rw [hdef, ← Category.assoc,
    MorphismProperty.cancel_right_of_respectsIso (P := @Flat) _ hU.isoSpec.inv]
  exact Proj.flat_toSpecZero_comp_of_flat_away_forall (A.grading U) _
    fun m f ↦ A.flat_away U N hflat hU m.2 f.2

/-- If the homogeneous piece `A_n` of a quasi-coherent graded `𝒪_S`-algebra is a flat
`𝒪_S`-module for every sufficiently large `n`, the structure morphism of the relative projective
spectrum of `A` is flat. -/
@[stacks 0D4C "flatness of relative Proj"]
public theorem flat_toBase
    (hflat : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ))) :
    Flat (relativeProj A).toBase := by
  obtain ⟨N, hN⟩ := hflat
  have := isZariskiLocalAtSource_flat
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (chartCover A (relativeProj A))
    fun U ↦ ?_
  change Flat ((relativeProj A).chart U.1 U.2 ≫ (relativeProj A).toBase)
  rw [((relativeProj A).chart_isPullback U.1 U.2).w]
  have := flat_projInclusionToOpen A N hN U.1 U.2
  infer_instance

end Stacks.AlgebraicGeometry.RelativeProjFlat

end
