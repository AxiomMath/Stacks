module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.IntegralModel
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TautologicalMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ChartSection
public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality

/-!
# The projective bundle of a free module is a projective tower

Let `U` be a scheme and `P = 𝐏(𝒪_U^{n+1}) = Proj_U(Sym(𝒪_U^{n+1}))` with its projection
`π : P ⟶ U` and its twist `𝒪_P(1)`, the degree-one piece of the canonical twist datum of
Tag 01NR. This file proves that `(π, 𝒪_P(1))` is a projective tower of fibre dimension `n`
(`Stacks.Chow.IsProjectiveTower`), which is the input the projective space bundle formula
[Stacks, Tag 02TX] needs about a trivial bundle.

The route is a comparison with the integral model. Tag 01OE identifies `P` with
`ℙⁿ_U = U ×_ℤ ℙⁿ_ℤ` over `U`, by the morphism `Stacks.SymGraded.projectiveBundleToIntegralModel`
to `ℙⁿ_ℤ`; so `P` is the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along `U ⟶ Spec ℤ`, and the integral
model is a projective tower (`Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceAtUniverse`).
What remains is the module half of Tag 01OE: `𝒪_P(1)` is the pullback of the integral `𝒪(1)`.
That is proved here through Tag 01NE: the homogeneous coordinates `ψ₁(Tᵢ)` of the twist datum
and the pulled-back coordinates agree after pullback along every projective-spectrum chart over
an affine open of `U` (`Stacks.Chow.FreeTower.isTautologicalOn_chart_of_map`), and such local
agreement on an open cover glues
(`Stacks.Chow.FreeTower.exists_iso_pullback_of_isTautologicalOn`).

## Main definitions

* `Stacks.Chow.FreeTower.coordPiece`: the coordinates of `𝒪_U^{n+1}` as sections of `Sym¹`.
* `Stacks.Chow.FreeTower.bundleCoord`: the homogeneous coordinates of `P`, global sections of
  `𝒪_P(1)`.

## Main results

* `Stacks.Chow.FreeTower.exists_tautologicalTwist_iso_pullback`: **`𝒪_P(1)` is the pullback of
  the integral `𝒪(1)`** along `projectiveBundleToIntegralModel`, with the homogeneous
  coordinates going to the pulled-back coordinates. This is
  `Stacks.SymGraded.HasFreeBundleTwistOne`, over an arbitrary base.
* `Stacks.Chow.FreeTower.isPullback_projectiveBundleToIntegralModel`: `P` is the base change of
  the integral model.
* `Stacks.Chow.isProjectiveTower_freeModule`: **the projective bundle of a free module of rank
  `n + 1` with `𝒪(1)` is a projective tower of fibre dimension `n`.**

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.ProjTwistSections
open Opposite

universe u

namespace Stacks.Chow.FreeTower

variable (U : Scheme.{u}) (n : ℕ)

/-- The `i`-th coordinate of `𝒪_U^{n+1}`, as a section of `Sym¹(𝒪_U^{n+1})` over an open. -/
def coordPiece (W : U.Opens) (i : Fin (n + 1)) :
    (freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).sectionPieces W 1 :=
  chartPieceEquiv n W 1 ⟨MvPolynomial.X (ULift.up i),
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _)⟩

/-- The coordinate piece is the image of the variable under the chart ring isomorphism. -/
theorem of_coordPiece' (W : U.Opens) (i : Fin (n + 1)) :
    DirectSum.of _ 1 (coordPiece U n W i) =
      chartSectionsRingEquiv n W (MvPolynomial.X (ULift.up i)) :=
  (chartSectionsRingEquiv_coe n W 1 _).symm

/-- The coordinate piece is the image of the integral coordinate `Tᵢ`. -/
theorem of_coordPiece (W : U.Opens) (i : Fin (n + 1)) :
    DirectSum.of _ 1 (coordPiece U n W i) = chartCoordHom n W (MvPolynomial.X i) := by
  rw [of_coordPiece', chartCoordHom_apply, coordGradedHom_apply, MvPolynomial.map_X,
    MvPolynomial.rename_X]

/-- The coordinate pieces are compatible with restriction. -/
theorem resPiece_coordPiece {W V : U.Opens} (h : W ≤ V) (i : Fin (n + 1)) :
    (freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).resPiece h 1 (coordPiece U n V i) =
      coordPiece U n W i := by
  apply DirectSum.of_injective (β := fun k =>
    (freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).sectionPieces W k) 1
  rw [← SheafGradedAlgebra.resRingHom_of, of_coordPiece', of_coordPiece',
    resRingHom_chartSectionsRingEquiv_X]

/-- The homogeneous coordinates of the projective bundle of `𝒪_U^{n+1}`: the images of the
coordinates of `𝒪_U^{n+1}` under the degree-one homogeneous-section map of the canonical twist
datum, global sections of `𝒪(1)`. -/
def bundleCoord (i : Fin (n + 1)) :
    Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist (freeModule (X := U) (coordIndex.{u} n))
      (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)), ⊤) :=
  ((projectiveBundleTwistData (freeModule (X := U) (coordIndex.{u} n))
    (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))).ψ 1).val.app (op ⊤)
      (coordPiece U n ⊤ i)

/-- The degree-one twist of a chart of the bundle is invertible. -/
theorem isInvertible_twistingSheaf_chart (W : U.Opens) (hW : IsAffineOpen W) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj
        ((freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).grading W)).presheaf
      (AlgebraicGeometry.Proj
        ((freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).grading W)).ringCatSheaf.2
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).grading W) ((1 : ℕ) : ℤ)) :=
  Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_adjoin_degree_one _
    (by
      have h := adjoin_grading_one_eq_top (freeModule (X := U) (coordIndex.{u} n)) W
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)) hW
      have hs : (Set.range fun f : (freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).grading W 1
          => (f : (freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).sectionRing W)) =
          ((freeSymGradedAlgebra (X := U) (coordIndex.{u} n)).grading W 1 : Set _) :=
        Subtype.range_coe
      rw [hs]
      exact h) _

/-- The twist of the bundle is invertible, in the spelling of the ampleness theory. -/
instance isInvertibleModule_tautologicalTwist :
    Stacks.Ample.IsInvertibleModule _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))) :=
  Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist _ _

/-- **On a chart, the twist of the bundle is the pullback of the integral `𝒪(1)`**, compatibly
with the coordinates: the chart identification of the canonical twist datum carries the
coordinates to the sections attached to the homogeneous coordinates, and so does the twist
comparison of `Proj.map` of those coordinates. -/
theorem isTautologicalOn_chart (W : U.Opens) (hW : IsAffineOpen W) :
    letI := (projectiveBundleTwistData (freeModule (X := U) (coordIndex.{u} n))
      (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))).chartData.chart_isOpenImmersion
        W hW
    IsTautologicalOn
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))
      (bundleCoord U n) (projectiveBundleToIntegralModel (X := U) n)
      ((relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).chart W hW) := by
  have := isInvertible_twistingSheaf_chart U n W hW
  exact isTautologicalOn_chart_of_map _ W hW (chartCoordHom n W)
    (irrelevant_le_map_chartCoordHom n W) (projectiveBundleToIntegralModel (X := U) n)
    (chart_comp_projectiveBundleToIntegralModel n W hW).symm (coordPiece U n ⊤)
    (fun i => by rw [resPiece_coordPiece, of_coordPiece])

/-- The projective bundle of `𝒪_U^{n+1}` is the base change of the integral model of `ℙⁿ`. -/
theorem isPullback_projectiveBundleToIntegralModel :
    IsPullback (projectiveBundleToIntegralModel (X := U) n)
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) (terminal.from U) := by
  refine (IsPullback.of_iso (IsPullback.of_hasPullback (terminal.from U)
    (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n))).flip
    (projectiveBundleIsoProjectiveSpace (X := U) n).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_) <;>
    simp [Iso.eq_inv_comp, projectiveBundleIsoProjectiveSpace_hom_comp_toIntegralAtUniverse,
      projectiveBundleIsoProjectiveSpace_hom_comp_fst]

/-- The projective bundle of a free module of rank `n + 1` with its twist, given the comparison
of the twist with the pullback of the integral `𝒪(1)`. -/
theorem isProjectiveTower_freeModule_of_iso
    (e : Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U)
          (coordIndex.{u} n)) ≅
      (Scheme.Modules.pullback (projectiveBundleToIntegralModel (X := U) n)).obj
        (twistingSheafAtUniverse.{u} n)) :
    IsProjectiveTower n
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))) :=
  (isProjectiveTower_projectiveSpaceAtUniverse n).of_isPullback
    (isPullback_projectiveBundleToIntegralModel U n) e


/-- **The twist of the projective bundle of `𝒪_U^{n+1}` is the pullback of the integral
`𝒪(1)`**, with the coordinates going to the coordinates: this is the module half of
[Stacks, Tag 01OE], `Stacks.SymGraded.HasFreeBundleTwistOne`, over an arbitrary base. -/
theorem exists_tautologicalTwist_iso_pullback :
    ∃ β : Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)) ≅
      (Scheme.Modules.pullback (projectiveBundleToIntegralModel (X := U) n)).obj
        (twistingSheafAtUniverse.{u} n),
      ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (bundleCoord U n i) =
        pullbackCoordSection (projectiveBundleToIntegralModel (X := U) n) i := by
  refine exists_iso_pullback_of_isTautologicalOn fun x => ?_
  obtain ⟨W, hW, hxW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := U) (x := (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U)
      (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase.base x)
    (U := ⊤) trivial
  let := (projectiveBundleTwistData (freeModule (X := U) (coordIndex.{u} n))
    (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))).chartData.chart_isOpenImmersion
      W hW
  refine ⟨_, _, inferInstance, ?_, isTautologicalOn_chart U n W hW⟩
  have hx : x ∈ (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U)
      (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase ⁻¹ᵁ W :=
    hxW
  rw [← (projectiveBundleTwistData (freeModule (X := U) (coordIndex.{u} n))
    (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))).chartData.chart_range W hW] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact ⟨y, hy⟩

/-- **The projective bundle of a free module of rank `n + 1` is a projective tower** of fibre
dimension `n`, with its twist `𝒪(1)`. -/
theorem _root_.Stacks.Chow.isProjectiveTower_freeModule :
    IsProjectiveTower n
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))) :=
  isProjectiveTower_freeModule_of_iso U n (exists_tautologicalTwist_iso_pullback U n).choose

end Stacks.Chow.FreeTower

end
