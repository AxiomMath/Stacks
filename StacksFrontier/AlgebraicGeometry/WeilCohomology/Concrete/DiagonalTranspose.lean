module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.TransposeGraph
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The transpose of the diagonal

The factor switch `X ×_S X ≅ X ×_S X` fixes the diagonal `Δ : X ⟶ X ×_S X`, so transposing the
cycle of the diagonal returns it: `[Δ]ᵗ = [Δ]`, on cycles, on Chow classes and on rational
correspondences. For `X` equidimensional of dimension `d` the transpose maps `Corr⁰(X, X)` to
`Corr^{d - d + 0}(X, X)`, and the diagonal class is fixed.

This is the identity of the proof of Stacks 0FGI that lets one class, the diagonal, serve both as
the unit `η ∈ Corr^d(Spec k, X × X)` and as the counit `ε ∈ Corr^{-d}(X × X, Spec k)`: the two are
the images of `[Δ]` and of `[Δ]ᵗ` under the identifications of Stacks 0FG0 (2) and (3).

## Main results

* `Stacks.WeilCohomology.pullbackDiagonal_comp_pullbackSymmetry_hom`: the factor switch fixes the
  diagonal.
* `Stacks.WeilCohomology.cycleTranspose_diagonal`: `[Δ]ᵗ = [Δ]` on cycles.
* `Stacks.WeilCohomology.chowTranspose_diagonal`: `[Δ]ᵗ = [Δ]` on Chow classes.
* `Stacks.WeilCohomology.transpose_diagonal`: `[Δ]ᵗ = [Δ]` on rational correspondences.

## References

* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- The factor switch `X ×_S X ≅ X ×_S X` fixes the diagonal. -/
@[reassoc (attr := simp)]
theorem pullbackDiagonal_comp_pullbackSymmetry_hom {S X : Scheme.{u}} (sX : X ⟶ S) :
    pullback.diagonal sX ≫ (pullbackSymmetry sX sX).hom = pullback.diagonal sX := by
  apply pullback.hom_ext <;> simp

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsClosedImmersion (pullback.diagonal sX)]

/-- Transposing the cycle of the diagonal returns it: `[Δ]ᵗ = [Δ]` on cycles. -/
theorem cycleTranspose_diagonal (k : ℤ) :
    cycleTranspose C sX sX k
        (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) k) =
      cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX) (pullback.diagonal sX) k := by
  have h := properPushforward_cycleAssociatedToClosedSubscheme_of_isIso C
    (pullback.fst sX sX ≫ sX) (pullback.fst sX sX ≫ sX) (pullbackSymmetry sX sX)
    (pullbackSymmetry_hom_comp_base sX sX) (pullback.diagonal sX) k
  simp only [pullbackDiagonal_comp_pullbackSymmetry_hom] at h
  exact h

/-- Transposing the Chow class of the diagonal returns it: `[Δ]ᵗ = [Δ]` on Chow classes. -/
theorem chowTranspose_diagonal (k : ℤ) :
    chowTranspose C sX sX k
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
          (pullback.diagonal sX) k)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
        (pullback.diagonal sX) k) :=
  congrArg QuotientAddGroup.mk (cycleTranspose_diagonal C sX k)

/-- `[Δ]ᵗ = [Δ]` on rational correspondences: for `X` equidimensional of dimension `d` the
transpose `Corrʳ(X, X) ⟶ Corr^{d - d + r}(X, X)` fixes every rational multiple of the class of the
diagonal, read in the degree `d - r` of the Chow group of `X ×_S X` it lives in. -/
theorem transpose_diagonal (d r : ℤ) (q : ℚ) :
    transpose C sX sX d d r (q ⊗ₜ[ℤ] QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX) (pullback.diagonal sX)
          (d - r))) =
      q ⊗ₜ[ℤ] chowGroupDegreeEquiv C (pullback.fst sX sX ≫ sX)
        (show d - r = d - (d - d + r) by omega)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C (pullback.fst sX sX ≫ sX)
          (pullback.diagonal sX) (d - r))) := by
  rw [transpose_tmul, chowTranspose_diagonal]

end Stacks.WeilCohomology

end
