module

public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorMapCommShift
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentRightUnitorCommShift
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonQcqs
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonUnitCommShift

/-!
# Equation 48.8.0.1 is compatible with distinguished triangles

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes and `a = f^×` the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. The map

  `Lf^*K ⊗ᴸ_{𝒪_X} a(𝒪_Y) ⟶ a(K)`

of [Stacks, Tag 0A9S], `Stacks.Duality.qcqsCompareWithPullback`, is a morphism between two exact
functors of `K` which commutes with the shift: this is what "compatible with distinguished
triangles" says. The shift structures are the ones the source has in mind: `Lf^*` and `a` carry
those they inherit as adjoints of the exact functor `Rf_*`, and `- ⊗ᴸ a(𝒪_Y)` the one of the
derived tensor product.

The proof is `CategoryTheory.MonoidalProjectionFormula.commShift_comparisonUnit`, which reduces
the statement to three facts about the monoidal structures, each in one variable:

* tensoring a morphism in the second variable commutes with the shift on `D_QCoh`
  (`Stacks.Duality.commShift_tensorRightMap_quasiCoherentDerivedMonoidal`);
* the right unitor of `D_QCoh(𝒪_Y)` commutes with the shift
  (`Stacks.Duality.commShift_rightUnitorNatIso_quasiCoherentDerivedMonoidal`);
* the cotensorator `Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M` of [Stacks, Tag 079U] commutes with the shift
  in `K`.

## Main results

* `Stacks.Duality.commShift_qcqsCompareWithPullback_of_commShift_oplaxNatTransLeft` — the map
  commutes with the shift, given the third fact.
* `Stacks.Duality.isTriangulated_qcqsCompareWithPullback_source` and
  `Stacks.Duality.isTriangulated_qcqsTwistedInverseImage` — its source and target are exact.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Stacks.Duality.DerivedPushforward

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The source `K ↦ Lf^*K ⊗ᴸ a(𝒪_Y)` of Equation 48.8.0.1 is an exact functor, for the shift
structure of `Lf^*` as the left adjoint of `Rf_*`. -/
theorem isTriangulated_qcqsCompareWithPullback_source :
    letI := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (quasiCoherentDerivedPullback' f ⋙
      (quasiCoherentDerivedTensor X).flip.obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (derivedStructureSheaf Y))).IsTriangulated := by
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  have := isTriangulated_quasiCoherentDerivedPullback' f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  infer_instance

/-- The target `a = f^×` of Equation 48.8.0.1 is an exact functor, for the shift structure it has
as the right adjoint of `Rf_*`. -/
theorem isTriangulated_qcqsTwistedInverseImage :
    letI := (twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).IsTriangulated
    := by
  let := (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
  let := (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).commShift_of_leftAdjoint ℤ
  exact (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).isTriangulated_rightAdjoint

/-- **Equation 48.8.0.1 commutes with the shift**, given that the cotensorator of `Lf^*` does in
its first variable. -/
theorem commShift_qcqsCompareWithPullback_of_commShift_oplaxNatTransLeft
    (hP : ∀ M : quasiCoherentDerivedCategory Y,
      letI := quasiCoherentDerivedMonoidal X
      letI := quasiCoherentDerivedMonoidal Y
      letI := quasiCoherentDerivedPullbackMonoidal f
      letI := commShift_quasiCoherentDerivedPullback f
        (isQuasicoherent_homology_derivedPullback' f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      NatTrans.CommShift
        (MonoidalProjectionFormula.oplaxNatTransLeft (quasiCoherentDerivedPullback' f) M) ℤ) :
    letI := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    letI := (twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
    NatTrans.CommShift (qcqsCompareWithPullback f) ℤ := by
  let := quasiCoherentDerivedMonoidal X
  let := quasiCoherentDerivedMonoidal Y
  let := quasiCoherentDerivedPullbackMonoidal f
  let := commShift_quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  let := (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).commShift_of_rightAdjoint ℤ
  let := (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).rightAdjointCommShift ℤ
  let := (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).commShift_of_leftAdjoint ℤ
  have := hP
  have := commShift_rightUnitorNatIso_quasiCoherentDerivedMonoidal Y
  have : ∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (MonoidalProjectionFormula.projectionFormulaMap
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) E K) := fun E K => by
    rw [← projectionFormulaMap_pullbackCotensorator]
    infer_instance
  have h := MonoidalProjectionFormula.commShift_comparisonUnit
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)) ℤ
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
  exact h

end Stacks.Duality

end
