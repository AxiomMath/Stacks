module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
import all StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonPerfect
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonStructureSheaf
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaDualizable
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso

/-!
# The pullback comparison at an exact pairing

Declarations built on
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonMonoidal`.

## Main results

* `isIso_projectionMap_of_isIso_projectionFormulaMap`
* `compareWithPullbackTensor_eq_comparisonMap`
* `isIso_compareWithPullbackTensor_of_exactPairing`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (α : quasiCoherentDerivedTensorSwap Y ⋙ quasiCoherentDerivedPullback' f ⟶
      (quasiCoherentDerivedPullback' f).prod (quasiCoherentDerivedPullback' f) ⋙
        quasiCoherentDerivedTensorSwap X)

/-! ### The projection formula and the comparison map as 2-squares -/

section Comparison

variable [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
    IsIso (projectionFormulaMap f hpush α E K)]

variable {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-! ### Equation 48.8.0.1 for a perfect complex -/

end Comparison

/-! ### The comparison map through the monoidal structure of `D_QCoh` -/

section Monoidal

open MonoidalCategory Functor.OplaxMonoidal

variable [(quasiCoherentDerivedPullback' f).Monoidal]
  (hα : ∀ P Q : quasiCoherentDerivedCategory Y, α.app (P, Q) =
    (quasiCoherentDerivedPullback' f).map
        (((quasiCoherentDerivedTensorIsoCurriedTensor Y).hom.app Q).app P) ≫
      δ (quasiCoherentDerivedPullback' f) Q P ≫
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).inv.app
        ((quasiCoherentDerivedPullback' f).obj Q)).app
        ((quasiCoherentDerivedPullback' f).obj P))

include hα

/-- When `α` is the oplax structure of the strong monoidal functor `Lf^*` read through the
identification of `⊗ᴸ` with the tensor product of `D_QCoh`, the projection-formula map is
invertible exactly when the projection map of the monoidal adjunction `Lf^* ⊣ Rf_*` is. -/
theorem isIso_projectionMap_of_isIso_projectionFormulaMap
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f hpush α E K)]
    (K : quasiCoherentDerivedCategory Y) (E : quasiCoherentDerivedCategory X) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      hpush).projectionMap K E) :=
  ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      hpush).isIso_projectionMap_iff _
    (quasiCoherentDerivedTensorIsoCurriedTensor Y) _
    (quasiCoherentDerivedTensorIsoCurriedTensor X) α hα E K).1
    (inferInstanceAs (IsIso (projectionFormulaMap f hpush α E K)))

/-- **The comparison map of Equation 48.8.0.1 is the comparison map of the monoidal adjunction**
`Lf^* ⊣ Rf_*`, read through the identification of `⊗ᴸ` with the tensor product of `D_QCoh`. -/
theorem compareWithPullbackTensor_eq_comparisonMap
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f hpush α E K)]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (K L : quasiCoherentDerivedCategory Y) :
    haveI := isIso_projectionMap_of_isIso_projectionFormulaMap f hpush α hα
    compareWithPullbackTensor f hpush α adj K L =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).hom.app
          ((quasiCoherentDerivedPullback' f).obj K)).app (a.obj L) ≫
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
            hpush).comparisonMap adj K L ≫
          a.map (((quasiCoherentDerivedTensorIsoCurriedTensor Y).inv.app K).app L) := by
  have := isIso_projectionMap_of_isIso_projectionFormulaMap f hpush α hα
  have : ∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (adjunctionTensorMap
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush)
        (quasiCoherentDerivedTensorSwap Y) (quasiCoherentDerivedTensorSwap X) α E K) :=
    fun E K => inferInstanceAs (IsIso (projectionFormulaMap f hpush α E K))
  unfold compareWithPullbackTensor projectionFormulaMap
  exact (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      hpush).homEquiv_inv_adjunctionTensorMap_eq_comparisonMap
    _ (quasiCoherentDerivedTensorIsoCurriedTensor Y) _
    (quasiCoherentDerivedTensorIsoCurriedTensor X) α hα adj K L

/-- **The comparison map of Equation 48.8.0.1 is invertible at a dualizable `K`.** -/
theorem isIso_compareWithPullbackTensor_of_exactPairing
    [∀ (E : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y),
      IsIso (projectionFormulaMap f hpush α E K)]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (K K' : quasiCoherentDerivedCategory Y)
    [ExactPairing K K'] (L : quasiCoherentDerivedCategory Y) :
    IsIso (compareWithPullbackTensor f hpush α adj K L) := by
  have := isIso_projectionMap_of_isIso_projectionFormulaMap f hpush α hα
  have := (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    hpush).isIso_comparisonMap_of_exactPairing adj K K' L
  rw [compareWithPullbackTensor_eq_comparisonMap f hpush α hα adj K L]
  infer_instance

end Monoidal

end Stacks.Duality

end
