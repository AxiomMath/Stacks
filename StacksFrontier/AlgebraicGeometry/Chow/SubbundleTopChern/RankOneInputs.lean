module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionFactor
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSectionAffineCriterion
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inputs for the class of a subbundle of corank one

Three facts used to compute the class of a subbundle of corank one in a vector bundle.

* **The dual of an invertible module.** For `ℒ` invertible on a scheme, `ℒ^∨ = SheafHom(ℒ, 𝒪)` is
  invertible and `ℒ^∨ ⊗ ℒ ≅ 𝒪` (Stacks 01CT), so `c₁(ℒ^∨) ∩ α = -(c₁(ℒ) ∩ α)` (Stacks 02SP).
* **The line bundle `𝐕(ℒ)` as a total space.** The total space of the line bundle attached to an
  invertible module is identified with its vector bundle `𝐕(ℒ)`; under this identification the
  module morphism attached to a point is the one of the functor of points of `𝐕(ℒ)`, and the zero
  section of the total space is the zero section of `𝐕(ℒ)`.

## Main results

* `Stacks.Chow.firstChernClassCapChow_dualSheaf`.
* `Stacks.LineBundle.Situation.vectorBundleOverZeroSection_comp_vectorBundleToTotalSpace`.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The dual of an invertible module is invertible** (Stacks 01CT), at the spelling of the dual
as `SheafHom(ℒ, 𝒪_X)` used for vector bundles. -/
@[ega "0 5.4.3" "special case"]
theorem isInvertible_dualSheaf :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) :=
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf
      (structureSheafRing X.toRingedSpace).property L)

/-- **The evaluation pairing `ℒ^∨ ⊗ ℒ ≅ 𝒪_X`** of an invertible module (Stacks 01CT), at the
spelling of the tensor product of Stacks 02SP. -/
def tensorObjDualSheafIso :
    Scheme.Modules.tensorObj (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) L ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  Stacks.SheafOfModules.Scheme.evaluationIso X L

/-- **`c₁(ℒ^∨) ∩ α = -(c₁(ℒ) ∩ α)`** for an invertible module `ℒ`: Stacks 02SP applied to the
evaluation pairing `ℒ^∨ ⊗ ℒ ≅ 𝒪_X`. -/
theorem firstChernClassCapChow_dualSheaf (C : ChowSituation.{u}) (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (α : chowGroup C q (k + 1)) :
    haveI := isInvertible_dualSheaf L
    firstChernClassCapChow C k q (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) α =
      -firstChernClassCapChow C k q L α := by
  have := isInvertible_dualSheaf L
  rw [firstChernClassCapChow_eq_neg_of_tensorObj_iso_unit C q k
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf L) L (tensorObjDualSheafIso L) α, neg_neg]

end Stacks.Chow

namespace Stacks.LineBundle

open AlgebraicGeometry.Scheme.Modules

variable (D : Situation.{u})

/-- **The functor of points of the total space of a line bundle, read on the vector bundle**: a
point of `𝐕(ℒ)`, carried to the total space, has as module morphism the one of the functor of
points of `𝐕(ℒ)`. -/
theorem Situation.totalSpaceHomEquiv_comp_vectorBundleToTotalSpace {Y : Scheme.{u}}
    (k : Y ⟶ vectorBundle D.X D.L) :
    D.totalSpaceHomEquiv Y (k ≫ D.vectorBundleToTotalSpace) =
      ⟨k ≫ vectorBundleToBase D.X D.L,
        vectorBundleHomEquiv D.L (Over.mk (k ≫ vectorBundleToBase D.X D.L))
          (Over.homMk k rfl)⟩ := by
  refine (congrArg (D.totalSpaceHomEquiv Y) ((congrArg (k ≫ ·)
    D.vectorBundleToTotalSpace_eq_pairToHom).trans
      (Stacks.RelativeSpec.comp_pairToHom k _))).trans ?_
  refine (D.totalSpaceHomEquiv_pairToHom _).trans (Sigma.ext rfl (heq_of_eq ?_))
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  rfl

/-- **The zero section of the vector bundle of `ℒ`, carried to the total space, is the zero
section of the total space.** -/
theorem Situation.vectorBundleOverZeroSection_comp_vectorBundleToTotalSpace :
    (vectorBundleOverZeroSection D.L).left ≫ D.vectorBundleToTotalSpace = D.zeroSection := by
  have h2 : (D.totalSpaceHomEquiv D.X
      ((vectorBundleOverZeroSection D.L).left ≫ D.vectorBundleToTotalSpace)).2 = 0 := by
    rw [D.totalSpaceHomEquiv_comp_vectorBundleToTotalSpace]
    have he : (Over.homMk (vectorBundleOverZeroSection D.L).left rfl :
        Over.mk ((vectorBundleOverZeroSection D.L).left ≫ vectorBundleToBase D.X D.L) ⟶
          vectorBundleOver D.X (F := D.L)) =
        Over.homMk (U := Over.mk ((vectorBundleOverZeroSection D.L).left ≫
          vectorBundleToBase D.X D.L)) (V := Over.mk (𝟙 D.X)) (𝟙 D.X)
          (by simp [vectorBundleOverZeroSection_left_comp]) ≫ vectorBundleOverZeroSection D.L :=
      Over.OverMorphism.ext (Category.id_comp _).symm
    exact (congrArg (vectorBundleHomEquiv D.L _) he).trans
      (vectorBundleHomEquiv_comp_vectorBundleOverZeroSection D.L _)
  obtain ⟨g, hg⟩ := (D.factorsThrough_zeroSection_iff _).mpr h2
  have hg1 : g = 𝟙 D.X := by
    have := congrArg (· ≫ D.totalSpaceToBase) hg
    simp only [Category.assoc, D.zeroSection_comp_totalSpaceToBase, Category.comp_id,
      D.vectorBundleToTotalSpace_comp_totalSpaceToBase] at this
    exact this.trans (vectorBundleOverZeroSection_left_comp D.L)
  rw [← hg, hg1, Category.id_comp]

end Stacks.LineBundle

end
