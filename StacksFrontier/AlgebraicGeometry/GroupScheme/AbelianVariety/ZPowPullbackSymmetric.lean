module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullbackFormula
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass

/-!
# Multiplication by `n` on a symmetric invertible module

Let `A` be an abelian variety over a field and `L` an invertible `𝒪_A`-module. The module
`𝓝 = L ⊗ [-1]^*L` is symmetric, `[-1]^*𝓝 ≅ 𝓝`, so [Stacks, Tag 0BFF] specialises to
`[n]^*𝓝 ≅ 𝓝^{⊗ n²}` when `A` satisfies the theorem of the cube
(`Stacks.Groupoids.HasTheoremOfTheCube A`).

## Main results

* `Stacks.Groupoids.pullbackPicardClass_inv_symmetrize`: `[-1]^*𝓝` and `𝓝` have the same class.
* `Stacks.Groupoids.nonempty_zpowId_pullback_symmetrize_iso`: `[n]^*𝓝 ≅ 𝓝^{⊗ n²}`.

## References

* [Stacks Project, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (schemeTensor schemeTensorPower picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

/-- The symmetrization `L ⊗ [-1]^*L` of an invertible module on a group scheme. -/
noncomputable abbrev symmetrize : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace) :=
  schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L)

include hL in
/-- The symmetrization `L ⊗ [-1]^*L` of an invertible module is invertible. -/
theorem isInvertible_symmetrize :
    Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf (symmetrize A L) :=
  Stacks.SheafOfModules.isInvertible_schemeTensor A.left _ _ hL
    (isInvertible_pullbackOver (ι : A ⟶ A) L hL)

/-- Inversion composed with itself is the identity, on the underlying scheme. -/
theorem inv_left_comp_inv_left : (ι : A ⟶ A).left ≫ (ι : A ⟶ A).left = 𝟙 A.left := by
  rw [← Over.comp_left, ← CategoryTheory.GrpObj.zpow_id_neg_one, GrpObj.comp_zpow,
    Category.comp_id, ← zpow_mul]
  norm_num

/-- The class of the symmetrization is `[L] + [[-1]^*L]`. -/
theorem picardClass_symmetrize :
    picardClass A.left.presheaf A.left.ringCatIsSheaf (symmetrize A L)
        (isInvertible_symmetrize A L hL) =
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL +
        pullbackPicardClass (ι : A ⟶ A).left L hL :=
  Stacks.SheafOfModules.picardClass_schemeTensor A.left _ _ hL
    (isInvertible_pullbackOver (ι : A ⟶ A) L hL)

/-- **The symmetrization is symmetric**: `[-1]^*𝓝` and `𝓝` have the same class. -/
theorem pullbackPicardClass_inv_symmetrize :
    pullbackPicardClass (ι : A ⟶ A).left (symmetrize A L) (isInvertible_symmetrize A L hL) =
      picardClass A.left.presheaf A.left.ringCatIsSheaf (symmetrize A L)
        (isInvertible_symmetrize A L hL) := by
  rw [Stacks.SheafOfModules.pullbackPicardClass_schemeTensor _ _ _ hL
      (isInvertible_pullbackOver (ι : A ⟶ A) L hL),
    pullbackPicardClass_inv_pullbackOver_inv, picardClass_symmetrize, add_comm]

/-- **`[n]^*𝓝 ≅ 𝓝^{⊗ n²}` for the symmetrization `𝓝 = L ⊗ [-1]^*L`**, on an abelian variety `A`
satisfying the theorem of the cube. -/
theorem nonempty_zpowId_pullback_symmetrize_iso [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) (symmetrize A L) ≅
      schemeTensorPower A.left (symmetrize A L) (isInvertible_symmetrize A L hL) (n * n)) := by
  have hN := isInvertible_symmetrize A L hL
  have key := zpowIdPicardClass_eq A (symmetrize A L) hN hcube n
  rw [pullbackPicardClass_inv_symmetrize A L hL, ← add_smul,
    triangularNumber_add_triangularNumber_neg,
    ← Stacks.SheafOfModules.picardClass_schemeTensorPower A.left _ hN (n * n),
    zpowIdPicardClass_def, Stacks.SheafOfModules.pullbackPicardClass_eq_picardClass _ _ _
      (isInvertible_pullbackOver _ _ hN)] at key
  exact (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _ _ _).1
    key

end Stacks.Groupoids
