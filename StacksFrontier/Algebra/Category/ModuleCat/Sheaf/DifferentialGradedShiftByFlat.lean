module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftBy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFlat

/-!
# Flatness and K-flatness of the shift of a differential graded module by an integer

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of differential graded
`O`-algebras and let `P` be a right differential graded `A`-module. For every integer `k` the
shift `P[k]` of `SheafOfModules.DifferentialGradedModule.shiftBy` is a degree `k` shift of `P` in
the sense of `SheafOfModules.RelativeTensor.IsDifferentialGradedShift`, so it is flat as a graded
module as soon as `P` is, and K-flat as soon as `P` is.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.isDifferentialGradedShift_shiftBy`: `P[k]` is a
  degree `k` shift of `P`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGradedFlat_shiftBy` and `isKFlat_shiftBy`.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- Degree `n` of `P[k]` is degree `p` of `P` whenever `n + k = p`. -/
theorem shiftBy_piece_eq (P : DifferentialGradedModule.{t, m, m} A) (k : ℤ) {n p : ℤ}
    (h : n + k = p) :
    (RelativeTensor.gP (shiftBy P k)).piece n = (RelativeTensor.gP P).piece p :=
  congrArg P.complex.X h

/-- **`P[k]` is a degree `k` shift of `P` as a right graded module**: the identification of
`P[k]^n` with `P^{n + k}` carries the right action. -/
noncomputable def isGradedShift_shiftBy (P : DifferentialGradedModule.{t, m, m} A) (k : ℤ) :
    RelativeTensor.IsGradedShift k (RelativeTensor.gP (shiftBy P k)) (RelativeTensor.gP P) where
  e h := eqToIso (shiftBy_piece_eq P k h)
  e_smul {n i p} h U x y := by
    have hβ : HEq (((shiftBy P k).mul n i).app U) ((P.mul p i).app U) := by
      subst h
      exact shiftBy_mul_heq P k n i U
    exact SheafOfModules.ShiftFlat.bilinear_transport (shiftBy_piece_eq P k h)
      (shiftBy_piece_eq P k (show n + i + k = p + i by omega))
      ((shiftBy P k).mul n i) (P.mul p i) U hβ x y

/-- **`P[k]` is a degree `k` shift of `P` as a right differential graded module**: the
identification carries the differential of `P[k]` to `(-1)^k` times that of `P`. -/
noncomputable def isDifferentialGradedShift_shiftBy (P : DifferentialGradedModule.{t, m, m} A)
    (k : ℤ) : RelativeTensor.IsDifferentialGradedShift k (shiftBy P k) P where
  toIsGradedShift := isGradedShift_shiftBy P k
  e_d {n p} h U x :=
    SheafOfModules.ShiftFlat.shifted_d_val_app k (shiftBy_complex P k) n (n + 1) p (p + 1) rfl h
      (by omega) U x

/-- **The shift of a right differential graded module whose underlying right graded module is
flat has flat underlying right graded module.** -/
theorem isGradedFlat_shiftBy (P : DifferentialGradedModule.{t, m, m} A) (k : ℤ)
    (hP : RelativeTensor.IsGradedFlat (RelativeTensor.gP P)) :
    RelativeTensor.IsGradedFlat (RelativeTensor.gP (shiftBy P k)) :=
  (isGradedShift_shiftBy P k).isGradedFlat hP

/-- **The shift of a K-flat right differential graded module is K-flat.** -/
theorem isKFlat_shiftBy (P : DifferentialGradedModule.{t, m, m} A) (k : ℤ)
    (hP : RelativeTensor.IsKFlat P) : RelativeTensor.IsKFlat (shiftBy P k) :=
  (isDifferentialGradedShift_shiftBy P k).isKFlat hP

end SheafOfModules.DifferentialGradedModule

end
