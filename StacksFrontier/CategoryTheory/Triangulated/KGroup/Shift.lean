module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring

/-!
# The shift on the zeroth K-group, and generation by the classes of objects

Let `C` be a pretriangulated category. The contractible triangle `Y ⟶ 0 ⟶ Y⟦1⟧ ⟶ Y⟦1⟧` is
distinguished, so in `K₀(C)` the shift by one negates classes, and the shift by `n` multiplies
them by `(-1)^n`. The classes of objects generate `K₀(C)`, so an additive map into `K₀(C)` is
surjective as soon as every class of an object is in its range.

## Main results

* `CategoryTheory.Pretriangulated.K0.cls_shift_one`: `[Y⟦1⟧] = -[Y]`.
* `CategoryTheory.Pretriangulated.K0.cls_shift`: `[Y⟦n⟧] = (-1)^n • [Y]`.
* `CategoryTheory.Pretriangulated.K0.surjective_of_forall_cls_mem_range`: an additive map into
  `K₀(C)` whose range contains the class of every object is surjective.

## Implementation notes

`CategoryTheory.Pretriangulated.K0` is a quotient of the free abelian group on the objects of
`C`, so surjectivity is read off that presentation by `FreeAbelianGroup.induction_on`; nothing
here uses the octahedron axiom.

## References

* [Stacks Project, Tag 0FCN](https://stacks.math.columbia.edu/tag/0FCN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Pretriangulated.K0

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The shift by one negates classes in `K₀(C)`.** The contractible triangle
`Y ⟶ 0 ⟶ Y⟦1⟧ ⟶ Y⟦1⟧` is distinguished, so `0 = [Y] + [Y⟦1⟧]`. -/
theorem cls_shift_one (Y : C) : cls (Y⟦(1 : ℤ)⟧) = - cls Y := by
  have h := cls_eq_add_of_distinguished (contractible_distinguished₂ Y)
  change cls (0 : C) = cls Y + cls (Y⟦(1 : ℤ)⟧) at h
  rw [cls_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **Shifting one step further negates the class.** The shift by `n + 1` is the shift by `n`
followed by the shift by one. -/
theorem cls_shift_succ (Y : C) (n : ℤ) : cls (Y⟦n + 1⟧) = - cls (Y⟦n⟧) := by
  rw [cls_eq_of_iso ((shiftFunctorAdd' C n 1 (n + 1) rfl).app Y)]
  change cls ((Y⟦n⟧)⟦(1 : ℤ)⟧) = - cls (Y⟦n⟧)
  exact cls_shift_one _

/-- **Shifting one step back negates the class.** This is `cls_shift_succ` at `n - 1`. -/
theorem cls_shift_pred (Y : C) (n : ℤ) : cls (Y⟦n - 1⟧) = - cls (Y⟦n⟧) := by
  have h : cls (Y⟦n⟧) = - cls (Y⟦n - 1⟧) := by
    simpa only [sub_add_cancel] using cls_shift_succ Y (n - 1)
  simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- **The shift by `n` multiplies classes in `K₀(C)` by `(-1)^n`.** -/
theorem cls_shift (Y : C) (n : ℤ) : cls (Y⟦n⟧) = (n.negOnePow : ℤ) • cls Y := by
  induction n using Int.induction_on with
  | zero =>
    rw [cls_eq_of_iso ((shiftFunctorZero C ℤ).app Y)]
    simp
  | succ n ih =>
    rw [cls_shift_succ, ih]
    simp [Int.negOnePow_add, Int.negOnePow_one]
  | pred n ih =>
    rw [cls_shift_pred, ih]
    simp [Int.negOnePow_sub, Int.negOnePow_one]

/-- **The classes of objects generate `K₀(C)`.** An additive map into `K₀(C)` whose range
contains the class of every object of `C` is surjective. -/
theorem surjective_of_forall_cls_mem_range {A : Type*} [AddCommGroup A] (φ : A →+ K0 C)
    (h : ∀ Y : C, cls Y ∈ φ.range) : Function.Surjective φ := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  induction x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of Y => exact h Y
  | neg Y hY => obtain ⟨a, ha⟩ := hY; exact ⟨-a, by rw [map_neg, ha]; rfl⟩
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩

end CategoryTheory.Pretriangulated.K0

end
