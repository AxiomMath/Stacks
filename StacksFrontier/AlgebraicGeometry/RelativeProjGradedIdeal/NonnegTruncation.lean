module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.PushforwardAlgebra
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The nonnegative truncation of a sheaf of graded algebras

Let `A` be a `ℤ`-graded sheaf of algebras on a scheme `S`. Its nonnegative truncation `A_{≥0}` is
the graded algebra with the same pieces as `A` in nonnegative degrees and zero in every negative
degree. It is concentrated in nonnegative degrees, commutative when `A` is, and has quasi-coherent
pieces when `A` has, so it is sheaf-level graded algebra data on `S` in the sense of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Applied to the direct image of a
graded algebra along a morphism of schemes `p : X ⟶ S`, this gives `(p_*A)_{≥0}`.

## Main definitions

* `Stacks.AlgebraicGeometry.NonnegTruncation.piece`: the pieces of the truncation, by cases on
  the sign of the degree.
* `NonnegTruncation.mul` and `NonnegTruncation.one`: its multiplication — the multiplication of
  `A` in nonnegative bidegrees and zero otherwise — and its unit.
* `NonnegTruncation.nonnegTruncation`: `A_{≥0}` as a `SheafOfModules.GradedAlgebra S.ringCatSheaf`.
* `NonnegTruncation.nonnegSheafGradedAlgebra`: `A_{≥0}` as sheaf-level graded algebra data on `S`.
* `NonnegTruncation.pushforwardNonnegSheafGradedAlgebra`: `(p_*A)_{≥0}` as sheaf-level graded
  algebra data on `S`, for a morphism of schemes `p : X ⟶ S` and a sheaf of graded algebras `A`
  on `X`.

## Main results

* `NonnegTruncation.piece_of_nonneg` and `NonnegTruncation.isZero_piece_of_neg`: the truncation
  agrees with `A` in nonnegative degrees and is zero in negative ones.
* `NonnegTruncation.vanishesInNegativeDegrees_nonnegTruncation`: the truncation is concentrated
  in nonnegative degrees.
* `NonnegTruncation.isCommutative_nonnegTruncation`: the truncation of a commutative graded
  algebra is commutative.
* `NonnegTruncation.isQuasicoherent_piece`: the pieces of the truncation are quasi-coherent when
  those of `A` are.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped ZeroObject

namespace Stacks.AlgebraicGeometry.NonnegTruncation

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}}

local instance hasZeroObject_sheafOfModules :
    HasZeroObject (SheafOfModules.{u} S.ringCatSheaf) :=
  inferInstanceAs (HasZeroObject S.Modules)

variable (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)

/-! ### Two facts about zero sheaves of modules -/

/-- A local section of a zero sheaf of modules is zero. -/
theorem eq_zero_of_isZero {M : SheafOfModules.{u} S.ringCatSheaf} (hM : IsZero M)
    (U : (S.Opens)ᵒᵖ) (x : M.val.obj U) : x = 0 := by
  simpa [show (0 : M ⟶ M).val = 0 from rfl] using
    congrArg (fun k : M ⟶ M ↦ k.val.app U x) (hM.eq_of_src (𝟙 M) 0)

/-- The kernel of an identity map is a zero object. -/
private theorem isZero_kernel_id (B : S.Modules) : IsZero (kernel (𝟙 B)) := by
  have h : kernel.ι (𝟙 B) = 0 := by simpa using kernel.condition (𝟙 B)
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono (kernel.ι (𝟙 B))).1 (by rw [Category.id_comp, zero_comp, h])

/-- **A zero sheaf of modules on a scheme is quasi-coherent**, given any quasi-coherent module `B`
on the scheme. -/
private theorem isQuasicoherent_of_isZero (B : S.Modules) [B.IsQuasicoherent]
    {M : SheafOfModules.{u} S.ringCatSheaf} (hM : IsZero M) : M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((isZero_kernel_id B).iso hM)
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (𝟙 B))

/-- The zero bilinear map of sheaves of modules; this is `SheafOfModules.zeroBilinear`. -/
def zeroBilinear (M N P : SheafOfModules.{u} S.ringCatSheaf) :
    SheafOfModules.BilinearMap M N P :=
  SheafOfModules.zeroBilinear M N P

/-! ### The pieces of the truncation -/

/-- **The homogeneous pieces of `A_{≥0}`**: those of `A` in nonnegative degrees, and zero
objects in negative degrees. -/
def piece : ℤ → SheafOfModules.{u} S.ringCatSheaf
  | .ofNat n => A.piece (.ofNat n)
  | .negSucc _ => 0

/-- In degree `n : ℕ` the truncation is the degree-`n` piece of `A`. -/
@[simp] theorem piece_ofNat (n : ℕ) : piece A (.ofNat n) = A.piece (.ofNat n) := rfl

/-- In degree `-(n + 1)` the truncation is the zero object. -/
@[simp] theorem piece_negSucc (n : ℕ) : piece A (.negSucc n) = 0 := rfl

/-- In a nonnegative degree the truncation is `A`. -/
theorem piece_of_nonneg {i : ℤ} (hi : 0 ≤ i) : piece A i = A.piece i := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = Int.ofNat n := ⟨i.toNat, (Int.toNat_of_nonneg hi).symm⟩
  rfl

/-- In a negative degree the truncation is a zero object. -/
theorem isZero_piece_negSucc (n : ℕ) : IsZero (piece A (.negSucc n)) := isZero_zero _

/-- In a negative degree the truncation is a zero object. -/
theorem isZero_piece_of_neg {i : ℤ} (hi : i < 0) : IsZero (piece A i) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  exact isZero_piece_negSucc A n

/-- **Every piece of the truncation is quasi-coherent** as soon as every piece of `A` is. -/
theorem isQuasicoherent_piece (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)
    (n : ℤ) : ((piece A n : S.Modules)).IsQuasicoherent := by
  have := hqc 0
  rcases n with a | a
  · exact hqc _
  · exact isQuasicoherent_of_isZero (A.piece 0) (isZero_piece_negSucc A a)

/-! ### The multiplication and the unit of the truncation -/

/-- **The multiplication of `A_{≥0}`**: that of `A` when both degrees are nonnegative, and the
zero bilinear map otherwise. -/
def mul (i j : ℤ) : SheafOfModules.BilinearMap (piece A i) (piece A j) (piece A (i + j)) :=
  match i, j with
  | .ofNat _, .ofNat _ => A.mul _ _
  | .ofNat _, .negSucc _ => zeroBilinear _ _ _
  | .negSucc _, _ => zeroBilinear _ _ _

/-- In two nonnegative degrees the truncated multiplication is that of `A`. -/
@[simp] theorem mul_ofNat_ofNat (a b : ℕ) :
    mul A (.ofNat a) (.ofNat b) = A.mul (.ofNat a) (.ofNat b) := rfl

/-- A product in which the left degree is negative vanishes. -/
theorem mul_app_apply_eq_zero_of_neg_left (a : ℕ) (j : ℤ) (U : (S.Opens)ᵒᵖ)
    (x : (piece A (.negSucc a)).val.obj U) (y : (piece A j).val.obj U) :
    (mul A (.negSucc a) j).app U x y = 0 := rfl

/-- A product in which the right degree is negative vanishes. -/
theorem mul_app_apply_eq_zero_of_neg_right (i : ℤ) (b : ℕ) (U : (S.Opens)ᵒᵖ)
    (x : (piece A i).val.obj U) (y : (piece A (.negSucc b)).val.obj U) :
    (mul A i (.negSucc b)).app U x y = 0 := by
  rcases i with a | a <;> rfl

/-- **The unit of `A_{≥0}`**: that of `A`, degree `0` being nonnegative. -/
def one : (piece A 0).sections := A.one

/-- The unit of the truncation evaluates to the unit of `A`. -/
@[simp] theorem one_eval (U : (S.Opens)ᵒᵖ) : (one A).eval U = A.one.eval U := rfl

/-! ### The graded-algebra laws -/

/-- Two local sections of the truncation in degrees that agree, both of them zero, are
heterogeneously equal. -/
private theorem heq_of_eq_zero {i j : ℤ} (h : i = j) {U : (S.Opens)ᵒᵖ}
    {x : (piece A i).val.obj U} {y : (piece A j).val.obj U} (hx : x = 0) (hy : y = 0) :
    HEq x y := by
  subst h
  exact heq_of_eq (hx.trans hy.symm)

/-- **Associativity of the truncated multiplication.** -/
theorem mul_assoc (i j k : ℤ) (U : (S.Opens)ᵒᵖ) (x : (piece A i).val.obj U)
    (y : (piece A j).val.obj U) (z : (piece A k).val.obj U) :
    HEq ((mul A (i + j) k).app U ((mul A i j).app U x y) z)
      ((mul A i (j + k)).app U x ((mul A j k).app U y z)) := by
  rcases i with a | a <;> rcases j with b | b <;> rcases k with c | c
  · exact A.mul_assoc _ _ _ U x y z
  all_goals
    refine heq_of_eq_zero A (add_assoc _ _ _) ?_ ?_ <;>
      first
      | exact mul_app_apply_eq_zero_of_neg_right A _ _ U _ _
      | exact mul_app_apply_eq_zero_of_neg_left A _ _ U _ _
      | (rw [mul_app_apply_eq_zero_of_neg_right A _ _ U _ _, map_zero]
         try rw [AddMonoidHom.zero_apply])
      | (rw [mul_app_apply_eq_zero_of_neg_left A _ _ U _ _, map_zero]
         try rw [AddMonoidHom.zero_apply])

/-- **The unit is a left identity for the truncated multiplication.** -/
theorem one_mul (i : ℤ) (U : (S.Opens)ᵒᵖ) (x : (piece A i).val.obj U) :
    HEq ((mul A 0 i).app U ((one A).eval U) x) x := by
  rcases i with a | a
  · exact A.one_mul _ U x
  · refine heq_of_eq_zero A (zero_add _) ?_ ?_
    · exact mul_app_apply_eq_zero_of_neg_right A 0 a U _ x
    · exact eq_zero_of_isZero (isZero_piece_negSucc A a) U x

/-- **The unit is a right identity for the truncated multiplication.** -/
theorem mul_one (i : ℤ) (U : (S.Opens)ᵒᵖ) (x : (piece A i).val.obj U) :
    HEq ((mul A i 0).app U x ((one A).eval U)) x := by
  rcases i with a | a
  · exact A.mul_one _ U x
  · refine heq_of_eq_zero A (add_zero _) ?_ ?_
    · exact mul_app_apply_eq_zero_of_neg_left A a 0 U x _
    · exact eq_zero_of_isZero (isZero_piece_negSucc A a) U x

/-! ### The truncation as a sheaf of graded algebras -/

/-- **The nonnegative truncation `A_{≥0}` of a sheaf of graded algebras.** -/
def nonnegTruncation : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf where
  piece := piece A
  mul := mul A
  one := one A
  mul_assoc := mul_assoc A
  one_mul := one_mul A
  mul_one := mul_one A

/-- The pieces of `nonnegTruncation A` are `piece A`. -/
@[simp] theorem nonnegTruncation_piece (n : ℤ) :
    (nonnegTruncation A).piece n = piece A n := rfl

/-- **The truncation is concentrated in nonnegative degrees**, with no hypothesis on `A`. -/
theorem vanishesInNegativeDegrees_nonnegTruncation :
    VanishesInNegativeDegrees (nonnegTruncation A) :=
  fun _ hn U x ↦ eq_zero_of_isZero (isZero_piece_of_neg A hn) U x

/-- **Commutativity is inherited by the truncation.** -/
theorem isCommutative_nonnegTruncation (hcomm : IsCommutative A) :
    IsCommutative (nonnegTruncation A) := by
  intro i j U a b
  rcases i with p | p
  · rcases j with q | q
    · exact hcomm _ _ U a b
    · refine heq_of_eq_zero A (add_comm _ _) ?_ ?_
      · exact mul_app_apply_eq_zero_of_neg_right A _ q U a b
      · exact mul_app_apply_eq_zero_of_neg_left A q _ U b a
  · refine heq_of_eq_zero A (add_comm _ _) ?_ ?_
    · exact mul_app_apply_eq_zero_of_neg_left A p _ U a b
    · exact mul_app_apply_eq_zero_of_neg_right A _ p U b a

/-- **`A_{≥0}` as sheaf-level graded algebra data on `S`**, for `A` commutative with
quasi-coherent pieces. -/
def nonnegSheafGradedAlgebra (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) :
    SheafGradedAlgebra S :=
  toSheafGradedAlgebra (nonnegTruncation A) (isCommutative_nonnegTruncation A hcomm)
    (vanishesInNegativeDegrees_nonnegTruncation A) (isQuasicoherent_piece A hqc)

/-- The pieces of `nonnegSheafGradedAlgebra A hcomm hqc` are `piece A`. -/
theorem nonnegSheafGradedAlgebra_piece (hcomm : IsCommutative A)
    (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent) (n : ℤ) :
    (nonnegSheafGradedAlgebra A hcomm hqc).piece n = piece A n := rfl

/-! ### The truncated direct image -/

section Pushforward

variable {X : Scheme.{u}} (p : X ⟶ S)
  (B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

open Stacks.AlgebraicGeometry.PushforwardGradedAlgebra

/-- **`(p_*B)_{≥0}` as sheaf-level graded algebra data on `S`**: the direct image of the
commutative `ℤ`-graded algebra `B` on `X`, truncated to the nonnegative degrees. Nothing is
assumed of the negative degrees of `B`. -/
@[ega "II 8.6.1" "more general"]
def pushforwardNonnegSheafGradedAlgebra (hcomm : IsCommutative B)
    (hqc : ∀ n : ℤ,
      (((Scheme.Modules.pushforward p).obj (B.piece n) : S.Modules)).IsQuasicoherent) :
    SheafGradedAlgebra S :=
  nonnegSheafGradedAlgebra (pushforwardGradedAlgebra p B)
    (isCommutative_pushforwardGradedAlgebra p B hcomm) hqc

/-- In a nonnegative degree the data is the direct image of the corresponding piece of `B`. -/
theorem pushforwardNonnegSheafGradedAlgebra_piece_ofNat (hcomm : IsCommutative B)
    (hqc : ∀ n : ℤ,
      (((Scheme.Modules.pushforward p).obj (B.piece n) : S.Modules)).IsQuasicoherent)
    (n : ℕ) :
    (pushforwardNonnegSheafGradedAlgebra p B hcomm hqc).piece (.ofNat n) =
      (Scheme.Modules.pushforward p).obj (B.piece (.ofNat n)) :=
  rfl

end Pushforward

end Stacks.AlgebraicGeometry.NonnegTruncation

end
