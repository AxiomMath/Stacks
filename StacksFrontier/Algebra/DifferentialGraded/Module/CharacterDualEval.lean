module

public import Mathlib.Algebra.Module.CharacterModule
public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
public import StacksFrontier.Algebra.DirectSum.ParityOperator
public import StacksFrontier.Algebra.DifferentialGraded.LeftModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDualRight
public import StacksCore.Tactic.StacksAttribute

/-! # The evaluation map of a right differential graded module into its double dual

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `M` be a
*right* differential graded `A`-module. Taking the graded `ℚ/ℤ`-dual twice returns a right
module: `M^∨ = DifferentialGradedModule.dual M` is a *left* module
(`StacksFrontier/Algebra/DifferentialGraded/Module/CharacterDualRight.lean`) and
`(M^∨)^∨ = DifferentialGraded.LeftModule.dual (dual M)` is a right module again
(`StacksFrontier/Algebra/DifferentialGraded/Module/CharacterDual.lean`). This file constructs the
canonical evaluation homomorphism `M ⟶ (M^∨)^∨`, `x ↦ (λ ↦ λ x)`, and shows that it is
injective, which is the statement of Stacks 0FQD that makes `ℚ/ℤ` an injective cogenerator
usable in the differential graded setting.

The file also supplies, for the dual of a *right* module, the degree-piece identification that
`CharacterDual.lean` already has for the dual of a left module: the degree-`n` part of `M^∨` is
the character module of `M^{-n}`. That identification is about the grading only, so its
statements and proofs are the mirror images of the ones in `CharacterDual.lean`; in particular
the sign of the dual differential, which is the one genuine difference between the two duals,
plays no part in it.

## Main definitions

* `DifferentialGradedModule.CharacterDual.dualPieceEquiv`: the degree-`n` part of `M^∨` is the
  character module of `M^{-n}`, together with the underlying restriction map
  `dualPieceRestrict` and its inverse-on-the-nose `extendChar`, extension by zero.
* `DifferentialGradedModule.CharacterDual.dualChar`: a point of `M^∨`, read as a character of
  `M`; the elementwise reader through which every statement about `M^∨` is proved.
* `DifferentialGradedModule.CharacterDual.evalChar`: the character of `M^∨` given by evaluation
  at a point of `M`.
* `DifferentialGradedModule.dualEval`: **the evaluation map `M → (M^∨)^∨`** (Stacks 0FQD).

## Main results

* `DifferentialGradedModule.CharacterDual.evalChar_mem_dualPiece`: evaluation at a homogeneous
  element of degree `n` is a homogeneous character of `M^∨` of degree `n`.
* `DifferentialGradedModule.CharacterDual.dualChar_d_eq`: evaluation intertwines the
  differential of `M` with the differential of `(M^∨)^∨`. This is the only step where the signs
  of the two dual differentials are visible, and they cancel.
* `DifferentialGradedModule.dualEval_injective`: the evaluation map is injective.

## Implementation notes

*Why the reader functions.* The carrier `(dual M).M` is equal to the subtype
`↥(CharacterDual.dualSub M)` only by default-transparency unfolding, and both instance search
and the `change` tactic run below that. Facts about `M^∨` are therefore stated through the
reader `dualChar` and discharged by `exact` or plain application, never by `change`; this is the
same discipline as in `CharacterDual.lean`.

*The sign in `dualChar_d_eq`.* For `λ ∈ (M^∨)^m` and `x ∈ M^n` the parity operator of `M^∨`
contributes `(-1)^m` and the differential of `M^∨` contributes `-(-1)^n` (the leading minus is
what distinguishes the dual of a right module), so evaluation picks up `-(-1)^{m+n}`. Since
`d x ∈ M^{n+1}` and `λ` is supported on `M^{-m}`, the only case in which `λ (d x)` can be
nonzero is `-m = n + 1`, and there `-(-1)^{m+n} = 1`; otherwise both sides vanish. Hence the
case split on `-m = n + 1` in the proof.

*Injectivity.* A nonzero `x` has a nonzero homogeneous component `x_{-m}`, and `ℚ/ℤ` separates
the points of `M^{-m}`; extending the separating character by zero with `extendChar M m` gives
a homogeneous character of degree `m` whose value at `x` is nonzero. This is exactly why Part 1
is needed before Part 2.

## References

* [Stacks Project, Tag 0FQD](https://stacks.math.columbia.edu/tag/0FQD)
* [Stacks Project, Tag 09K3](https://stacks.math.columbia.edu/tag/09K3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule.CharacterDual

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

attribute [local instance] charModule charIsScalarTower

/-! ### The degree-`n` part of the dual of a right module -/

/-- Restriction of a homogeneous character of degree `n` to the graded piece `M^{-n}` it is
supported on. -/
def dualPieceRestrict (M : DifferentialGradedModule A) (n : ℤ) :
    dualPiece M n →ₗ[R] CharacterModule (M.grading (-n)) where
  toFun l := CharacterModule.dual (M.grading (-n)).subtype (l : CharacterModule M.M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the supporting graded piece, applied to an element. -/
theorem dualPieceRestrict_apply (M : DifferentialGradedModule A) (n : ℤ) (l : dualPiece M n)
    (x : M.grading (-n)) : dualPieceRestrict M n l x = (l : CharacterModule M.M) (x : M.M) :=
  rfl

/-- A homogeneous character is determined by its restriction to the graded piece it is
supported on. -/
theorem dualPieceRestrict_injective (M : DifferentialGradedModule A) (n : ℤ) :
    Function.Injective (dualPieceRestrict M n) := by
  intro l l' h
  apply Subtype.ext
  ext x
  refine induction_homogeneous (M := M)
    (p := fun y => (l : CharacterModule M.M) y = (l' : CharacterModule M.M) y) x
    (fun m y hy => ?_) (by simp) (fun y z hy hz => by rw [map_add, map_add, hy, hz])
  by_cases hm : m = -n
  · have hy' : y ∈ M.grading (-n) := hm ▸ hy
    simpa only [dualPieceRestrict_apply] using DFunLike.congr_fun h ⟨y, hy'⟩
  · rw [l.2 m hm y hy, l'.2 m hm y hy]

/-- Extension of a character of `M^{-n}` to a character of `M`, by zero on the other graded
pieces. -/
def extendChar (M : DifferentialGradedModule A) (n : ℤ)
    (μ : CharacterModule (M.grading (-n))) : CharacterModule M.M :=
  μ.comp ((DFinsupp.evalAddMonoidHom (-n)).comp
    (DirectSum.decomposeAddEquiv M.grading).toAddMonoidHom)

/-- The extension by zero of a character of `M^{-n}`, evaluated at a point: it reads off the
degree-`(-n)` component. -/
@[simp] theorem extendChar_apply (M : DifferentialGradedModule A) (n : ℤ)
    (μ : CharacterModule (M.grading (-n))) (x : M.M) :
    extendChar M n μ x = μ ((DirectSum.decompose M.grading x) (-n)) := rfl

/-- A character extended by zero from `M^{-n}` is homogeneous of degree `n`. -/
theorem extendChar_mem (M : DifferentialGradedModule A) (n : ℤ)
    (μ : CharacterModule (M.grading (-n))) : extendChar M n μ ∈ dualPiece M n := by
  intro m hm y hy
  rw [extendChar_apply, show ((DirectSum.decompose M.grading y) (-n)) = 0 from
    Subtype.ext (DirectSum.decompose_of_mem_ne M.grading hy hm), map_zero]

/-- Every character of `M^{-n}` is the restriction of a homogeneous character of degree `n`,
namely of its extension by zero. -/
theorem dualPieceRestrict_surjective (M : DifferentialGradedModule A) (n : ℤ) :
    Function.Surjective (dualPieceRestrict M n) := by
  intro μ
  refine ⟨⟨extendChar M n μ, extendChar_mem M n μ⟩, ?_⟩
  ext x
  rw [dualPieceRestrict_apply]
  change extendChar M n μ (x : M.M) = μ x
  rw [extendChar_apply,
    show ((DirectSum.decompose M.grading (x : M.M)) (-n)) = x from
      Subtype.ext (DirectSum.decompose_of_mem_same M.grading x.2)]

/-- **The degree-`n` part of `M^∨` is the character module of `M^{-n}`**, for `M` a right
differential graded module. This is the mirror image of
`DifferentialGraded.LeftModule.dualPieceEquiv`. -/
def dualPieceEquiv (M : DifferentialGradedModule A) (n : ℤ) :
    dualPiece M n ≃ₗ[R] CharacterModule (M.grading (-n)) :=
  LinearEquiv.ofBijective (dualPieceRestrict M n)
    ⟨dualPieceRestrict_injective M n, dualPieceRestrict_surjective M n⟩

/-! ### Reading the dual of a right module elementwise -/

/-- A point of the graded dual `M^∨`, read as a character of `M`. -/
def dualChar {M : DifferentialGradedModule A} (x : (dual M).M) : CharacterModule M.M :=
  (show ↥(dualSub M) from x).1

/-- A point of the dual is determined by the character underlying it. -/
theorem dualChar_injective {M : DifferentialGradedModule A} :
    Function.Injective (dualChar (M := M)) :=
  fun _ _ h => Subtype.ext (p := fun l => l ∈ dualCarrier M) h

/-- The character underlying a point of the dual is a sum of homogeneous characters. -/
theorem dualChar_mem {M : DifferentialGradedModule A} (x : (dual M).M) :
    dualChar x ∈ dualCarrier M := (show ↥(dualSub M) from x).2

/-- The character underlying the zero point of the dual is the zero character. -/
@[simp] theorem dualChar_zero {M : DifferentialGradedModule A} :
    dualChar (0 : (dual M).M) = 0 := rfl

/-- The reader `dualChar` is additive. -/
@[simp] theorem dualChar_add {M : DifferentialGradedModule A} (x y : (dual M).M) :
    dualChar (x + y) = dualChar x + dualChar y := rfl

/-- The reader `dualChar` is `R`-linear. -/
@[simp] theorem dualChar_smul {M : DifferentialGradedModule A} (r : R) (x : (dual M).M) :
    dualChar (r • x) = r • dualChar x := rfl

/-- The reader `dualChar` commutes with integer scaling. -/
theorem dualChar_zsmul {M : DifferentialGradedModule A} (c : ℤ) (x : (dual M).M) :
    dualChar (c • x) = c • dualChar x := rfl

/-- Homogeneity in `M^∨` is support of the underlying character in a single degree. -/
theorem mem_dual_grading {M : DifferentialGradedModule A} {n : ℤ} {x : (dual M).M} :
    x ∈ (dual M).grading n ↔ dualChar x ∈ dualPiece M n :=
  Submodule.mem_inducedGrading

/-- The differential of `M^∨`, read on underlying characters. -/
theorem dualChar_d {M : DifferentialGradedModule A} (x : (dual M).M) :
    dualChar ((dual M).d x) = dualD0 M (dualChar x) := rfl

/-- The left action on `M^∨`, read on underlying characters. -/
theorem dualChar_action {M : DifferentialGradedModule A} (a : A.A) (x : (dual M).M) :
    dualChar (a • x) = charSMul M a (dualChar x) := rfl

/-- A homogeneous-sum character of `M`, read as a point of `M^∨`. -/
def dualOf {M : DifferentialGradedModule A} (l : CharacterModule M.M)
    (hl : l ∈ dualCarrier M) : (dual M).M := ⟨l, hl⟩

/-- Reading back the character a point of `M^∨` was built from. -/
@[simp] theorem dualChar_dualOf {M : DifferentialGradedModule A} (l : CharacterModule M.M)
    (hl : l ∈ dualCarrier M) : dualChar (dualOf l hl) = l := rfl

/-- The sum of two characters, evaluated at a point. -/
theorem add_char_apply (M : DifferentialGradedModule A) (l l' : CharacterModule M.M)
    (y : M.M) : (l + l') y = l y + l' y := rfl

/-! ### Evaluation as a character of the dual -/

/-- Evaluation at a point of `M`, as a character of `M^∨`: the map `λ ↦ λ x`. This is the
character that the double-dual evaluation map assigns to `x`. -/
def evalChar {M : DifferentialGradedModule A} (x : M.M) :
    CharacterModule ((dual M).M) :=
  AddMonoidHom.mk' (fun l => dualChar l x) (fun _ _ => rfl)

/-- Evaluation at a point of `M`, applied to a point of `M^∨`. -/
@[simp] theorem evalChar_apply {M : DifferentialGradedModule A} (x : M.M)
    (l : (dual M).M) : evalChar x l = dualChar l x := rfl

/-- Evaluation at `0` is the zero character. -/
theorem evalChar_zero (M : DifferentialGradedModule A) :
    evalChar (M := M) 0 = 0 := by
  ext l
  exact map_zero (dualChar l)

/-- Evaluation is additive in the point of `M`. -/
theorem evalChar_add {M : DifferentialGradedModule A} (x y : M.M) :
    evalChar (x + y) = evalChar x + evalChar y := by
  ext l
  exact map_add (dualChar l) x y

/-- Evaluation is `R`-linear in the point of `M`. -/
theorem evalChar_smul {M : DifferentialGradedModule A} (r : R) (x : M.M) :
    evalChar (r • x) = r • evalChar (M := M) x := rfl

/-- Evaluation turns the right `A`-action on `M` into the right `A`-action on the characters of
`M^∨`: this is the compatibility `(λ · a)(x) = λ (x · a)` read backwards. -/
theorem evalChar_charSMul (M : DifferentialGradedModule A) (a : A.A) (x : M.M) :
    evalChar (MulOpposite.op a • x)
      = DifferentialGraded.LeftModule.charSMul (dual M) (MulOpposite.op a) (evalChar x) := by
  ext l
  rfl

/-- Evaluation at a homogeneous element of degree `n` is a homogeneous character of `M^∨` of
degree `n`: a character of `M^∨` of degree `m ≠ -n` is supported on `(M^∨)^{-m}`, whose members
are supported on `M^m`, and `-n ≠ m` means they kill `M^n`. -/
theorem evalChar_mem_dualPiece (M : DifferentialGradedModule A) {n : ℤ} {x : M.M}
    (hx : x ∈ M.grading n) :
    evalChar x ∈ DifferentialGraded.LeftModule.dualPiece (dual M) n := by
  intro m hm y hy
  exact (mem_dual_grading.mp hy) n (fun h => hm (by omega)) x hx

/-- Evaluation at an arbitrary point of `M` lands in the carrier of the double dual: decompose
the point into homogeneous components and apply the homogeneous case to each. -/
theorem evalChar_mem_dualCarrier (M : DifferentialGradedModule A) (x : M.M) :
    evalChar x ∈ DifferentialGraded.LeftModule.dualCarrier (dual M) := by
  refine induction_homogeneous (M := M)
    (p := fun y => evalChar y ∈ DifferentialGraded.LeftModule.dualCarrier (dual M)) x
    (fun n y hy => Submodule.mem_iSup_of_mem n (evalChar_mem_dualPiece M hy)) ?_ ?_
  · rw [evalChar_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [evalChar_add]
    exact Submodule.add_mem _ hy hz

/-- The sign identity behind the compatibility of evaluation with the differentials: when the
degree at which `λ (d x)` can be nonzero is actually hit, the two Koszul signs multiply to
`-1`, which cancels the leading minus of the dual differential of a right module. -/
theorem negOnePow_mul_of_neg_eq_succ {m n : ℤ} (h : -m = n + 1) :
    (m.negOnePow : ℤ) * (n.negOnePow : ℤ) = -1 := by
  have hm : m = -(n + 1) := by omega
  subst hm
  rw [Int.negOnePow_neg, Int.negOnePow_succ, Units.val_neg, neg_mul, negOnePow_mul_self]

/-- **Evaluation intertwines the differentials.** For a point `l` of `M^∨` and a point `x` of
`M`, evaluating `l` on `d x` is the same as evaluating the signed differential of `l` on `x`.
For `l` of degree `m` and `x` of degree `n` the parity operator of `M^∨` contributes `(-1)^m`
and the differential of `M^∨` contributes `-(-1)^n`; since `d x ∈ M^{n+1}` and `l` is supported
on `M^{-m}`, either `-m = n + 1`, where `-(-1)^{m+n} = 1`, or both sides vanish. -/
theorem dualChar_d_eq (M : DifferentialGradedModule A) (l : (dual M).M) (x : M.M) :
    dualChar l (M.d x)
      = dualChar (DifferentialGraded.LeftModule.signedDifferential (dual M) l) x := by
  refine DifferentialGraded.LeftModule.induction_homogeneous (M := dual M)
    (p := fun z => ∀ y : M.M, dualChar z (M.d y)
      = dualChar (DifferentialGraded.LeftModule.signedDifferential (dual M) z) y)
    l ?_ ?_ ?_ x
  · intro m z hz y
    refine induction_homogeneous (M := M) (p := fun w => dualChar z (M.d w)
      = dualChar (DifferentialGraded.LeftModule.signedDifferential (dual M) z) w) y
      (fun n w hw => ?_) (by simp) (fun w w' hw hw' => by simp only [map_add, hw, hw'])
    have key : dualChar (DifferentialGraded.LeftModule.signedDifferential (dual M) z) w
        = -((m.negOnePow * n.negOnePow : ℤ) • dualChar z (M.d w)) := by
      rw [DifferentialGraded.LeftModule.signedDifferential_apply_mem (dual M) hz,
        dualChar_zsmul, dualChar_d, zsmul_char_apply, dualD0_apply,
        signedDifferential_apply_mem M hw, map_neg, map_zsmul, smul_neg, smul_smul]
    by_cases hc : -m = n + 1
    · simp [key, negOnePow_mul_of_neg_eq_succ hc]
    · simp [key, (mem_dual_grading.mp hz) (n + 1) (fun h => hc h.symm) _ (M.d_mem n w hw)]
  · intro y
    rw [map_zero (DifferentialGraded.LeftModule.signedDifferential (dual M)), dualChar_zero]
    rfl
  · intro z z' hz hz' y
    rw [dualChar_add, map_add, dualChar_add, add_char_apply, add_char_apply, hz y, hz' y]

/-- Evaluation commutes with the differentials, at the level of characters: this is
`dualChar_d_eq` packaged as an identity between characters of `M^∨`. -/
theorem evalChar_d (M : DifferentialGradedModule A) (x : M.M) :
    evalChar (M.d x)
      = DifferentialGraded.LeftModule.dualD0 (dual M) (evalChar x) := by
  ext l
  exact dualChar_d_eq M l x

end DifferentialGradedModule.CharacterDual

namespace DifferentialGradedModule

open CharacterDual

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The underlying `R`-linear map of the evaluation map into the double dual. -/
def dualEvalFun (M : DifferentialGradedModule A) :
    M.M →ₗ[R] (DifferentialGraded.LeftModule.dual (dual M)).M where
  toFun x := DifferentialGraded.LeftModule.dualOf (evalChar x) (evalChar_mem_dualCarrier M x)
  map_add' x y := DifferentialGraded.LeftModule.dualChar_injective (evalChar_add x y)
  map_smul' r x := DifferentialGraded.LeftModule.dualChar_injective (evalChar_smul r x)

/-- The evaluation map, read on underlying characters of `M^∨`. -/
@[simp] theorem dualChar_dualEvalFun (M : DifferentialGradedModule A) (x : M.M) :
    DifferentialGraded.LeftModule.dualChar (dualEvalFun M x) = evalChar x := rfl

/-- **The evaluation map `M → (M^∨)^∨`** (Stacks 0FQD). A point `x` of `M` is sent to the
character `λ ↦ λ x` of the graded dual `M^∨`; this is a homomorphism of right differential
graded `A`-modules, the degree, the action and the differential all being respected. -/
def dualEval (M : DifferentialGradedModule A) :
    M ⟶ DifferentialGraded.LeftModule.dual (dual M) where
  toFun := dualEvalFun M
  map_smul x a := DifferentialGraded.LeftModule.dualChar_injective
    ((evalChar_charSMul M a x).trans
      (DifferentialGraded.LeftModule.dualChar_op_smul a (dualEvalFun M x)).symm)
  map_grading _ _ hx :=
    DifferentialGraded.LeftModule.mem_dual_grading.mpr (evalChar_mem_dualPiece M hx)
  map_d := LinearMap.ext (fun x => DifferentialGraded.LeftModule.dualChar_injective
    ((evalChar_d M x).trans (DifferentialGraded.LeftModule.dualChar_d (dualEvalFun M x)).symm))

/-- Evaluation at a nonzero point of `M` is a nonzero character of `M^∨`: a nonzero point has a
nonzero homogeneous component `x_{-m}`, the group `ℚ/ℤ` separates the points of `M^{-m}`, and
the extension by zero of a separating character is a point of `M^∨` not killing `x`. -/
theorem evalChar_ne_zero (M : DifferentialGradedModule A) {x : M.M} (hx : x ≠ 0) :
    evalChar x ≠ 0 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (DirectSum.decompose M.grading x) n ≠ 0 := by
    by_contra hcon
    refine hx ?_
    rw [← DirectSum.sum_support_decompose M.grading x]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    exact absurd ⟨i, DFinsupp.mem_support_iff.mp hi⟩ hcon
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, -m = n := ⟨-n, neg_neg n⟩
  obtain ⟨μ, hμ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hn
  intro h0
  have hl : extendChar M m μ ∈ dualCarrier M :=
    Submodule.mem_iSup_of_mem m (extendChar_mem M m μ)
  exact hμ ((extendChar_apply M m μ x).symm.trans (DFunLike.congr_fun h0 (dualOf _ hl)))

/-- The evaluation map into the double dual is injective, because the characters supported in a
single degree separate the points of `M`. -/
theorem dualEval_injective (M : DifferentialGradedModule A) :
    Function.Injective (dualEval M).toFun := by
  intro x y h
  rw [← sub_eq_zero]
  by_contra hne
  refine evalChar_ne_zero M hne ?_
  have h0 : dualEvalFun M (x - y) = 0 := by
    rw [map_sub, show dualEvalFun M x = dualEvalFun M y from h, sub_self]
  exact congrArg DifferentialGraded.LeftModule.dualChar h0

end DifferentialGradedModule

end
