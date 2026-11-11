module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedModules
public import StacksCore.Tactic.StacksAttribute

/-!
# The sections of a graded bimodule form a graded bimodule

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of graded `O`-algebras and let `N` be a
graded `(A, B)`-bimodule. Following [Stacks, Tag 0FR4], for an object `U` of the site the
sections

`N(U) = Γ(U, N) = ⨁_n N^n(U)`

form a graded `(A(U), B(U))`-bimodule in the sense of [Stacks, Tag 0FQH], where
`A(U) = ⨁_n A^n(U)` and `B(U) = ⨁_n B^n(U)` are the graded rings of sections.

## Main definitions

* `Stacks.RightGradedModule.rightModuleTotal`: the direct sum of the homogeneous components of a
  right graded module is a right module over the direct sum of the homogeneous components of the
  algebra, written as a module over the opposite ring.
* `SheafOfModules.GradedBimodule.Sections N U`: the direct sum `⨁_n N^n(U)`, with its left
  `A(U)`-module structure (`SheafOfModules.GradedBimodule.leftModuleSections`) and its right
  `B(U)`-module structure (`SheafOfModules.GradedBimodule.rightModuleSections`).

## Main results

* `SheafOfModules.GradedBimodule.smulCommClass_sections`: **the two actions commute**,
  `a (x b) = (a x) b`, so `N(U)` is an `(A(U), B(U))`-bimodule; the actions are bilinear over
  `O(U)` (`isScalarTower_left_sections`, `smulCommClass_base_left_sections`,
  `isScalarTower_right_sections`, `smulCommClass_base_right_sections`).
* `SheafOfModules.GradedBimodule.incl_smul_incl` and `op_incl_smul_incl`: the grading is
  respected, `A^n(U) N^m(U) ⊂ N^{n + m}(U)` and `N^n(U) B^m(U) ⊂ N^{n + m}(U)`.

## Implementation notes

A right module is a module over the opposite ring, as in Mathlib. The direct sums are the ones of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedAlgebras.lean` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedModules.lean`; the left action is
`SheafOfModules.LeftGradedModule.moduleTotal` of the left graded module underlying `N`, and the
right action is `Stacks.RightGradedModule.act` of the right graded module underlying `N`. The
right action needs no commutativity: it is associativity of the right action read on the
opposite ring. The base is an arbitrary sheaf of rings and the universes are independent.

## References

* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FQH](https://stacks.math.columbia.edu/tag/0FQH)
-/

@[expose] public section

open CategoryTheory MulOpposite

universe t a m v u

namespace Stacks.RightGradedModule

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{a} R} {A : GradedAlgebra P}
  {Q : ι → PresheafOfModules.{m} R} (M : RightGradedModule A Q)

/-- **The right action is associative**: `x (a b) = (x a) b`. -/
lemma act_mul_right {X : Cᵒᵖ} (x : M.Total X) (a b : A.Total X) :
    M.act X x (a * b) = M.act X (M.act X x a) b := by
  induction x using M.incl_induction with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | incl n y =>
    induction a using A.incl_induction with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | incl i u =>
      induction b using A.incl_induction with
      | zero => simp only [mul_zero, map_zero]
      | incl j v =>
        rw [A.incl_mul_incl, M.act_incl_incl, M.act_incl_incl, M.act_incl_incl]
        exact (M.incl_eq_incl_of_heq (add_assoc n i j).symm (M.smul_mul n i j X y u v).symm)
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
    | add a a' ha ha' => simp only [add_mul, map_add, AddMonoidHom.add_apply, ha, ha']
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The direct sum of the homogeneous components of a right graded module is a right module
over the direct sum of the homogeneous components of the algebra**, over each object of the
site: `x • op a` is the right action `x a`. -/
noncomputable instance rightModuleTotal (X : Cᵒᵖ) : Module (A.Total X)ᵐᵒᵖ (M.Total X) where
  smul a x := M.act X x a.unop
  one_smul x := M.act_one x
  mul_smul a b x := M.act_mul_right x b.unop a.unop
  smul_zero a := congrArg (fun φ : A.Total X →+ M.Total X => φ a.unop) (map_zero (M.act X))
  smul_add a x y :=
    congrArg (fun φ : A.Total X →+ M.Total X => φ a.unop) (map_add (M.act X) x y)
  add_smul a b x := map_add (M.act X x) a.unop b.unop
  zero_smul x := map_zero (M.act X x)

/-- The right action of `op a` is the action `Stacks.RightGradedModule.act`. -/
lemma op_smul_eq_act {X : Cᵒᵖ} (a : A.Total X) (x : M.Total X) : op a • x = M.act X x a := rfl

end Stacks.RightGradedModule

namespace SheafOfModules.GradedBimodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R} (N : GradedBimodule.{t, a, m} A B)

/-- The sections `N(U) = ⨁_n N^n(U)` of a graded bimodule over an object of the site. -/
def Sections (X : Cᵒᵖ) : Type m := N.toGradedModule.toPresheafRightGradedModule.Total X

variable (X : Cᵒᵖ)

/-- The additive group of sections of a graded bimodule. -/
noncomputable instance : AddCommGroup (N.Sections X) :=
  inferInstanceAs (AddCommGroup (N.toGradedModule.toPresheafRightGradedModule.Total X))

/-- The module of sections of a graded bimodule over the ring of sections `O(U)`. -/
noncomputable instance : Module (R.obj.obj X) (N.Sections X) :=
  inferInstanceAs (Module (R.obj.obj X) (N.toGradedModule.toPresheafRightGradedModule.Total X))

/-- The sections `N(U)` are a left module over `A(U) = ⨁_n A^n(U)`. -/
noncomputable instance leftModuleSections :
    Module (A.toPresheafGradedAlgebra.Total X) (N.Sections X) :=
  inferInstanceAs (Module (A.toPresheafGradedAlgebra.Total X) (N.toLeftGradedModule.Total X))

/-- The sections `N(U)` are a right module over `B(U) = ⨁_n B^n(U)`. -/
noncomputable instance rightModuleSections :
    Module (B.toPresheafGradedAlgebra.Total X)ᵐᵒᵖ (N.Sections X) :=
  inferInstanceAs (Module (B.toPresheafGradedAlgebra.Total X)ᵐᵒᵖ
    (N.toGradedModule.toPresheafRightGradedModule.Total X))

variable {X}

/-- A homogeneous section of degree `n` of `N` over `U`, viewed in `N(U)`. -/
def incl (n : ℤ) (x : (N.piece n).val.obj X) : N.Sections X :=
  N.toGradedModule.toPresheafRightGradedModule.incl n x

/-- Every section of `N(U)` is a finite sum of homogeneous ones. -/
lemma incl_induction {motive : N.Sections X → Prop} (z : N.Sections X) (zero : motive 0)
    (incl : ∀ (n : ℤ) (x : (N.piece n).val.obj X), motive (N.incl n x))
    (add : ∀ z z', motive z → motive z' → motive (z + z')) : motive z :=
  N.toGradedModule.toPresheafRightGradedModule.incl_induction z zero incl add

/-- `incl` is linear over the ring of sections `O(U)`. -/
lemma incl_smul_base (n : ℤ) (r : R.obj.obj X) (x : (N.piece n).val.obj X) :
    N.incl n (r • x) = r • N.incl n x :=
  N.toGradedModule.toPresheafRightGradedModule.incl_smul n r x

/-- **`A^n(U) N^m(U) ⊂ N^{n + m}(U)`**: the left action of `A(U)` on homogeneous sections is the
left multiplication of the bimodule. -/
lemma incl_smul_incl (i n : ℤ) (a : (A.piece i).val.obj X) (x : (N.piece n).val.obj X) :
    A.toPresheafGradedAlgebra.incl i a • N.incl n x =
      N.incl (i + n) ((N.leftMul i n).app X a x) :=
  N.toLeftGradedModule.incl_smul_incl i n a x

/-- **`N^n(U) B^m(U) ⊂ N^{n + m}(U)`**: the right action of `B(U)` on homogeneous sections is the
right multiplication of the bimodule. -/
lemma op_incl_smul_incl (n i : ℤ) (x : (N.piece n).val.obj X) (b : (B.piece i).val.obj X) :
    op (B.toPresheafGradedAlgebra.incl i b) • N.incl n x =
      N.incl (n + i) ((N.rightMul n i).app X x b) :=
  N.toGradedModule.toPresheafRightGradedModule.act_incl_incl x b

/-- Two homogeneous sections of propositionally equal degrees which are heterogeneously equal have
the same image in `N(U)`. -/
lemma incl_eq_incl_of_heq {n n' : ℤ} (h : n = n') {x : (N.piece n).val.obj X}
    {y : (N.piece n').val.obj X} (hxy : HEq x y) : N.incl n x = N.incl n' y :=
  N.toGradedModule.toPresheafRightGradedModule.incl_eq_incl_of_heq h hxy

/-- **Stacks 0FR4: the two actions on the sections of a graded bimodule commute**,
`a (x b) = (a x) b`. Together with `leftModuleSections` and `rightModuleSections` this makes
`N(U) = ⨁_n N^n(U)` an `(A(U), B(U))`-bimodule, graded by `incl_smul_incl` and
`op_incl_smul_incl`, and bilinear over `O(U)` by `isScalarTower_left_sections`,
`smulCommClass_base_left_sections`, `isScalarTower_right_sections` and
`smulCommClass_base_right_sections`. -/
@[stacks 0FR4 "N(U) = ⨁ N^n(U) is a graded (A(U), B(U))-bimodule"]
instance smulCommClass_sections :
    SMulCommClass (A.toPresheafGradedAlgebra.Total X) (B.toPresheafGradedAlgebra.Total X)ᵐᵒᵖ
      (N.Sections X) where
  smul_comm a b z := by
    induction b using MulOpposite.rec' with | h b => ?_
    induction z using N.incl_induction with
    | zero => simp only [smul_zero]
    | incl n x =>
      induction a using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [zero_smul, smul_zero]
      | incl i u =>
        induction b using Stacks.GradedAlgebra.incl_induction with
        | zero => simp only [op_zero, zero_smul, smul_zero]
        | incl j v =>
          rw [N.op_incl_smul_incl, N.incl_smul_incl, N.incl_smul_incl, N.op_incl_smul_incl]
          exact N.incl_eq_incl_of_heq (add_assoc i n j).symm
            (N.left_right_assoc i n j X u x v).symm
        | add b b' hb hb' => simp only [MulOpposite.op_add, add_smul, smul_add, hb, hb']
      | add a a' ha ha' => simp only [add_smul, smul_add, ha, ha']
    | add z z' hz hz' => simp only [smul_add, hz, hz']

/-- The left action is linear over `O(U)` in the section of the algebra: `(r a) x = r (a x)`. -/
instance isScalarTower_left_sections :
    IsScalarTower (R.obj.obj X) (A.toPresheafGradedAlgebra.Total X) (N.Sections X) where
  smul_assoc r a z := by
    induction z using N.incl_induction with
    | zero => simp only [smul_zero]
    | incl n x =>
      induction a using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [smul_zero, zero_smul]
      | incl i u =>
        rw [← Stacks.GradedAlgebra.incl_smul, N.incl_smul_incl, N.incl_smul_incl,
          (N.leftMul i n).map_smul_left, N.incl_smul_base]
      | add a a' ha ha' => simp only [smul_add, add_smul, ha, ha']
    | add z z' hz hz' => simp only [smul_add, hz, hz']

/-- The left action is linear over `O(U)` in the section of the bimodule: `a (r x) = r (a x)`. -/
instance smulCommClass_base_left_sections :
    SMulCommClass (R.obj.obj X) (A.toPresheafGradedAlgebra.Total X) (N.Sections X) where
  smul_comm r a z := by
    induction z using N.incl_induction with
    | zero => simp only [smul_zero]
    | incl n x =>
      induction a using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [smul_zero, zero_smul]
      | incl i u =>
        rw [← N.incl_smul_base, N.incl_smul_incl, N.incl_smul_incl,
          (N.leftMul i n).map_smul_right, N.incl_smul_base]
      | add a a' ha ha' => simp only [smul_add, add_smul, ha, ha']
    | add z z' hz hz' => simp only [smul_add, hz, hz']

/-- The right action is linear over `O(U)` in the section of the algebra: `x (r b) = r (x b)`. -/
instance isScalarTower_right_sections :
    IsScalarTower (R.obj.obj X) (B.toPresheafGradedAlgebra.Total X)ᵐᵒᵖ (N.Sections X) where
  smul_assoc r b z := by
    induction b using MulOpposite.rec' with | h b => ?_
    induction z using N.incl_induction with
    | zero => simp only [smul_zero]
    | incl n x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [smul_zero, op_zero, zero_smul]
      | incl i v =>
        rw [← op_smul, ← Stacks.GradedAlgebra.incl_smul, N.op_incl_smul_incl,
          N.op_incl_smul_incl, (N.rightMul n i).map_smul_right, N.incl_smul_base]
      | add b b' hb hb' => simp only [smul_add, MulOpposite.op_add, add_smul, hb, hb']
    | add z z' hz hz' => simp only [smul_add, hz, hz']

/-- The right action is linear over `O(U)` in the section of the bimodule: `(r x) b = r (x b)`. -/
instance smulCommClass_base_right_sections :
    SMulCommClass (R.obj.obj X) (B.toPresheafGradedAlgebra.Total X)ᵐᵒᵖ (N.Sections X) where
  smul_comm r b z := by
    induction b using MulOpposite.rec' with | h b => ?_
    induction z using N.incl_induction with
    | zero => simp only [smul_zero]
    | incl n x =>
      induction b using Stacks.GradedAlgebra.incl_induction with
      | zero => simp only [smul_zero, op_zero, zero_smul]
      | incl i v =>
        rw [← N.incl_smul_base, N.op_incl_smul_incl, N.op_incl_smul_incl,
          (N.rightMul n i).map_smul_left, N.incl_smul_base]
      | add b b' hb hb' => simp only [smul_add, MulOpposite.op_add, add_smul, hb, hb']
    | add z z' hz hz' => simp only [smul_add, hz, hz']

end SheafOfModules.GradedBimodule
