module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule

/-!
# A right graded module over a commutative graded algebra is a left graded module

A right graded module over a sheaf of graded algebras `A` has an action
`M_n ⊗ A_i ⟶ M_{n + i}`, a left one an action `A_i ⊗ M_n ⟶ M_{i + n}`. When `A` is commutative
the two notions agree: the left action is the right action with its arguments exchanged. The
degrees `n + i` and `i + n` of the value agree only propositionally, so the exchanged action is a
transport of the right action along that equality, and every law of the left module is the
corresponding law of the right module read across the transport — for the associativity, together
with the commutativity of `A`.

The transport is pushed into a single auxiliary family
`SheafOfModules.GradedModule.flipSmul`, whose defining equality is stated with the target degree
as a *variable*. All of its computation rules are then proved by substituting that variable away,
after which the transport disappears and each rule is the matching field of the right module. The
degrees of the arguments and the value of an action cannot all be made to match on the nose, so
the rules that move a degree are heterogeneous equalities, exactly as the associativity and
unitality fields of a graded module already are.

## Main definitions

* `SheafOfModules.GradedModule.flipSmul`: the right action with its arguments exchanged and its
  value transported to the degree `i + n`.
* `SheafOfModules.GradedModule.toLeftGradedModule`: **a right graded module over a commutative
  sheaf of graded algebras, read as a left graded module.**

## Main results

* `SheafOfModules.GradedModule.flipSmul_heq`: the exchanged action is the right action.
* `SheafOfModules.GradedModule.smul_congr`: the right action is a congruence for heterogeneous
  equality of its arguments along equalities of their degrees.
* `SheafOfModules.GradedModule.toLeftGradedModule_smul_heq`: **the left action of the left graded
  module obtained is the right action of the right one.**

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

namespace GradedModule

variable (M : GradedModule.{t, a, m} A)

/-- The action of a right graded module with its arguments exchanged, its value transported from
the degree `n + i` to a degree `k` equal to it. Stating the target degree as a variable is what
lets every computation rule below be proved by substituting the equality away. -/
def flipSmul {i n k : ℤ} (hk : n + i = k) (U : Cᵒᵖ) :
    (A.piece i).val.obj U →+ (M.piece n).val.obj U →+ (M.piece k).val.obj U :=
  hk ▸ (M.smul n i U).flip

/-- **The exchanged action is the right action.** -/
theorem flipSmul_heq {i n k : ℤ} (hk : n + i = k) (U : Cᵒᵖ) (α : (A.piece i).val.obj U)
    (x : (M.piece n).val.obj U) : HEq (M.flipSmul hk U α x) (M.smul n i U x α) := by
  subst hk
  exact HEq.rfl

/-- The exchanged action is linear over the sheaf of rings in the algebra variable. -/
theorem flipSmul_smul_left {i n k : ℤ} (hk : n + i = k) (U : Cᵒᵖ) (r : R.obj.obj U)
    (α : (A.piece i).val.obj U) (x : (M.piece n).val.obj U) :
    M.flipSmul hk U (r • α) x = r • M.flipSmul hk U α x := by
  subst hk
  exact M.smul_smul_right n i U r x α

/-- The exchanged action is linear over the sheaf of rings in the module variable. -/
theorem flipSmul_smul_right {i n k : ℤ} (hk : n + i = k) (U : Cᵒᵖ) (r : R.obj.obj U)
    (α : (A.piece i).val.obj U) (x : (M.piece n).val.obj U) :
    M.flipSmul hk U α (r • x) = r • M.flipSmul hk U α x := by
  subst hk
  exact M.smul_smul_left n i U r x α

/-- The exchanged action commutes with restriction. -/
theorem flipSmul_naturality {i n k : ℤ} (hk : n + i = k) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : (A.piece i).val.obj U) (x : (M.piece n).val.obj U) :
    (M.piece k).val.map f (M.flipSmul hk U α x)
      = M.flipSmul hk V ((A.piece i).val.map f α) ((M.piece n).val.map f x) := by
  subst hk
  exact M.smul_naturality n i f x α

/-- **The action of a right graded module is a congruence for heterogeneous equality of its
arguments**, along equalities of the degrees they live in. -/
theorem smul_congr {n n' i i' : ℤ} (hn : n = n') (hi : i = i') (U : Cᵒᵖ)
    {x : (M.piece n).val.obj U} {x' : (M.piece n').val.obj U} (hx : HEq x x')
    {α : (A.piece i).val.obj U} {α' : (A.piece i').val.obj U} (hα : HEq α α') :
    HEq (M.smul n i U x α) (M.smul n' i' U x' α') := by
  subst hn
  subst hi
  rw [eq_of_heq hx, eq_of_heq hα]

/-- **A right graded module over a commutative sheaf of graded algebras, read as a left graded
module**: the left action is the right action with its arguments exchanged. -/
def toLeftGradedModule
    (hcomm : ∀ (i j : ℤ) (U : Cᵒᵖ) (α : (A.piece i).val.obj U) (β : (A.piece j).val.obj U),
      HEq ((A.mul i j).app U α β) ((A.mul j i).app U β α)) :
    LeftGradedModule.{t, a, m} A where
  piece := M.piece
  smul i n U := M.flipSmul (add_comm n i) U
  smul_smul_left _ _ U r α x := M.flipSmul_smul_left _ U r α x
  smul_smul_right _ _ U r α x := M.flipSmul_smul_right _ U r α x
  smul_naturality _ _ _ _ f α x := M.flipSmul_naturality _ f α x
  mul_smul i j n U α β x :=
    (M.flipSmul_heq _ U _ x).trans
      ((M.smul_congr rfl (add_comm i j) U HEq.rfl (hcomm i j U α β)).trans
        ((M.smul_mul n j i U x β α).symm.trans
          ((M.smul_congr (add_comm n j) rfl U (M.flipSmul_heq _ U β x).symm HEq.rfl).trans
            (M.flipSmul_heq _ U α _).symm)))
  one_smul n U x := (M.flipSmul_heq _ U _ x).trans (M.smul_one n U x)

/-- The left graded module read off a right one has the same pieces. -/
@[simp]
theorem toLeftGradedModule_piece
    (hcomm : ∀ (i j : ℤ) (U : Cᵒᵖ) (α : (A.piece i).val.obj U) (β : (A.piece j).val.obj U),
      HEq ((A.mul i j).app U α β) ((A.mul j i).app U β α)) (n : ℤ) :
    (toLeftGradedModule M hcomm).piece n = M.piece n := rfl

/-- **The left action of the left graded module read off a right one is the right action.** -/
theorem toLeftGradedModule_smul_heq
    (hcomm : ∀ (i j : ℤ) (U : Cᵒᵖ) (α : (A.piece i).val.obj U) (β : (A.piece j).val.obj U),
      HEq ((A.mul i j).app U α β) ((A.mul j i).app U β α)) (i n : ℤ) (U : Cᵒᵖ)
    (α : (A.piece i).val.obj U) (x : (M.piece n).val.obj U) :
    HEq ((toLeftGradedModule M hcomm).smul i n U α x) (M.smul n i U x α) :=
  M.flipSmul_heq _ U α x

end GradedModule

end SheafOfModules

end
