module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleLeftRight
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimodule

/-!
# A left graded module over a commutative graded algebra is a right graded module, and a bimodule

A left graded module over a sheaf of graded algebras `A` has an action `A_i ⊗ M_n ⟶ M_{i + n}`, a
right one an action `M_n ⊗ A_i ⟶ M_{n + i}`. When `A` is commutative the two notions agree: the
right action is the left action with its arguments exchanged. This file is the direction
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleLeftRight.lean` does not do — that file
reads a right graded module as a left one — and then puts the two actions together, making a left
graded module over a commutative `A` a graded `(A, A)`-bimodule.

As in that file the transport is pushed into a single auxiliary family
`SheafOfModules.LeftGradedModule.flipSmul`, whose defining equality is stated with the target
degree as a *variable*; each of its computation rules is proved by substituting that variable
away, after which the transport disappears and the rule is the matching field of the left module.
The rules that move a degree are heterogeneous equalities, exactly as the associativity and
unitality fields of a left graded module already are.

The graded relative tensor product takes a right module on the left and a left module on the
right, and carries an action only when the right-hand factor is a bimodule; so the bimodule
structure is what defines the relative tensor product `ℳ ⊗_𝒜 𝒩` of two left graded modules over a
commutative graded algebra, as in property (6) of [Stacks, Tag 01O7].

## Main definitions

* `SheafOfModules.GradedAlgebra.MulComm` is commutativity of the multiplication of a sheaf of
  graded algebras, which `SheafOfModules.GradedAlgebra` does not ask for.
* `SheafOfModules.LeftGradedModule.flipSmul`: the left action with its arguments exchanged and its
  value transported to the degree `n + i`.
* `SheafOfModules.LeftGradedModule.toGradedModule`: **a left graded module over a commutative
  sheaf of graded algebras, read as a right graded module.**
* `SheafOfModules.LeftGradedModule.toGradedBimodule`: **a left graded module over a commutative
  sheaf of graded algebras, read as a graded `(A, A)`-bimodule**, the left action being its own
  and the right action the exchanged one.

## Main results

* `SheafOfModules.LeftGradedModule.flipSmul_heq`: the exchanged action is the left action.
* `SheafOfModules.LeftGradedModule.smul_congr`: the left action is a congruence for heterogeneous
  equality of its arguments along equalities of their degrees.
* `SheafOfModules.LeftGradedModule.toGradedModule_smul_heq`: the right action of the right graded
  module obtained is the left action of the left one.
* `SheafOfModules.LeftGradedModule.toGradedBimodule_rightMul`: the right action of the bimodule
  is the action of the right graded module read off the same left graded module.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0FR5](https://stacks.math.columbia.edu/tag/0FR5)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace GradedAlgebra

/-- Commutativity of the multiplication of a sheaf of graded algebras.
`SheafOfModules.GradedAlgebra` does not ask for it, so it is an extra property. The two sides lie
in the pieces of the degrees `i + j` and `j + i`, which agree only propositionally, so the
statement is heterogeneous, exactly as the associativity field of a sheaf of graded algebras
is. -/
abbrev MulComm (A : GradedAlgebra.{t, a} R) : Prop :=
  ∀ (i j : ℤ) (U : Cᵒᵖ) (α : (A.piece i).val.obj U) (β : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U α β) ((A.mul j i).app U β α)

end GradedAlgebra

variable {A : GradedAlgebra.{t, a} R}

namespace LeftGradedModule

variable (M : LeftGradedModule.{t, a, m} A)

/-- The action of a left graded module with its arguments exchanged, its value transported from
the degree `i + n` to a degree `k` equal to it. Stating the target degree as a variable is what
lets every computation rule below be proved by substituting the equality away. -/
def flipSmul {n i k : ℤ} (hk : i + n = k) (U : Cᵒᵖ) :
    (M.piece n).val.obj U →+ (A.piece i).val.obj U →+ (M.piece k).val.obj U :=
  hk ▸ (M.smul i n U).flip

/-- **The exchanged action is the left action.** -/
theorem flipSmul_heq {n i k : ℤ} (hk : i + n = k) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (α : (A.piece i).val.obj U) : HEq (M.flipSmul hk U x α) (M.smul i n U α x) := by
  subst hk
  exact HEq.rfl

/-- The exchanged action is linear over the sheaf of rings in the module variable. -/
theorem flipSmul_smul_left {n i k : ℤ} (hk : i + n = k) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : (M.piece n).val.obj U) (α : (A.piece i).val.obj U) :
    M.flipSmul hk U (r • x) α = r • M.flipSmul hk U x α := by
  subst hk
  exact M.smul_smul_right i n U r α x

/-- The exchanged action is linear over the sheaf of rings in the algebra variable. -/
theorem flipSmul_smul_right {n i k : ℤ} (hk : i + n = k) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : (M.piece n).val.obj U) (α : (A.piece i).val.obj U) :
    M.flipSmul hk U x (r • α) = r • M.flipSmul hk U x α := by
  subst hk
  exact M.smul_smul_left i n U r α x

/-- The exchanged action commutes with restriction. -/
theorem flipSmul_naturality {n i k : ℤ} (hk : i + n = k) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (M.piece n).val.obj U) (α : (A.piece i).val.obj U) :
    (M.piece k).val.map f (M.flipSmul hk U x α)
      = M.flipSmul hk V ((M.piece n).val.map f x) ((A.piece i).val.map f α) := by
  subst hk
  exact M.smul_naturality i n f α x

/-- **The action of a left graded module is a congruence for heterogeneous equality of its
arguments**, along equalities of the degrees they live in. -/
theorem smul_congr {i i' n n' : ℤ} (hi : i = i') (hn : n = n') (U : Cᵒᵖ)
    {α : (A.piece i).val.obj U} {α' : (A.piece i').val.obj U} (hα : HEq α α')
    {x : (M.piece n).val.obj U} {x' : (M.piece n').val.obj U} (hx : HEq x x') :
    HEq (M.smul i n U α x) (M.smul i' n' U α' x') := by
  subst hi
  subst hn
  rw [eq_of_heq hα, eq_of_heq hx]

/-- **A left graded module over a commutative sheaf of graded algebras, read as a right graded
module**: the right action is the left action with its arguments exchanged. -/
def toGradedModule (hcomm : A.MulComm) : GradedModule.{t, a, m} A where
  piece := M.piece
  smul n i U := M.flipSmul (add_comm i n) U
  smul_smul_left _ _ U r x α := M.flipSmul_smul_left _ U r x α
  smul_smul_right _ _ U r x α := M.flipSmul_smul_right _ U r x α
  smul_naturality _ _ _ _ f x α := M.flipSmul_naturality _ f x α
  smul_mul n i j U x α β :=
    (M.flipSmul_heq _ U _ β).trans
      ((M.smul_congr rfl (add_comm n i) U HEq.rfl (M.flipSmul_heq _ U x α)).trans
        ((M.mul_smul j i n U β α x).symm.trans
          ((M.smul_congr (add_comm j i) rfl U (hcomm j i U β α) HEq.rfl).trans
            (M.flipSmul_heq _ U x _).symm)))
  smul_one n U x := (M.flipSmul_heq _ U x _).trans (M.one_smul n U x)

/-- The pieces of the right graded module read off a left graded module are its own pieces. -/
@[simp]
theorem toGradedModule_piece (hcomm : A.MulComm) (n : ℤ) :
    (M.toGradedModule hcomm).piece n = M.piece n := rfl

/-- **The right action of the right graded module read off a left one is the left action.** -/
theorem toGradedModule_smul_heq (hcomm : A.MulComm) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.piece n).val.obj U) (α : (A.piece i).val.obj U) :
    HEq ((M.toGradedModule hcomm).smul n i U x α) (M.smul i n U α x) :=
  M.flipSmul_heq _ U x α

/-- The left action of a left graded module, as a bilinear map on sections. -/
def leftMulBil (i n : ℤ) : BilinearMap (A.piece i) (M.piece n) (M.piece (i + n)) where
  app := M.smul i n
  map_smul_left := M.smul_smul_left i n
  map_smul_right := M.smul_smul_right i n
  naturality f α x := M.smul_naturality i n f α x

/-- The exchanged action of a left graded module over a commutative sheaf of graded algebras, as
a bilinear map on sections. -/
def rightMulBil (n i : ℤ) : BilinearMap (M.piece n) (A.piece i) (M.piece (n + i)) where
  app := M.flipSmul (add_comm i n)
  map_smul_left U r x α := M.flipSmul_smul_left _ U r x α
  map_smul_right U r x α := M.flipSmul_smul_right _ U r x α
  naturality f x α := M.flipSmul_naturality _ f x α

/-- **A left graded module over a commutative sheaf of graded algebras, read as a graded
`(A, A)`-bimodule**: the left action is its own and the right action is the exchanged one. The two
commute because `A` is commutative. -/
def toGradedBimodule (hcomm : A.MulComm) : GradedBimodule.{t, a, m} A A where
  piece := M.piece
  leftMul := M.leftMulBil
  rightMul := M.rightMulBil
  left_assoc i j n U α β x := (M.mul_smul i j n U α β x).symm
  right_assoc n i j U x α β := (M.toGradedModule hcomm).smul_mul n i j U x α β
  left_right_assoc i n j U α x β :=
    (M.flipSmul_heq _ U _ β).trans
      (((M.mul_smul j i n U β α x).symm.trans
        ((M.smul_congr (add_comm j i) rfl U (hcomm j i U β α) HEq.rfl).trans
          (M.mul_smul i j n U α β x))).trans
        (M.smul_congr rfl (add_comm j n) U HEq.rfl (M.flipSmul_heq _ U x β).symm))
  one_left n U x := M.one_smul n U x
  one_right n U x := (M.toGradedModule hcomm).smul_one n U x

/-- The pieces of the bimodule read off a left graded module are its own pieces. -/
@[simp]
theorem toGradedBimodule_piece (hcomm : A.MulComm) (n : ℤ) :
    (M.toGradedBimodule hcomm).piece n = M.piece n := rfl

/-- The left action of the bimodule read off a left graded module is the action it was built
from. -/
theorem toGradedBimodule_leftMul (hcomm : A.MulComm) (i n : ℤ) (U : Cᵒᵖ) :
    ((M.toGradedBimodule hcomm).leftMul i n).app U = M.smul i n U := rfl

/-- The right action of the bimodule read off a left graded module is the action of the right
graded module read off it directly. -/
theorem toGradedBimodule_rightMul (hcomm : A.MulComm) (n i : ℤ) (U : Cᵒᵖ) :
    ((M.toGradedBimodule hcomm).rightMul n i).app U = (M.toGradedModule hcomm).smul n i U := rfl

end LeftGradedModule

end SheafOfModules

end
