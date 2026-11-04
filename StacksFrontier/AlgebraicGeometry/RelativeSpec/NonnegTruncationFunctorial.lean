module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.NonnegTruncation
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.GradedAlgebraSheafIso

/-!
# Functoriality of the nonnegative truncation of a sheaf of graded algebras

`Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation` is `A_{≥0}`, the sheaf of graded
algebras whose pieces are those of `A` in nonnegative degrees and zero objects in negative ones.
This file proves its functoriality in `A`: a unital homomorphism of sheaves of graded algebras
induces a unital homomorphism of the truncations, which is an isomorphism in every degree when the
given homomorphism is, and hence an isomorphism of the truncations' algebra sheaves.

## The construction

A homomorphism is truncated degreewise: in a nonnegative degree it is the given component, in a
negative degree it is the zero morphism between two zero objects. Multiplicativity splits into
the four cases of the two degrees' signs — in the one case where both are nonnegative it is the
given multiplicativity on the nose, since
`Stacks.AlgebraicGeometry.NonnegTruncation.mul_ofNat_ofNat` makes the truncated multiplication
the original one there, and in each of the other three both sides vanish by
`…NonnegTruncation.mul_app_apply_eq_zero_of_neg_left` and `…_of_neg_right`. Unitality is the
given unitality: the truncation's unit is `A.one` and its degree-zero piece is `A.piece 0`, both
by definition, `0` being `Int.ofNat 0`.

Invertibility is preserved degree by degree: in a nonnegative degree the component is unchanged,
and in a negative degree the zero morphism between two zero objects is an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.NonnegTruncation.homApp`: the degreewise components of the truncated
  homomorphism.
* `Stacks.AlgebraicGeometry.NonnegTruncation.unitalHom`: **a unital homomorphism of sheaves of
  graded algebras induces one of their nonnegative truncations.**
* `Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncationAlgebraSheafIso`: **an isomorphism
  of the truncations' algebra sheaves**, for a homomorphism invertible in every degree.

## Main results

* `Stacks.AlgebraicGeometry.NonnegTruncation.isIso_homApp`: **the truncated homomorphism is an
  isomorphism in every degree** as soon as the given one is.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped ZeroObject

namespace Stacks.AlgebraicGeometry.NonnegTruncation

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}}

attribute [local instance] hasZeroObject_sheafOfModules

variable {A B : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf}

/-! ### The degreewise components of a truncated homomorphism -/

/-- **The degreewise components of the nonnegative truncation of a homomorphism of sheaves of
graded algebras**: the given component in a nonnegative degree, and the zero morphism between the
two zero objects in a negative degree. -/
def homApp (f : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    ∀ n : ℤ, piece A n ⟶ piece B n
  | .ofNat n => f.app (.ofNat n)
  | .negSucc _ => 0

/-- In a nonnegative degree, the truncated component is the given component. -/
@[simp] theorem homApp_ofNat (f : SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℕ) :
    homApp f (.ofNat n) = f.app (.ofNat n) :=
  rfl

/-- In a negative degree, the truncated component is the zero morphism. -/
@[simp] theorem homApp_negSucc (f : SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℕ) :
    homApp f (.negSucc n) = 0 :=
  rfl

/-! ### The truncated homomorphism -/

/-- **A unital homomorphism of sheaves of graded algebras induces one of their nonnegative
truncations.**

Multiplicativity is the given multiplicativity where both degrees are nonnegative and `0 = 0`
elsewhere; unitality is the given unitality, the truncation's unit and degree-zero piece being
those of `A` by definition. -/
def unitalHom (f : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    SheafOfModules.GradedAlgebra.UnitalHom (nonnegTruncation A) (nonnegTruncation B) where
  app := homApp f
  map_mul i j U x y := by
    rcases i with a | a
    · rcases j with b | b
      · exact f.map_mul (.ofNat a) (.ofNat b) U x y
      · refine Eq.trans (congrArg (fun z => (homApp f ((a : ℤ) + Int.negSucc b)).val.app U z)
          (mul_app_apply_eq_zero_of_neg_right A (a : ℤ) b U x y)) ?_
        exact (map_zero _).trans
          (mul_app_apply_eq_zero_of_neg_right B (a : ℤ) b U _ _).symm
    · refine Eq.trans (congrArg (fun z => (homApp f (Int.negSucc a + j)).val.app U z)
        (mul_app_apply_eq_zero_of_neg_left A a j U x y)) ?_
      exact (map_zero _).trans (mul_app_apply_eq_zero_of_neg_left B a j U _ _).symm
  map_one U := f.map_one U

/-- The components of `unitalHom f` are the truncated components `homApp f`. -/
@[simp] theorem unitalHom_app (f : SheafOfModules.GradedAlgebra.UnitalHom A B) (n : ℤ) :
    (unitalHom f).app n = homApp f n :=
  rfl

/-! ### Invertibility -/

/-- **The truncated homomorphism is an isomorphism in every degree** as soon as the given one is.
In a nonnegative degree the component is unchanged; in a negative degree it is the zero morphism
between two zero objects, which is an isomorphism. -/
theorem isIso_homApp (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hf : ∀ m : ℤ, IsIso (f.app m)) (n : ℤ) : IsIso (homApp f n) := by
  rcases n with a | a
  · rw [homApp_ofNat]
    exact hf _
  · rw [homApp_negSucc]
    exact ⟨0, (isZero_piece_negSucc A a).eq_of_src _ _,
      (isZero_piece_negSucc B a).eq_of_src _ _⟩

/-! ### The algebra sheaves of the truncations -/

variable (A B)

/-- **An isomorphism of the algebra sheaves of the nonnegative truncations**, for a unital
homomorphism of sheaves of graded algebras which is an isomorphism in every degree. -/
def nonnegTruncationAlgebraSheafIso (hcA : IsCommutative A) (hcB : IsCommutative B)
    (f : SheafOfModules.GradedAlgebra.UnitalHom A B) (hf : ∀ m : ℤ, IsIso (f.app m)) :
    Stacks.RelativeSpec.gradedAlgebraSheaf S (nonnegTruncation A)
        (isCommutative_nonnegTruncation A hcA) ≅
      Stacks.RelativeSpec.gradedAlgebraSheaf S (nonnegTruncation B)
        (isCommutative_nonnegTruncation B hcB) :=
  haveI : ∀ n : ℤ, IsIso ((unitalHom f).app n) := isIso_homApp f hf
  Stacks.RelativeSpec.gradedAlgebraSheafIso S (isCommutative_nonnegTruncation A hcA)
    (isCommutative_nonnegTruncation B hcB) (unitalHom f)

end Stacks.AlgebraicGeometry.NonnegTruncation

end
