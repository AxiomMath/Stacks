module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.NonnegTruncationFunctorial

/-!
# The inclusion of the nonnegative truncation of a sheaf of graded algebras

`Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation A` is `A_{≥0}`: the pieces of `A` in
nonnegative degrees and zero objects in negative ones. **This file supplies the inclusion
`A_{≥0} ⟶ A`** as a unital homomorphism of sheaves of graded algebras — the identity in a
nonnegative degree and the zero morphism out of a zero object in a negative one — and its
naturality: for a unital homomorphism `f : A ⟶ B`, the truncation of `f` followed by the
inclusion of `B_{≥0}` is the inclusion of `A_{≥0}` followed by `f`.

## Main definitions

* `Stacks.AlgebraicGeometry.NonnegTruncation.inclusionApp`: the degreewise components.
* `Stacks.AlgebraicGeometry.NonnegTruncation.inclusion`: **the inclusion `A_{≥0} ⟶ A`** as a
  unital homomorphism.

## Main results

* `Stacks.AlgebraicGeometry.NonnegTruncation.unitalHom_comp_inclusion`: the inclusion is natural
  in `A`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped ZeroObject

namespace Stacks.AlgebraicGeometry.NonnegTruncation

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}}

attribute [local instance] hasZeroObject_sheafOfModules

variable {A B : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf}

/-- **The degreewise components of the inclusion `A_{≥0} ⟶ A`**: the identity in a nonnegative
degree, where the truncation is `A`, and the zero morphism out of the zero object in a negative
one. -/
def inclusionApp (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf) :
    ∀ n : ℤ, piece A n ⟶ A.piece n
  | .ofNat _ => 𝟙 _
  | .negSucc _ => 0

/-- In a nonnegative degree `n`, the component of the inclusion `A_{≥0} ⟶ A` is the identity. -/
@[simp] theorem inclusionApp_ofNat (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
    (n : ℕ) : inclusionApp A (.ofNat n) = 𝟙 _ :=
  rfl

/-- In a negative degree `Int.negSucc n`, the component of the inclusion `A_{≥0} ⟶ A` is zero. -/
@[simp] theorem inclusionApp_negSucc (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
    (n : ℕ) : inclusionApp A (.negSucc n) = 0 :=
  rfl

/-- **The inclusion `A_{≥0} ⟶ A` of the nonnegative truncation**, as a unital homomorphism of
sheaves of graded algebras. -/
def inclusion (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf) :
    SheafOfModules.GradedAlgebra.UnitalHom (nonnegTruncation A) A where
  app := inclusionApp A
  map_mul i j U x y := by
    -- Where both degrees are nonnegative, multiplicativity is `rfl`: the truncated multiplication
    -- is that of `A` and the components are identities. Where a degree is negative, the section in
    -- that degree lies in a zero object, so both sides vanish.
    rcases i with a | a
    · rcases j with b | b
      · rfl
      · have hy : y = 0 := eq_zero_of_isZero (isZero_piece_negSucc A b) U y
        subst hy
        refine Eq.trans (congrArg
          (fun z => (inclusionApp A ((a : ℤ) + Int.negSucc b)).val.app U z)
          (map_zero _)) ?_
        refine (map_zero _).trans ?_
        exact ((congrArg (fun z => (A.mul (a : ℤ) (Int.negSucc b)).app U
          ((inclusionApp A (a : ℤ)).val.app U x) z) (map_zero _)).trans (map_zero _)).symm
    · have hx : x = 0 := eq_zero_of_isZero (isZero_piece_negSucc A a) U x
      subst hx
      refine Eq.trans (congrArg
        (fun z => (inclusionApp A (Int.negSucc a + j)).val.app U z)
        (show ((nonnegTruncation A).mul (Int.negSucc a) j).app U 0 y = 0 from
          mul_app_apply_eq_zero_of_neg_left A a j U 0 y)) ?_
      refine (map_zero _).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => (A.mul (Int.negSucc a) j).app U z
        ((inclusionApp A j).val.app U y)) (map_zero _).symm)
      rw [map_zero, AddMonoidHom.zero_apply]
  -- Unitality is `rfl`, degree zero being nonnegative.
  map_one _ := rfl

/-- The degree-`n` component of `inclusion A` is `inclusionApp A n`. -/
@[simp] theorem inclusion_app (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
    (n : ℤ) : (inclusion A).app n = inclusionApp A n :=
  rfl

/-- **The inclusion of the nonnegative truncation is natural**: truncating a unital homomorphism
`f : A ⟶ B` and including `B_{≥0}` in `B` is including `A_{≥0}` in `A` and applying `f`. -/
theorem unitalHom_comp_inclusion (f : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    (unitalHom f).comp (inclusion B) = (inclusion A).comp f := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  -- In a nonnegative degree both are `f`; in a negative degree both are morphisms out of a zero
  -- object.
  rcases n with a | a
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (isZero_piece_negSucc A a).eq_of_src _ _

end Stacks.AlgebraicGeometry.NonnegTruncation

end
