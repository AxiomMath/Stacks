module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksCore.Tactic.StacksAttribute

/-! ## Abelian Categories & Opposites -/

@[expose] public section

open CategoryTheory Opposite

@[stacks 010A]
local instance CategoryTheory.Preadditive.fromOpposite {C : Type*} [Category* C]
    [Preadditive Cᵒᵖ] : Preadditive C where
  homGroup X Y := fast_instance% Equiv.addCommGroup (opEquiv (op Y) (op X)).symm
  add_comp _ _ _ f f' g := Quiver.Hom.op_inj (Preadditive.comp_add _ _ _ g.op f.op f'.op)
  comp_add _ _ _ f g g' := Quiver.Hom.op_inj (Preadditive.add_comp _ _ _ g.op g'.op f.op)

add_to_stacks 010A CategoryTheory.instPreadditiveOpposite

@[stacks 010A]
noncomputable local instance CategoryTheory.Abelian.fromOpposite {C : Type*} [Category* C]
    [Abelian Cᵒᵖ] : Abelian C :=
  -- Provide `Preadditive Cᵒᵖ` directly from the ambient `Abelian Cᵒᵖ`, otherwise typeclass
  -- search loops through `Preadditive.fromOpposite` (`Cᵒᵖ` ← `Cᵒᵖᵒᵖ` ← …) and times out.
  haveI : Preadditive Cᵒᵖ := ‹Abelian Cᵒᵖ›.toPreadditive
  haveI := CategoryTheory.Preadditive.fromOpposite (C := C)
  haveI := CategoryTheory.Limits.hasFiniteCoproducts_of_opposite (C := C)
  haveI := CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteCoproducts (C := C)
  CategoryTheory.abelianOfEquivalence (CategoryTheory.opOp C)

add_to_stacks 010A CategoryTheory.instAbelianOpposite
