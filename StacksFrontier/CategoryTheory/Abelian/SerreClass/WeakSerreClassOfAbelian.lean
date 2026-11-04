module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Weak Serre classes do not depend on the abelian structure

Being a weak Serre class (Stacks 0754) is a condition on zero objects, isomorphisms, kernels,
cokernels and short exact sequences, all of which only see the zero morphisms of the category.
Zero morphisms are unique when they exist (`CategoryTheory.Limits.HasZeroMorphisms` is a
subsingleton), so a property which is a weak Serre class for one `Abelian` structure on a
category is one for every other. This lets a statement proved for one choice of instance be used
under another.

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_of_abelian`
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

/-- **A weak Serre class for one abelian structure is a weak Serre class for any other**, the
conditions only involving the zero morphisms, which are unique. -/
theorem isWeakSerreClass_of_abelian {C : Type u} [Category.{v} C] (A₁ A₂ : Abelian C)
    (P : ObjectProperty C) (h : @IsWeakSerreClass C _ A₁ P) : @IsWeakSerreClass C _ A₂ P := by
  have hz : (@Preadditive.preadditiveHasZeroMorphisms C _ A₂.toPreadditive) =
      @Preadditive.preadditiveHasZeroMorphisms C _ A₁.toPreadditive := Subsingleton.elim _ _
  let := A₂
  exact
  { toContainsZero := @IsWeakSerreClass.toContainsZero C _ A₁ P h
    toIsClosedUnderIsomorphisms := @IsWeakSerreClass.toIsClosedUnderIsomorphisms C _ A₁ P h
    toIsClosedUnderKernels := by
      convert @IsWeakSerreClass.toIsClosedUnderKernels C _ A₁ P h
    toIsClosedUnderCokernels := by
      convert @IsWeakSerreClass.toIsClosedUnderCokernels C _ A₁ P h
    toIsClosedUnderExtensions := by
      convert @IsWeakSerreClass.toIsClosedUnderExtensions C _ A₁ P h }

end CategoryTheory.ObjectProperty
