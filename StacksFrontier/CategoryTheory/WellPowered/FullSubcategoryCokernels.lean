module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import StacksFrontier.CategoryTheory.WellPowered.FullyFaithful

/-!
# Well-copoweredness of a full subcategory closed under cokernels

Let `P` be a property of objects of a preadditive category `C` with cokernels, closed under
cokernels. Then an epimorphism of the full subcategory `P` is an epimorphism of `C`: the cokernel
of its image in `C` lies in `P`, and its projection is killed by the epimorphism inside `P`. So
the opposite of the inclusion is a fully faithful functor preserving monomorphisms, and the
quotient objects of an object of `P` inject into its quotient objects in `C`. Hence `P` is
well-copowered as soon as `C` is.

This is the shape in which the special adjoint functor theorem consumes well-copoweredness of the
quasi-coherent modules on an algebraic stack: they are closed under cokernels in all modules,
which are well-copowered being abelian and well-powered.

## Main results

* `CategoryTheory.ObjectProperty.preservesEpimorphisms_ι_of_isClosedUnderCokernels`: the
  inclusion of a full subcategory closed under cokernels preserves epimorphisms.
* `CategoryTheory.ObjectProperty.wellPowered_op_of_isClosedUnderCokernels`: such a full
  subcategory of a well-copowered category is well-copowered.

## Implementation notes

Mathlib has the first statement as
`CategoryTheory.ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory`, for a normal mono
category and a property containing a zero object. Neither hypothesis is needed: the argument
below uses only the cokernel of the image and the zero morphisms of the full subcategory, which
it inherits from `C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C] (P : ObjectProperty C)
  [P.IsClosedUnderCokernels]

/-- The inclusion of a full subcategory closed under cokernels preserves epimorphisms: the
projection to the cokernel of the image of an epimorphism lies in the full subcategory, where it
is killed by the epimorphism, hence vanishes. -/
theorem preservesEpimorphisms_ι_of_isClosedUnderCokernels : P.ι.PreservesEpimorphisms where
  preserves {X Y} f _ := by
    let Q : P.FullSubcategory := ⟨cokernel f.hom, P.prop_cokernel f.hom X.property Y.property⟩
    have h : P.homMk (cokernel.π f.hom) = (0 : Y ⟶ Q) :=
      (cancel_epi f).1 (by ext; simp)
    exact Preadditive.epi_of_cokernel_zero (congrArg InducedCategory.Hom.hom h)

/-- **A full subcategory closed under cokernels inherits well-copoweredness.** Its quotient
objects inject into the quotient objects in the ambient category, the inclusion being fully
faithful and preserving epimorphisms. -/
theorem wellPowered_op_of_isClosedUnderCokernels [LocallySmall.{w} C] [WellPowered.{w} Cᵒᵖ] :
    WellPowered.{w} P.FullSubcategoryᵒᵖ :=
  have := P.preservesEpimorphisms_ι_of_isClosedUnderCokernels
  have : P.ι.op.PreservesMonomorphisms :=
    ⟨fun f _ => (op_mono_iff (P.ι.map f.unop)).2 inferInstance⟩
  Stacks.WellPoweredTransfer.wellPowered_of_fullyFaithful P.ι.op

end CategoryTheory.ObjectProperty

end
