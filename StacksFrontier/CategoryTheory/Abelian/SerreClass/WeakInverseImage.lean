module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# A weak Serre class pulls back along an exact functor

Let `F : C ⥤ D` be an exact functor between abelian categories and let `P` be a weak Serre class
in `D`. Then `P.inverseImage F` is a weak Serre class in `C`.

Mathlib already has the inverse-image instances for three of the five conditions of
[Stacks, Tag 0754] — containing zero, strict fullness and closure under extensions. What is
missing, and is supplied here, are closure under kernels and under cokernels; with those the
weak Serre class instance is assembled with no further work.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderKernels_inverseImage` and
  `CategoryTheory.ObjectProperty.isClosedUnderCokernels_inverseImage`: the two missing closure
  conditions.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage`: the inverse image of a weak
  Serre class under an exact functor is a weak Serre class.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_of_iff`: the same statement with the
  correspondence of the two classes given pointwise, `∀ A, P A ↔ Q (F.obj A)`, which is the form
  in which a comparison of two categories of modules delivers it.

## Implementation notes

The two closure conditions are stated for an arbitrary limit cone rather than for the chosen
`kernel`, so the proofs transport along
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso` before applying
`CategoryTheory.Limits.PreservesKernel.iso`; strict fullness of `P` is what makes that
transport available, and it is an instance as soon as `P` is a weak Serre class.

`isWeakSerreClass_of_iff` takes the correspondence pointwise, as
`StacksFrontier/CategoryTheory/Abelian/SerreClass/InverseImage.lean` does for Serre classes,
because a consumer obtains it from two `iff` lemmas about a specific pair of functors rather
than as an equality of object properties.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **Closure under kernels pulls back along a left exact functor.** A kernel of a morphism
between objects of `P.inverseImage F` is carried by `F` to a kernel of a morphism between
objects of `P`. -/
instance isClosedUnderKernels_inverseImage (P : ObjectProperty D) [P.IsClosedUnderKernels]
    [P.IsClosedUnderIsomorphisms] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] : (P.inverseImage F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    refine P.prop_of_iso ((F.mapIso
      (IsLimit.conePointUniqueUpToIso hk (kernelIsKernel f))).trans
        (PreservesKernel.iso F f)).symm ?_
    exact P.prop_kernel (F.map f) hf.1 hf.2

/-- **Closure under cokernels pulls back along a right exact functor**, the dual of
`CategoryTheory.ObjectProperty.isClosedUnderKernels_inverseImage`. -/
instance isClosedUnderCokernels_inverseImage (P : ObjectProperty D) [P.IsClosedUnderCokernels]
    [P.IsClosedUnderIsomorphisms] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] : (P.inverseImage F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    refine P.prop_of_iso ((F.mapIso
      (IsColimit.coconePointUniqueUpToIso hk (cokernelIsCokernel f))).trans
        (PreservesCokernel.iso F f)).symm ?_
    exact P.prop_cokernel (F.map f) hf.1 hf.2

/-- **The inverse image of a weak Serre class under an exact functor is a weak Serre class.**
All five conditions of [Stacks, Tag 0754] pull back: containing zero, strict fullness and
closure under extensions are Mathlib instances, and closure under kernels and cokernels are
`isClosedUnderKernels_inverseImage` and `isClosedUnderCokernels_inverseImage`. -/
instance isWeakSerreClass_inverseImage (P : ObjectProperty D) [P.IsWeakSerreClass]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (P.inverseImage F).IsWeakSerreClass where

/-- **A class corresponding pointwise to a weak Serre class across an exact functor is a weak
Serre class.** This is `isWeakSerreClass_inverseImage` with the inverse image presented by the
`iff` that identifies it. -/
theorem isWeakSerreClass_of_iff {P : ObjectProperty C} (Q : ObjectProperty D)
    [Q.IsWeakSerreClass] (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (h : ∀ A : C, P A ↔ Q (F.obj A)) : P.IsWeakSerreClass := by
  have hPQ : P = Q.inverseImage F := funext fun A ↦ propext (h A)
  subst hPQ
  infer_instance

end CategoryTheory.ObjectProperty

end
