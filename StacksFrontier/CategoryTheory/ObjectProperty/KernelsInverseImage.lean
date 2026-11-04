module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Closure under kernels and cokernels transported along an exact functor

Let `F : D ⥤ C` be a functor between categories with zero morphisms which preserves zero
morphisms, and let `P` be a property of objects of `C`. This file records that the inverse image
`P.inverseImage F`, the property of objects of `D` whose image satisfies `P`, inherits closure
under kernels from `P` when `F` is left exact, and closure under cokernels when `F` is right
exact.

Mathlib has the analogues for the properties indexed by a shape
(`CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage`) and for closure under
extensions, but not these two: `CategoryTheory.ObjectProperty.IsClosedUnderKernels` asks for the
kernel of a map *between objects of `P`*, which is not the closure of the property under limits
of the shape of a parallel pair, and so neither statement follows from the other.

## Main results

* `CategoryTheory.ObjectProperty.IsClosedUnderKernels.inverseImage`: the inverse image of a
  property closed under kernels along a left exact functor is closed under kernels.
* `CategoryTheory.ObjectProperty.IsClosedUnderCokernels.inverseImage`: the inverse image of a
  property closed under cokernels along a right exact functor is closed under cokernels.

## Implementation notes

The proofs are `CategoryTheory.Limits.KernelFork.mapIsLimit` and its dual: a left exact functor
preserving zero morphisms carries a limit kernel fork to a limit kernel fork, with the same
vertex up to the identification of `F.obj k.pt` with the vertex of the image fork, which is
definitional.

Transport along an *equivalence* needs no separate statement: the inverse image along either
half of an equivalence is covered, both halves preserving all limits and colimits. Only a
functor is assumed here, and nothing is required of it beyond exactness in the relevant
direction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (P : ObjectProperty C) (F : D ⥤ C) [F.PreservesZeroMorphisms]

/-- The inverse image along a left exact functor of a property of objects closed under kernels is
closed under kernels: a limit kernel fork of a map of `D` whose two ends land in `P` is carried
to a limit kernel fork of a map between objects of `P`. -/
instance IsClosedUnderKernels.inverseImage [P.IsClosedUnderKernels] [PreservesFiniteLimits F] :
    (P.inverseImage F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact (P.prop_of_isLimit_kernelFork (k.mapIsLimit hk F) hf.1 hf.2 :)

/-- The inverse image along a right exact functor of a property of objects closed under cokernels
is closed under cokernels, by the colimit counterpart of the argument for
`CategoryTheory.ObjectProperty.IsClosedUnderKernels.inverseImage`. -/
instance IsClosedUnderCokernels.inverseImage [P.IsClosedUnderCokernels]
    [PreservesFiniteColimits F] : (P.inverseImage F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact (P.prop_of_isColimit_cokernelCofork (k.mapIsColimit hk F) hf.1 hf.2 :)

end CategoryTheory.ObjectProperty

end
