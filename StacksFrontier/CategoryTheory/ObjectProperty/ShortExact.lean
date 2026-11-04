module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Two out of three for a property of objects

Let `P` be a property of objects of a balanced preadditive category and let
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence.  Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` records the middle case of the
two-out-of-three principle, that `P X₁` and `P X₃` give `P X₂`.  This file adds the two outer
cases, which need no class of their own: in a balanced category the first term of a short exact
sequence *is* a kernel of the second map and the third term *is* a cokernel of the first, so the
outer cases are closure under kernels and closure under cokernels with nothing further to prove.

## Main results

* `CategoryTheory.ObjectProperty.prop_X₁_of_shortExact_of_isClosedUnderKernels`: a property
  closed under kernels holds for the first term of a short exact sequence whose last two terms
  satisfy it.
* `CategoryTheory.ObjectProperty.prop_X₃_of_shortExact_of_isClosedUnderCokernels`: a property
  closed under cokernels holds for the third term of a short exact sequence whose first two
  terms satisfy it.

## Implementation notes

`CategoryTheory.ShortComplex.Exact.fIsKernel` and
`CategoryTheory.ShortComplex.Exact.gIsCokernel` are the two inputs, and both are available in a
balanced preadditive category, so no abelian structure is assumed; the monomorphism and the
epimorphism are taken from the `CategoryTheory.ShortComplex.ShortExact` structure rather than
hypothesized.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  (P : ObjectProperty C) {S : ShortComplex C}

/-- The first term of a short exact sequence satisfies a property closed under kernels as soon
as the other two terms do: it is a kernel of the second map. -/
lemma prop_X₁_of_shortExact_of_isClosedUnderKernels [P.IsClosedUnderKernels]
    (hS : S.ShortExact) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁ :=
  have := hS.mono_f
  (P.prop_of_isLimit_kernelFork hS.exact.fIsKernel h₂ h₃ :)

/-- The third term of a short exact sequence satisfies a property closed under cokernels as soon
as the other two terms do: it is a cokernel of the first map. -/
lemma prop_X₃_of_shortExact_of_isClosedUnderCokernels [P.IsClosedUnderCokernels]
    (hS : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃ :=
  have := hS.epi_g
  (P.prop_of_isColimit_cokernelCofork hS.exact.gIsCokernel h₁ h₂ :)

end CategoryTheory.ObjectProperty

end
