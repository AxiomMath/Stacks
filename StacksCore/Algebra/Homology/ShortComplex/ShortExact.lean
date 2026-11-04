module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Algebra.Homology.ShortComplex.Exact
import StacksCore.Tactic.StacksAttribute

/-! # Short exact sequences

Stacks 010E defines, among other notions, the short exact sequences `0 → X₁ → X₂ → X₃ → 0`,
and Stacks 010J calls such a sequence an extension of `X₃` by `X₁`; this file records both tags
on Mathlib's `CategoryTheory.ShortComplex.ShortExact`.

A monomorphism followed by its cokernel is a short exact sequence
(`CategoryTheory.ShortComplex.shortExact_mk_cokernel_π`), and so is an epimorphism preceded by
its kernel (`CategoryTheory.ShortComplex.shortExact_mk_kernel_ι`).

In a preadditive balanced category, a short exact sequence is determined up to isomorphism by
its second arrow: `CategoryTheory.ShortComplex.ShortExact.isoMk` constructs an isomorphism of
short exact sequences from isomorphisms between the middle terms and between the last terms that
commute with the second arrows, inducing the first component on the kernels. It is the case of
short exact sequences of `CategoryTheory.ShortComplex.Exact.isoMk₁` in
`StacksCore.Algebra.Homology.ShortComplex.Exact`.
-/

add_to_stacks 010E CategoryTheory.ShortComplex.ShortExact
add_to_stacks 010J CategoryTheory.ShortComplex.ShortExact

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

section

variable {C : Type*} [Category* C] [Preadditive C] [CategoryWithHomology C]

/-- A monomorphism followed by its cokernel is a short exact sequence. -/
lemma shortExact_mk_cokernel_π {Y W : C} (m : Y ⟶ W) [Mono m] [HasCokernel m] :
    (ShortComplex.mk m (cokernel.π m) (cokernel.condition m)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel m)

/-- An epimorphism preceded by its kernel is a short exact sequence. -/
lemma shortExact_mk_kernel_ι {W Z : C} (e : W ⟶ Z) [Epi e] [HasKernel e] :
    (ShortComplex.mk (kernel.ι e) e (kernel.condition e)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel e)

end

section

variable {C : Type*} [Category* C] [Preadditive C] [Balanced C]

/-- A short exact sequence is determined up to isomorphism by its second arrow: isomorphisms
`e₂ : S.X₂ ≅ S'.X₂` and `e₃ : S.X₃ ≅ S'.X₃` with `e₂.hom ≫ S'.g = S.g ≫ e₃.hom` extend to an
isomorphism `S ≅ S'`. This is `Exact.isoMk₁` for short exact sequences. -/
@[simps!]
noncomputable def ShortExact.isoMk {S S' : ShortComplex C} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (e₂ : S.X₂ ≅ S'.X₂) (e₃ : S.X₃ ≅ S'.X₃)
    (comm : e₂.hom ≫ S'.g = S.g ≫ e₃.hom) : S ≅ S' :=
  have := hS.mono_f
  have := hS'.mono_f
  hS.exact.isoMk₁ hS'.exact e₂ e₃ comm

end

end CategoryTheory.ShortComplex
