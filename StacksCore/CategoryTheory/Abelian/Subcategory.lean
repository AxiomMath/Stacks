module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-! # Short exact sequences in full subcategories

Let `A` be a preadditive category with kernels and cokernels (for example an abelian category),
and `P : ObjectProperty A` a property of objects that contains `0` and is closed under kernels and
cokernels. `ObjectProperty.shortExact_map_ι` shows that the inclusion `P.ι : P.FullSubcategory ⥤ A`
sends short exact sequences to short exact sequences. For abelian `A`, `P.FullSubcategory` need
not be abelian: closure under finite products, which Mathlib's `Abelian P.FullSubcategory`
instance needs, is not assumed.

## Implementation notes

The short complex is taken with the binder `⦃S⦄`, so that `P.shortExact_map_ι` itself proves
`∀ ⦃S⦄, S.ShortExact → (S.map P.ι).ShortExact`, the hypothesis of
`CategoryTheory.GrothendieckGroup.map` (in `StacksCore.CategoryTheory.GrothendieckGroup.Basic`).
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasKernels A] [HasCokernels A]
  (P : ObjectProperty A)

/-- The inclusion of a full subcategory containing `0` and closed under kernels and cokernels
preserves short exact sequences; no closure under finite products is needed. For Serre and weak
Serre classes, where the inclusion is exact, compare `preservesFiniteLimits_ι`
(Stacks 02MP, in `StacksCore.CategoryTheory.Abelian.SerreClass.Basic`) and
`preservesFiniteLimits_ι_of_isWeakSerreClass` / `preservesFiniteColimits_ι_of_isWeakSerreClass`
(Stacks 0754, in `StacksCore.CategoryTheory.Abelian.SerreClass.Weak`). -/
lemma shortExact_map_ι [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    ⦃S : ShortComplex P.FullSubcategory⦄ (hS : S.ShortExact) : (S.map P.ι).ShortExact := by
  have : HasZeroObject A := ⟨P.exists_prop_of_containsZero.imp fun _ h ↦ h.1⟩
  have : P.ι.PreservesHomology := ⟨P.preservesKernels_ι, P.preservesCokernels_ι⟩
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map P.ι

end CategoryTheory.ObjectProperty
