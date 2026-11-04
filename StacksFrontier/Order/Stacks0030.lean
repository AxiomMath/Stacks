module

public import Mathlib.CategoryTheory.Category.Preorder
import StacksCore.Tactic.EgaSgaAttribute

/-! # (Inverse) systems over a preordered set in a category

Stacks tag 0030 records two basic pieces of data over a preordered set `(I, ≤)`
and a category `𝒞`:

1. A *system* (also: *inductive system*) consists of objects `Mᵢ : 𝒞` and, for
   each `i ≤ i'`, transition maps `f_{ii'} : Mᵢ ⟶ M_{i'}` satisfying the
   identity / cocycle axioms.
2. An *inverse system* (also: *projective system*) reverses the direction of
   the transition maps.

Under Mathlib's preorder-as-category instance (`Preorder.smallCategory`), a
system over `I` in `𝒞` *is* a functor `I ⥤ 𝒞`, and an inverse system *is* a
functor `Iᵒᵖ ⥤ 𝒞`. -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable (I : Type*) [Preorder I] (𝒞 : Type*) [Category 𝒞]

/-- **Stacks 0030** (part 1, inductive systems). A *system* over a preordered
set `I` in a category `𝒞` is a functor `I ⥤ 𝒞`. -/
def System : Type _ := I ⥤ 𝒞

/-- **Stacks 0030** (part 2, projective systems). An *inverse system* over a
preordered set `I` in a category `𝒞` is a functor `Iᵒᵖ ⥤ 𝒞`. -/
@[ega "0 8.1.9", ega "IV 8.13.3", sga "3 IV 4.3.17" "preordered base category", sga "4 VII 5.3"]
def InverseSystem : Type _ := Iᵒᵖ ⥤ 𝒞

end CategoryTheory
