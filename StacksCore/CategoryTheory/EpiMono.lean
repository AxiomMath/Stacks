module

public import Mathlib.CategoryTheory.Limits.EpiMono
import StacksCore.Tactic.StacksAttribute

/-! # Monomorphisms and epimorphisms
This file adds stacks tags from section 4.13: monomorphisms and epimorphisms to some
existing declarations.
-/

@[expose] public section

open CategoryTheory

add_to_stacks 08LR mono_iff_isPullback
add_to_stacks 08LR epi_iff_isPushout
