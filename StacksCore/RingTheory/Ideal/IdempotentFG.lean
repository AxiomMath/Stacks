module

public import Mathlib.RingTheory.Ideal.IdempotentFG
import StacksCore.Tactic.StacksAttribute

/-! # Finitely generated idempotent ideals -/

@[expose] public section

-- Mathlib proves the `iff`, which is stronger than the tag's one-way statement; the tag's `(e)`
-- is `Ideal.span {e}`, definitionally equal to the `R ∙ e` appearing here.
add_to_stacks 00EH "(1)" Ideal.isIdempotentElem_iff_of_fg
