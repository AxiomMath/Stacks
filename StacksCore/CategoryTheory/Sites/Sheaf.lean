module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The singleton sheaf

Stacks 00W3 says that the sheaf with a single section over every object — the limit of the empty
diagram of sheaves — is a terminal object of the category of sheaves.

Mathlib's `CategoryTheory.Sheaf.terminal J hX` is the sheaf `(Functor.const Cᵒᵖ).obj X` attached to
a terminal object `X` of the value category, which for `Type` and `Types.isTerminalPUnit` is the
singleton presheaf; `CategoryTheory.Sheaf.isTerminalTerminal` says it is terminal in `Sheaf J A`.

## References

* [Stacks Project, Tag 00W3](https://stacks.math.columbia.edu/tag/00W3)
-/

@[expose] public section

add_to_stacks 00W3 "the singleton sheaf: the constant sheaf on a terminal object of the value
  category, which for sheaves of sets is the presheaf with a single section over every object"
  CategoryTheory.Sheaf.terminal
add_to_stacks 00W3 "the singleton sheaf is a terminal object of the category of sheaves, i.e. the
  limit of the empty diagram of sheaves" CategoryTheory.Sheaf.isTerminalTerminal
