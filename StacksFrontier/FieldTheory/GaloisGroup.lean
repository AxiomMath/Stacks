module

public import Mathlib.FieldTheory.Galois.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# The Galois group of a field extension

Stacks 09DV defines the Galois group of an extension `E/F` as the group of `F`-algebra
automorphisms of `E`. That is Mathlib's `AlgEquiv F E E`, with its group structure given by
`AlgEquiv.aut`.

This file exists only to record that citation. The declaration that previously carried the
tag was an abbreviation for `AlgEquiv F E E`, i.e. for Mathlib's own type, and it lived in
the `StacksDraftArchive` tree, which has been deleted; without this file the tag would have
no Lean at all.
-/

@[expose] public section

add_to_stacks 09DV "the Galois group as a type" AlgEquiv
add_to_stacks 09DV "its group structure" AlgEquiv.aut

end
