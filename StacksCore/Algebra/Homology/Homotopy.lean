module

public import Mathlib.Algebra.Homology.Homotopy
import StacksCore.Tactic.StacksAttribute

/-! # Homotopies between morphisms of complexes

Stacks tags 010W, 010X and 0110 for chain complexes, and 0112, 0113 and 0116 for cochain
complexes. Each pair is a single declaration here, because `Homotopy` is defined in Mathlib for
an arbitrary `c : ComplexShape ι`: the component `Homotopy.hom i j` is allowed to be nonzero
exactly when `c.Rel j i`, and the two Stacks indexing conventions are the two instances of that
condition. For `ComplexShape.down ℤ` it reads `j = i + 1`, giving the chain-complex homotopy
`hᵢ : Bᵢ → C_{i+1}` of 010W; for `ComplexShape.up ℤ` it reads `j = i - 1`, giving the
cochain-complex homotopy `hⁱ : Bⁱ → Cⁱ⁻¹` of 0112. The same remark applies throughout §12.13, so
each tag below is paired with its twin rather than proved twice.

The definitions 010X and 0113 are stated here in the corrected form the Stacks project adopted on
2026-05-06 (comments #11253 and #11254): it is `b ∘ a` that is homotopic to `id_A`, and `a ∘ b`
to `id_B`. The earlier wording had the two identities the wrong way round.
-/

add_to_stacks 010W "together with `Homotopy.compRight`. The Stacks family `c_{i+1} ∘ h_i ∘ a_i` is
`(h.compRight c).compLeft a`, whose components are `a.f i ≫ h.hom i j ≫ c.f j` definitionally, so
composing the two one-sided lemmas is the whole of the tag and needs no declaration of its own."
  Homotopy.compLeft

add_to_stacks 010W "together with `Homotopy.compLeft`; see the comment there."
  Homotopy.compRight

add_to_stacks 0112 "the cochain-complex case of 010W, and the same two declarations: both are
stated for an arbitrary `ComplexShape`."
  Homotopy.compLeft

add_to_stacks 0112 "together with `Homotopy.compLeft`; see the comment there."
  Homotopy.compRight

add_to_stacks 010X "the morphism `a` together with a `b` and the two homotopies; `A` and `B` are
*homotopy equivalent* when `Nonempty (HomotopyEquiv A B)`, which Mathlib does not name separately."
  HomotopyEquiv

add_to_stacks 0113 "the cochain-complex case of 010X; `HomotopyEquiv` is stated for an arbitrary
`ComplexShape`, so it is the same declaration."
  HomotopyEquiv

add_to_stacks 0110 "part 1" Homotopy.homologyMap_eq

add_to_stacks 0116 "part 1" Homotopy.homologyMap_eq
