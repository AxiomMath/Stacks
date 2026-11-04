module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.SimpleModule.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Length of a module and simple modules

Stacks 02LY defines the length of an `R`-module `M` as the supremum of the lengths `n` of
strictly increasing chains `0 = M₀ ⊊ M₁ ⊊ ⋯ ⊊ Mₙ = M` of submodules. Mathlib's
`Module.length` is that invariant, presented as the Krull dimension of the submodule lattice;
`Module.length_eq_height` rewrites it as the height of `⊤`, i.e. the supremum over chains
ending at `⊤`, and `Module.length_compositionSeries` reads it off any composition series.

Stacks 00J1 defines a simple module — nonzero, with no submodules besides `0` and `M`. This is
Mathlib's `IsSimpleModule`, whose defining pair is exposed by `isSimpleModule_iff`.

Stacks 00IV is additivity of length along a short exact sequence
(`Module.length_eq_add_of_exact`), and Stacks 00J2 is the equivalence of being simple, having
length `1` (`Module.length_eq_one_iff`) and being isomorphic to `R ⧸ 𝔪` for a maximal ideal `𝔪`
(`isSimpleModule_iff_quot_maximal`).
-/

@[expose] public section

-- The former @[stacks 02LY] definition and bridge lemma are the Mathlib definition.
add_to_stacks 02LY "the length of a module" Module.length
add_to_ega "IV 3.4.1" Module.length
add_to_stacks 02LY "as a supremum over chains of submodules" Module.length_eq_height
add_to_stacks 02LY "read off a composition series" Module.length_compositionSeries

-- The former @[stacks 00J1] definition is the Mathlib definition.
add_to_stacks 00J1 "simple modules" IsSimpleModule
add_to_stacks 00J1 "unfolded" isSimpleModule_iff

-- The former @[stacks 00IV] theorem is the Mathlib theorem.
add_to_stacks 00IV Module.length_eq_add_of_exact

-- The former @[stacks 00J2] theorem is the pair of Mathlib equivalences.
add_to_stacks 00J2 "simple ↔ length one" Module.length_eq_one_iff
add_to_stacks 00J2 "simple ↔ a quotient by a maximal ideal" isSimpleModule_iff_quot_maximal

end
