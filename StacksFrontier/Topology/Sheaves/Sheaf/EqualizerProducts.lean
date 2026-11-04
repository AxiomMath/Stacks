module

public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0072 — sheaves with values in a category with products, via equalizer diagrams

Stacks 0072 defines a presheaf `F` on a topological space `X` with values in a category `C`
with products to be a *sheaf* when for every open covering `U = ⋃ i, U i` the diagram
`F(U) → ∏ i, F(U i) ⇉ ∏ (i₀, i₁), F(U i₀ ∩ U i₁)` is an equalizer in `C`.

Mathlib states this: the diagram is `TopCat.Presheaf.SheafConditionEqualizerProducts.diagram`,
the condition that it is an equalizer for every covering is
`TopCat.Presheaf.IsSheafEqualizerProducts`, and its equivalence with Mathlib's own definition
of a sheaf with values in an arbitrary category is
`TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts`.
-/

@[expose] public section

-- The former @[stacks 0072] theorem is Mathlib's, as is the definition it compares against.
add_to_stacks 0072 "the equalizer diagram `F(U) → ∏ F(Uᵢ) ⇉ ∏ F(U_{i₀} ∩ U_{i₁})`"
  TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
add_to_sga "3 IV 4.1.4.0" "special case" TopCat.Presheaf.SheafConditionEqualizerProducts.diagram
add_to_stacks 0072 "the sheaf condition: that diagram is an equalizer for every open covering"
  TopCat.Presheaf.IsSheafEqualizerProducts
add_to_stacks 0072 "agreement with the sheaf condition for a general target category"
  TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
add_to_sga "3 IV 4.3.5" "special case" TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
add_to_sga "4 II 2.4" "opens of a space" TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
