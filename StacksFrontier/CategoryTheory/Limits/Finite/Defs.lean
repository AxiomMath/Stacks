module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite limits (Stacks 002O)

A category has finite limits as soon as it has enough of the small shapes: finite
products together with equalizers, or — even less — a terminal object together
with fibre products.

The three conditions of the source are rendered by Mathlib's own classes:
condition (1) is `HasFiniteLimits C`, condition (2) is
`HasFiniteProducts C ∧ HasEqualizers C`, and condition (3) is
`HasTerminal C ∧ HasPullbacks C`. Note that `HasFiniteProducts` quantifies over
*all* `Fin n`, including `n = 0`, so it already contains the empty product, i.e.
the terminal object; that is why (2) does not mention a terminal object
separately, while (3), which only has fibre products available, must.

Mathlib supplies the two hard directions (2) → (1) and (3) → (1) as
`hasFiniteLimits_of_hasEqualizers_and_finite_products` and
`hasFiniteLimits_of_hasTerminal_and_pullbacks`; the forward directions are
instance resolution. This file only assembles them into the `List.TFAE`
statement the tag asserts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- **Stacks 002O.** For a category `C` the following are equivalent:
1. finite limits exist in `C`;
2. finite products and equalizers exist in `C`;
3. a terminal object and fibre products exist in `C`. -/
@[stacks 002O, sga "4 I 2.3.1"]
theorem hasFiniteLimits_tfae (C : Type*) [Category C] :
    List.TFAE
      [HasFiniteLimits C,
       HasFiniteProducts C ∧ HasEqualizers C,
       HasTerminal C ∧ HasPullbacks C] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ ↦ hasFiniteLimits_of_hasEqualizers_and_finite_products
  tfae_have 1 → 3 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ ↦ hasFiniteLimits_of_hasTerminal_and_pullbacks
  tfae_finish

end CategoryTheory.Limits
