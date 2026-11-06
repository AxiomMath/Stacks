module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite colimits (Stacks 002Q)

The dual of Stacks 002O: a category has finite colimits as soon as it has finite
coproducts and coequalizers, or — even less — an initial object and pushouts.

The three conditions of the source are rendered by Mathlib's own classes:
condition (1) is `HasFiniteColimits C`, condition (2) is
`HasFiniteCoproducts C ∧ HasCoequalizers C`, and condition (3) is
`HasInitial C ∧ HasPushouts C`. As in 002O, `HasFiniteCoproducts` quantifies over
all `Fin n` including `n = 0` and so already contains the initial object, which is
why (3) has to name it explicitly and (2) does not.

The cycle is closed through Mathlib: (2) → (3) by
`hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers`, (3) → (2) by first
recovering binary coproducts with `hasBinaryCoproducts_of_hasInitial_and_pushouts`
and then `hasFiniteCoproducts_of_has_binary_and_initial` and
`hasCoequalizers_of_hasPushouts_and_binary_coproducts`, and (2) → (1) by
`hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- **Stacks 002Q.** For a category `C` the following are equivalent:
1. finite colimits exist in `C`;
2. finite coproducts and coequalizers exist in `C`;
3. an initial object and pushouts exist in `C`. -/
@[stacks 002Q, sga "4 I 2.3.1"]
theorem hasFiniteColimits_tfae (C : Type*) [Category C] :
    List.TFAE
      [HasFiniteColimits C,
       HasFiniteCoproducts C ∧ HasCoequalizers C,
       HasInitial C ∧ HasPushouts C] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 3 := fun ⟨_, _⟩ ↦
    ⟨inferInstance, hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers C⟩
  tfae_have 3 → 2 := fun ⟨_, _⟩ ↦
    have : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasInitial_and_pushouts C
    ⟨hasFiniteCoproducts_of_has_binary_and_initial,
     hasCoequalizers_of_hasPushouts_and_binary_coproducts⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ ↦
    hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  tfae_finish

end CategoryTheory.Limits
