module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Tactic.TFAE

/-!
# Characterizations of left exact functors

For a functor `F : C ⥤ D` out of a category with finite limits, the following are equivalent:
`F` preserves finite limits; `F` preserves finite products and equalizers; `F` preserves the
terminal object and pullbacks.

## Main results

* `CategoryTheory.Limits.preservesFiniteLimits_tfae_of_hasFiniteLimits`: the equivalence above.
-/

@[expose] public section

universe v v₂ u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor out of a category with finite limits is left exact if and only if it preserves
finite products and equalizers, if and only if it preserves the terminal object and pullbacks. -/
@[stacks 0035 "Left exactness is `PreservesFiniteLimits`; `(2) → (1)` is Mathlib's
`preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts` and `(3) → (1)` is
`preservesFiniteLimits_of_preservesTerminal_and_pullbacks`, while `(1) → (2)` and `(1) → (3)`
hold because finite products, equalizers, the empty limit and pullbacks are finite limits."]
theorem preservesFiniteLimits_tfae_of_hasFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) :
    List.TFAE [PreservesFiniteLimits F,
      PreservesFiniteProducts F ∧ PreservesLimitsOfShape WalkingParallelPair F,
      PreservesLimitsOfShape (Discrete.{0} PEmpty) F ∧ PreservesLimitsOfShape WalkingCospan F] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ ↦
    preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts F
  tfae_have 1 → 3 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ ↦ preservesFiniteLimits_of_preservesTerminal_and_pullbacks F
  tfae_finish

end CategoryTheory.Limits
