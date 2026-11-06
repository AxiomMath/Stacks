module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Topology.Category.FinTopCat

/-!
# Changing the universe of a finite discrete continuous action

For a topological group `G`, the category of finite sets in one universe with a continuous
`G`-action is equivalent to the same category formed in any other universe, through the
equivalence `CategoryTheory.FintypeCat.uSwitchEquivalence` between categories of finite sets.

## Main definitions

* `CategoryTheory.contActionUniverseEquivalence`: the equivalence of categories.
-/

@[expose] public noncomputable section

open scoped FintypeCatDiscrete

universe u v

namespace CategoryTheory

/-- Finite discrete continuous `G`-sets in one universe are the same as finite discrete
continuous `G`-sets in any other universe. -/
def contActionUniverseEquivalence (G : Type*) [Group G] [TopologicalSpace G] :
    ContAction FintypeCat.{u} G ≌ ContAction FintypeCat.{v} G :=
  FintypeCat.uSwitchEquivalence.{u, v}.mapContAction G
    (fun A ↦ by
      rw [Action.isContinuous_def]
      change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv A.obj.V).symm p) ∘
          (fun p : G × _ ↦ (A.obj.ρ p.1).asHom p.2) ∘
          (fun p : G × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
      exact Continuous.comp (by fun_prop) (Continuous.comp A.2.1 (by fun_prop)))
    (fun A ↦ by
      rw [Action.isContinuous_def]
      change Continuous ((fun p ↦ (FintypeCat.uSwitchEquiv A.obj.V).symm p) ∘
          (fun p : G × _ ↦ (A.obj.ρ p.1).asHom p.2) ∘
          (fun p : G × _ ↦ (p.1, FintypeCat.uSwitchEquiv _ p.2)))
      exact Continuous.comp (by fun_prop) (Continuous.comp A.2.1 (by fun_prop)))

end CategoryTheory

end
