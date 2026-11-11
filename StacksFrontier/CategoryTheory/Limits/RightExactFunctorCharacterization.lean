module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.Tactic.TFAE
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of right exact functors

Let `F : C ⥤ D` be a functor and suppose `C` has all finite colimits. This file proves that the
following are equivalent:

1. `F` is right exact, i.e. preserves finite colimits;
2. `F` preserves finite coproducts and coequalizers;
3. `F` sends initial objects of `C` to initial objects of `D` and preserves pushouts.

## Main results

* `CategoryTheory.Limits.preservesFiniteColimits_tfae`: the three conditions are equivalent.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor sending every initial object to an initial object preserves colimits of the empty
diagram. -/
lemma preservesColimitsOfShape_pempty_of_isInitial_obj [HasInitial C] (F : C ⥤ D)
    (h : ∀ X : C, IsInitial X → Nonempty (IsInitial (F.obj X))) :
    PreservesColimitsOfShape (Discrete.{0} PEmpty) F := by
  have : PreservesColimit (Functor.empty.{0} C) F :=
    preservesColimit_of_preserves_colimit_cocone initialIsInitial
      ((isColimitMapCoconeEmptyCoconeEquiv F (⊥_ C)).symm (h _ initialIsInitial).some)
  exact preservesColimitsOfShape_pempty_of_preservesInitial F

/-- Let `F : C ⥤ D` be a functor and suppose all finite colimits exist in `C`. The following
are equivalent:
1. `F` is right exact (preserves finite colimits);
2. `F` commutes with finite coproducts and coequalizers;
3. `F` transforms initial objects of `C` into initial objects of `D`, and commutes with pushouts.

The implications `2 → 1` and `3 → 1` are Mathlib's
`preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts` and
`preservesFiniteColimits_of_preservesInitial_and_pushouts`; the implications out of `1` hold since
the walking parallel pair, the finite discrete categories, the empty category and the walking span
are finite categories. -/
@[stacks 0GMN "The complete statement: the equivalence of (1), (2) and (3) for a functor out of a
  category with all finite colimits."]
theorem preservesFiniteColimits_tfae [HasFiniteColimits C] (F : C ⥤ D) :
    List.TFAE
      [PreservesFiniteColimits F,
        PreservesFiniteCoproducts F ∧ PreservesColimitsOfShape WalkingParallelPair F,
        (∀ X : C, IsInitial X → Nonempty (IsInitial (F.obj X))) ∧
          PreservesColimitsOfShape WalkingSpan F] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ ↦
    preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts F
  tfae_have 1 → 3 := fun _ ↦ ⟨fun X hX ↦ ⟨hX.isInitialObj F X⟩, inferInstance⟩
  tfae_have 3 → 1 := fun ⟨h, _⟩ ↦ by
    have := preservesColimitsOfShape_pempty_of_isInitial_obj F h
    exact preservesFiniteColimits_of_preservesInitial_and_pushouts F
  tfae_finish

end CategoryTheory.Limits
