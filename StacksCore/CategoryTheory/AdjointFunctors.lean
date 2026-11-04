module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Monad.Adjunction
import StacksCore.Tactic.StacksAttribute

/-! # Adjoint Functors -/

@[expose] public section

namespace CategoryTheory

open _root_.CategoryTheory.Functor

add_to_stacks 0037 "constructor using the hom-isomorphism definition" Adjunction.mkOfHomEquiv

add_to_stacks 0A8B isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top

/-- Given an adjunction `L ⊣ R`, if `L ⋙ R` is fully faithful `L` is too. -/
@[simps, stacks 0FWV "Case 1"]
def Adjunction.fullyFaithfulLeftOfComp {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (h : (L ⋙ R).FullyFaithful) : L.FullyFaithful where
  preimage f := h.preimage (R.map f)
  map_preimage f := by
    refine (adj.homEquiv _ _).injective ?_
    simp only [adj.homEquiv_apply, ← Functor.comp_map, h.map_preimage (R.map f)]
  preimage_map f := h.preimage_map f

/-- Given an adjunction `L ⊣ R`, if `R ⋙ L` is fully faithful `R` is too. -/
@[simps, stacks 0FWV "Case 2"]
def Adjunction.fullyFaithfulRightOfComp {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (h : (R ⋙ L).FullyFaithful) : R.FullyFaithful where
  preimage f := h.preimage (L.map f)
  map_preimage {X Y} f := by
    refine (adj.homEquiv _ _).symm.injective ?_
    simp only [adj.homEquiv_symm_apply, ← Functor.comp_map, h.map_preimage (L.map f)]
  preimage_map f := h.preimage_map f

add_to_stacks 07RB "Part 1, (2) => (1)" Adjunction.fullyFaithfulLOfCompIsoId
add_to_stacks 07RB "Part 1, (1) => (3)" Adjunction.unit_isIso_of_L_fully_faithful
add_to_stacks 07RB "Part 1, (3) => (1)" Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_stacks 07RB "Part 2, (2) => (1)" Adjunction.fullyFaithfulROfCompIsoId
add_to_stacks 07RB "Part 2, (1) => (3)" Adjunction.counit_isIso_of_R_fully_faithful
add_to_stacks 07RB "Part 2, (3) => (1)" Adjunction.fullyFaithfulROfIsIsoCounit

add_to_stacks 0038 instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_stacks 0038 instPreservesLimitsOfSizeOfIsRightAdjoint

add_to_stacks 0039 "implies 0039 for left adjoints with `PreservesColimits.preservesFiniteColimits`"
  Adjunction.leftAdjoint_preservesColimits
add_to_stacks 0039 "implies 0039 for right adjoints with `PreservesLimits.preservesFiniteLimits`"
  Adjunction.rightAdjoint_preservesLimits

add_to_stacks 0GLL "first equation" Adjunction.left_triangle_components
add_to_stacks 0GLL "second equation" Adjunction.right_triangle_components

add_to_stacks 0B65 "in components" conjugateEquiv_counit

add_to_stacks 0DV0 "counit equation" Adjunction.comp_counit_app

add_to_stacks 0AHQ isRightAdjoint_of_preservesLimits_of_solutionSetCondition

end CategoryTheory
