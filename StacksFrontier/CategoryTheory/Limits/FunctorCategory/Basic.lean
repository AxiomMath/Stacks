module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Limits and colimits of abelian presheaves

Abelian presheaves are the functor category `Cᵒᵖ ⥤ Ab`, whose limits and colimits exist and
are computed sectionwise.
-/

@[expose] public section

-- Tag 03CL: `PAb(C)` has all limits and colimits, and both commute with taking sections.
add_to_stacks 03CL "(1) limits" CategoryTheory.Limits.functorCategoryHasLimitsOfSize
add_to_stacks 03CL "(1) colimits" CategoryTheory.Limits.functorCategoryHasColimitsOfSize
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.functorCategoryHasColimitsOfSize
add_to_stacks 03CL "(2) limits sectionwise" CategoryTheory.Limits.evaluationPreservesLimits
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.evaluationPreservesLimits
add_to_stacks 03CL "(2) colimits sectionwise" CategoryTheory.Limits.evaluation_preservesColimits
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.evaluation_preservesColimits
add_to_stacks 03CL "Ab has limits" AddCommGrpCat.hasLimits
add_to_sga "4 I 2.3.2" AddCommGrpCat.hasLimits
add_to_ega "0 13.1.1" "special case" AddCommGrpCat.hasLimits
add_to_stacks 03CL "Ab has colimits" AddCommGrpCat.hasColimitsOfSize
