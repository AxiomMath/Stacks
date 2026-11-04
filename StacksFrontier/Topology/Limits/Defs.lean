module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of topological spaces

Mathlib already states both parts of Stacks tag 08ZT: the category of topological spaces has
limits (`TopCat.topCat_hasLimits`) and the forgetful functor to sets preserves them
(`TopCat.forget_preservesLimits`), so the underlying set of a limit is the limit of the underlying
sets.

## Main results

* `TopCat.limitCone_π_app_apply`: the projections of the explicit limit cone `TopCat.limitCone F`
  are the coordinate maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

add_to_stacks 08ZT "the category of topological spaces has limits" TopCat.topCat_hasLimits
add_to_stacks 08ZT "the forgetful functor to sets preserves limits" TopCat.forget_preservesLimits

namespace TopCat

variable {J : Type*} [Category J] (F : J ⥤ TopCat)

/-- The projections of the explicit limit cone `TopCat.limitCone F` are the coordinate maps. -/
lemma limitCone_π_app_apply (j : J) (u : (limitCone F).pt) :
    (limitCone F).π.app j u = u.val j :=
  rfl

end TopCat
