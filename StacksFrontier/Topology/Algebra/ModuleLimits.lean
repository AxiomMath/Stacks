module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Limits of topological modules

Stacks 0B26: for a topological ring `R`, the category of topological `R`-modules has limits, and
those limits commute with the forgetful functors to topological spaces and to `R`-modules.

All of this is in Mathlib for `TopModuleCat R`. Limits commuting with the forgetful functor to
`ModuleCat R` is `TopModuleCat.isLimit`, which builds the limit cone by giving the limit of the
underlying modules the induced topology; the `PreservesLimits` instance for
`forget₂ (TopModuleCat R) (ModuleCat R)` then follows from that functor being a right adjoint.
-/

@[expose] public section

-- The former @[stacks 0B26] theorems were `inferInstance` against these Mathlib declarations.
add_to_stacks 0B26 "the category of topological modules has limits" TopModuleCat.instHasLimits
add_to_stacks 0B26 "limits are computed on the underlying modules" TopModuleCat.isLimit
add_to_stacks 0B26 "the forgetful functor to topological spaces preserves limits"
  TopModuleCat.instPreservesLimitsTopCatForget₂ContinuousLinearMapIdCarrierContinuousMapCarrier
