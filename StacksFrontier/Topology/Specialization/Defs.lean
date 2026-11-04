module

public import Mathlib.Topology.Inseparable

import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of points

Stacks 0061 defines the specialization relation `x' ⤳ x` ("`x` lies in the closure of `{x'}`") and
the two induced stability conditions on subsets. Mathlib has all three: `Specializes` (equal to
membership in the closure of a singleton by `specializes_iff_mem_closure`),
`StableUnderSpecialization` and `StableUnderGeneralization`.
-/

@[expose] public section

-- The former @[stacks 0061] declarations are now these three Mathlib definitions.
add_to_stacks 0061 "specialization and generalization of points" Specializes
add_to_sga "1 IV 6.3" Specializes
add_to_sga "4 IV 4.2.2" Specializes
add_to_sga "7 IX 3.1" Specializes
add_to_ega "I 2.4.2" Specializes
add_to_ega "IV 21.13.15" Specializes
add_to_ega "0 2.1.2" "specialization relation" Specializes
add_to_stacks 0061 "subsets stable under specialization" StableUnderSpecialization
add_to_ega "IV 5.9.1" StableUnderSpecialization
add_to_stacks 0061 "subsets stable under generalization" StableUnderGeneralization
add_to_ega "IV 7.4.1" "partial" StableUnderGeneralization
