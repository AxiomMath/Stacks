module  -- shake: keep-all

public import StacksFrontier.EgaSgaIndex.EGA0.LocalizationNoetherianSpaces
public import StacksFrontier.EgaSgaIndex.EGA0.SheavesFlatnessAdicRings
public import StacksFrontier.EgaSgaIndex.EGA0.HomologicalAlgebraRegularRings
public import StacksFrontier.EgaSgaIndex.EGA0.SmoothnessDifferentials

/-!
# EGA 0 references registered by name

Declarations realizing numbered items of EGA 0, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.

The registrations are split by section of EGA 0: §§1–2 in `EGA0.LocalizationNoetherianSpaces`,
§§3–7 in `EGA0.SheavesFlatnessAdicRings`, §§8–17 in `EGA0.HomologicalAlgebraRegularRings`
and §§18–23 in `EGA0.SmoothnessDifferentials`; this module imports them all.
-/
