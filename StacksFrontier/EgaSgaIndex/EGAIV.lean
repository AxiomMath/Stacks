module  -- shake: keep-all

public import StacksFrontier.EgaSgaIndex.EGAIV.FinitenessFlatness
public import StacksFrontier.EgaSgaIndex.EGAIV.DimensionDepthLimits
public import StacksFrontier.EgaSgaIndex.EGAIV.FibresSmoothEtale
public import StacksFrontier.EgaSgaIndex.EGAIV.HenselianDivisors

/-!
# EGA IV references registered by name

Declarations realizing numbered items of EGA IV, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.

The registrations are split by section of EGA IV into
`StacksFrontier.EgaSgaIndex.EGAIV.FinitenessFlatness` (§§1–3),
`StacksFrontier.EgaSgaIndex.EGAIV.DimensionDepthLimits` (§§4–10),
`StacksFrontier.EgaSgaIndex.EGAIV.FibresSmoothEtale` (§§11–17) and
`StacksFrontier.EgaSgaIndex.EGAIV.HenselianDivisors` (§§18–21).
-/
