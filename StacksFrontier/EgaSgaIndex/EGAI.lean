module  -- shake: keep-all

public import StacksFrontier.EgaSgaIndex.EGAI.AffineSchemes
public import StacksFrontier.EgaSgaIndex.EGAI.PreschemesProducts
public import StacksFrontier.EgaSgaIndex.EGAI.ImmersionsSeparationFiniteness
public import StacksFrontier.EgaSgaIndex.EGAI.RationalMapsFormalSchemes

/-!
# EGA I references registered by name

Declarations realizing numbered items of EGA I, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
The registrations are split by chapter of EGA I across the modules imported above.
-/
