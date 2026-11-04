module  -- shake: keep-all

public import StacksFrontier.EgaSgaIndex.SGA4.ExposeI
public import StacksFrontier.EgaSgaIndex.SGA4.ExposesIIAndIII
public import StacksFrontier.EgaSgaIndex.SGA4.ExposesIVAndIX
public import StacksFrontier.EgaSgaIndex.SGA4.ExposesVToVIIIAndVbis
public import StacksFrontier.EgaSgaIndex.SGA4.ExposesXToXIX

/-!
# SGA 4 references registered by name

Declarations realizing numbered items of SGA 4, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
The registrations are split by exposé into the modules imported above.
-/
