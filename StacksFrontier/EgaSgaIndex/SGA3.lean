module  -- shake: keep-all

public import StacksFrontier.EgaSgaIndex.SGA3.ExposesItoIII
public import StacksFrontier.EgaSgaIndex.SGA3.ExposesIVandIX
public import StacksFrontier.EgaSgaIndex.SGA3.ExposesVtoVI
public import StacksFrontier.EgaSgaIndex.SGA3.ExposesVIItoVIII
public import StacksFrontier.EgaSgaIndex.SGA3.ExposesXtoXXVI

/-!
# SGA 3 references registered by name

Declarations realizing numbered items of SGA 3, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
The registrations live in the parts imported above, by exposé.
-/
