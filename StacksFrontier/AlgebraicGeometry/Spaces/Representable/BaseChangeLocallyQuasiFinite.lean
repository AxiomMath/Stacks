module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally quasi-finite morphisms are stable under base change

A morphism of schemes is locally quasi-finite when it is locally of finite type and every
one of its fibres is discrete, the latter being Mathlib's
`AlgebraicGeometry.LocallyQuasiFinite`. Both conditions are preserved by arbitrary base
change, by `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange` and
`AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite`, and so therefore is
local quasi-finiteness. This is the entry of the base-change list for that property.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

add_to_stacks 02WF "locally_quasi_finite"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite

end
