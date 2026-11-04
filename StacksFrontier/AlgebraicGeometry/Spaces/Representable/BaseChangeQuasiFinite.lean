module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChangeFiniteType

/-!
# Quasi-finite morphisms are stable under base change

A morphism of schemes is quasi-finite in the sense of the Stacks Project when it is of
finite type and locally quasi-finite, so the notion is the morphism property
`(@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.QuasiCompact) ⊓
@AlgebraicGeometry.LocallyQuasiFinite` already used for it elsewhere in the library:
Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` is the affine-local property attached to
`RingHom.QuasiFinite` and carries neither a finite-type nor a quasi-compactness hypothesis.
Being of finite type is preserved by arbitrary base change by
`AlgebraicGeometry.Space.finiteType_isStableUnderBaseChange` and local quasi-finiteness by
`AlgebraicGeometry.instIsStableUnderBaseChangeSchemeLocallyQuasiFinite`, so the conjunction
is too, by `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`. This is the entry
of the base-change list for being quasi-finite.

## Main results

* `AlgebraicGeometry.Space.quasiFinite_isStableUnderBaseChange`: a quasi-finite morphism of
  schemes stays quasi-finite after arbitrary base change.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

/-- Quasi-finite morphisms of schemes remain quasi-finite after arbitrary base change. -/
@[stacks 02WF "quasi_finite", ega "II 6.2.4"]
public instance quasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (((@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ⊓ @QuasiCompact) ⊓
        @LocallyQuasiFinite) := .inf

end AlgebraicGeometry.Space

end
