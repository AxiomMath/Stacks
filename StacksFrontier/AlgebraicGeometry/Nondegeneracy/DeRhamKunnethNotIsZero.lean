module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormula
public import StacksFrontier.AlgebraicGeometry.Nondegeneracy.DeRhamNotIsZero

/-!
# The de Rham complex is a non-degenerate input to the relative Künneth comparison

The relative Künneth map of [Stacks, Tag 0G4B] and the de Rham Künneth map of [Stacks, Tag 0FMC]
are quantified over cochain complexes `K` of finite-order differential operators which are
strictly bounded below. Nothing in the development exhibited such a complex that is not a zero
complex, so every instance of those maps that could be named was one between zero objects.

This file names one: the `ℤ`-indexed relative de Rham complex of a morphism out of a nonempty
scheme, whose degree-zero term is `Ω^0_{X/S} ≅ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.not_isZero_deRhamDiffOpCochainComplex_X_zero`: the degree-zero
  term of the `ℤ`-indexed relative de Rham complex is not a zero object.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- **The `ℤ`-indexed relative de Rham complex is not a zero complex** when `X` is nonempty: in
degree `0` it is `Ω^0_{X/S}`, which is `𝒪_X`.

Together with `isStrictlyGE_deRhamDiffOpCochainComplex` this is a non-degenerate inhabitant of
the complex binder of `relativeBoxKunnethMap` ([Stacks, Tag 0G4B]) and of the source of
`deRhamRelativeKunnethMap` ([Stacks, Tag 0FMC]). -/
theorem not_isZero_deRhamDiffOpCochainComplex_X_zero [Nonempty X] :
    ¬ IsZero ((deRhamDiffOpCochainComplex a).X ((0 : ℕ) : ℤ)) :=
  fun h => not_isZero_deRhamDiffOpComplex_X_zero a
    (((deRhamDiffOpCochainComplexXIso a 0).isZero_iff).mp h)

end AlgebraicGeometry.Scheme.Hom
