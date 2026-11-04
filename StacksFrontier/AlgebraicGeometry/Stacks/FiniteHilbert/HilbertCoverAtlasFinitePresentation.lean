module

public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverUniversalAtlas

/-!
# The scheme of structure constants over `S` is locally of finite presentation over `S`

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
scheme of structure constants of **Stacks 05YM** is the spectrum of a polynomial ring in
`d ^ 3` variables over the integers modulo finitely many relations, so it is locally of finite
presentation over the integers; base changing to `S` therefore gives an object of the big fppf
site of `S` whose structure morphism is locally of finite presentation.

This is the finiteness behind the source of
`AlgebraicGeometry.Stack.finiteCoverUniversalAtlas`: a point of the scheme of structure constants
over `S` is `d ^ 3` sections of the base satisfying finitely many equations, so such a point over
a cofiltered limit of affine objects of the site is already defined at one of the stages.

## Main results

* `AlgebraicGeometry.Stack.locallyOfFinitePresentation_structureConstantsSpec`: the spectrum of
  the ring of global sections of the scheme of structure constants is locally of finite
  presentation over the terminal scheme.
* `AlgebraicGeometry.Stack.locallyOfFinitePresentation_structureConstantsBaseChangeSnd`: the
  structure morphism to `S` of the scheme of structure constants over `S` is locally of finite
  presentation.

## Implementation notes

The finite presentation of the universal ring over the integers is
`AlgebraicGeometry.universalRing_finitePresentation`, and its scheme form is
`AlgebraicGeometry.scheme_locallyOfFinitePresentation`, both of which are stated for
`AlgebraicGeometry.FiniteFreeAlgebra.scheme` itself. The base of the universal cover is instead
the spectrum of the ring of global sections of that scheme, as
`AlgebraicGeometry.FiniteFreeAlgebra.specCover` builds a cover over the spectrum of its ring of
definition; the two schemes are canonically isomorphic, that scheme being affine, and the two
morphisms to the terminal scheme agree because the terminal object receives exactly one morphism
from each scheme.

Base change is `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, which Mathlib registers
for `AlgebraicGeometry.LocallyOfFinitePresentation` as an instance on the projections of a fibre
product, so the base-changed statement needs only the statement over the terminal scheme in
scope.

No `@[stacks]` attribute is placed here. Stacks 05YM asserts that the scheme of structure
constants represents free `d`-dimensional algebra structures, which is
`AlgebraicGeometry.FiniteFreeAlgebra.representation`; the finiteness of that scheme over its base
is not part of that statement.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable (S : Scheme.{u}) (d : ℕ) [NeZero d]

/-- **The spectrum of the ring of global sections of the scheme of structure constants is locally
of finite presentation over the terminal scheme.** It is isomorphic to the scheme of structure
constants, which is locally of finite presentation over the integers by
`AlgebraicGeometry.scheme_locallyOfFinitePresentation`, and both morphisms to the terminal scheme
are the unique one. -/
theorem locallyOfFinitePresentation_structureConstantsSpec :
    LocallyOfFinitePresentation (specULiftZIsTerminal.from (structureConstantsSpec.{u} d)) := by
  have := scheme_locallyOfFinitePresentation.{u} d
  have : LocallyOfFinitePresentation (FiniteFreeAlgebra.scheme.{u} d).isoSpec.inv :=
    inferInstance
  have he : specULiftZIsTerminal.from (structureConstantsSpec.{u} d) =
      (FiniteFreeAlgebra.scheme.{u} d).isoSpec.inv ≫
        specULiftZIsTerminal.from (FiniteFreeAlgebra.scheme.{u} d) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [he]
  infer_instance

/-- **The scheme of structure constants over `S` is locally of finite presentation over `S`.**
It is the base change to `S` of the scheme of structure constants, which is locally of finite
presentation over the terminal scheme. -/
theorem locallyOfFinitePresentation_structureConstantsBaseChangeSnd :
    LocallyOfFinitePresentation (structureConstantsBaseChangeSnd.{u} S d) := by
  have := locallyOfFinitePresentation_structureConstantsSpec.{u} d
  infer_instance

end AlgebraicGeometry.Stack

end
