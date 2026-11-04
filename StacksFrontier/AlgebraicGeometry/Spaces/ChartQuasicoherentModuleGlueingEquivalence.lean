module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartQuasicoherentGlueing

/-!
# Quasi-coherence of a module against quasi-coherence of its chartwise glueing datum

Stacks 03LZ is Stacks 03LY cut down to the quasi-coherent objects on both sides.  The two
conditions correspond: an `𝒪_X`-module is quasi-coherent exactly when its restriction to every
étale scheme chart of `X` is, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_chartModuleRestriction`, and the
chartwise glueing datum of a module carries exactly those restrictions.  This file records that
correspondence in the form `CategoryTheory.Equivalence.congrFullSubcategory` consumes: an
equality of object properties, the chartwise condition pulled back along the canonical chartwise
description being quasi-coherence.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
* [Stacks Project, Tag 03LZ](https://stacks.math.columbia.edu/tag/03LZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **Datum (1) of Stacks 03LZ pulled back along the canonical chartwise description is
quasi-coherence.**  The chartwise glueing datum of an `𝒪_X`-module carries its restrictions to
the charts, so the chartwise quasi-coherence of that datum is the quasi-coherence of all those
restrictions, which by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_chartModuleRestriction` is the
quasi-coherence of the module.

This is the hypothesis of `CategoryTheory.Equivalence.congrFullSubcategory`, through which the
equivalence of Stacks 03LY cuts down to the equivalence of Stacks 03LZ. -/
theorem inverseImage_isChartwiseQuasicoherent :
    (isChartwiseQuasicoherent B S hS X).inverseImage (chartModuleGlueingFunctor B S hS X) =
      SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) := by
  funext M
  exact propext (isQuasicoherentOnSite_iff_forall_chartModuleRestriction B S hS X M).symm

end AlgebraicGeometry.Space

end
