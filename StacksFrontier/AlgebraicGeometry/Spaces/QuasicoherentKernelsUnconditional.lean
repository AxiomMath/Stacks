module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite

/-!
# The kernel clause of Stacks 03M1 at the universe of the schemes, with no hypothesis

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` proves that quasi-coherence
of `𝒪_F`-modules is closed under kernels from one input: Descent, Proposition 03DX (2), the
identification of quasi-coherence with being cartesian on the affine étale charts.  At the
module universe `u` of the schemes that input is a theorem of this development,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, so the clause
holds outright there.  This module records that instantiation in the shape
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` in which the closure is consumed as an
instance.

## Main results

* `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse`: the kernel
  clause of Stacks 03M1 for the small étale site of an algebraic space, at the universe of the
  schemes, with no hypothesis.

## Implementation notes

`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence` is an alias of
this statement.  The proof lives here, not there, and that is load-bearing.  The consumers of
the closure as an instance are the Stacks 077V statements of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCoherator`, whose types mention
`CategoryTheory.Abelian (QCoh(𝒪_F))` and so need the instance in scope while the statement
elaborates; importing `QuasicoherentPushforwardExactSequence` there puts enough extra instances
in scope that the module universe of that `Abelian` instance is no longer determined, and the
statements fail to elaborate with `stuck at solving universe constraint`.  Everything this
module imports is already in that file's import closure, so it adds no instance at all.

No `@[stacks]` attribute is carried.  Stacks 03M1 asserts six closure properties and this is
one clause of one of them, at one module universe; the tag belongs on a covering set for the
whole statement, which this development does not yet have.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The kernel clause of Stacks 03M1 for the small étale site of an algebraic space, at the
universe of the schemes, outright.**  Quasi-coherence of `𝒪_F`-modules is closed under kernels
with no hypothesis at all: the only input of
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves` is Descent,
Proposition 03DX(2), and that is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`. -/
theorem isClosedUnderKernels_quasicoherentSheaves_schemeUniverse :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels :=
  isClosedUnderKernels_quasicoherentSheaves B S hS F hF
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF)

end AlgebraicGeometry.Space

end
