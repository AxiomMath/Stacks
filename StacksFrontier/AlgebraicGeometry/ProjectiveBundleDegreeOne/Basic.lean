module

public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Consumers
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# `Sym(E)` is generated in degree one, for a merely quasi-coherent `E`

The graded algebra `Stacks.SymGraded.schemeSheafGradedAlgebra E hqc` defining the projective
bundle of a module `E` on a scheme is generated in degree one under the hypothesis
`hqc : Stacks.SymGraded.IsQuasicoherentPieces E`
(`Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`). That hypothesis holds for
every quasi-coherent module (`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`), so
degree-one generation holds under `[E.IsQuasicoherent]` alone.

## Main results

* `Stacks.ProjectiveBundleDegreeOne.isGeneratedInDegreeOne_projectiveBundle`: **the graded
  algebra defining the projective bundle of a quasi-coherent module on an arbitrary scheme is
  generated in degree one.**

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjRepresentsF1 (IsGeneratedInDegreeOne)
open Stacks.SymGraded
  (schemeSheafGradedAlgebra isQuasicoherentPieces_of_isQuasicoherent
    isGeneratedInDegreeOne_schemeSheafGradedAlgebra)

namespace Stacks.ProjectiveBundleDegreeOne

universe u

/-- **The graded algebra defining the projective bundle of a quasi-coherent module on an
arbitrary scheme is generated in degree one**: over every affine open of the base, the degree-one
part of `Sym(E)` generates its ring of homogeneous sections as an algebra over the degree-zero
part. -/
public theorem isGeneratedInDegreeOne_projectiveBundle {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] :
    IsGeneratedInDegreeOne
      (schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)) :=
  isGeneratedInDegreeOne_schemeSheafGradedAlgebra E (isQuasicoherentPieces_of_isQuasicoherent E)

end Stacks.ProjectiveBundleDegreeOne

end
