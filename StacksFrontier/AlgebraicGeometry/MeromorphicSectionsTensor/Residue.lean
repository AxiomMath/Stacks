module

public import StacksFrontier.AlgebraicGeometry.MeromorphicCardResidues.SectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.MeromorphicSectionsTensor.Quasicoherent

/-!
# Meromorphic sections of a quasi-coherent module are quasi-coherent over `𝒦_X`

The extension of scalars of a quasi-coherent `𝒪_X`-module along `𝒪_X ⟶ 𝒦_X` is quasi-coherent as
a `𝒦_X`-module, on a reduced scheme whose quasi-compact opens have finitely many irreducible
components, and on a locally Noetherian scheme without embedded points.

## Main results

Both in the namespace `Stacks.AlgebraicGeometry.MeromorphicSectionsTensor`.

* `isQuasicoherent_meromorphicSectionSheaf_of_isReduced`: the extension of scalars is
  quasi-coherent over `𝒦_X` on a reduced scheme whose quasi-compact opens have finitely many
  irreducible components.
* `isQuasicoherent_meromorphicSectionSheaf_of_noEmbeddedPoints`: the same on a locally Noetherian
  scheme without embedded points.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

open Stacks.AlgebraicGeometry.GenericPointDecomposition

/-- **The extension of scalars of a quasi-coherent module to the sheaf of total quotient rings is
quasi-coherent over that sheaf of rings**, on a reduced scheme whose quasi-compact opens have
finitely many irreducible components. -/
theorem isQuasicoherent_meromorphicSectionSheaf_of_isReduced (X : Scheme.{u}) [IsReduced X]
    (hfinite : GenericPointProduct.FiniteComponentsOnCompactOpens X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf F).IsQuasicoherent :=
  QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    (toTotalQuotientRingCatSheaf X)
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent X hfinite) _
    (meromorphicSections_isQuasicoherent X hfinite F)

/-- The extension of scalars of a quasi-coherent module to the sheaf of total quotient rings is
quasi-coherent over that sheaf of rings, on a locally Noetherian scheme without embedded
points. -/
theorem isQuasicoherent_meromorphicSectionSheaf_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf F).IsQuasicoherent :=
  QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    (toTotalQuotientRingCatSheaf X)
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints X hX) _
    (meromorphicSections_isQuasicoherent_of_noEmbeddedPoints X hX F hF)

end Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

end
