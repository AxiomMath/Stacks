module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatInBothVariables
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkDerivedTensorTransport

/-!
# K-flatness on a slice site: the left variable

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction of sheaves of modules to
the localized site `C/U` carries K-flat complexes to K-flat complexes
([Stacks, Tag 0E8K], `Stacks.DerivedTensor.ExtensionByZero.kFlat_restrictionComplex`). The same
holds in the other variable of the tensor product: restriction carries a complex K-flat in the
first variable of `⊗_O` to a complex K-flat in the first variable of `⊗_{O|_U}`.

## Main results

* `Stacks.DerivedTensor.ExtensionByZero.kFlatLeft_restrictionComplex`: the restriction to `C/U`
  of a complex of `O`-modules which is K-flat in the first variable of `⊗_O` is K-flat in the
  first variable of `⊗_{O|_U}`.

## Implementation notes

`kFlatLeft_restrictionComplex` passes through the symmetry of the tensor product on each side:
left K-flatness for `⊗_O` is K-flatness for `(⊗_O)ᶠˡᶦᵖ`, and K-flatness is invariant under the
isomorphism of bifunctors `Stacks.SheafOfModules.Tensor.sheafTensorFlipNatIso`
(`Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft` and
`Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat`).

## References

* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.ExtensionByZero
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)

universe u

namespace Stacks.DerivedTensor.ExtensionByZero

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Stacks 0E8K in the left variable of the tensor product -/

/-- **The restriction to `C/U` of a complex of `O`-modules which is K-flat in the first
variable of `⊗_O` is K-flat in the first variable of `⊗_{O|_U}`.** -/
theorem kFlatLeft_restrictionComplex (Q : CochainComplex (Modules X.O) ℤ)
    (hQ : CochainComplex.KFlatBifunctor.KFlatLeft (sheafTensor X.O) Q) :
    CochainComplex.KFlatBifunctor.KFlatLeft (sheafTensor (X.O.over U))
      ((restrictionComplex X U).obj Q) :=
  Stacks.DerivedTensor.RingedSite.kFlatLeft_of_kFlat (X.O.over U)
    (kFlat_restrictionComplex X U Q
      (Stacks.DerivedTensor.RingedSite.kFlat_of_kFlatLeft X.O hQ))

end Stacks.DerivedTensor.ExtensionByZero

end
