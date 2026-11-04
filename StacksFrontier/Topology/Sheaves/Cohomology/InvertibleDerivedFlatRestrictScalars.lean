module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTensorRestrictScalars
public import StacksFrontier.Topology.Sheaves.Modules.Flat.RestrictScalarsTransitivity

/-!
# An invertible module over a factor is flat over the structure sheaf

Let `(X, 𝒪_X)` be a ringed space with a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of its structure sheaf (`Stacks.Cohomology.InvertibleDerived`'s
`ProductDecomposition`) and let `H` be an invertible `𝒪_n`-module.  Then `H`, read as an
`𝒪_X`-module along the projection `𝒪_X ⟶ 𝒪_n`, is flat over `𝒪_X`.

## Main results

All names are in the namespace `Stacks.Cohomology.InvertibleDerived`.

* `ProductDecomposition.isFlat_toOXMod_of_isInvertibleModule`: an invertible `𝒪_n`-module read
  as an `𝒪_X`-module is flat.
* `ProductDecomposition.exists_derivedTensor_iso_of_isInvertibleModule`: an invertible
  `𝒪_n`-module `H` has an `𝒪_n`-module `H'` with `H ⊗^L H' ≅ 𝒪_n` in `D(𝒪_X)`.
* `isInvertibleObject_of_hasInvertibleModuleDecomposition_unconditional`: an object of `D(𝒪_X)`
  with a locally finite invertible module decomposition is invertible.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace Stacks.Cohomology.InvertibleDerived

variable {X : RingedSpace.{u, u}}

namespace ProductDecomposition

/-- **An invertible module over a factor of a product decomposition, read as a module over the
structure sheaf, is flat.** -/
public theorem isFlat_toOXMod_of_isInvertibleModule (D : ProductDecomposition X) (n : ℤ)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((D.toOXMod n).obj H) :=
  Stacks.SheafOfModules.FlatRestrictScalars.isFlat_restrictScalars_of_isFlat
    (D.iso.hom ≫ Pi.π D.factor n) H
    (Stacks.SheafOfModules.isFlat_of_isInvertible
      (X := AlgebraicGeometry.SheafOfModules.ringedSpaceOfSheaf (D.factor n)) H hH)
    (D.isFlat_toOXMod_unit n)

/-- For an invertible `𝒪_n`-module `H` there is an `𝒪_n`-module `H'` such that, read as
`𝒪_X`-modules placed in degree `0`, the derived tensor product of `H` and `H'` is isomorphic to
`𝒪_n` in `D(𝒪_X)`. -/
public theorem exists_derivedTensor_iso_of_isInvertibleModule (D : ProductDecomposition X)
    [HasDerivedCategory.{d} (Mod X.sheaf)] (n : ℤ)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H) :
    ∃ H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)),
      letI := MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
      Nonempty (MonoidalCategory.tensorObj
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj H))
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj H')) ≅
          (DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj ((D.toOXMod n).obj
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))) :=
  exists_derivedTensor_iso_of_isInvertibleModule_of_isFlat.{u, d} D n H hH
    (isFlat_toOXMod_of_isInvertibleModule D n H hH)

end ProductDecomposition

/-- If `M` admits a locally finite invertible module decomposition, then `M` is an invertible
object of `D(𝒪_X)`. -/
@[stacks 0FPG "clause (2) implies clause (1): a locally finite invertible module decomposition of \
M makes M an invertible object of D(𝒪_X) for the derived tensor product of Stacks 0FPB"]
public theorem isInvertibleObject_of_hasInvertibleModuleDecomposition_unconditional
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M : DerivedModules X.sheaf)
    (hM : HasInvertibleModuleDecomposition X M) :
    IsInvertibleObject M :=
  isInvertibleObject_of_hasInvertibleModuleDecomposition.{u, d}
    (fun D n H hH ↦
      ProductDecomposition.exists_derivedTensor_iso_of_isInvertibleModule.{u, d} D n H hH) M hM

end Stacks.Cohomology.InvertibleDerived

end
