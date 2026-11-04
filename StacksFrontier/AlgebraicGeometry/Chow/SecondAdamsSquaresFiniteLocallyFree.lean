module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFiniteLocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two squares of a finite locally free module are finite locally free

Let `X` be a scheme and `ℰ` a finite locally free sheaf of `𝒪_X`-modules, in the sense of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`. Then `Sym² ℰ` and `⋀² ℰ`, the degree-two pieces
`AlgebraicGeometry.VectorBundleKZero.secondSymmetricPower` and
`AlgebraicGeometry.VectorBundleKZero.secondExteriorPower` of the chosen package
`SheafOfModules.algebras`, are again finite locally free.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_secondSymmetricPower`: `Sym² ℰ` is
  finite locally free when `ℰ` is.
* `AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_secondExteriorPower`: `⋀² ℰ` is finite
  locally free when `ℰ` is.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory
open Stacks.FiniteLocallyFree

universe u

namespace AlgebraicGeometry.VectorBundleKZero

variable {X : Scheme.{u}}

/-- **The second symmetric power of a finite locally free module on a scheme is finite locally
free.** -/
theorem isFiniteLocallyFree_secondSymmetricPower (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondSymmetricPower X E) :=
  Stacks.SheafOfModules.isFiniteLocallyFree_symmetricPower
    (J := _root_.Opens.grothendieckTopology (X : TopCat)) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ E) 2 hE

/-- **The second exterior power of a finite locally free module on a scheme is finite locally
free.** -/
@[sga "6 X 6.1" "special case"]
theorem isFiniteLocallyFree_secondExteriorPower (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (secondExteriorPower X E) :=
  Scheme.Modules.isFiniteLocallyFree_exteriorPower E 2 hE

end AlgebraicGeometry.VectorBundleKZero

end
