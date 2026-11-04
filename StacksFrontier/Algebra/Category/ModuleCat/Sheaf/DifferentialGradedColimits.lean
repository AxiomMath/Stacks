module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDirectSums
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian

/-!
# Colimits of differential graded modules over a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of differential graded
`R`-algebras. The category of right differential graded `A`-modules has all colimits of
diagrams small relative to the module universe.

## Main results

* `SheafOfModules.DifferentialGradedModule.hasColimitsOfSize`: right differential graded
  modules admit all colimits of the size of the module universe.

## Implementation notes

The proof is the standard reduction of arbitrary colimits to direct sums and coequalizers:
direct sums are `SheafOfModules.DifferentialGradedModule.hasCoproducts`, and coequalizers come
from the cokernels of the abelian structure
`SheafOfModules.DifferentialGradedModule.abelian`. It is the differential graded counterpart of
`SheafOfModules.GradedModule.hasColimitsOfSize` and is proved the same way.

The size universe is the module universe `m` rather than a free one: a coproduct indexed by a
type larger than `m` need not exist, because `SheafOfModules.{m} R` itself has colimits only of
shapes small relative to `m`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- **Right differential graded modules over a sheaf of differential graded algebras have all
colimits of the size of the module universe**: they have direct sums and coequalizers. -/
instance hasColimitsOfSize [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    HasColimitsOfSize.{m, m} (DifferentialGradedModule.{t, a, m} A) :=
  have : HasCoequalizers (DifferentialGradedModule.{t, a, m} A) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  has_colimits_of_hasCoequalizers_and_coproducts.{m}

end DifferentialGradedModule

end SheafOfModules

end
