module

public import StacksFrontier.Homology.TorAmplitude.Comparison
import all StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# The components of the termwise tensor comparison

`StacksDraft.TorAmplitude.termwiseTensorSingleIso` identifies termwise tensoring by a module `M`
with the total tensor product with `M` placed in degree `0`.  Its component at a complex is the
inclusion `StacksDraft.TorAmplitude.tensorSingleInclusion` of the summands of bidegree `(n, 0)`.

## Main results

* `StacksDraft.TorAmplitude.termwiseTensorSingleIso_hom_app`: the component at a complex `K` is
  `StacksDraft.TorAmplitude.tensorSingleInclusion M K`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

universe u

variable {R : Type u} [CommRing R]

/-- The component of `termwiseTensorSingleIso` at a complex is the inclusion of the summands of
bidegree `(n, 0)`. -/
public theorem termwiseTensorSingleIso_hom_app (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (termwiseTensorSingleIso M).hom.app K = tensorSingleInclusion M K := by
  rfl

end StacksDraft.TorAmplitude
