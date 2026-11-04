module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyPresheafSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology presheaf on an open, as cohomology of the open subspace

Let `(X, O_X)` be a ringed space and `K` an object of `D(O_X)`. The value on an open `U` of the
presheaf `U ↦ H^q(U, K)`, whose sheafification is the cohomology sheaf `H^q(K)` (Tag 0BKJ), is
`H^q(U, K|_U)`: the degree-`q` cohomology of the open subspace `U` with coefficients in the
restriction of `K`. This is the composite of the identification of the value with `H^q(U, K)`
and of `H^q(U, K) = H^q(U, K|_U)` (Tag 0D5V).

## Main results

* `Stacks.Cohomology.CohomologyPresheaf.cohomologyPresheafEvaluationIsoRestriction`: the value on
  `U` of the cohomology presheaf is `H^q(U, K|_U)`, naturally in `K`.

## References

* [Stacks Project, Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open ExtensionByZeroModules (resRing)
open Stacks.Cohomology.OpenSubspace (derivedRestriction derivedSectionsOnOpenSubspace
  cohomologyOnOpenIsoRestriction)

universe wX wU wP wG u

namespace Stacks.Cohomology.CohomologyPresheaf

/-- **Stacks Project, Tag 0BKJ, the value on an open as cohomology of the open subspace.** The
value on `U` of the presheaf `U ↦ H^q(U, K)` is `H^q(U, K|_U)`, the degree-`q` cohomology of the
open subspace `U` with coefficients in the derived restriction of `K`, naturally in `K`. -/
@[stacks 0BKJ "values on opens: the value of the presheaf on U is H^q(U, K|_U)"]
public def cohomologyPresheafEvaluationIsoRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} O)]
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (resRing U O))]
    [HasDerivedCategory.{wP} (PresheafOfModules.{u} O.obj)]
    [HasDerivedCategory.{wG} AddCommGrpCat.{u}]
    (q : ℤ) :
    derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{u} O.obj) q ⋙
          PresheafOfModules.evaluation O.obj (Opposite.op U) ⋙
          forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op U))) AddCommGrpCat.{u} ≅
      derivedRestriction O U ⋙ derivedSectionsOnOpenSubspace O U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} q :=
  cohomologyPresheafEvaluationIso O U q ≪≫ cohomologyOnOpenIsoRestriction O U q

end Stacks.Cohomology.CohomologyPresheaf
