module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of modules to an open subspace is a monoidal functor

Let `(X, O_X)` be a ringed space and `U` an open subset. Then the restriction functor
`Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U : Mod(O_X) ⥤ Mod(O_{X|_U})` is a
monoidal functor for the tensor product of sheaves of modules on each side.

## Main definitions

* `Stacks.Cohomology.LeftDualPerfect.restrictModulesRing_monoidal`: the monoidal structure on
  `Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U`, for
  `Stacks.PullbackMonoidalSheaf.monoidalCategory` on each side.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Cohomology.LeftDualPerfect

/-- The restriction of sheaves of modules from a ringed space `X` to an open subspace `U` is a
monoidal functor, for `Stacks.PullbackMonoidalSheaf.monoidalCategory` on each side. -/
@[instance_reducible, sga "4 IV 13.4" "special case"]
def restrictModulesRing_monoidal (X : RingedSpace.{u, u}) (U : Opens X) :
    letI : MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
      Stacks.PullbackMonoidalSheaf.monoidalCategory X
    letI : MonoidalCategory
        (SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :=
      Stacks.PullbackMonoidalSheaf.monoidalCategory (X.restrict U.isOpenEmbedding)
    (Stacks.Cohomology.ClosedSupportPerfect.restrictModulesRing X U).Monoidal :=
  letI : MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
    Stacks.PullbackMonoidalSheaf.monoidalCategory X
  letI : MonoidalCategory
      (SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :=
    Stacks.PullbackMonoidalSheaf.monoidalCategory (X.restrict U.isOpenEmbedding)
  letI : (RingedSpaceModuleAdjunction.modulePullback
      (X.ofRestrict U.isOpenEmbedding)).Monoidal :=
    Stacks.PullbackMonoidalSheaf.pullbackMonoidal (X.ofRestrict U.isOpenEmbedding)
  Functor.Monoidal.transport
    (Stacks.Cohomology.ClosedSupportPerfect.pullbackOpenRestrictModulesIso X U)

end Stacks.Cohomology.LeftDualPerfect

end
