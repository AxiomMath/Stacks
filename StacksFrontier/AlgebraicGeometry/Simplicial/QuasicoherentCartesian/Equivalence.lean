module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseAMain
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseBMain
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesian

/-!
# Stacks 0D7M: quasi-coherent modules on a total site

In Situation 09WE, let `O` be a sheaf of rings on the total site `C_total` and `F` a sheaf of
`O`-modules. Then `F` is quasi-coherent in the sense of Stacks 03DL if and only if `F` is
cartesian (Stacks 07TF (2)) and every component `Fₙ` is a quasi-coherent `Oₙ`-module.

## Main results

In the namespace `CategoryTheory.SimplicialSiteSituation`:

* `isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule`:
  **Stacks 0D7M**.

## Implementation notes

The two cases of Stacks 09WE are proved separately, as
`isQuasicoherentOnSite_iff_isCartesianModule_caseA` in the namespace
`CategoryTheory.SimplicialSite.CartesianSlice` and
`isQuasicoherentOnSite_iff_isCartesianModule_caseB` in
`CategoryTheory.CocontinuousSimplicialSite.CartesianSlice`, along the source's proof: the
components of a quasi-coherent module are quasi-coherent by the generic argument of
`CartesianSlice.isQuasicoherentOnSite_componentModuleRestriction`; a quasi-coherent module is
cartesian because its transition, restricted to a slice over which the module is presented, is
the localized transition read through an invertible Beck–Chevalley comparison, and a localized
transition is invertible on presented modules; conversely a cartesian module with quasi-coherent
components is presented over every object where a component is.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- **Stacks 0D7M.** In Situation 09WE, let `O` be a sheaf of rings on the total site and `F` a
sheaf of `O`-modules. Then `F` is quasi-coherent in the sense of Stacks 03DL if and only if `F` is
cartesian in the sense of Stacks 07TF (2) and every component `Fₙ` is a quasi-coherent
`Oₙ`-module.

The right-hand side is
`CategoryTheory.SimplicialSiteSituation.IsCartesianWithQuasicoherentComponents`, spelled out. -/
@[stacks 0D7M]
theorem isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule
    (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
    (F : SheafOfModules.{u} (S.totalRingSheaf O)) :
    F.IsQuasicoherentOnSite ↔
      S.IsCartesianModule O F ∧
        ∀ n : SimplexCategory, (S.componentModule O F n).IsQuasicoherentOnSite := by
  rcases S with ⟨C | C⟩
  · exact SimplicialSite.CartesianSlice.isQuasicoherentOnSite_iff_isCartesianModule_caseA C O F
  · exact
      CocontinuousSimplicialSite.CartesianSlice.isQuasicoherentOnSite_iff_isCartesianModule_caseB
        C O F

end CategoryTheory.SimplicialSiteSituation
