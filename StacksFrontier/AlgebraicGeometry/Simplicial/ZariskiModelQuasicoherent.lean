module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalenceOfUniv

/-!
# Quasi-coherence passes between the total Zariski site and its equi-universe model

The module docstring of `StacksFrontier/AlgebraicGeometry/Simplicial/ZariskiEquiUniverseModel.lean`
records three steps still missing after the equi-universe model of the total Zariski site of a
simplicial scheme has been built, the third being *the passage of quasi-coherence back from the
model*, which `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex` gives only when the two
sites share their morphism universe — which the total Zariski site, with morphisms in `Type 0`,
and its model, with morphisms in `Type u`, do not.

That step is this file.  It is one application of
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff`, at `v = 0` on the
side of the site and `v' = u` on the side of the model, the two universes of objects being
`Type u` on both sides.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_zariskiModulesEquivModelModules_iff`:
  **a sheaf of `𝒪_X`-modules on the total Zariski site of a simplicial scheme is quasi-coherent
  exactly when the sheaf of modules it becomes on the equi-universe model is.**

## Implementation notes

The statement needs no comparison isomorphism of sheaves of rings: the sheaf of rings of
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite` is, on the nose, the transport of
the sheaf of rings of the total Zariski site, which is
`Stacks.SheafOfModules.SmallModelSite.ringSheaf_ringedSite`; and the functor of
`AlgebraicGeometry.SimplicialScheme.zariskiModulesEquivModelModules` is, on the nose, the
reindexing along the model equivalence with the identity structure map, which is what the
transport lemma is stated about.

The universe arguments are given explicitly, as everywhere the transport lemmas are applied:
the module universe of the lemma is `max u v v' w n`, which at `v = 0`, `v' = w = n = u` is `u`,
the universe of `AlgebraicGeometry.SimplicialScheme.Modules` and of the model's modules alike.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.SimplicialScheme

universe u

/-- **Quasi-coherence passes between the total Zariski site of a simplicial scheme and its
equi-universe model.**  A sheaf of `𝒪_X`-modules on the total Zariski site is quasi-coherent
exactly when the sheaf of modules it becomes on
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite`, under
`AlgebraicGeometry.SimplicialScheme.zariskiModulesEquivModelModules`, is quasi-coherent.

The two sites have their objects in `Type u` and their morphisms in `Type 0` and in `Type u`
respectively, so this is an instance of
`Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff` and not of
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`. -/
public theorem isQuasicoherentOnSite_zariskiModulesEquivModelModules_iff
    (X : SimplicialObject Scheme.{u}) (M : Modules X) :
    ((zariskiModulesEquivModelModules X).functor.obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_transport_iff.{u, 0, u, u, u}
    (ZariskiOpen X) _ _ _ (zariskiTopology X) (zariskiModelRingedSite X).J
    (Stacks.SheafOfModules.SmallModelSite.equivalence.{u} (C := ZariskiOpen X))
    (Stacks.SheafOfModules.SmallModelSite.ringedSite_functor_isContinuous
      (zariskiTopology X) (structureSheaf X))
    (Stacks.SheafOfModules.SmallModelSite.inverse_isDenseSubsite.{u} (zariskiTopology X))
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (zariskiTopology X))) (structureSheaf X)) M

end AlgebraicGeometry.SimplicialScheme

end
