module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherentOfHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModelModulePullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModelQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback preserves quasi-coherence on the total Zariski site

Let `f : V ⟶ U` be a morphism of simplicial schemes and let `F` be a quasi-coherent module on
`U_Zar`. Then `f^*F` is a quasi-coherent module on `V_Zar`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isQuasicoherentOnSite_modulePullback`: the pullback of a
  quasi-coherent module on the total Zariski site of a simplicial scheme along a morphism of
  simplicial schemes is quasi-coherent.

## Implementation notes

The objects of the total Zariski site lie in `Type u` and its morphisms in `Type 0`, so it is not
an endpoint of an `AlgebraicGeometry.RingedSite.Hom`. Quasi-coherence is carried to its
equi-universe model, along `AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom`, where the
localization of a morphism of ringed sites at an object (Stacks 04J0) gives the preservation of
quasi-coherence of Stacks 03DO, and is carried back.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- Let `f : V ⟶ U` be a morphism of simplicial schemes and let `F` be a quasi-coherent module on
`U_Zar`. Then the pullback `f^*F` is a quasi-coherent module on `V_Zar`. -/
@[stacks 07TI "for a quasi-coherent module, which is the hypothesis the source states; proved \
through the localization 04J0 of a morphism of ringed sites at an object, in the form asking \
only that every object of the source site admit an arrow into the image of the functor, applied \
on the equi-universe model of the total Zariski site, and not through 0D7M"]
public theorem isQuasicoherentOnSite_modulePullback (f : V ⟶ U) {F : Modules U}
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback f).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_zariskiModulesEquivModelModules_iff V ((modulePullback f).obj F)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (zariskiModelPullbackObjIso f F)
      (Stacks.Sheaves.LocalizedPullback.isQuasicoherentOnSite_pullbackTopos_ofHom
        (zariskiModelSiteHom f) (exists_hom_zariskiModelSiteHom f)
        ((isQuasicoherentOnSite_zariskiModulesEquivModelModules_iff U F).2 hF)))

end AlgebraicGeometry.SimplicialScheme

end
