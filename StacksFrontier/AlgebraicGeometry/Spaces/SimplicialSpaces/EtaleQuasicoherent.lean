module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.Equivalence

/-!
# Quasi-coherent modules on the small étale site of a simplicial algebraic space

Let `U` be a simplicial algebraic space over a scheme `S` with structure sheaf `𝒪` on its small
étale site `U_étale` (Section 0DE7). As on any ringed topos there is a notion of a
quasi-coherent `𝒪`-module on `U_étale` (Stacks 03DL). By Stacks 0D7M, applied to the
simplicial-site situation of `U_étale`, a sheaf of `𝒪`-modules `𝓕` is quasi-coherent if and only
if it is cartesian and each of its components `𝓕_n`, a module over the restriction `𝒪_n` of `𝒪`
to the site of degree `n`, is quasi-coherent; the site of degree `n` is the strict model of
`U_{n, spaces, étale}` and `𝒪_n` is the structure sheaf of `U_n`
(`AlgebraicGeometry.Space.etaleStructurePresheafRestrictIso`).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianModule_etale`: the
  quasi-coherent `𝒪`-modules on `U_étale` are the cartesian `𝒪`-modules with quasi-coherent
  components.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.SimplicialSiteSituation

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

/-- **Section 0DE7, quasi-coherent modules on `U_étale`.** A sheaf of modules `𝓕` over the
structure sheaf `𝒪` of the small étale site of a simplicial algebraic space is quasi-coherent
(Stacks 03DL) if and only if it is cartesian and every component `𝓕_n` is a quasi-coherent
`𝒪_n`-module on the site of degree `n`: Stacks 0D7M for the simplicial-site situation of
`U_étale`. -/
theorem isQuasicoherentOnSite_iff_isCartesianModule_etale
    (F : SheafOfModules.{u + 1} ((etaleSituation A).totalRingSheaf (etaleStructureSheaf A))) :
    F.IsQuasicoherentOnSite ↔
      (etaleSituation A).IsCartesianModule (etaleStructureSheaf A) F ∧
        ∀ n : SimplexCategory,
          ((etaleSituation A).componentModule (etaleStructureSheaf A) F n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule _ _ F

end AlgebraicGeometry.Space

end
