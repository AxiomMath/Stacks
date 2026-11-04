module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Quasi-coherence on the small Zariski site and on the scheme

Let `S` be a scheme in a big Zariski site. Descent, Remark 03FG identifies the sheaves of modules
on the ringed site `(S_Zar, 𝒪)` with the sheaves of modules on the ringed space `(S, 𝒪_S)`: the
functor is restriction along the inclusion of the opens of `S` into `S_Zar`,
`AlgebraicGeometry.SmallZariski.restrictModule`, with quasi-inverse the associated-module functor
`𝓕 ↦ 𝓕^a` of Stacks 03DU (4). Stacks 03DV (2) says that `𝓕^a` is quasi-coherent when `𝓕` is,
and is `AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`;
the converse, that the restriction of a quasi-coherent module on `(S_Zar, 𝒪)` is a quasi-coherent
`𝒪_S`-module, is `AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule`. This file puts
the two together: the identification of 03FG matches up the quasi-coherent modules on both sides,
which is the Zariski half of clause (2) of Descent, Proposition 03DX at the level of objects.

## Main results

* `AlgebraicGeometry.SmallZariski.isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule`: a
  module on `(S_Zar, 𝒪)` is quasi-coherent if and only if its restriction to `S` is.

## References

* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A module on `(S_Zar, 𝒪)` is quasi-coherent if and only if its restriction to `S` is.** The
forward implication is `AlgebraicGeometry.SmallZariski.isQuasicoherent_restrictModule`; the
backward one is Stacks 03DV (2), that `𝓕^a` is quasi-coherent for a quasi-coherent `𝓕`, applied
to the restriction of `M`, whose associated module is `M` again because the associated-module
adjunction of the small Zariski site is an adjoint equivalence. -/
theorem isQuasicoherentOnSite_iff_isQuasicoherent_restrictModule
    (M : SheafOfModules.{u} (structureSheaf B S hS)) :
    M.IsQuasicoherentOnSite ↔ ((restrictModule B S hS).obj M).IsQuasicoherent := by
  refine ⟨isQuasicoherent_restrictModule B S hS M, fun h => ?_⟩
  have h' := isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ h
  exact (inferInstance : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (structureSheaf B S hS)).IsClosedUnderIsomorphisms).of_iso
      (asIso ((associatedModuleAdjunction B S hS).counit.app M)) h'

end AlgebraicGeometry.SmallZariski

end
