module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# The derived projection-formula map against the unit of `Lf^* ⊣ Rf_*`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `G, E ∈ D(𝒪_Y)`. Two maps
`G ⊗^L E ⟶ Rf_*(Lf^*G ⊗^L Lf^*E)` present themselves: the unit of `Lf^* ⊣ Rf_*` at `G ⊗^L E`
followed by `Rf_*` of the pullback-tensor comparison of [Stacks, Tag 079U], and the unit at `G`
tensored with `E` followed by the projection-formula map of [Stacks, Tag 0B53] at `(Lf^*G, E)`.
They agree.

## Main results

* `DerivedProjectionFormula.unit_comp_derivedPushforward_map_derivedPullbackTensorIso`:
  the equality of the two maps.

## Conventions

The unit is applied in the **left** tensor factor, which is the factor the projection-formula map
of [Stacks, Tag 0B53] pushes forward:
`projectionFormulaMap f E K : Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` with `E := Lf^*G`, `K := E`. No
swap of tensor factors occurs anywhere.

## Implementation notes

The statement is the instance at `Lf^* ⊣ Rf_*` of the abstract
`CategoryTheory.adjunctionTensorMap_unit`, read through `Adjunction.homEquiv_unit`; nothing about
derived categories is used. Like the projection-formula map itself it lives at the standard model
`HasDerivedCategory.standard`, which is installed for the one declaration only.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The projection-formula map against the unit.** For a morphism of ringed spaces
`f : X ⟶ Y` and `G, E ∈ D(𝒪_Y)`, the unit `G ⊗^L E ⟶ Rf_*Lf^*(G ⊗^L E)` followed by `Rf_*` of
the comparison `Lf^*(G ⊗^L E) ⟶ Lf^*G ⊗^L Lf^*E` of [Stacks, Tag 079U] equals the unit at `G`
tensored with `E`, followed by the projection-formula map
`Rf_*Lf^*G ⊗^L E ⟶ Rf_*(Lf^*G ⊗^L Lf^*E)` of [Stacks, Tag 0B53].

The unit sits in the left tensor factor, the one the projection-formula map pushes forward; no
tensor factors are swapped. Stated at the standard model `HasDerivedCategory.standard`, the model
of `projectionFormulaMap`, installed for this declaration only. -/
theorem unit_comp_derivedPushforward_map_derivedPullbackTensorIso
    (G E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedAdjunction f).unit.app
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj G).obj E) ≫
      (derivedPushforward f).map
        ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).hom.app (G, E)) =
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
        ((derivedAdjunction f).unit.app G)).app E ≫
      projectionFormulaMap f ((derivedPullback f).obj G) E := by
  refine (Adjunction.homEquiv_unit _ _ _ _).symm.trans
    ((adjunctionTensorMap_unit (derivedAdjunction f)
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
      (pullbackTensorComparison f) G E).symm.trans ?_)
  exact congrArg (· ≫ projectionFormulaMap f ((derivedPullback f).obj G) E)
    (uncurry_map_id_right _ _ _)

end Stacks.Cohomology.DerivedProjectionFormula

end
