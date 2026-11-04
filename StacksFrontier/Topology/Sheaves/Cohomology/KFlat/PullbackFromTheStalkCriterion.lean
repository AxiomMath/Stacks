module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackStalkComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion

/-!
# Stacks 06YB discharges the stalk-criterion hypothesis of Stacks 06YC

`Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_of_stalkCriterion` — the pullback of a K-flat
  complex of sheaves
of modules along a morphism of ringed spaces is K-flat — is stated granted
`Stacks.SheafOfModules.KFlatPullback.StalkCriterion`, the stalk criterion for K-flatness at a
  ringed space. That
criterion is `Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise`, so this file is the
  join of the two
developments and nothing more.

The criterion is stated at a ringed space `Z` and proved at a sheaf of commutative rings on
`Opens X`; the passage is `Z.sheaf`, and `Stacks.SheafOfModules.IsKFlat` and
`Stacks.SheafOfModules.KFlat.KFlat` are the same predicate — both are the `abbrev` asking that
`Tot(F ⊗_O K)` be acyclic for every acyclic `F`.

## Main results

* `Stacks.SheafOfModules.KFlatPullback.stalkCriterion`:
  `Stacks.SheafOfModules.KFlatPullback.StalkCriterion`, unconditionally.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_pullback`: **Stacks 06YC**, with no hypotheses left.
* `Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback`: the same at the retyped pullback
  functor.

## References

* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.SheafOfModules.KFlatPullback

/-- **The stalk criterion for K-flatness at a ringed space**, which is the Stacks 06YB
hypothesis of Stacks 06YC. Both of its fields are
  `Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise` at the
structure sheaf of the ringed space. -/
theorem stalkCriterion : StalkCriterion.{u} where
  kFlat_of_kFlatStalkwise Z M h := (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise
    Z.sheaf M).2 h
  kFlatStalkwise_of_kFlat Z M h := (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise
    Z.sheaf M).1 h

/-- **Stacks 06YC.** The degreewise pullback of a K-flat complex of `𝒪_Y`-modules along
a morphism of ringed spaces is a K-flat complex of `𝒪_X`-modules. -/
@[stacks 06YC]
theorem kFlat_pullback_unconditional {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.sheaf K) :
    Stacks.SheafOfModules.IsKFlat X.sheaf
      (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  kFlat_pullback_of_stalkCriterion stalkCriterion f K hK

/-- `kFlat_pullback_unconditional` at the retyped pullback functor
`StacksDraft.KFlat.modulePullback`, which is the shape
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput.kFlat_pullback` consumes. -/
theorem kFlat_modulePullback_unconditional
    {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (hK :
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X (((StacksDraft.KFlat.modulePullback
      f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) :=
  kFlat_modulePullback_of_stalkCriterion stalkCriterion f K hK

end Stacks.SheafOfModules.KFlatPullback

end

end
