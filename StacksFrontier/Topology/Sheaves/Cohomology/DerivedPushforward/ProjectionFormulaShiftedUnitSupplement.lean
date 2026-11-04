module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaShiftedUnit
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaTensorFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedUnitorOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaDevissageSupplement

/-!
# The projection formula at objects that tensor to a shift

For a morphism of ringed spaces `f : X ⟶ Y` and `E` in `D(𝒪_X)`, the derived projection-formula
morphism `Rf_*E ⊗^𝐋_{𝒪_Y} V ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*V)` of [Stacks, Tag 0B53] is an isomorphism
when tensoring with `V` is a shift, compatibly with the comparison of [Stacks, Tag 079U].

## Main results

* `isIso_projectionFormulaMap_shiftedUnit`: the projection-formula morphism is an isomorphism at
  an object `V` of `D(𝒪_Y)` such that tensoring with `V` and with an object `V' ≅ Lf^*V` of
  `D(𝒪_X)` is the `n`-fold shift, naturally and coherently.
* `isIso_projectionFormulaMap_shiftedUnitObject`: the projection-formula morphism is an
  isomorphism at `𝒪_Y[-a]`, provided the comparison of [Stacks, Tag 079U] is coherent for the
  translated unitors.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **[Stacks, Tag 08EU] at an object of `D(𝒪_Y)` that tensors to the `n`-fold shift.**  For an
arbitrary morphism of ringed spaces `f : X ⟶ Y`, an arbitrary `E` in `D(𝒪_X)`, an integer `n` and
objects `V ∈ D(𝒪_Y)`, `V' ∈ D(𝒪_X)`, the derived projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} V ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*V)`

of [Stacks, Tag 0B53] is an isomorphism, granted that tensoring with `V` on `Y` and with `V'` on
`X` is the `n`-fold shift (`ρY`, `ρX`), that `Lf^*V ≅ V'` (`ν`), that `ρX` is natural (`hρX`), and
that the comparison of [Stacks, Tag 079U] is coherent for them (`hcoh`). -/
theorem isIso_projectionFormulaMap_shiftedUnit (n : ℤ)
    (V : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (V' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (ρY : ∀ Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      ((derivedTensorProductFunctor Y.sheaf).obj Z).obj V ≅
        (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n).obj Z)
    (ρX : ∀ W : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)),
      ((derivedTensorProductFunctor X.sheaf).obj W).obj V' ≅
        (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) n).obj W)
    (ν : (derivedPullback f).obj V ≅ V')
    (hρX : ∀ {W W' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (u : W ⟶ W'),
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((u ×ₘ 𝟙 V') : ((W, V') : _ × _) ⟶ (W', V')) ≫ (ρX W').hom =
        (ρX W).hom ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) n).map u)
    (hcoh : ∀ Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      (pullbackTensorComparison f).app (Z, V) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj Z) ×ₘ ν.hom) :
              (((derivedPullback f).obj Z, (derivedPullback f).obj V) : _ × _) ⟶
                ((derivedPullback f).obj Z, V')) ≫
            (ρX ((derivedPullback f).obj Z)).hom =
        (derivedPullback f).map (ρY Z).hom ≫
          (((derivedPullback f).commShiftIso n).hom.app Z))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E V) := by
  let : (derivedPushforward f).CommShift ℤ := (derivedAdjunction f).rightAdjointCommShift ℤ
  let : (derivedAdjunction f).CommShift ℤ := (derivedAdjunction f).commShift_of_leftAdjoint ℤ
  exact Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_of_tensorFunctorIso
    (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) ρY ρX ν
    (((derivedPullback f).commShiftIso n).hom) (fun u => hρX u) hcoh E
    (Stacks.AlgebraicGeometry.ProjectionFormula.isIso_commutationMate_shift
      (derivedAdjunction f) n E)

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[-a]`, carrying one hypothesis.**  For an arbitrary morphism
of ringed spaces `f : X ⟶ Y`, an arbitrary `E` in `D(𝒪_X)` and an arbitrary `a : ℤ`, the derived
projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y[-a] ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*(𝒪_Y[-a]))`

of [Stacks, Tag 0B53] is an isomorphism, provided the comparison of [Stacks, Tag 079U] is
coherent for the translated unitors
`Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso` and the unit comparison
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso`. -/
theorem isIso_projectionFormulaMap_shiftedUnitObject (a : ℤ)
    (hcoh : ∀ Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      (pullbackTensorComparison f).app (Z, Stacks.RingedSpace.shiftedUnitObject Y a) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((𝟙 ((derivedPullback f).obj Z) ×ₘ
                (Stacks.RingedSpace.derivedPullbackShiftedUnitIso f a).hom) :
              (((derivedPullback f).obj Z,
                  (derivedPullback f).obj (Stacks.RingedSpace.shiftedUnitObject Y a)) : _ × _) ⟶
                ((derivedPullback f).obj Z, Stacks.RingedSpace.shiftedUnitObject X a)) ≫
            ((Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso X a).app
              ((derivedPullback f).obj Z)).hom =
        (derivedPullback f).map
            ((Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso Y a).app Z).hom ≫
          (((derivedPullback f).commShiftIso (-a)).hom.app Z))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E (Stacks.RingedSpace.shiftedUnitObject Y a)) :=
  isIso_projectionFormulaMap_shiftedUnit f (-a)
    (Stacks.RingedSpace.shiftedUnitObject Y a) (Stacks.RingedSpace.shiftedUnitObject X a)
    (fun Z => (Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso Y a).app Z)
    (fun W => (Stacks.RingedSpace.derivedTensorShiftedUnitorNatIso X a).app W)
    (Stacks.RingedSpace.derivedPullbackShiftedUnitIso f a)
    (fun u => Stacks.RingedSpace.derivedTensorShiftedUnitor_naturality X a u)
    hcoh E

end Stacks.Cohomology.DerivedProjectionFormula

end
