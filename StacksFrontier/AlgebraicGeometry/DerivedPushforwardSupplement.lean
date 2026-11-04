module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# Further results on `DerivedPushforward`

The canonical comparison `f_* ⟶ Rf_*` exhibiting `Stacks.Duality.derivedPushforward` as the
unbounded right derived functor of direct image.

## Main definitions

* `AlgebraicGeometry.derivedPushforwardUnitAtModel` — the comparison `f_* ⟶ Rf_*`, at a chosen
  model of the two derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective natTrans_isIso_of_kInjectives)

universe w u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-- The canonical comparison `f_* ⟶ Rf_*` exhibiting `Stacks.Duality.derivedPushforward` as the
unbounded right derived functor of direct image, at an arbitrary chosen model of the two derived
categories. -/
abbrev derivedPushforwardUnitAtModel [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} Y.Modules] :
    Stacks.Duality.homotopyPushforward f ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.derivedPushforward f :=
  (Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

end AlgebraicGeometry

end
