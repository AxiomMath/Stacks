module

public import Mathlib.RingTheory.Flat.Stability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Pullback preserves flat sheaves of modules

The pullback of a flat sheaf of modules along a morphism of ringed spaces is flat.

## Main results

* `Stacks.SheafOfModules.modulePullback_isFlat`: pullback along a morphism of ringed spaces
  preserves flatness.

## References

* [Stacks Project, Tag 0H97](https://stacks.math.columbia.edu/tag/0H97)
-/

@[expose] public section
noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TensorProduct
open TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- Sheafification of presheaves of abelian groups on the opens of a topological space. -/
noncomputable local instance (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- For presheaves of abelian groups on the opens of a topological space, the morphisms inverted
by sheafification are the locally bijective ones. -/
noncomputable local instance (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Pullback along a morphism of ringed spaces preserves flat sheaves of modules. -/
@[stacks 0H97, sga "4 V 1.7.1" "ringed spaces"]
theorem modulePullback_isFlat {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      (J := Opens.grothendieckTopology Y.carrier) (O := Y.sheaf) G) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (J := Opens.grothendieckTopology X.carrier) (O := X.sheaf)
      ((modulePullback f).obj G) := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat (X := X.carrier)
    (O := X.sheaf) ((modulePullback f).obj G)).mpr fun x => ?_
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.carrier) G.val.presheaf
        (f.hom.base x)) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := Y.carrier)
      Y.sheaf.obj (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.carrier)
        ((id G.val : _root_.PresheafOfModules.{u}
          (Y.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) (f.hom.base x)))
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.carrier)
        ((modulePullback f).obj G).val.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
      X.sheaf.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.carrier)
        ((id ((modulePullback f).obj G).val : _root_.PresheafOfModules.{u}
          (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
  let : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.carrier) G.val.presheaf
        (f.hom.base x)) :=
    (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat Y.sheaf G).mp hG (f.hom.base x)
  obtain ⟨e, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f G x
  exact Module.Flat.of_linearEquiv (R := X.presheaf.stalk x)
    (M := TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := Y.carrier) G.val.presheaf
        (f.hom.base x)))
    (N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.carrier)
      ((modulePullback f).obj G).val.presheaf x) e

end Stacks.SheafOfModules
