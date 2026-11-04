module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor

/-!
# Module stalks over the `RingCat`-valued stalk ring

For a presheaf of modules over `𝒪 ⋙ forget₂ CommRingCat RingCat` on a topological space, the
stalk of the module carries an action of the `CommRingCat`-valued stalk of `𝒪` and of the
`RingCat`-valued stalk of `𝒪 ⋙ forget₂ CommRingCat RingCat`. These two actions agree through
the ring isomorphism `SemilinearStalk.commStalkRingEquiv`.

## Main results

* `AlgebraicGeometry.SheafOfModules.commStalk_smul_germ`: the two actions agree on germs.
* `AlgebraicGeometry.SheafOfModules.commStalk_smul_eq`: the two scalar actions on a module
  stalk agree through `SemilinearStalk.commStalkRingEquiv`, at an arbitrary universe.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

section CommStalk

variable {X : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)

/-- On germs, the `CommRingCat`-stalk action and the `RingCat`-stalk action on a module stalk
agree. -/
public theorem commStalk_smul_germ
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    R.germ U x hx r •
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx m
      = TopCat.Presheaf.germ (C := RingCat.{u})
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r •
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf U x hx m := by
  exact SemilinearStalk.comm_smul_germ R x M U hx r m

/-- **The `CommRingCat` and `RingCat` stalk actions on a module stalk agree** through
`SemilinearStalk.commStalkRingEquiv`. -/
public theorem commStalk_smul_eq
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x))
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) :
    SemilinearStalk.commStalkRingEquiv R x s • m = s • m := by
  exact SemilinearStalk.comm_smul_eq R x M s m

end CommStalk

end AlgebraicGeometry.SheafOfModules

end

end
