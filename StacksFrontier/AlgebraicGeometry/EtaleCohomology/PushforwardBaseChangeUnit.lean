module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# The defining identity of the base change map of sheaves of sets

The base change map `f⁻¹ g_* ⟶ h_* e⁻¹` of a commutative square of schemes
(`Stacks.EtaleCohomology.smallEtaleSetBaseChange`) is the mate of the identification of the two
composite direct images. This file records the identity characterising that mate: the unit of
`f⁻¹ ⊣ f_*` at `g_* F` followed by `f_*` of the base change map is `g_*` of the unit of
`e⁻¹ ⊣ e_*` at `F` followed by the identification of the composite direct images.

It is kept in a file with the imports of the definition, so that the elaborated instances agree
with those of the definition and the kernel check is syntactic.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_eq`: the base change map is the mate of the
  identification of the composite direct images.
* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_unit`: the defining identity of the base change
  map in terms of the units of the two adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u v

namespace Stacks.EtaleCohomology

variable {X Y S T : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)

/-- The base change map is the mate of the identification of the composite direct images. -/
theorem smallEtaleSetBaseChange_eq : smallEtaleSetBaseChange.{u, v} e h g f w =
  (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
      (smallEtaleInverseImageAdjunction.{u, v} f)).symm
    ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
      (eqToIso (congrArg (fun k : Y ⟶ S ↦
        (smallEtaleBaseChange k).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w)).hom ≫
      (smallEtalePushforwardCompIso.{u, v} h f).inv) := rfl

/-- **The defining identity of the base change map of sheaves of sets.** -/
theorem smallEtaleSetBaseChange_unit (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (smallEtaleInverseImageAdjunction.{u, v} f).unit.app
        (((smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
          (smallEtaleTopology S) (smallEtaleTopology T)).obj F) ≫
      ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology S) (smallEtaleTopology X)).map
          ((smallEtaleSetBaseChange.{u, v} e h g f w).app F) =
    ((smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology S) (smallEtaleTopology T)).map
        ((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F) ≫
      ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        (eqToIso (congrArg (fun k : Y ⟶ S ↦
          (smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w)).hom ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app
          ((smallEtaleInverseImage.{u, v} e).obj F) := by
  rw [smallEtaleSetBaseChange_eq]
  exact (unit_mateEquiv_symm (smallEtaleInverseImageAdjunction.{u, v} e)
    (smallEtaleInverseImageAdjunction.{u, v} f)
    ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
      (eqToIso (congrArg (fun k : Y ⟶ S ↦
        (smallEtaleBaseChange k).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology Y)) w)).hom ≫
      (smallEtalePushforwardCompIso.{u, v} h f).inv) F).symm

end Stacks.EtaleCohomology
