module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatIdealTorsionFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's condition `(S₁)` for the structure sheaf

Serre's condition `(S₁)` for the structure sheaf read as a module over itself is Serre's
condition `(S₁)` for the scheme, because the stalk of that module is the local ring.

## Main results

* `AlgebraicGeometry.structureSheaf_sheafHasPropertySk_one_iff`: the two conditions agree.

## Implementation notes

This file exists only to hold that one comparison where both of its consumers can import it.
It was stated twice -- once publicly in `ResolutionOfSurfaces/Vanishing/GenericPointSection.lean`
and once privately in `Divisors/EmbeddedPoints/DimensionOne.lean` -- and those two files are
ordered, the first importing the second, so neither could serve as the other's survivor. A
common ancestor both import is the resolution.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Serre's condition `(S₁)` for the structure sheaf read as a module over itself is Serre's
condition `(S₁)` for the scheme, because the stalk of that module is the local ring. -/
@[ega "IV 5.7.2" "special case"]
theorem structureSheaf_sheafHasPropertySk_one_iff (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SheafHasPropertySk X (SheafOfModules.unit X.ringCatSheaf) 1 ↔ HasPropertySk X 1 := by
  rw [hasPropertySk_iff]
  have key (x : X) :
      (min (1 : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule X).val.presheaf x)) ≤
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (structureSheafModule X).val.presheaf x) :
            WithBot ℕ∞)) ↔
      (min (1 : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) : WithBot ℕ∞)) := by
    rw [Module.supportDim_eq_of_equiv (structureSheafStalkLinearEquiv X x),
      Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (structureSheafStalkLinearEquiv X x),
      Module.supportDim_self_eq_ringKrullDim]
  refine forall_congr' fun x => ?_
  rw [Stacks.SheafOfModules.stalkModule_eq _ _ _]
  exact key x

end AlgebraicGeometry

end
