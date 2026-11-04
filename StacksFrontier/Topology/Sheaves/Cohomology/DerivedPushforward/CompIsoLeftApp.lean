module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting

/-!
# The comparison down the left of a square, at an object

For a commutative square `gZ ≫ j = j' ≫ g'` of ringed spaces the comparison
`L(g')^* ⋙ L(j')^* ≅ L(gZ ≫ j)^*` is the composition isomorphism of Tag 0D5S followed by the
transport along the commutativity of the square.  This file records that splitting at an object,
for the inverse, and the resulting form of a datum transported along the square.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_inv_app`: the splitting.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_inv_app_comp`: the transported
  datum.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.DerivedBaseChange

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The inverse of the transport along an equality of morphisms, at an object. -/
theorem eqToIso_derivedPullback_inv_app' {A C : RingedSpace.{u, u}} {a b : A ⟶ C}
    (e : a = b) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing C))) :
    (eqToIso (congrArg (fun q : A ⟶ C => derivedPullback q) e)).inv.app M =
      eqToHom (congrArg (fun q : A ⟶ C => (derivedPullback q).obj M) e.symm) := by
  subst e
  simp

variable {X' X Z' Z : RingedSpace.{u, u}} (g' : X' ⟶ X) (j : Z ⟶ X) (j' : Z' ⟶ X')
  (gZ : Z' ⟶ Z) (hg : gZ ≫ j = j' ≫ g')

/-- The inverse of the comparison down the left of a square. -/
theorem derivedPullbackCompIsoLeft_inv :
    (derivedPullbackCompIsoLeft gZ j' j g' hg).inv =
      (eqToIso (congrArg (fun r : Z' ⟶ X => derivedPullback r) hg.symm)).inv ≫
        (derivedPullbackCompIsoCanonical j' g').inv :=
  (congrArg Iso.inv (derivedPullbackCompIsoLeft_eq_trans gZ j' j g' hg)).trans
    (Iso.trans_inv _ _)

/-- The inverse of the comparison down the left of a square, at an object. -/
theorem derivedPullbackCompIsoLeft_inv_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullbackCompIsoLeft gZ j' j g' hg).inv.app K =
      (eqToIso (congrArg (fun r : Z' ⟶ X => derivedPullback r) hg.symm)).inv.app K ≫
        (derivedPullbackCompIsoCanonical j' g').inv.app K :=
  (congrArg (fun t => t.app K) (derivedPullbackCompIsoLeft_inv g' j j' gZ hg)).trans
    (NatTrans.comp_app _ _ K)

/-- The datum along the left composite is the transport of the datum along the right one. -/
theorem derivedPullbackCompIsoLeft_inv_app_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullbackCompIsoLeft gZ j' j g' hg).inv.app K ≫ (derivedPullback j').map φ =
      eqToHom (congrArg (fun r : Z' ⟶ X => (derivedPullback r).obj K) hg) ≫
        (derivedPullbackCompIsoCanonical j' g').inv.app K ≫ (derivedPullback j').map φ := by
  rw [derivedPullbackCompIsoLeft_inv_app, eqToIso_derivedPullback_inv_app' hg.symm K,
    Category.assoc]

end Stacks.Cohomology.DerivedBaseChange
