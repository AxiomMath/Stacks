module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ReflexiveDualHullInput.Basic

/-!
# The stalk of the dual sheaf is the dual of the stalk

The companion file identifies the stalk of `F^∨` with the module of linear maps from the
stalk of `F` to the stalk of the structure sheaf *read as a module*.  That target is a
different colimit from the local ring `𝒪_{X, x}`, and the two are identified by
`AlgebraicGeometry.structureSheafStalkLinearEquiv`, which had no germ formula recorded --
`StacksFrontier/AlgebraicGeometry/ReflexiveTorsionFree/Converse.lean` says so in its
implementation notes and arranges its own statement to avoid needing one.

This file records that germ formula and uses it to put the stalk of the dual sheaf in the
form the module-level theory of reflexive modules is stated over: for `F` of finite
presentation, the stalk of `F^∨` at `x` is the `𝒪_{X, x}`-linear dual of the stalk of `F`,
by an identification carrying the germ of a functional and the germ of a section to the germ
of the value of the one on the other.

## Main definitions

* `dualSheafStalkDualEquiv F x`: the stalk of `F^∨` at `x` as `Module.Dual 𝒪_{X, x} F_x`.

## Main results

* `unitStalkLEquiv_germ`: the germ formula for `LocallyFreeRank.unitStalkLEquiv`, which
  that definition proves internally and does not export.
* `structureSheafStalkLinearEquiv_germ`: the germ formula for the identification of the
  stalk of the structure sheaf read as a module with the local ring.
* `dualSheafStalkDualEquiv_germ`: the germ formula for the dual identification.

## Implementation notes

`LocallyFreeRank.unitStalkLEquiv` is definitionally the inverse of
`Stacks.AlgebraPullbackQcoh.unitAbStalkIso`, whose germ formula *is* public, so the first
lemma is that inverse read off against `Iso.hom_inv_id`.  The step is taken by `change`
rather than by `rw`: the germ of a section of the structure sheaf read as a module is spelled
through `(structureSheafModule X).val.presheaf` at one site and through
`(PresheafOfModules.unit _).presheaf` at the other, and those are definitionally equal but
not syntactically so, which makes `rw` report that it cannot find a pattern that is present.
For the same reason the composite germ formulas are assembled as term-mode `congrArg`
chains.

The scalar ring is spelled `Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x`
throughout, never `X.presheaf.stalk x`.  The two are definitionally equal, but the module
structures on the stalks are registered at the first spelling only, and mixing the two makes
instance search fail on goals that are definitionally solved -- one spelling per statement is
what keeps the composite elaborating.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveDualHull

/-- **The germ formula for the unit-stalk equivalence.**  The identification of the stalk of
the presheaf of rings `R` regarded as a module over itself with the stalk of `R` carries the
germ of a section to the germ of the same section.  The equivalence proves this internally
and does not export it; it is recovered here from the germ formula of the underlying
comparison isomorphism. -/
theorem unitStalkLEquiv_germ {Y : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} Y) (x : Y)
    (U : Opens Y) (h : x ∈ U) (r : R.obj (op U)) :
    LocallyFreeRank.unitStalkLEquiv R x
        (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x h r) =
      R.germ U x h r := by
  have hinv := Stacks.AlgebraPullbackQcoh.unitAbStalkIso_hom_germ R x U h r
  change (Stacks.AlgebraPullbackQcoh.unitAbStalkIso R x).inv.hom
      (TopCat.Presheaf.germ (PresheafOfModules.unit R).presheaf U x h r) = _
  rw [← hinv]
  exact ConcreteCategory.congr_hom (Stacks.AlgebraPullbackQcoh.unitAbStalkIso R x).hom_inv_id _

/-- **The germ formula for the structure-sheaf stalk identification.**  Reading the stalk of
the structure sheaf as a module and then identifying it with the local ring carries the germ
of a function to the germ of the same function. -/
theorem structureSheafStalkLinearEquiv_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(X, U)) :
    structureSheafStalkLinearEquiv X x
        (TopCat.Presheaf.germ (C := Ab.{u}) (structureSheafModule X).val.presheaf U x hx s) =
      X.presheaf.germ U x hx s := by
  change SemilinearStalk.commStalkRingEquiv X.presheaf x
      (LocallyFreeRank.unitStalkLEquiv (X.presheaf ⋙ forget₂ CommRingCat RingCat) x
        (TopCat.Presheaf.germ (C := Ab.{u}) (structureSheafModule X).val.presheaf U x hx s)) = _
  exact (congrArg (fun m => SemilinearStalk.commStalkRingEquiv X.presheaf x m)
      (unitStalkLEquiv_germ (X.presheaf ⋙ forget₂ CommRingCat RingCat) x U hx s)).trans
    (commStalkRingEquiv_germ X.presheaf x U hx s)

variable (X : Scheme.{u}) (F : X.Modules)

/-- **The stalk of the dual sheaf is the dual of the stalk.**  For a module of finite
presentation, Stacks Tag 01CP composed with the identification of the stalk of the structure
sheaf with the local ring exhibits the stalk of `F^∨` at `x` as the `𝒪_{X, x}`-linear dual
of the stalk of `F`. -/
noncomputable def dualSheafStalkDualEquiv [F.IsFinitePresentation] (x : X) :
    modStalk (dualSheaf F) x ≃ₗ[ringStalk X.sheaf x]
      Module.Dual (ringStalk X.sheaf x) (modStalk F x) := by
  letI e2 : modStalk (SheafOfModules.unit (structureSheaf X.sheaf)) x
      ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x := structureSheafStalkLinearEquiv X x
  exact (dualSheafStalkEquiv X F x).equiv.trans (LinearEquiv.congrRight e2)

/-- **The germ formula for the dual identification.**  A germ of a local functional, applied
to a germ of a local section, is the germ of the value of the functional on the section. -/
theorem dualSheafStalkDualEquiv_germ [F.IsFinitePresentation] (x : X) (U : X.Opens)
    (hxU : x ∈ U) (t : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    dualSheafStalkDualEquiv X F x (germAt (dualSheaf F) U x hxU t) (germAt F U x hxU m) =
      X.presheaf.germ U x hxU (dualPairing F t (Over.mk (𝟙 U)) m) :=
  (congrArg (fun y => structureSheafStalkLinearEquiv X x y)
      (dualSheafStalkEquiv_germ X F x U hxU t m)).trans
    (structureSheafStalkLinearEquiv_germ X x U hxU (dualPairing F t (Over.mk (𝟙 U)) m))

end Stacks.AlgebraicGeometry.ReflexiveDualHull

end
