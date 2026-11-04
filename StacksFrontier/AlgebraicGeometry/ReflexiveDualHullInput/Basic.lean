module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion

/-!
# The dual sheaf as an internal hom, and its stalks

The dual `F^∨ = SheafHom(F, 𝒪_X)` of a module on a scheme, as built in
`StacksFrontier/AlgebraicGeometry/Reflexive/Basic.lean`, is the internal hom of
[Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) with the structure sheaf as
target.  That is a definitional fact and nothing had recorded it, so the dual sheaf was
cut off from the internal-hom theory of
[Stacks, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO) and in particular from
[Stacks, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP), the computation of the
stalks of an internal hom.

This file supplies the missing identification and reads 01CP off through it: for a module
of finite presentation, the stalk of `F^∨` at a point is the module of linear functionals on
the stalk of `F`, and the identification sends the germ of a local section of `F^∨` and the
germ of a local section of `F` to the germ of their pairing.

## Main definitions

* `dualSheafStalkEquiv F x`: Tag 01CP at the dual sheaf -- the canonical linear equivalence
  from the stalk of `F^∨` at `x` to the module of linear maps from the stalk of `F` to the
  stalk of the structure sheaf read as a module, for `F` of finite presentation.

## Main results

* `dualSheafHom_obj`: the packaging is of `dualSheaf F` on the nose.
* `dualSheafHom_sectionsEquiv_app_id`: the section identification of the packaging, read at
  the terminal object of a slice site, is the pairing `dualPairing`.  This is what makes the
  germ formula below a statement about the dual sheaf's own API.
* `dualSheafStalkEquiv_germ`: the stalk identification carries the germ of a functional and
  the germ of a section to the germ of the value of the one on the other.

## Implementation notes

The packaging of the dual as a `SheafHom` in the sense of Tag 01CO is
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafHom` of
`StacksFrontier/AlgebraicGeometry/Reflexive/ExtensionChain/StalkCriterion.lean`, which this file
imports and uses; its `obj` field is `dualSheaf F` itself, not an isomorphic copy, and all three
of its compatibility fields hold by definitional unfolding.  Underneath it is the `private`
`internalSheafHom` of `StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/LocalHom.lean`,
instantiated with the structure sheaf as target.

The target of the stalk equivalence is the stalk of `SheafOfModules.unit`, i.e. the stalk of
the structure sheaf read as a module, which is a different colimit from the local ring
`𝒪_{X, x}`.  `AlgebraicGeometry.structureSheafStalkLinearEquiv` identifies the two, but has
no germ formula recorded, so the equivalence is stated here over the module stalk and the
passage to `Module.Dual 𝒪_{X, x} F_x` is left to a consumer that needs it.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveDualHull

variable (X : Scheme.{u}) (F : X.Modules)

/-- The packaging is of the dual sheaf itself. -/
theorem dualSheafHom_obj : (dualSheafHom F).obj = dualSheaf F := rfl

/-- **The section identification of the packaging is the dual pairing.**  Read at the
terminal object of the slice site over `U`, the module map that `dualSheafHom` associates
to a local section `t` of `F^∨` evaluates `t` on a local section of `F`. -/
theorem dualSheafHom_sectionsEquiv_app_id {U : X.Opens} (t : Γ(dualSheaf F, U))
    (m : Γ(F, U)) :
    (((dualSheafHom F).sectionsEquiv U t).val.app (op (Over.mk (𝟙 U)))).hom m =
      dualPairing F t (Over.mk (𝟙 U)) m :=
  rfl

/-- **Stacks Tag 01CP at the dual sheaf.**  For a module of finite presentation the stalk of
`F^∨` at a point is canonically the module of linear maps from the stalk of `F` to the stalk
of the structure sheaf read as a module. -/
noncomputable def dualSheafStalkEquiv [F.IsFinitePresentation] (x : X) :
    SheafHomStalkLinearEquiv X.sheaf F (SheafOfModules.unit (structureSheaf X.sheaf))
      (dualSheafHom F) x :=
  sheafHomStalkLinearEquivOfFinitePresentation (dualSheafHom F) x

/-- **The germ formula for the stalk of the dual sheaf.**  The canonical identification
sends the germ at `x` of a local functional `t` and the germ at `x` of a local section `m`,
both over the same open, to the germ of the value `t m`. -/
theorem dualSheafStalkEquiv_germ [F.IsFinitePresentation] (x : X) (U : X.Opens) (hxU : x ∈ U)
    (t : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    (dualSheafStalkEquiv X F x).equiv
        (germAt (dualSheafHom F).obj U x hxU t) (germAt F U x hxU m) =
      germAt (SheafOfModules.unit (structureSheaf X.sheaf)) U x hxU
        (dualPairing F t (Over.mk (𝟙 U)) m) :=
  (dualSheafStalkEquiv X F x).germ_apply U hxU t m

end Stacks.AlgebraicGeometry.ReflexiveDualHull

end
