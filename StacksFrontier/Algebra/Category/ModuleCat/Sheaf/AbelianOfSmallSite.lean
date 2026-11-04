module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The abelian structure on sheaves of modules over a small site, pinned

`SheafOfModules.instAbelian` makes the sheaves of modules over a sheaf of rings `R` an abelian
category, subject to two sheafification side conditions, `HasSheafify` and
`WEqualsLocallyBijective` for `AddCommGrpCat`. On a small site whose universe matches the module
universe both side conditions hold, and this file discharges them once.

## Main results

* `Stacks.SheafOfModules.abelianOfSmallSite` is that same abelian structure with the two
  sheafification side conditions discharged, for a sheaf of rings on a small site whose universe
  matches the module universe. It is a `local instance`: it adds no global instance, and is
  meant to be pinned with `attribute [local instance]` where the generic search is too dear.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

/-- **Sheaves of modules over a sheaf of rings on a small site form an abelian category**, when
the module universe agrees with the site's: `SheafOfModules.instAbelian` with its two
sheafification side conditions, `HasSheafify` and `WEqualsLocallyBijective` for
`AddCommGrpCat`, discharged once.

This is `SheafOfModules.instAbelian` and nothing else, and it is deliberately a `local
instance`: no global instance is added, and a consumer that needs it writes
`attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite`.  The reason to name it is
cost.  Synthesising the abelian structure from `SheafOfModules.instAbelian` at a concrete ring
sheaf rediscovers both side conditions from scratch, which exceeds the default
instance-synthesis budget at the binders of a sizeable development; against this declaration
there are no side goals left to solve, only the unification that reads `C` and `J` off the type
of `R`. -/
noncomputable local instance abelianOfSmallSite {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    Abelian (_root_.SheafOfModules.{u} R) :=
  _root_.SheafOfModules.instAbelian R

end Stacks.SheafOfModules

end
