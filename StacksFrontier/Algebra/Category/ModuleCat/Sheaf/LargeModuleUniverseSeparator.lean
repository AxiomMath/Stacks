module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separator and enough injectives for sheaves of modules on a space, as instances

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LargeModuleUniverse.lean` makes
`SheafOfModules.{max u v} R`, for `R` a sheaf of `RingCat.{u}`-valued rings on a space in
`Type u`, abelian, and reduces its Grothendieck abelianness — hence its injective resolutions
and right derived functors — to the existence of a separator.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean` constructs that separator,
for an arbitrary site and with the universes of the site, of its homs, of the rings and of the
modules independent, under `UnivLE` between them.

Each of those two files leaves the other's contribution as a hypothesis, so neither alone
produces an instance: `SheafOfModules.hasSeparator_of_univLE` needs
`HasWeakSheafify J AddCommGrpCat.{v}` and `J.WEqualsLocallyBijective AddCommGrpCat.{v}`, which
Mathlib supplies only at the universe of the site and which the first file supplies at
`max u v`; and it is a `theorem`, so instance search does not see it. This file joins them and
registers the result, for the site of open sets of a topological space, as instances.

## Main results

* `Stacks.LargeModuleUniverse.hasSeparator_sheafOfModules` — **sheaves of modules on a space in
  `Type u` have a separator in every module universe above `u`**, as an instance.
* `Stacks.LargeModuleUniverse.enoughInjectives` — and therefore enough injectives, as an
  instance. This is what makes the left-hand side of Stacks 0DWR in positive degrees —
  `Stacks.LocalCohomology.cohomologyOverBase`, a right derived functor on
  `SheafOfModules.{max u v} X.ringCatSheaf` — elaborate with no hypothesis.
* `Stacks.LargeModuleUniverse.isGrothendieckAbelian` — the Grothendieck abelianness that
  `Stacks.LargeModuleUniverse.isGrothendieckAbelian_of_hasSeparator` was waiting for.

## Implementation notes

The module universe of `SheafOfModules.hasSeparator_of_univLE` is its first universe parameter
but is not determined by its arguments, so it is pinned here by applying the universes
explicitly; a type ascription on the result does the same job and is what
`SeparatorUnivLE.lean` recommends.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Stacks.LargeModuleUniverse

variable {Y : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})

/-- **Sheaves of modules on a space in `Type u` have a separator in every module universe above
`u`.** This is the fourth Grothendieck axiom, the one Mathlib supplies only at `v = u`, and the
only hypothesis of `Stacks.LargeModuleUniverse.isGrothendieckAbelian_of_hasSeparator` and
`Stacks.LargeModuleUniverse.enoughInjectives_of_hasSeparator`.

It is `SheafOfModules.hasSeparator_of_univLE` at the site of open sets of `Y`, whose two
sheafification hypotheses at the module universe `max u v` are
`Stacks.LargeModuleUniverse.hasSheafify` and
`Stacks.LargeModuleUniverse.wEqualsLocallyBijective`; the three `UnivLE` hypotheses hold
because the site, its homs and the rings all live in `u`. -/
instance hasSeparator_sheafOfModules : HasSeparator (SheafOfModules.{max u v} R) :=
  SheafOfModules.hasSeparator_of_univLE.{max u v, u, u, u} R

/-- **Sheaves of modules on a space in `Type u` with module universe `max u v` are Grothendieck
abelian relative to `max u v`**: three axioms from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LargeModuleUniverse.lean` and the separator
above. -/
theorem isGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} R) :=
  isGrothendieckAbelian_of_hasSeparator R inferInstance

/-- **Sheaves of modules on a space in `Type u` with module universe `max u v` have enough
injectives**, hence injective resolutions and right derived functors. This is what the
higher-degree comparison of Stacks 0DWR needs in order to be expressible at an independent
module universe, and as an instance it needs no hypothesis at the point of use. -/
@[sga "4½ Etat_0 6.2" "special case"]
instance enoughInjectives : EnoughInjectives (SheafOfModules.{max u v} R) :=
  enoughInjectives_of_hasSeparator R inferInstance

end Stacks.LargeModuleUniverse

end
