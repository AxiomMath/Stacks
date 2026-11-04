module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify

import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of a presheaf of modules

The sheafification `F^#` of a presheaf of `O`-modules `F`, taken as a presheaf of abelian
groups, carries a map `O^# × F^# → F^#` making it a sheaf of `O^#`-modules compatibly with
`O × F → F`, and this sheafification has the expected universal property: a morphism of
presheaves of `O`-modules from `F` into a sheaf of `O^#`-modules `G` factors uniquely through
`F^#`.

Both parts are in Mathlib. `PresheafOfModules.sheafify` is the sheaf of modules of the first
part, `PresheafOfModules.toSheafify` the canonical map `F → F^#` making the square commute, and
`PresheafOfModules.sheafifyHomEquiv` the adjunction bijection of the second part, whose
existence and uniqueness of the factorisation are the two directions of its being an
equivalence.
-/

@[expose] public section

add_to_stacks 0089 "the sheafification `F^#` as a sheaf of `O^#`-modules"
  PresheafOfModules.sheafify
add_to_sga "4 IV 12.4" PresheafOfModules.sheafify
add_to_ega "I 1.3.13" "more general" PresheafOfModules.sheafify
add_to_stacks 0089 "the canonical map `F → F^#` of presheaves of `O`-modules"
  PresheafOfModules.toSheafify
add_to_stacks 0089 "the universal property: morphisms out of `F^#` correspond to morphisms out
  of `F`" PresheafOfModules.sheafifyHomEquiv
