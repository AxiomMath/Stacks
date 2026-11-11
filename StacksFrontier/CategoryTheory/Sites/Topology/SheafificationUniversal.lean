module

public import Mathlib.CategoryTheory.Sites.Sheafification

import StacksCore.Tactic.StacksAttribute

/-!
# The universal property of sheafification

Mathlib's abstract sheafification `CategoryTheory.presheafToSheaf` comes with the adjunction
`CategoryTheory.sheafificationAdjunction`, whose unit is `CategoryTheory.toSheafify`: composing
with it is a bijection `Mor_{Sh(C)}(F^#, G) ≃ Mor_{PSh(C)}(F, G)`.

Stacks 00ZM is the same universal property for the specific construction `F^# = L L F` of
Stacks 00ZL (the plus construction applied twice), not for an abstract left adjoint. It is
registered on `CategoryTheory.GrothendieckTopology.existsUnique_toSheafify_comp_eq` in
`StacksFrontier.CategoryTheory.Sites.Topology.AssociatedSheaf`, which states the unique
factorization through `J.toSheafify F : F ⟶ J.plusObj (J.plusObj F)`.
-/
