module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib's `CategoryTheory.GrothendieckTopology.Point` is the fiber functor of SGA 4 IV 6.3.

Stacks tag 00ZT (a point of a topology) is a weaker notion, registered on
`CategoryTheory.GrothendieckTopology.IsPointOfTopology` in
`StacksFrontier/CategoryTheory/Sites/Point/OfTopology.lean`; every Mathlib point gives one
(`CategoryTheory.GrothendieckTopology.Point.isPointOfTopology`). -/

@[expose] public section

add_to_sga "4 IV 6.3" CategoryTheory.GrothendieckTopology.Point
