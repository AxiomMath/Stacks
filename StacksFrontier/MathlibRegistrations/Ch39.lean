module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations for Stacks Project Chapter 39, Groupoid Schemes

* Tag 03BF: the ring of invariants `C = {a ∈ A | t♯(a) = s♯(a)}` is the equalizer
  subring `RingHom.eqLocus t♯ s♯`.
-/

add_to_stacks 03BF RingHom.eqLocus

-- Definition: a group scheme `G` over `S` is smooth, flat or separated if `G → S` is so.
add_to_stacks 047E "(1) smooth: `Smooth G.hom` for `G` a group object over `S`"
  AlgebraicGeometry.Smooth
add_to_stacks 047E "(2) flat: `Flat G.hom`" AlgebraicGeometry.Flat
add_to_stacks 047E "(3) separated: `IsSeparated G.hom`" AlgebraicGeometry.IsSeparated
