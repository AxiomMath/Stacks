module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations for Stacks Project Chapter 41, Étale Morphisms of Schemes

* Tag 039K: a flat morphism locally of finite type to a locally Noetherian scheme is universally
  open. Mathlib states it for flat morphisms locally of finite presentation; over a locally
  Noetherian base this is the same as locally of finite type.
-/

add_to_stacks 039K "flat and locally of finite presentation implies universally open"
  AlgebraicGeometry.UniversallyOpen.of_flat
add_to_stacks 039K "over a locally Noetherian base, locally of finite type is locally of finite \
  presentation" AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType

/-! ### Further tags of this chapter covered by Mathlib

Where a Mathlib declaration is more general than the tag, the note says how the tag is the
special case.

Not recorded here: Tag 024M. Mathlib has no definition of an unramified homomorphism of local rings
with the three conditions of the tag: `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`
characterizes conditions (1) and (2), but only under the hypothesis `EssFiniteType`, which is
condition (3), and no Mathlib notion bundles the three. -/

add_to_stacks 0251 "(1) flat module"
  Module.Flat
add_to_stacks 0251 "(1) flat: M ↦ M ⊗_A N is exact"
  Module.Flat.iff_rTensor_exact
add_to_stacks 0251 "(2) faithfully flat module"
  Module.FaithfullyFlat
add_to_stacks 0251 "(2) faithfully flat: flat, and M ↦ M ⊗_A N is faithful (kills no nonzero \
  map)"
  Module.FaithfullyFlat.iff_zero_iff_rTensor_zero
add_to_stacks 0251 "(3) flat ring map"
  RingHom.Flat
add_to_stacks 0251 "(3) faithfully flat ring map"
  RingHom.FaithfullyFlat

add_to_stacks 0256 "faithfully flat means flat and surjective"
  AlgebraicGeometry.Flat.isQuotientMap_of_surjective
