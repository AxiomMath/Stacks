module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible sheaves of modules on a topological space

An invertible sheaf of modules is locally isomorphic to the structure sheaf. A sheaf of modules
is trivial when such an isomorphism exists globally.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible` says that a sheaf of modules is
  locally isomorphic to the structure sheaf.
* `AlgebraicGeometry.SheafOfModules.OnSpace.IsTrivial` says that a sheaf of modules is globally
  isomorphic to the structure sheaf.

## Main results

* `AlgebraicGeometry.SheafOfModules.OnSpace.isInvertible_iff` is the characterizing
  local-isomorphism criterion.
* `AlgebraicGeometry.SheafOfModules.OnSpace.isTrivial_unit` says that the structure sheaf is
  trivial.
* `AlgebraicGeometry.SheafOfModules.OnSpace.IsTrivial.isInvertible` says that every trivial
  sheaf is invertible.

## Implementation notes

Restriction to an open subset `U` is represented by restriction to the over-site of `U`, which
is equivalent to working with sheaves on the open subspace. The definition is made for a sheaf
of rings on an arbitrary topological space; in particular it applies to the structure sheaf of a
locally ringed space without using localness of its stalks. The characterization theorem lets
the class be used without unfolding it, while the structure sheaf has a canonical invertibility
instance.

The `OnSpace` namespace distinguishes these predicates from the tensor-equivalence form of
invertibility and the corresponding triviality predicate on a general site, which carry the
plain names in `AlgebraicGeometry.SheafOfModules`.

## References

* [Stacks Project, Tag 02AD](https://stacks.math.columbia.edu/tag/02AD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.SheafOfModules.OnSpace

/-- A sheaf of modules is invertible if every point has an open neighbourhood on which it is
isomorphic to the structure sheaf. -/
@[stacks 02AD "invertible sheaves", ega "0 5.4.1" "invertible"]
class IsInvertible {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (L : _root_.SheafOfModules.{v} R) : Prop where
  /-- Every point has an open neighbourhood on which the sheaf is isomorphic to the structure
  sheaf. -/
  locally_iso : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    Nonempty (L.over U ≅ _root_.SheafOfModules.unit (R.over U))

/-- A sheaf of modules is trivial if it is globally isomorphic to the structure sheaf. -/
@[stacks 02AD "trivial sheaves"]
abbrev IsTrivial {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (L : _root_.SheafOfModules.{v} R) : Prop :=
  Nonempty (L ≅ _root_.SheafOfModules.unit R)

/-- A sheaf is invertible exactly when it is locally isomorphic to the structure sheaf. -/
theorem isInvertible_iff {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (L : _root_.SheafOfModules.{v} R) :
    IsInvertible L ↔ ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      Nonempty (L.over U ≅ _root_.SheafOfModules.unit (R.over U)) :=
  ⟨fun h ↦ h.locally_iso, fun h ↦ ⟨h⟩⟩

/-- The structure sheaf, regarded as a module over itself, is trivial. -/
@[simp]
theorem isTrivial_unit {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    IsTrivial (_root_.SheafOfModules.unit R) := ⟨Iso.refl _⟩

/-- A globally trivial sheaf of modules is invertible. -/
theorem IsTrivial.isInvertible {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    {L : _root_.SheafOfModules.{v} R} (h : IsTrivial L) : IsInvertible L :=
  ⟨fun _ ↦ ⟨⊤, by simp, Nonempty.map (_root_.SheafOfModules.overFunctor R ⊤).mapIso h⟩⟩

/-- The structure sheaf, regarded as a module over itself, is invertible. -/
instance unit_isInvertible {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}) :
    IsInvertible (_root_.SheafOfModules.unit R) := isTrivial_unit R |>.isInvertible

end AlgebraicGeometry.SheafOfModules.OnSpace
