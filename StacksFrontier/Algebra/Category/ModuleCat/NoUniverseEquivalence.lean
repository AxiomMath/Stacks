module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Logic.Small.Basic

/-!
# A category of modules is not equivalent to a category with smaller Hom-sets

Let `R` be a nontrivial ring in `Type (u + 1)`.  The category `ModuleCat.{u + 1} R` of
`R`-modules whose carrier lies in `Type (u + 1)` is **not** equivalent to any category whose
Hom-sets lie in `Type u`.  In particular it is not equivalent to `ModuleCat.{u} R'` for any ring
`R'`, however `R` and `R'` are related — a module category remembers the universe of its modules,
and no ring equivalence, however it crosses universes, moves it.

The obstruction is a cardinality one and it is visible in a single Hom-set.  The free `R`-module
on the index type `Type u` lies in `Type (u + 1)`, and the morphisms to it out of the free module
of rank one are its own elements, of which there are at least as many as there are objects of
`Type u`.  An equivalence is fully faithful, so it would put that Hom-set in bijection with one in
`Type u`, making `Type u` itself `u`-small — and `Small.{u} (Type u)` is false,
`not_small_type`.

## Main results

* `ModuleCat.not_nonempty_equivalence_of_category_succ`: **the non-equivalence.**

## Implementation notes

The hypothesis `Nontrivial R` cannot be dropped and is not a technicality: over the zero ring
every module is zero, so `ModuleCat.{v} 0` is equivalent to the one-object one-morphism category
at every `v`, and all of these are equivalent to each other.  It enters exactly once, as
`one_ne_zero` in the injectivity of `t ↦ Finsupp.single t 1`.

The statement is about `Type (u + 1)` and `Type u` rather than about two general universes
because that is the step at which it is used:  a ring of global sections read as compatible
families over a site whose objects lie in `Type (u + 1)` lives one universe above the sections
themselves, and a proposed identification of its modules with modules over a ring in `Type u` is
exactly what this refutes.  Nothing in the argument is special to that step; the same proof with
`max (u + 1) w` in place of `u + 1` works for `R : Type w`.

## References

* Mathlib, `not_small_type`, in `Mathlib.Logic.Small.Basic`.
-/

@[expose] public section

open CategoryTheory

universe u u₂

namespace ModuleCat

/-- **A category of modules is not equivalent to a category with smaller Hom-sets.**  For a
nontrivial ring `R` in `Type (u + 1)` there is no equivalence between `ModuleCat.{u + 1} R` and a
category whose Hom-sets lie in `Type u`.

Applied to `D := ModuleCat.{u} R'` this says that the module category of a ring cannot be
identified with the module category of another ring one universe down, so an identification of two
rings across a universe step — a `RingEquiv` between a ring in `Type (u + 1)` and a ring in
`Type u` — never induces one of their module categories at their own universes.

The free module on `Type u` has at least as many elements as `Type u` has objects, and the
morphisms to it from the free module of rank one are exactly its elements; a fully faithful
functor into `D` would make that set `u`-small, hence `Type u` itself `u`-small. -/
theorem not_nonempty_equivalence_of_category_succ {R : Type (u + 1)} [Ring R] [Nontrivial R]
    {D : Type u₂} [Category.{u} D] : ¬ Nonempty (ModuleCat.{u + 1} R ≌ D) := by
  rintro ⟨E⟩
  let e : (ModuleCat.of R R ⟶ ModuleCat.of R ((Type u) →₀ R)) ≃ ((Type u) →₀ R) :=
    ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv
  have : Small.{u} ((Type u) →₀ R) :=
    small_map (e.symm.trans E.fullyFaithfulFunctor.homEquiv)
  exact not_small_type.{u, u}
    (small_of_injective (Finsupp.single_left_injective (b := (1 : R)) one_ne_zero))

end ModuleCat

end
