module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Ideal.Colon
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Associated points of a sheaf of modules on a scheme

Let `X` be a scheme and let `F` be an `𝒪_X`-module. A point `x : X` is *associated* to `F`
when the maximal ideal `𝔪_x` of the local ring `𝒪_{X, x}` is an associated prime of the
`𝒪_{X, x}`-module `F_x`, that is, when some element of the stalk `F_x` has annihilator
exactly `𝔪_x`. The associated points of the scheme `X` itself are the associated points of
its structure sheaf.

## Main definitions

* `Stacks.Divisors.IsAssociatedPoint` is the predicate that a point of a scheme is associated
  to a sheaf of modules on it.
* `Stacks.Divisors.associatedPoints` is the set `Ass(F)` of associated points of a sheaf of
  modules.
* `Stacks.Divisors.schemeAssociatedPoints` is the set `Ass(X)` of associated points of a
  scheme.

## Main results

* `Stacks.Divisors.mem_associatedPoints_iff` and
  `Stacks.Divisors.mem_schemeAssociatedPoints_iff` identify membership in the two sets with
  the corresponding associated point predicate.
* `Stacks.Divisors.isAssociatedPoint_iff`,
  `Stacks.Divisors.isAssociatedPoint_iff_annihilator_span_eq` and
  `Stacks.Divisors.isAssociatedPoint_iff_forall_smul_eq_zero_iff` describe the predicate
  in terms of the stalk: some element of `F_x` has colon ideal, equivalently annihilator, the
  maximal ideal, or is killed by exactly the elements of the maximal ideal.
* `Stacks.Divisors.IsAssociatedPoint.nontrivial`: an associated point has nonzero stalk.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- A point `x` is *associated* to an `𝒪_X`-module `F` when the maximal ideal of the local ring
`𝒪_{X, x}` is an associated prime of the stalk `F_x`. -/
@[stacks 02OJ "part (1)"]
abbrev IsAssociatedPoint (F : X.Modules) (x : X) : Prop :=
  IsAssociatedPrimeStacks (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- The set `Ass(F)` of points associated to an `𝒪_X`-module `F`. -/
@[stacks 02OJ "part (2)"]
abbrev associatedPoints (F : X.Modules) : Set X := {x | IsAssociatedPoint F x}

/-- Membership in the associated points of a sheaf of modules is the associated point
predicate. -/
@[simp]
theorem mem_associatedPoints_iff (F : X.Modules) (x : X) :
    x ∈ associatedPoints F ↔ IsAssociatedPoint F x :=
  Iff.rfl

/-- The associated points `Ass(X)` of a scheme `X` are the associated points of its structure
sheaf. -/
@[stacks 02OJ "part (3)"]
abbrev schemeAssociatedPoints (X : Scheme.{u}) : Set X :=
  associatedPoints (SheafOfModules.unit X.ringCatSheaf)

/-- A point is associated to a scheme exactly when it is associated to the structure
sheaf. -/
@[simp]
theorem mem_schemeAssociatedPoints_iff (X : Scheme.{u}) (x : X) :
    x ∈ schemeAssociatedPoints X ↔
      IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x :=
  Iff.rfl

/-- Being an associated point is membership of the maximal ideal in the set of associated
primes of the stalk. -/
theorem isAssociatedPoint_iff_mem_assStacks (F : X.Modules) (x : X) :
    IsAssociatedPoint F x ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        assStacks (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  Iff.rfl

/-- A point `x` is associated to `F` exactly when some element of the stalk `F_x` has colon ideal
the maximal ideal. -/
theorem isAssociatedPoint_iff {F : X.Modules} {x : X} :
    IsAssociatedPoint F x ↔
      ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        (⊥ : Submodule (X.presheaf.stalk x)
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)).colon
            (Submodule.span (X.presheaf.stalk x) {m}) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  ⟨And.right, fun h => ⟨inferInstance, h⟩⟩

/-- A point is associated to `F` exactly when some element of the stalk `F_x` generates a
submodule whose annihilator is the maximal ideal. -/
theorem isAssociatedPoint_iff_annihilator_span_eq {F : X.Modules} {x : X} :
    IsAssociatedPoint F x ↔
      ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        (Submodule.span (X.presheaf.stalk x) {m}).annihilator =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  simp only [isAssociatedPoint_iff, Submodule.bot_colon]

/-- Elementwise form: a point is associated to `F` exactly when some element of the stalk
`F_x` is killed by precisely the elements of the maximal ideal. -/
theorem isAssociatedPoint_iff_forall_smul_eq_zero_iff {F : X.Modules} {x : X} :
    IsAssociatedPoint F x ↔
      ∃ m : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        ∀ r : X.presheaf.stalk x,
          r • m = 0 ↔ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  simp only [isAssociatedPoint_iff, SetLike.ext_iff, Submodule.colon_span,
    Submodule.mem_colon_singleton, Submodule.mem_bot]

/-- The stalk of `F` at an associated point is nontrivial. -/
theorem IsAssociatedPoint.nontrivial {F : X.Modules} {x : X} (h : IsAssociatedPoint F x) :
    Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := by
  obtain ⟨m, hm⟩ := isAssociatedPoint_iff.mp h
  refine ⟨m, 0, fun hm0 => (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top ?_⟩
  rw [← hm, hm0, Submodule.span_zero_singleton, Submodule.colon_bot]

end Stacks.Divisors

end
