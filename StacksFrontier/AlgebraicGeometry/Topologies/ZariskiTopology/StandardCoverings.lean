module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard Zariski coverings

A standard Zariski covering of an affine scheme is a finite Zariski covering whose
members identify with standard affine opens of the scheme.

## Main definitions

* `AlgebraicGeometry.IsStandardZariskiCovering` is the predicate that a Zariski covering is
  finite and each of its maps identifies its source with a basic open of the target.

## References

* [Stacks Project, Tag 020R](https://stacks.math.columbia.edu/tag/020R)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A Zariski covering of an affine scheme `T` is standard if it has finitely many members and
every member identifies with a standard affine open `T.basicOpen f` of the target. -/
@[stacks 020R] public abbrev IsStandardZariskiCovering {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.Cover.{v} Scheme.zariskiPrecoverage) : Prop :=
  Finite 𝒰.I₀ ∧ ∀ j, ∃ f : Γ(T, ⊤), ∃ e : 𝒰.X j ≅ (T.basicOpen f).toScheme,
    𝒰.f j = e.hom ≫ (T.basicOpen f).ι

end AlgebraicGeometry
