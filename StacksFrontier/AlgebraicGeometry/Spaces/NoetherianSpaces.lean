module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Noetherian algebraic spaces

An algebraic space over a scheme `S` is *Noetherian* when it is quasi-compact,
quasi-separated and locally Noetherian, where locally Noetherian means that the property
`AlgebraicGeometry.IsLocallyNoetherian` of schemes holds étale-locally on it in the sense
of `AlgebraicGeometry.Space.HasEtaleLocalProperty`.

## Main definitions

* `AlgebraicGeometry.Space.IsNoetherian` is Noetherianity of an algebraic space over `S`.

## Implementation notes

Quasi-separatedness in the definition is the *absolute* notion
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of Stacks 03BS, part (3), not the
notion `AlgebraicGeometry.Space.IsQuasiSeparatedOver` relative to the base scheme `S` of
Stacks 02X5: the source takes the diagonal over `Spec ℤ`. That is why the containment
`hZ : B.Contains (⊤_ Scheme)` of the terminal scheme in the chosen big fppf site is a
hypothesis of the definition, as it is for the four absolute separation properties
themselves. As for those, the predicate is meaningful for an arbitrary presheaf on the big
fppf site of `S` and no algebraicity hypothesis is imposed; clients supply one.

The definition is an abbreviation, so a client can use its three components directly.

## References

* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` is *Noetherian* when it is quasi-compact, quasi-separated and
locally Noetherian. Quasi-separatedness is the absolute notion of Stacks 03BS, part (3), which
is why the containment `hZ` of the terminal scheme in the site is required; local
Noetherianity is the étale-local scheme property `AlgebraicGeometry.IsLocallyNoetherian`. -/
@[stacks 03EA]
abbrev IsNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  IsQuasiCompactSpace B S hS F ∧
    IsAbsolutelyQuasiSeparated B S hS hZ F ∧
      HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X)

end AlgebraicGeometry.Space

end
