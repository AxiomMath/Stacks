module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen–Macaulay schemes

A scheme is Cohen–Macaulay when every point has an affine open neighbourhood whose ring of
sections is Noetherian and Cohen–Macaulay.

## Main definitions

* `AlgebraicGeometry.IsCohenMacaulay` is the Cohen–Macaulay property for schemes.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_iff` is the pointwise affine-neighbourhood
  characterization.
* `AlgebraicGeometry.IsCohenMacaulay.exists_affineOpen` extracts such a neighbourhood at a
  point.
* `AlgebraicGeometry.isCohenMacaulay_of_isEmpty` handles schemes with no points.

## Implementation notes

Affine open neighbourhoods are represented by `X.affineOpens`. The Noetherian structure on the
ring of sections is included in the existential data because `IsCohenMacaulayRing`, the predicate
of Stacks Project Tag 00NC, takes it as a typeclass argument. The named predicate is a definition
boundary; clients can rewrite with `isCohenMacaulay_iff` or apply
`IsCohenMacaulay.exists_affineOpen` without unfolding it. The empty-scheme behavior is exposed in
the more general typeclass form `isCohenMacaulay_of_isEmpty`.

## References

* [Stacks Project, Tag 02IO](https://stacks.math.columbia.edu/tag/02IO)
-/

public section

universe u

namespace AlgebraicGeometry

/-- **Cohen–Macaulay scheme.** A scheme `X` is Cohen–Macaulay if every point belongs to an
affine open `U` whose ring of sections `Γ(X, U)` is Noetherian and Cohen–Macaulay. -/
@[stacks 02IO, ega "IV 5.7.1"] public def IsCohenMacaulay (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
    ∃ h : IsNoetherianRing Γ(X, U.val),
      @IsCohenMacaulayRing Γ(X, U.val) _ h

/-- The pointwise affine-neighbourhood characterization of a Cohen–Macaulay scheme. -/
@[simp] public theorem isCohenMacaulay_iff (X : Scheme.{u}) :
    IsCohenMacaulay X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
        ∃ h : IsNoetherianRing Γ(X, U.val),
          @IsCohenMacaulayRing Γ(X, U.val) _ h :=
  Iff.rfl

/-- Extract a Cohen–Macaulay affine open neighbourhood of a point. -/
public theorem IsCohenMacaulay.exists_affineOpen {X : Scheme.{u}} (hX : IsCohenMacaulay X)
    (x : X) :
    ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ h : IsNoetherianRing Γ(X, U.val),
        @IsCohenMacaulayRing Γ(X, U.val) _ h :=
  hX x

/-- A scheme without points is Cohen–Macaulay. In particular, the empty scheme is
Cohen–Macaulay. -/
@[simp] public theorem isCohenMacaulay_of_isEmpty (X : Scheme.{u}) [IsEmpty X] :
    IsCohenMacaulay X := fun x => isEmptyElim x

end AlgebraicGeometry

end
