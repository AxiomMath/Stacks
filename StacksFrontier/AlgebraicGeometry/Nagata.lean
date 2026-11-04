module

import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties

public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# Japanese and Nagata schemes

A scheme is *Japanese* (when integral) or *Nagata* when every point has an affine
open neighbourhood whose ring of sections is a Japanese, resp. Nagata, ring.

## Main definitions

* `IsJapaneseScheme`, `IsNagataScheme`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/-- An integral scheme `X` is **Japanese** if every point has an affine open neighbourhood `U`
whose ring of sections `O_X(U)` — a domain, since `X` is integral and `U` is nonempty — is a
Japanese ring. -/
def IsJapaneseScheme (X : Scheme.{u}) [IsIntegral X] : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, ∃ hx : x ∈ U.val,
    haveI : Nonempty U.val := ⟨⟨x, hx⟩⟩
    haveI : IsDomain Γ(X, U.val) := IsIntegral.component_integral U.val
    IsJapaneseRing Γ(X, U.val)

/-- A scheme `X` is **Nagata** if every point has an affine open neighbourhood `U` whose ring of
sections `O_X(U)` is a Nagata ring. -/
def IsNagataScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ IsNagataRing Γ(X, U.val)
