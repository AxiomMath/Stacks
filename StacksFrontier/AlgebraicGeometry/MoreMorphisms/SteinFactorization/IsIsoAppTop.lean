module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A proper morphism to an affine scheme with the right global functions

Let `g : X ⟶ Spec B` be proper with `B ⟶ Γ(X, 𝒪_X)` bijective. Then the relative normalization of
`Spec B` in `X` is `Spec B` itself, so `g` is the first factor of its Stein factorization, and its
fibres are geometrically connected ([Stacks, Tag 03H2]).

## Main results

* `Stacks.SteinFactorization.geometricallyConnected_of_isIso_appTop`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.SteinFactorization

variable {X : Scheme.{u}} {B : CommRingCat.{u}} (g : X ⟶ Spec B)

/-- **A proper morphism to an affine scheme inducing a bijection on global functions has
geometrically connected fibres** ([Stacks, Tag 03H2], clause (1)): it is the first factor of its
Stein factorization up to the isomorphism `fromNormalization`. -/
@[sga "1 X 1.3" "special case"]
theorem geometricallyConnected_of_isIso_appTop [IsProper g] [IsIso g.appTop] :
    GeometricallyConnected g := by
  have := isIso_fromNormalization_of_isIso_appTop g inferInstance
  have h := geometricallyConnected_toNormalization_of_isProper g
  rw [← g.toNormalization_fromNormalization]
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected.{u} _ _).2 h

end Stacks.SteinFactorization
