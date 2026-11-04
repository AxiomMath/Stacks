module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Base change of an identity in a slice category

Base changing the identity of `A` along `f : B ⟶ A` gives the identity of `B`: the pullback of
`𝟙 A` along `f` is `f` itself, so the second projection is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base changing the identity of `A` along `f : B ⟶ A` gives the identity of `B`. -/
def overPullbackIdIso {A B : Scheme.{u}} (f : B ⟶ A) :
    (Over.pullback f).obj (Over.mk (𝟙 A)) ≅ Over.mk (𝟙 B) :=
  Over.isoMk (asIso (pullback.snd (𝟙 A) f))

/-- Composing the comparison of `Over.mk (𝟙 B)` with the base change of `Over.mk (𝟙 A)` with the
first projection gives back `f`. -/
theorem overPullbackIdIso_inv_left_comp_fst {A B : Scheme.{u}} (f : B ⟶ A) :
    (overPullbackIdIso f).inv.left ≫ pullback.fst (𝟙 A) f = f := by
  simp [overPullbackIdIso]

end AlgebraicGeometry

end
