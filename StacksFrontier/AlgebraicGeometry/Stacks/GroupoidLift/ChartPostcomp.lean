module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartDescent.Transport

/-!
# Composing a chart with a natural bijection

A chart `b` of a functor `X` on `κ`-small `A'`-algebras by `Q`, followed by a natural
transformation `τ : X ⟶ Y`, is a chart of `Y` by `Q`
(`AlgebraicGeometry.Stack.GroupoidLift.chartPostcomp`). When `τ` is bijective at every algebra,
the composite is formally étale as soon as `b` is
(`AlgebraicGeometry.Stack.GroupoidLift.chartPostcomp_isFormallyEtale`): the lifting problems of
the two charts correspond under `τ`.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.chartPostcomp`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.chartPostcomp_isFormallyEtale`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {X Y : SmallAlg A' κ ⥤ Type u}
  {Q : Type u} [CommRing Q] [Algebra A' Q]

/-- A chart followed by a natural transformation. -/
def chartPostcomp (b : Chart X Q) (τ : X ⟶ Y) : Chart Y Q where
  app C v := τ.app C (b.app C v)
  natural f v := by
    rw [← b.natural]
    exact (NatTrans.naturality_apply τ f (b.app _ v)).symm

/-- The chart `chartPostcomp b τ` sends `v : Q →ₐ[A'] C` to `τ.app C (b.app C v)`. -/
theorem chartPostcomp_app (b : Chart X Q) (τ : X ⟶ Y) (C : SmallAlg A' κ) (v : Q →ₐ[A'] C.obj) :
    (chartPostcomp b τ).app C v = τ.app C (b.app C v) := rfl

/-- **A formally étale chart followed by a natural bijection is formally étale.** -/
theorem chartPostcomp_isFormallyEtale {b : Chart X Q} (hb : b.IsFormallyEtale) (τ : X ⟶ Y)
    (hτ : ∀ C, Function.Bijective (τ.app C)) : (chartPostcomp b τ).IsFormallyEtale := by
  intro R R₀ q hq hsq c z hz
  obtain ⟨z', rfl⟩ := (hτ R).2 z
  have hz' : X.map q z' = b.app R₀ c := by
    refine (hτ R₀).1 ?_
    exact (NatTrans.naturality_apply τ q z').trans hz
  obtain ⟨ℓ, ⟨hℓ₁, hℓ₂⟩, huniq⟩ := hb R R₀ q hq hsq c z' hz'
  refine ⟨ℓ, ⟨hℓ₁, congrArg (τ.app R) hℓ₂⟩, fun ℓ' ⟨h₁, h₂⟩ ↦ huniq ℓ' ⟨h₁, (hτ R).1 h₂⟩⟩

end AlgebraicGeometry.Stack.GroupoidLift

end
