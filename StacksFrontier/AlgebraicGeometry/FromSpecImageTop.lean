module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The image of the whole spectrum under `fromSpec`

For an affine open `U` of a scheme `X`, the canonical morphism
`AlgebraicGeometry.IsAffineOpen.fromSpec : Spec Γ(X, U) ⟶ X` has range `U`, so the image of the
whole of `Spec Γ(X, U)` is `U`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.fromSpec_image_top`: the image of the whole of
  `Spec Γ(X, U)` under `fromSpec` is `U`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.IsAffineOpen

/-- The image of the whole of `Spec Γ(X, U)` under `fromSpec` is the affine open `U`. -/
public theorem fromSpec_image_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec

end AlgebraicGeometry.IsAffineOpen

end
