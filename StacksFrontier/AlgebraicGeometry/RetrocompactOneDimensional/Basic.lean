module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.RetrocompactOneDimensional.Affine
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images from a retrocompact open of a one-dimensional scheme

Let `X` be a scheme all of whose local rings are Noetherian of Krull dimension at most one, and
let `U ⊆ X` be a retrocompact open subscheme with inclusion `j = U.ι`.  Then `R ᵖ j_* ℱ = 0` for
every `p > 0` and every quasi-coherent `𝒪_U`-module `ℱ`.

## Main results

* `Stacks.RetrocompactOneDimensional.isZero_rightDerived_pushforward_of_isRetrocompact`: the
  positive higher direct images of a quasi-coherent module along `U.ι` vanish.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.RetrocompactOneDimensional

/-- The positive higher direct images of a quasi-coherent module along the inclusion of a
retrocompact open subscheme of a scheme whose local rings are Noetherian of dimension at most one
vanish. -/
@[stacks 09N8]
theorem isZero_rightDerived_pushforward_of_isRetrocompact
    (X : Scheme.{u}) (U : X.Opens)
    (hU : IsRetrocompact (U : Set X))
    (h_noetherian : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (F : U.toScheme.Modules) (hF : F.IsQuasicoherent)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward U.ι).rightDerived p).obj F) :=
  have := isAffineHom_ι_of_isRetrocompact X U hU h_noetherian h_dimension
  have := hF
  Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward U.ι F p hp

end Stacks.RetrocompactOneDimensional

end
