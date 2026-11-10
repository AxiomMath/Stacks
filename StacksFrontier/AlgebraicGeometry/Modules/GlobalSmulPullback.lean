module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing

/-!
# Multiplication by a global function commutes with pullback

For a morphism of schemes `σ : X ⟶ Y`, a global function `r ∈ Γ(Y, 𝒪_Y)` and an
`𝒪_Y`-module `M`, the pullback of multiplication by `r` on `M` is multiplication by `σ^♯ r` on
`σ^*M`. On the pushforward side this is a computation on sections, and the pullback side follows
from it through the adjunction `σ^* ⊣ σ_*`, multiplication by a global function being a natural
endomorphism of the identity functor.

## Main results

* `Stacks.RegularSequence.pushforward_map_globalSmulCenter` — `σ_*(σ^♯ r ·) = r · σ_*`.
* `Stacks.RegularSequence.pullback_map_globalSmulCenter` — `σ^*(r ·) = (σ^♯ r) · σ^*`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.RegularSequence

variable {X Y : Scheme.{u}} (σ : X ⟶ Y) (r : Γ(Y, ⊤))

/-- **The pushforward of multiplication by `σ^♯ r` is multiplication by `r`.** -/
theorem pushforward_map_globalSmulCenter (N : X.Modules) :
    (Scheme.Modules.pushforward σ).map ((globalSmulCenter X (σ.appTop r)).app N) =
      (globalSmulCenter Y r).app ((Scheme.Modules.pushforward σ).obj N) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  rw [Scheme.Modules.pushforward_map_app]
  revert m
  change ∀ m : Γ(N, σ ⁻¹ᵁ U), X.presheaf.map (σ ⁻¹ᵁ U).leTop.op (σ.appTop r) • m =
    ((globalSmulCenter Y r).app ((Scheme.Modules.pushforward σ).obj N)).app U m
  intro m
  have hr : X.presheaf.map (σ ⁻¹ᵁ U).leTop.op (σ.appTop r) =
      σ.app U (Y.presheaf.map U.leTop.op r) :=
    (congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(X, σ ⁻¹ᵁ U) => g r) (σ.naturality U.leTop.op)).symm
  rw [hr]
  rfl

/-- **The pullback of multiplication by `r` is multiplication by `σ^♯ r`.** -/
theorem pullback_map_globalSmulCenter (M : Y.Modules) :
    (Scheme.Modules.pullback σ).map ((globalSmulCenter Y r).app M) =
      (globalSmulCenter X (σ.appTop r)).app ((Scheme.Modules.pullback σ).obj M) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction σ
  apply (adj.homEquiv _ _).injective
  rw [← Category.comp_id ((Scheme.Modules.pullback σ).map ((globalSmulCenter Y r).app M)),
    ← Category.id_comp ((globalSmulCenter X (σ.appTop r)).app ((Scheme.Modules.pullback σ).obj M)),
    adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    pushforward_map_globalSmulCenter]
  exact ((globalSmulCenter Y r).naturality _).symm

end Stacks.RegularSequence

end
