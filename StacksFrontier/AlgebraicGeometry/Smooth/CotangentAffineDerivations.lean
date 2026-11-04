module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective

/-!
# Derivations at an affine chart as linear maps out of the sections of `a^*Ω_{X/S}`

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and `W` an affine open
of `X` with `W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X` be a morphism from an affine scheme `T` mapping
into `W`. For a sheaf of modules `M` on `T` this file identifies the `Γ(S, V)`-derivations of
`Γ(X, W)` with values in `Γ(M, ⊤)` with the `Γ(T, ⊤)`-linear maps
`Γ(a^*Ω_{X/S}, ⊤) ⟶ Γ(M, ⊤)`, the identification being composition with the pullback
`Stacks.Smooth.pullbackD` of the universal differential.

The point of the statement is that the left-hand side depends on the *chart* `(V, W)` while the
right-hand side does not. It is the form in which the correction step of
[Stacks Project, Tag 02H6] — step (II) of the Stacks proof — consumes the affine computation of
`Ω_{X/S}`: over an overlap of two charts the difference of the two local lifts along a
first-order thickening is a derivation, and to compare the derivation computed in one chart with
the derivation computed in the other one needs both to be read inside one chart-independent
group.

## Main results

* `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD`: exactly one `Γ(T, ⊤)`-linear map
  `Γ(a^*Ω_{X/S}, ⊤) ⟶ Γ(M, ⊤)` induces a given `Γ(S, V)`-derivation of `Γ(X, W)`.
* `Stacks.Smooth.compDer_pullbackCotangentDerivation_apply`: the derivation induced by such a
  linear map is `b ↦ θ (pullbackD b)`, so that the statement above says exactly that
  `θ ↦ θ.compDer (pullbackCotangentDerivation …)` is a bijection.

## Implementation notes

This is a corollary of `Stacks.Smooth.bijective_cotangentComparison`. Writing `R = Γ(S, V)`,
`B = Γ(X, W)` and `A = Γ(T, ⊤)`:

* a derivation `δ` gives a `B`-linear map `Ω[B⁄R] ⟶ Γ(M, ⊤)` by
  `Derivation.liftKaehlerDifferential`, hence an `A`-linear map `A ⊗[B] Ω[B⁄R] ⟶ Γ(M, ⊤)` by
  `LinearMap.liftBaseChange`, and transporting along the isomorphism
  `Stacks.Smooth.cotangentComparisonEquiv` gives the required `θ`; and
* two candidates `θ₁`, `θ₂` agree after composing with the comparison map by
  `Stacks.Smooth.tensorKaehlerDifferential_linearMap_ext`, since
  `cotangentComparison (1 ⊗ d b) = pullbackD b`, hence agree because the comparison map is
  surjective.

Note that unlike `Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf`, whose uniqueness is
for a *morphism of sheaves of modules*, the uniqueness here is for a linear map on global
sections alone; that is strictly stronger and is what makes the identification a bijection of
groups rather than merely a surjection. It is bijectivity of the comparison map that supplies
it.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens}

/-- The derivation induced by a `Γ(T, ⊤)`-linear map out of the global sections of
`a^*Ω_{X/S}` is composition with the pullback of the universal differential. -/
theorem compDer_pullbackCotangentDerivation_apply (M : T.Modules) (hWV : W ≤ f ⁻¹ᵁ V)
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    letI := moduleAppLE a M hUW
    letI := moduleAppLEBase f a M hWV hUW
    letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
    letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
    letI := isScalarTowerAppLE a M hUW
    letI := isScalarTowerAppLE a (pullbackCotangentSheaf f a) hUW
    letI := isScalarTowerAppLEBase f a M hWV hUW
    letI := isScalarTowerAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
    ∀ (θ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] Γ(M, (⊤ : T.Opens)))
      (b : Γ(X, W)),
      (θ.restrictScalars Γ(X, W)).compDer (pullbackCotangentDerivation f a W hWV hUW) b
        = θ (pullbackD f a W hUW b) :=
  fun _ _ ↦ rfl

/-- **Derivations at an affine chart are the linear maps out of the sections of `a^*Ω_{X/S}`.**
Let `V` be an affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, let `T` be an
affine scheme and `a : T ⟶ X` a morphism mapping into `W`, and let `M` be a sheaf of modules on
`T`. Every `Γ(S, V)`-derivation of `Γ(X, W)` with values in `Γ(M, ⊤)` is induced by exactly one
`Γ(T, ⊤)`-linear map `Γ(a^*Ω_{X/S}, ⊤) ⟶ Γ(M, ⊤)`.

Together with `Stacks.Smooth.compDer_pullbackCotangentDerivation_apply` this says that
`θ ↦ θ.compDer (pullbackCotangentDerivation f a W hWV hUW)` is a bijection from those linear
maps onto the derivations, which is the chart-independent description of the group acting on the
lifts along a first-order thickening that [Stacks Project, Tag 02H6] needs. -/
theorem existsUnique_linearMap_comp_pullbackD [IsAffine T] (M : T.Modules) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := moduleAppLE a M hUW
    letI := moduleAppLEBase f a M hWV hUW
    ∀ δ : Derivation Γ(S, V) Γ(X, W) Γ(M, (⊤ : T.Opens)),
      ∃! θ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] Γ(M, (⊤ : T.Opens)),
        ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) = δ b := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := moduleAppLE a M hUW
  let := moduleAppLEBase f a M hWV hUW
  let := isScalarTowerAppLE a M hUW
  let := isScalarTowerAppLEBase f a M hWV hUW
  intro δ
  set E := cotangentComparisonEquiv f a hV hW hWV hUW with hE
  have hE2 : ∀ b : Γ(X, W),
      E (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b) = pullbackD f a W hUW b := fun b ↦ by
    rw [hE, cotangentComparisonEquiv_apply, cotangentComparison_one_tmul_D]
  have hE1 : ∀ b : Γ(X, W),
      E.symm (pullbackD f a W hUW b) = 1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b := fun b ↦
    E.symm_apply_eq.mpr (hE2 b).symm
  have huniq : ∀ θ₁ θ₂ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)]
      Γ(M, (⊤ : T.Opens)),
      (∀ b : Γ(X, W), θ₁ (pullbackD f a W hUW b) = δ b) →
      (∀ b : Γ(X, W), θ₂ (pullbackD f a W hUW b) = δ b) → θ₁ = θ₂ := by
    intro θ₁ θ₂ h₁ h₂
    have hc : θ₁ ∘ₗ E.toLinearMap = θ₂ ∘ₗ E.toLinearMap := by
      refine tensorKaehlerDifferential_linearMap_ext _ _ fun b ↦ ?_
      show θ₁ (E (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b))
        = θ₂ (E (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b))
      rw [hE2 b, h₁ b, h₂ b]
    refine LinearMap.ext fun y ↦ ?_
    have h := LinearMap.congr_fun hc (E.symm y)
    change θ₁ (E (E.symm y)) = θ₂ (E (E.symm y)) at h
    rwa [E.apply_symm_apply] at h
  refine ⟨(δ.liftKaehlerDifferential.liftBaseChange Γ(T, ⊤)) ∘ₗ E.symm.toLinearMap,
    fun b ↦ ?_, fun θ hθ ↦ huniq θ _ hθ fun b ↦ ?_⟩ <;>
  · show (δ.liftKaehlerDifferential.liftBaseChange Γ(T, ⊤))
      (E.symm (pullbackD f a W hUW b)) = δ b
    rw [hE1, LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

end Stacks.Smooth

end
