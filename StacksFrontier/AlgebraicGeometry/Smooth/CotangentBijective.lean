module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentExistence
public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport

/-!
# The affine computation of the sheaf of relative differentials

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and `W` an affine open
of `X` with `W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X` be a morphism from an **affine** scheme `T`
mapping into `W`. Writing `R = Γ(S, V)`, `B = Γ(X, W)` and `A = Γ(T, ⊤)`, the comparison map
`Stacks.Smooth.cotangentComparison` is an `A`-linear map

`A ⊗[B] Ω[B⁄R] ⟶ Γ(a^*Ω_{X/S}, ⊤)`.

This file proves that it is **bijective**. That is the affine computation of
[Stacks Project, Tag 01UM] in the form that [Stacks Project, Tag 02H6] consumes.

## Main results

* `Stacks.Smooth.bijective_cotangentComparison`: the comparison map is bijective.
* `Stacks.Smooth.cotangentComparisonEquiv` packages it as a linear equivalence.
* `Stacks.Smooth.kaehlerDifferential_linearMap_ext` and
  `Stacks.Smooth.tensorKaehlerDifferential_linearMap_ext` are the two extensionality principles
  the proof runs on: a `B`-linear map out of `Ω[B⁄R]` is determined by its values on the
  differentials `d b`, and an `A`-linear map out of `A ⊗[B] Ω[B⁄R]` is determined by its values
  on the `1 ⊗ d b`.

## Implementation notes

Both halves come from the corepresentability of derivations by `a^*Ω_{X/S}`, which is
`Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf`, applied to a sheaf of modules `N` on `T`
whose global sections are `A ⊗[B] Ω[B⁄R]`. Such an `N`, together with the adjointness needed
below, is produced by `Stacks.Modules.exists_modules_globalSections`, which transports Mathlib's
`AlgebraicGeometry.tilde.adjunction` from `Spec A` to `T`.

Fix such an `N` and an isomorphism `e : A ⊗[B] Ω[B⁄R] ≃ Γ(N, ⊤)` of `A`-modules, and let
`δ : b ↦ e (1 ⊗ d b)` be the resulting `R`-derivation of `B` with values in `Γ(N, ⊤)`.
Corepresentability produces a morphism `φ : a^*Ω_{X/S} ⟶ N` with
`φ.app ⊤ (pullbackD b) = δ b`.

* *Retraction.* `e⁻¹ ∘ φ.app ⊤ ∘ cotangentComparison` is an `A`-linear endomorphism of
  `A ⊗[B] Ω[B⁄R]` carrying `1 ⊗ d b` to `1 ⊗ d b`, hence is the identity by
  `Stacks.Smooth.tensorKaehlerDifferential_linearMap_ext`. So `cotangentComparison` is injective.
* *Section.* Let `χ : N ⟶ a^*Ω_{X/S}` be the morphism adjoint to
  `cotangentComparison ∘ e⁻¹`, so that `χ.app ⊤ (e m) = cotangentComparison m`. Then
  `φ ≫ χ` and `𝟙` agree on the image of `Stacks.Smooth.pullbackD`, so they are equal by the
  uniqueness half `Stacks.Smooth.pullbackCotangentSheaf_hom_ext`. Hence
  `χ.app ⊤ ∘ φ.app ⊤ = id`, and `cotangentComparison` is surjective.

Note that the two halves use the presentation of `A ⊗[B] Ω[B⁄R]` by a sheaf of modules in
genuinely different ways: the retraction only needs the isomorphism `e`, while the section needs
the adjointness, i.e. that an `A`-linear map out of `Γ(N, ⊤)` is induced by a morphism out of
`N`. Using `tilde` here is not circular: it manufactures a sheaf of modules out of a given
module, and never computes `a^*Ω_{X/S}` from its sections — which is what would require
`Ω_{X/S}` to be quasi-coherent, i.e. the conclusion.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 01UR](https://stacks.math.columbia.edu/tag/01UR)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

/-! ### Extensionality for maps out of Kähler differentials -/

/-- **A linear map out of `Ω[B⁄R]` is determined by the differentials.** Two `B`-linear maps out
of the module of Kähler differentials agreeing on every `d b` are equal, because the `d b` span
`Ω[B⁄R]` (`KaehlerDifferential.span_range_derivation`). -/
theorem kaehlerDifferential_linearMap_ext {R B P : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup P] [Module B P] (g₁ g₂ : Ω[B⁄R] →ₗ[B] P)
    (h : ∀ b : B, g₁ (KaehlerDifferential.D R B b) = g₂ (KaehlerDifferential.D R B b)) :
    g₁ = g₂ :=
  LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R B) h

/-- **A linear map out of `A ⊗[B] Ω[B⁄R]` is determined by the elements `1 ⊗ d b`.** Two
`A`-linear maps out of the base change of the module of Kähler differentials agreeing on every
`1 ⊗ d b` are equal: by `LinearMap.liftBaseChangeEquiv` they correspond to `B`-linear maps out of
`Ω[B⁄R]`, and those are compared by `Stacks.Smooth.kaehlerDifferential_linearMap_ext`. -/
theorem tensorKaehlerDifferential_linearMap_ext {R B A P : Type*} [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [AddCommGroup P] [Module B P] [Module A P]
    [IsScalarTower B A P] (g₁ g₂ : A ⊗[B] Ω[B⁄R] →ₗ[A] P)
    (h : ∀ b : B, g₁ (1 ⊗ₜ KaehlerDifferential.D R B b)
      = g₂ (1 ⊗ₜ KaehlerDifferential.D R B b)) :
    g₁ = g₂ :=
  (LinearMap.liftBaseChangeEquiv A).symm.injective (kaehlerDifferential_linearMap_ext _ _ h)

/-! ### Bijectivity of the comparison map -/

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens}

/-- **The affine computation of `Ω_{X/S}`.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be
an affine open of `S` and `W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X` be a
morphism from an affine scheme `T` mapping into `W`. Then the comparison map

`Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)] ⟶ Γ(a^*Ω_{X/S}, ⊤)`

of `Stacks.Smooth.cotangentComparison` is bijective.

This is the affine computation of [Stacks Project, Tag 01UM] in the form that
[Stacks Project, Tag 02H6] consumes. See the implementation notes of this file for the
argument. -/
theorem bijective_cotangentComparison [IsAffine T] (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    Function.Bijective (cotangentComparison f a W hWV hUW) := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  obtain ⟨N, e, hlift⟩ := Stacks.Modules.exists_modules_globalSections T
    (Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)])
  let := moduleAppLE a N hUW
  let := moduleAppLEBase f a N hWV hUW
  let := isScalarTowerAppLE a N hUW
  let := isScalarTowerAppLEBase f a N hWV hUW
  -- the `Γ(S, V)`-derivation `b ↦ e (1 ⊗ d b)` of `Γ(X, W)` with values in `Γ(N, ⊤)`
  let L : Ω[Γ(X, W)⁄Γ(S, V)] →ₗ[Γ(X, W)] Γ(N, (⊤ : T.Opens)) :=
    (e.toLinearMap.restrictScalars Γ(X, W)) ∘ₗ
      (TensorProduct.mk Γ(X, W) Γ(T, ⊤) Ω[Γ(X, W)⁄Γ(S, V)] 1)
  let δ : Derivation Γ(S, V) Γ(X, W) Γ(N, (⊤ : T.Opens)) :=
    L.compDer (KaehlerDifferential.D Γ(S, V) Γ(X, W))
  obtain ⟨φ, hφ, -⟩ := existsUnique_hom_pullbackCotangentSheaf f a N hWV hW hUW δ hV
  replace hφ : ∀ b, (φ.app ⊤).hom (pullbackD f a W hUW b)
      = e (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b) := hφ
  let ψ : Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) →ₗ[Γ(T, ⊤)] Γ(N, (⊤ : T.Opens)) :=
    { toFun := fun x ↦ (φ.app ⊤).hom x
      map_add' := fun x y ↦ map_add (φ.app ⊤).hom x y
      map_smul' := fun r x ↦ Scheme.Modules.Hom.app_smul φ r x }
  -- `e⁻¹ ∘ φ.app ⊤` is a retraction of the comparison map
  have hretract : e.symm.toLinearMap ∘ₗ (ψ ∘ₗ cotangentComparison f a W hWV hUW)
      = LinearMap.id := by
    refine tensorKaehlerDifferential_linearMap_ext _ _ fun b ↦ ?_
    change e.symm (φ.app ⊤ (cotangentComparison f a W hWV hUW
        (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b))) = _
    rw [cotangentComparison_one_tmul_D, hφ b, e.symm_apply_apply]
    rfl
  -- the morphism adjoint to the comparison map is a section of `φ`
  obtain ⟨χ, hχ⟩ := hlift (pullbackCotangentSheaf f a) (cotangentComparison f a W hWV hUW)
  have hsection : φ ≫ χ = 𝟙 _ := by
    refine pullbackCotangentSheaf_hom_ext f a _ hW hUW fun b ↦ ?_
    change (χ.app ⊤).hom ((φ.app ⊤).hom (pullbackD f a W hUW b)) = _
    rw [hφ b, hχ (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b),
      cotangentComparison_one_tmul_D]
    rfl
  refine ⟨Function.LeftInverse.injective (g := fun z ↦ e.symm (ψ z))
    (fun m ↦ LinearMap.congr_fun hretract m), fun y ↦ ⟨e.symm (ψ y), ?_⟩⟩
  rw [← hχ, e.apply_symm_apply]
  change ((φ ≫ χ).app ⊤).hom y = y
  rw [hsection]
  rfl

/-- **The affine computation of `Ω_{X/S}`, as a linear equivalence.** For `V` and `W` affine
opens with `W ≤ f ⁻¹ᵁ V` and `a : T ⟶ X` a morphism from an affine scheme mapping into `W`, the
comparison map identifies `Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]` with the global sections of
`a^*Ω_{X/S}`. -/
noncomputable def cotangentComparisonEquiv [IsAffine T] (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    (Γ(T, ⊤) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]) ≃ₗ[Γ(T, ⊤)]
      Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) :=
  letI := algebraAppLE f hWV
  letI := algebraAppLE a hUW
  LinearEquiv.ofBijective (cotangentComparison f a W hWV hUW)
    (bijective_cotangentComparison f a hV hW hWV hUW)

/-- The underlying map of `Stacks.Smooth.cotangentComparisonEquiv` is
`Stacks.Smooth.cotangentComparison`. -/
theorem cotangentComparisonEquiv_apply [IsAffine T] (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    ∀ x, cotangentComparisonEquiv f a hV hW hWV hUW x = cotangentComparison f a W hWV hUW x :=
  fun _ ↦ rfl

end Stacks.Smooth

end
