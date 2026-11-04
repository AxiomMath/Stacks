module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme

/-!
# The ideal sheaf of the base change of a rational point

Let `φ₀ : R ⟶ k` be a surjective ring map onto a field, `f : P ⟶ Spec R` a morphism of schemes
and `W = P ×_{Spec R} Spec k`, the fibre of `f` over the point `ker φ₀`. Then `W ⟶ P` is a
closed immersion with ideal sheaf `(ker φ₀) · 𝒪_P`.

In the cube proof (step 1(a)) this identifies `W × {e}` with the closed
subscheme of `W × Spec R` cut out by the maximal ideal of the unit `e`, so that the level-zero
quotient `ℒ / 𝔪ℒ` is the pushforward of the restriction of `ℒ` to `W`.

## Main results

* `Stacks.CubeOpenAtUnit.ker_eq_baseIdealSheaf_of_isPullback`: the statement above, for any
  pullback square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.CubeOpenAtUnit

/-- **The base change of a rational point of `Spec R` is cut out by its ideal.** For a surjection
`φ₀ : R ⟶ k` onto a field and a pullback square `W = P ×_{Spec R} Spec k`, the projection
`s : W ⟶ P` is a closed immersion whose ideal sheaf is `(ker φ₀) · 𝒪_P`. -/
theorem ker_eq_baseIdealSheaf_of_isPullback {R k : Type u} [CommRing R] [Field k]
    (φ₀ : R →+* k) (hφ₀ : Function.Surjective φ₀) {P W : Scheme.{u}}
    (f : P ⟶ Spec (.of R)) (s : W ⟶ P) (h : W ⟶ Spec (.of k))
    (hsq : IsPullback s h f (Spec.map (CommRingCat.ofHom φ₀))) :
    IsClosedImmersion s ∧
      s.ker = Stacks.Cohomology.FormalFunctions.baseIdealSheaf R (RingHom.ker φ₀) f ^ 1 := by
  let ψ : R ⧸ RingHom.ker φ₀ ≃+* k := RingHom.quotientKerEquivOfSurjective hφ₀
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ₀)))
  let ψs : Spec (.of k) ≅ Spec (.of (R ⧸ RingHom.ker φ₀)) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso ψ).op
  have hcomp : Spec.map (CommRingCat.ofHom φ₀) = ψs.hom ≫ q := by
    show _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ q
    rw [← Spec.map_comp]
    congr 1
  have H : IsPullback s (h ≫ ψs.hom) f q :=
    hsq.of_iso (Iso.refl _) (Iso.refl _) ψs (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [hcomp])
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_quotient_mk (R := .of R) _
  rw [← H.isoPullback_hom_fst]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.ker_comp_of_isIso, pow_one]
  exact (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst _ _ _).symm

end Stacks.CubeOpenAtUnit

end
