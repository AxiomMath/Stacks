module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.InjectiveModMaximalIdealClaimOne
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningHenselianCore
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningTransport

/-!
# The two ends of Claim 1 of the proof of Stacks 05U9, in Situation 0AT0

Claim 1 of the proof of Stacks 05U9 says that in Situation 0AT0, with the local algebra presented
as the localization at a prime of a polynomial algebra over `A` and the module of finite
presentation over it, some finitely generated nilpotent ideal `I₀ ⊆ A` has `N ⧸ I₀N` flat over
`A ⧸ I₀`. Its proof is an induction on the length of a generic flatness stratification. This file
holds the two ends of that argument, read off Situation 0AT0's own data.

## Main results

* `AlgebraicGeometry.essentiallyOfFinitePresentation_of_presentation`: a presented situation has
  `A → B` essentially of finite presentation, which is what the finite generation of the
  flattening ideal of Stacks 05PG asks for.
* `AlgebraicGeometry.exists_flatStratification_of_presentation`: **the input end.** Situation
  0AT0 with a presentation carries a generic flatness stratification of `N` over `A`.
* `AlgebraicGeometry.exists_fg_isNilpotent_flat_quotient_of_cover`: **the output end.** Once
  every prime of `A` is known to contain a flattening ideal, Claim 1's conclusion follows.

## Implementation notes

What is *not* here is the middle: Claim 1 at each index of the stratification, which
`Stacks.exists_flat_quotient_le_of_isPrime` needs in order to produce the `hcover` that
`AlgebraicGeometry.exists_fg_isNilpotent_flat_quotient_of_cover` consumes. That induction, and
with it Stacks 05U9 itself, is in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningClaimOneIndex`.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- The structure map of a situation presented as a localization of a polynomial algebra is
essentially of finite presentation. -/
theorem essentiallyOfFinitePresentation_of_presentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B) :
    (algebraMap S.A S.B).EssentiallyOfFinitePresentation := by
  let := P.polynomialAlgebra
  let := P.scalarTower
  let := P.prime_isPrime
  let := P.isLocalization
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization
    (C := MvPolynomial (Fin P.variableCount) S.A) P.prime.primeCompl

/-- **Situation 0AT0 with a presentation carries a generic flatness stratification of `N` over
`A`.** The polynomial algebra `A[x₁, …, x_n]` of the presentation is of finite presentation over
`A`, and `N` is a localization of a finitely presented module over it
(`Module.exists_finite_isLocalizedModule_comp`, which clears denominators), so
`Stacks.exists_flatStratification_of_isLocalizedModule` applies. The unlocalized
`Stacks.exists_flatStratification` does not: `B` is a localization at a prime of the polynomial
algebra and is not of finite presentation over `A`. -/
theorem exists_flatStratification_of_presentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N) :
    ∃ t : ℕ, Nonempty (Stacks.FlatStratification S.A S.N t) := by
  let := P.polynomialAlgebra
  let := P.scalarTower
  let := P.prime_isPrime
  let := P.isLocalization
  have := hfp
  let : Module (MvPolynomial (Fin P.variableCount) S.A) S.N :=
    Module.compHom _ (algebraMap (MvPolynomial (Fin P.variableCount) S.A) S.B)
  have : IsScalarTower (MvPolynomial (Fin P.variableCount) S.A) S.B S.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower S.A (MvPolynomial (Fin P.variableCount) S.A) S.N :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      show algebraMap (MvPolynomial (Fin P.variableCount) S.A) S.B _ • x = _
      rw [← IsScalarTower.algebraMap_apply S.A (MvPolynomial (Fin P.variableCount) S.A) S.B,
        algebraMap_smul]
  have : IsLocalizedModule P.prime.primeCompl
      (LinearMap.id : S.N →ₗ[MvPolynomial (Fin P.variableCount) S.A] S.N) :=
    isLocalizedModule_id P.prime.primeCompl S.N S.B
  obtain ⟨N₀, _, _, φ, _, hloc, hfp₀⟩ :=
    Module.exists_finite_isLocalizedModule_comp P.prime.primeCompl S.B
      (LinearMap.id : S.N →ₗ[MvPolynomial (Fin P.variableCount) S.A] S.N)
  have := hloc
  have := hfp₀ inferInstance
  let : Module S.A N₀ :=
    Module.compHom _ (algebraMap S.A (MvPolynomial (Fin P.variableCount) S.A))
  have : IsScalarTower S.A (MvPolynomial (Fin P.variableCount) S.A) N₀ :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Stacks.exists_flatStratification_of_isLocalizedModule S.A
    (MvPolynomial (Fin P.variableCount) S.A) N₀ S.N P.prime.primeCompl
    (LinearMap.id ∘ₗ φ)

/-- **The paragraph after Claim 1 of the proof of Stacks 05U9, in Situation 0AT0.** Given that
every prime of `A` contains a flattening ideal of `N`, some finitely generated *nilpotent* ideal
`I₀ ⊆ A` has `N ⧸ I₀N` flat over `A ⧸ I₀`.

The smallest flattening ideal exists only over a henselian base, so the argument runs over a
henselization `A^h` of `A`, for `N' = B' ⊗_B N` over the localization `B'` of `A^h ⊗_A B`:
`Stacks.ResidueFibre.exists_least_flattening_tensorPrime` produces it there, and
`Stacks.ResidueFibre.exists_fg_isNilpotent_flat_quotient_of_least_tensorPrime` descends the
resulting ideal to `A` through Stacks 0ASE. -/
theorem exists_fg_isNilpotent_flat_quotient_of_cover
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (P : PolynomialLocalizationPresentation S.A S.B)
    (hfp : Module.FinitePresentation S.B S.N)
    (hcover : ∀ p : Ideal S.A, p.IsPrime →
      ∃ K : Ideal S.A, K ≤ p ∧ Module.Flat (S.A ⧸ K) (S.N ⧸ (K • (⊤ : Submodule S.A S.N)))) :
    ∃ I₀ : Ideal S.A, I₀.FG ∧ IsNilpotent I₀ ∧
      Module.Flat (S.A ⧸ I₀) (S.N ⧸ (I₀ • (⊤ : Submodule S.A S.N))) := by
  have := hfp
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField S.A
  obtain ⟨I, hIfg, hI⟩ := Stacks.ResidueFibre.exists_least_flattening_tensorPrime
    (A := S.A) (B := S.B) (N := S.N) Ah (essentiallyOfFinitePresentation_of_presentation S P)
  exact Stacks.ResidueFibre.exists_fg_isNilpotent_flat_quotient_of_least_tensorPrime
    Ah I hIfg hI hcover

end AlgebraicGeometry

end
