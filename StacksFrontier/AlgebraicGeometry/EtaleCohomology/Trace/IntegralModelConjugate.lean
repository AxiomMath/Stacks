module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# Integral models of conjugate representations

If `ρ ∘ φ` is conjugate to `ρ'` (over `E`, then over `ℚ_ℓ` after restriction of scalars), the
integral models of `ρ'` and `ρ` (`Stacks.EtaleCohomology.integralModel`) are conjugate along `φ`
over `ℚ_ℓ` (`Stacks.EtaleCohomology.exists_conj_integralModel_comp`); a twist by a character
compatible with `φ` preserves the conjugacy (`Stacks.EtaleCohomology.characterTwist_comp_eq_conj`);
and the integral model takes equal values where `ρ` does
(`Stacks.EtaleCohomology.integralModel_eq_of_eq`). These are the inputs of the lattice comparison
of Laumon's Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) on the side of
the representations.

## Main results

* `Stacks.EtaleCohomology.characterTwist_comp_eq_conj`.
* `Stacks.EtaleCohomology.restrictScalarsRep_comp_eq_conj`.
* `Stacks.EtaleCohomology.exists_conj_integralModel_comp`.
* `Stacks.EtaleCohomology.integralModel_eq_of_eq`.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

section Twist

variable {G G' : Type*} [Group G] [Group G'] {n : Type*} [Fintype n] [DecidableEq n] {O : Type}
  [CommRing O]

/-- **The twist of a conjugate is the conjugate of the twist**, for compatible characters. -/
theorem characterTwist_comp_eq_conj (ρ : G →* GL n O) (χ : G →* Oˣ) (ρ' : G' →* GL n O)
    (χ' : G' →* Oˣ) (φ : G' →* G) (C : GL n O) (hρ : ∀ g, ρ (φ g) = C * ρ' g * C⁻¹)
    (hχ : ∀ g, χ (φ g) = χ' g) (g : G') :
    characterTwist ρ χ (φ g) = C * characterTwist ρ' χ' g * C⁻¹ := by
  have hc : ∀ (c : Oˣ) (M : GL n O),
      Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom c * M =
        M * Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom c := fun c M =>
    Units.ext (Matrix.scalar_commute (c : O) (fun r => Commute.all _ _) M.val)
  change ρ (φ g) * Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ (φ g)) =
    C * (ρ' g * Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ' g)) * C⁻¹
  rw [hρ, hχ, mul_assoc, mul_assoc, mul_assoc, mul_assoc, hc (χ' g) C⁻¹]

end Twist

section RestrictScalars

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {G G' : Type*} [Group G] [Group G'] {m : ℕ}

/-- **Restriction of scalars preserves conjugacy.** -/
theorem restrictScalarsRep_comp_eq_conj (ρ : G →* GL (Fin m) E) (ρ' : G' →* GL (Fin m) E)
    (φ : G' →* G) (C : GL (Fin m) E) (hρ : ∀ g, ρ (φ g) = C * ρ' g * C⁻¹) (g : G') :
    restrictScalarsRep b ρ (φ g) = Units.map (restrictScalarsMonoidHom b m) C *
      restrictScalarsRep b ρ' g * (Units.map (restrictScalarsMonoidHom b m) C)⁻¹ := by
  change Units.map (restrictScalarsMonoidHom b m) (ρ (φ g)) = _
  rw [hρ, map_mul, map_mul, map_inv]
  rfl

end RestrictScalars

section Integral

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {G G' : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  [CompactSpace G']

/-- **Integral models of representations conjugate along `φ` are conjugate along `φ` over
`ℚ_ℓ`.** -/
theorem exists_conj_integralModel_comp (ρ : G →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (ρ' : G' →* GL (Fin r) ℚ_[ℓ]) (hρ' : Continuous ρ') (φ : G' →* G) (C : GL (Fin r) ℚ_[ℓ])
    (h : ∀ g, ρ (φ g) = C * ρ' g * C⁻¹) :
    ∃ Q : GL (Fin r) ℚ_[ℓ], ∀ g, Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
      (integralModel ρ' hρ' g) = Q⁻¹ * Matrix.GeneralLinearGroup.map
        (PadicInt.Coe.ringHom (p := ℓ)) (integralModel ρ hρ (φ g)) * Q := by
  refine ⟨(exists_conj_integral ρ hρ).choose⁻¹ * C * (exists_conj_integral ρ' hρ').choose,
    fun g => ?_⟩
  rw [map_integralModel, map_integralModel, h]
  group

/-- **The integral model takes equal values where `ρ` does.** -/
theorem integralModel_eq_of_eq (ρ : G →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) {g₁ g₂ : G}
    (h : ρ g₁ = ρ g₂) : integralModel ρ hρ g₁ = integralModel ρ hρ g₂ := by
  have h₁ := map_integralModel ρ hρ g₁
  have h₂ := map_integralModel ρ hρ g₂
  rw [h] at h₁
  exact Units.ext (mapMatrix_padicInt_injective (congrArg Units.val (h₁.trans h₂.symm)))

end Integral

end Stacks.EtaleCohomology

end
