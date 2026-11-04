module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationCoefficients

/-!
# Twisting by a continuous `ℤ_ℓ`-valued character keeps the restriction of scalars continuous

For `σ : G → GL_m(E)` with `Res_b σ` continuous and a continuous character `χ : G → ℤ_ℓˣ`, the
twist `g ↦ χ(g) σ(g)` (`Stacks.EtaleCohomology.characterTwist`, `χ` read in `E` through
`ℤ_ℓ → ℚ_ℓ → E`) has continuous restriction of scalars.

## Main definitions

* `Stacks.EtaleCohomology.padicUnitsCharacter`: a `ℤ_ℓˣ`-valued character read in `Eˣ`.

## Main results

* `Stacks.EtaleCohomology.continuous_restrictScalarsRep_characterTwist_padicUnitsCharacter`: the
  twist of `σ` by a continuous `ℤ_ℓˣ`-valued character has continuous restriction of scalars
  when `σ` does.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {G : Type*} [Group G]

/-- **A `ℤ_ℓˣ`-valued character read in `Eˣ`** through `ℤ_ℓ → ℚ_ℓ → E`. -/
public def padicUnitsCharacter (χ : G →* ℤ_[ℓ]ˣ) : G →* Eˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] E).comp (PadicInt.Coe.ringHom (p := ℓ))).toMonoidHom).comp χ

/-- The value of `padicUnitsCharacter χ` at `g` in `E` is the image of `χ g` under
`ℤ_ℓ → ℚ_ℓ → E`. -/
@[simp]
public theorem padicUnitsCharacter_apply (χ : G →* ℤ_[ℓ]ˣ) (g : G) :
    ((padicUnitsCharacter χ g : Eˣ) : E) = algebraMap ℚ_[ℓ] E ((χ g : ℤ_[ℓ]) : ℚ_[ℓ]) :=
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The twist of `σ` by a continuous `ℤ_ℓˣ`-valued character has continuous restriction of
scalars** when `σ` does. -/
public theorem continuous_restrictScalarsRep_characterTwist_padicUnitsCharacter {m : ℕ}
    (σ : G →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ)) (χ : G →* ℤ_[ℓ]ˣ)
    (hχ : Continuous χ) :
    Continuous (restrictScalarsRep b (characterTwist σ (padicUnitsCharacter χ))) := by
  refine continuous_restrictScalarsRep b _ ?_
  have h : (fun g => restrictScalarsMatrix b (characterTwist σ (padicUnitsCharacter χ) g).val) =
      fun g => restrictScalarsMatrix b (σ g).val * restrictScalarsMatrix b
        ((Matrix.scalar (Fin m) ((χ g : ℤ_[ℓ]) : ℚ_[ℓ])).map (algebraMap ℚ_[ℓ] E)) := by
    funext g
    rw [← restrictScalarsMatrix_mul]
    congr 1
    change (σ g).val * Matrix.scalar (Fin m) ((padicUnitsCharacter χ g : Eˣ) : E) = _
    rw [padicUnitsCharacter_apply, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _)]
  rw [h]
  have h1 : Continuous fun g ↦ (χ g : ℤ_[ℓ]) := Units.continuous_val.comp hχ
  have hval : Continuous fun g ↦ ((χ g : ℤ_[ℓ]) : ℚ_[ℓ]) := continuous_subtype_val.comp h1
  have hsc : Continuous fun g => Matrix.scalar (Fin m) ((χ g : ℤ_[ℓ]) : ℚ_[ℓ]) := by
    simp only [Matrix.scalar_apply]
    exact continuous_pi fun i ↦ continuous_pi fun j ↦ by
      by_cases hij : i = j
      · subst hij
        simpa [Matrix.diagonal_apply_eq] using hval
      · simpa [Matrix.diagonal_apply_ne _ hij] using continuous_const
  exact (show Continuous fun g ↦ restrictScalarsMatrix b (σ g).val from
    Units.continuous_val.comp hσ).matrix_mul (continuous_restrictScalarsMatrix_map b hsc)

end Stacks.EtaleCohomology

end
