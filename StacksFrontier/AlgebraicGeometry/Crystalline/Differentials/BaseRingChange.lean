module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel

/-!
# Divided power differentials over a surjection of base rings

Let `R₁ → R₂` be a surjective ring map and `B` an `R₂`-algebra, hence an `R₁`-algebra.  An
`R₁`-derivation of `B` kills the image of `R₂`, because that image is the image of `R₁`; so the
Kähler differentials `Ω_{B/R₁}` and `Ω_{B/R₂}` coincide, and with them the divided power
differentials `Ω_{B/R₁,δ}`, `Ω_{B/R₂,δ}` of [Stacks, Tag 07HZ], their exterior powers, their
de Rham differentials, and the `p`-adic completions of all of these.

## Main definitions

* `Crystalline.kaehlerBaseRingEquiv` — `Ω_{B/R₁} ≃ Ω_{B/R₂}`, `d b ↦ d b`.
* `Crystalline.dividedPowerDifferentialsBaseRingEquiv` — `Ω_{B/R₁,δ} ≃ Ω_{B/R₂,δ}`.
* `Crystalline.dividedPowerFormsBaseRingEquiv` — `Ωⁱ_{B/R₁,δ} ≃ Ωⁱ_{B/R₂,δ}`.
* `Crystalline.completedFormsBaseRingEquiv` — the same for the `p`-adic completions.

## Main results

* `Crystalline.dividedPowerFormsBaseRingEquiv_deRham` and
  `Crystalline.completedFormsBaseRingEquiv_deRham` — the identifications commute with the de Rham
  differentials, and `Crystalline.completedFormsBaseRingEquiv_differential` with the universal
  differential.
-/

@[expose] public section

open DividedPowers

universe u₁ u₂ v

namespace Crystalline

variable (R₁ : Type u₁) (R₂ : Type u₂) [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
  (B : Type v) [CommRing B] [Algebra R₂ B] [Algebra R₁ B] [IsScalarTower R₁ R₂ B]
  (hR : Function.Surjective (algebraMap R₁ R₂))

/-! ### Kähler differentials -/

/-- The universal `R₁`-derivation of `B`, read as an `R₂`-derivation: it kills the image of `R₂`,
which is the image of `R₁`. -/
noncomputable def kaehlerDerivationOfSurjective : Derivation R₂ B Ω[B⁄R₁] where
  toFun := KaehlerDifferential.D R₁ B
  map_add' := map_add _
  map_smul' r b := by
    obtain ⟨s, rfl⟩ := hR r
    rw [RingHom.id_apply, algebraMap_smul, Derivation.map_smul, algebraMap_smul]
  map_one_eq_zero' := (KaehlerDifferential.D R₁ B).map_one_eq_zero
  leibniz' a b := (KaehlerDifferential.D R₁ B).leibniz a b

/-- **The Kähler differentials over `R₁` and over `R₂` agree** when `R₁ → R₂` is surjective. -/
noncomputable def kaehlerBaseRingEquiv : Ω[B⁄R₁] ≃ₗ[B] Ω[B⁄R₂] :=
  LinearEquiv.ofLinearMap (KaehlerDifferential.map R₁ R₂ B B)
    (kaehlerDerivationOfSurjective R₁ R₂ B hR).liftKaehlerDifferential
    (by
      refine Derivation.liftKaehlerDifferential_unique _ _ ?_
      ext b
      change KaehlerDifferential.map R₁ R₂ B B
          ((kaehlerDerivationOfSurjective R₁ R₂ B hR).liftKaehlerDifferential
            (KaehlerDifferential.D R₂ B b)) = KaehlerDifferential.D R₂ B b
      rw [Derivation.liftKaehlerDifferential_comp_D]
      exact KaehlerDifferential.map_D R₁ R₂ B B b)
    (by
      refine Derivation.liftKaehlerDifferential_unique _ _ ?_
      ext b
      change (kaehlerDerivationOfSurjective R₁ R₂ B hR).liftKaehlerDifferential
          (KaehlerDifferential.map R₁ R₂ B B (KaehlerDifferential.D R₁ B b)) =
        KaehlerDifferential.D R₁ B b
      rw [KaehlerDifferential.map_D]
      exact Derivation.liftKaehlerDifferential_comp_D _ b)

/-- The identification `kaehlerBaseRingEquiv` sends `d b` over `R₁` to `d b` over `R₂`. -/
@[simp] theorem kaehlerBaseRingEquiv_D (b : B) :
    kaehlerBaseRingEquiv R₁ R₂ B hR (KaehlerDifferential.D R₁ B b) =
      KaehlerDifferential.D R₂ B b :=
  KaehlerDifferential.map_D R₁ R₂ B B b

/-! ### Divided power differentials -/

variable {J : Ideal B} (hJ : DividedPowers J)

/-- The identification of the Kähler differentials carries the divided power relations over
`R₁` onto those over `R₂`. -/
theorem map_dividedPowerDifferentialRelations :
    (dividedPowerDifferentialRelations (A := R₁) hJ).map
        (kaehlerBaseRingEquiv R₁ R₂ B hR).toLinearMap =
      dividedPowerDifferentialRelations (A := R₂) hJ := by
  rw [dividedPowerDifferentialRelations, dividedPowerDifferentialRelations, Submodule.map_span,
    ← Set.range_comp]
  congr 1
  ext z
  simp [dividedPowerDifferentialRelation]

/-- **The divided power differentials over `R₁` and over `R₂` agree.** -/
noncomputable def dividedPowerDifferentialsBaseRingEquiv :
    dividedPowerDifferentials (A := R₁) hJ ≃ₗ[B] dividedPowerDifferentials (A := R₂) hJ :=
  Submodule.Quotient.equiv _ _ (kaehlerBaseRingEquiv R₁ R₂ B hR)
    (map_dividedPowerDifferentialRelations R₁ R₂ B hR hJ)

/-- The identification `dividedPowerDifferentialsBaseRingEquiv` sends the divided power
differential `d b` over `R₁` to `d b` over `R₂`. -/
@[simp] theorem dividedPowerDifferentialsBaseRingEquiv_differential (b : B) :
    dividedPowerDifferentialsBaseRingEquiv R₁ R₂ B hR hJ
        (dividedPowerDifferential (A := R₁) hJ b) =
      dividedPowerDifferential (A := R₂) hJ b :=
  congrArg Submodule.Quotient.mk (kaehlerBaseRingEquiv_D R₁ R₂ B hR b)

/-- **The divided power differential forms over `R₁` and over `R₂` agree**, in every degree. -/
noncomputable def dividedPowerFormsBaseRingEquiv (i : ℕ) :
    dividedPowerDifferentialForms (A := R₁) hJ i ≃ₗ[B]
      dividedPowerDifferentialForms (A := R₂) hJ i :=
  LinearEquiv.ofLinearMap
    (exteriorPower.map i (dividedPowerDifferentialsBaseRingEquiv R₁ R₂ B hR hJ).toLinearMap)
    (exteriorPower.map i (dividedPowerDifferentialsBaseRingEquiv R₁ R₂ B hR hJ).symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])

/-- The identification `dividedPowerFormsBaseRingEquiv` sends `d f₁ ∧ ⋯ ∧ d fᵢ` over `R₁` to
`d f₁ ∧ ⋯ ∧ d fᵢ` over `R₂`. -/
theorem dividedPowerFormsBaseRingEquiv_ιMulti (i : ℕ) (f : Fin i → B) :
    dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i
        (exteriorPower.ιMulti B i fun j ↦ dividedPowerDifferential (A := R₁) hJ (f j)) =
      exteriorPower.ιMulti B i fun j ↦ dividedPowerDifferential (A := R₂) hJ (f j) := by
  change exteriorPower.map i _ _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  exact dividedPowerDifferentialsBaseRingEquiv_differential R₁ R₂ B hR hJ (f j)

/-- **The identification of the forms commutes with the de Rham differentials.** -/
theorem dividedPowerFormsBaseRingEquiv_deRham (i : ℕ)
    (x : dividedPowerDifferentialForms (A := R₁) hJ i) :
    dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ (i + 1) (dividedPowerDeRham (A := R₁) hJ i x) =
      dividedPowerDeRham (A := R₂) hJ i (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i x) := by
  let F : dividedPowerDifferentialForms (A := R₁) hJ i →+
      dividedPowerDifferentialForms (A := R₂) hJ (i + 1) :=
    (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ (i + 1)).toLinearMap.toAddMonoidHom.comp
      (dividedPowerDeRhamHom (A := R₁) hJ i)
  let G : dividedPowerDifferentialForms (A := R₁) hJ i →+
      dividedPowerDifferentialForms (A := R₂) hJ (i + 1) :=
    (dividedPowerDeRhamHom (A := R₂) hJ i).comp
      (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i).toLinearMap.toAddMonoidHom
  have hFG : F.toIntLinearMap = G.toIntLinearMap := by
    refine LinearMap.ext_on
      (span_range_smul_ιMulti_eq_top (R := ℤ) (dividedPowerDifferential (A := R₁) hJ)
        (dividedPowerDifferentials_span hJ) i) ?_
    rintro _ ⟨f, rfl⟩
    change dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ (i + 1)
        (dividedPowerDeRham (A := R₁) hJ i
          (f 0 • exteriorPower.ιMulti B i fun j ↦ dividedPowerDifferential (A := R₁) hJ
            (f j.succ))) =
      dividedPowerDeRham (A := R₂) hJ i
        (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i
          (f 0 • exteriorPower.ιMulti B i fun j ↦ dividedPowerDifferential (A := R₁) hJ
            (f j.succ)))
    rw [dividedPowerDeRham_generator, LinearEquiv.map_smul,
      dividedPowerFormsBaseRingEquiv_ιMulti, dividedPowerFormsBaseRingEquiv_ιMulti]
    exact (dividedPowerDeRham_generator hJ i f).symm
  exact LinearMap.congr_fun hFG x

/-! ### The `p`-adic completions -/

variable (p : ℕ)

/-- **The completed divided power forms over `R₁` and over `R₂` agree**, linearly over the
completion of `B`. -/
noncomputable def completedFormsBaseRingEquiv (i : ℕ) :
    completedDividedPowerForms p R₁ hJ i ≃ₗ[completedDividedPowerRing p (B := B)]
      completedDividedPowerForms p R₂ hJ i :=
  AdicCompletion.congr _ (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i)

/-- On the image of an uncompleted form, `completedFormsBaseRingEquiv` is
`dividedPowerFormsBaseRingEquiv`. -/
theorem completedFormsBaseRingEquiv_of (i : ℕ) (x : dividedPowerDifferentialForms (A := R₁) hJ i) :
    completedFormsBaseRingEquiv R₁ R₂ B hR hJ p i (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i x) :=
  rfl

/-- **The identification of the completed forms commutes with the completed de Rham
differentials.** -/
theorem completedFormsBaseRingEquiv_deRham (i : ℕ) (x : completedDividedPowerForms p R₁ hJ i) :
    completedFormsBaseRingEquiv R₁ R₂ B hR hJ p (i + 1)
        (completedDividedPowerDeRham p R₁ hJ i x) =
      completedDividedPowerDeRham p R₂ hJ i (completedFormsBaseRingEquiv R₁ R₂ B hR hJ p i x) := by
  let F : completedDividedPowerForms p R₁ hJ i →+ completedDividedPowerForms p R₂ hJ (i + 1) :=
    (completedFormsBaseRingEquiv R₁ R₂ B hR hJ p (i + 1)).toLinearMap.toAddMonoidHom.comp
      (completedDividedPowerDeRham p R₁ hJ i)
  let G : completedDividedPowerForms p R₁ hJ i →+ completedDividedPowerForms p R₂ hJ (i + 1) :=
    (completedDividedPowerDeRham p R₂ hJ i).comp
      (completedFormsBaseRingEquiv R₁ R₂ B hR hJ p i).toLinearMap.toAddMonoidHom
  have hFG : F = G := by
    refine adicCompletion_addMonoidHom_ext_of_of p fun x ↦ ?_
    change completedFormsBaseRingEquiv R₁ R₂ B hR hJ p (i + 1)
        (completedDividedPowerDeRham p R₁ hJ i (AdicCompletion.of _ _ x)) =
      completedDividedPowerDeRham p R₂ hJ i (AdicCompletion.of _ _
        (dividedPowerFormsBaseRingEquiv R₁ R₂ B hR hJ i x))
    rw [completedDividedPowerDeRham_of, completedDividedPowerDeRham_of,
      completedFormsBaseRingEquiv_of, dividedPowerFormsBaseRingEquiv_deRham]
  exact DFunLike.congr_fun hFG x

/-- **The identification of the completed one-forms carries the universal differential over `R₁`
to the one over `R₂`.** -/
theorem completedFormsBaseRingEquiv_differential (b : completedDividedPowerRing p (B := B)) :
    completedFormsBaseRingEquiv R₁ R₂ B hR hJ p 1 (completedFormsDifferential p R₁ hJ b) =
      completedFormsDifferential p R₂ hJ b := by
  let F : completedDividedPowerRing p (B := B) →+ completedDividedPowerForms p R₂ hJ 1 :=
    (completedFormsBaseRingEquiv R₁ R₂ B hR hJ p 1).toLinearMap.toAddMonoidHom.comp
      (PAdicCompletion.mapAddHom p B B (dividedPowerOneForm R₁ hJ))
  let G : completedDividedPowerRing p (B := B) →+ completedDividedPowerForms p R₂ hJ 1 :=
    PAdicCompletion.mapAddHom p B B (dividedPowerOneForm R₂ hJ)
  have hFG : F = G := by
    refine adicCompletion_addMonoidHom_ext_of_of p fun x ↦ ?_
    change completedFormsBaseRingEquiv R₁ R₂ B hR hJ p 1
        (completedFormsDifferential p R₁ hJ (AdicCompletion.of _ _ x)) =
      completedFormsDifferential p R₂ hJ (AdicCompletion.of _ _ x)
    rw [completedFormsDifferential_of, completedFormsDifferential_of,
      completedFormsBaseRingEquiv_of, dividedPowerOneForm_apply, dividedPowerOneForm_apply]
    congr 1
    change exteriorPower.map 1 _ _ = _
    rw [← dividedPowerDifferentialsBaseRingEquiv_differential R₁ R₂ B hR hJ x]
    simp only [exteriorPower.oneEquiv_symm_apply]
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  exact DFunLike.congr_fun hFG b

end Crystalline

end
