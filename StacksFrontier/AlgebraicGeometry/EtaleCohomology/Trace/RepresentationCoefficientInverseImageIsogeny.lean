module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCoefficientLatticeChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRestrictionIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.TwistInverseImage

/-!
# The inverse image of `ℱ_ρ` with coefficients is isogenous to `ℱ_{ρ ∘ f_*}`

For `f : Y ⟶ X` of connected Noetherian schemes, a geometric point `ȳ` of `Y`, a continuous
`ρ : π₁(X, f(ȳ)) → GL_r(ℚ_ℓ)` and `α : E → M_r(ℚ_ℓ)` commuting with `ρ`, the inverse image of the
commutant sheaf `ℱ_ρ` (with the action of the integral part `O_ρ` of `E`) is isogenous to the
commutant sheaf of `ρ ∘ f_*` (with the action of `O_{ρ∘f_*}`), compatibly with the two actions
wherever they agree in `E`. For `ρ = Res_b σ` this is the inverse image of `ℱ_{Res_b σ}` used to
identify the fibres of Laumon's families in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
All names are in the namespace `Stacks.EtaleCohomology`.

## Main results

* `exists_inverseImage_representationSheafCommutantCoefficientSheaf_isogeny`: the isogeny for the
  commutant sheaf of `ρ`.
* `exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny`: the case `ρ = Res_b σ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [IsNoetherian Y.1] (y : GeometricPoint Y.1)

/-- Conjugating `P₁⁻¹ A P₁` by `P₁⁻¹ P₂` gives `P₂⁻¹ A P₂`. -/
public theorem conj_inv_mul_conj {r : ℕ} (P₁ P₂ : GL (Fin r) ℚ_[ℓ])
    (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]) :
    (P₁⁻¹ * P₂)⁻¹.val * (P₁⁻¹.val * A * P₁.val) * (P₁⁻¹ * P₂).val =
      P₂⁻¹.val * A * P₂.val := by
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]

section Commutant

variable {r : ℕ} (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℚ_[ℓ])
  (hρ : Continuous ρ) {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])
  (hα : ∀ e g, α e * (ρ g).val = (ρ g).val * α e)
  (hα' : ∀ e g, α e * ((ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) g).val =
    ((ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) g).val * α e)

/-- **`f⁻¹ℱ_ρ` is isogenous to `ℱ_{ρ ∘ f_*}`, compatibly with the actions of the integral parts
of `E`**, for the commutant sheaves of `ρ` and of `ρ ∘ f_*`. -/
public theorem exists_inverseImage_representationSheafCommutantCoefficientSheaf_isogeny :
    ∃ (φ : (LAdicSheaf.CoefficientSheaf.inverseImage f
          (representationSheafCommutantCoefficientSheaf B X (y.map f.hom) ρ hρ α hα)).toLAdicSheaf ⟶
        (representationSheafCommutantCoefficientSheaf B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) α hα').toLAdicSheaf)
      (ψ : (representationSheafCommutantCoefficientSheaf B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) α hα').toLAdicSheaf ⟶
        (LAdicSheaf.CoefficientSheaf.inverseImage f
          (representationSheafCommutantCoefficientSheaf B X (y.map f.hom) ρ hρ α hα)).toLAdicSheaf)
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring (representationSheafConj B X (y.map f.hom) ρ hρ) α)
        (o₂ : conjIntegralSubring (representationSheafConj B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous)) α),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ (representationSheafCommutantCoefficientSheaf B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) α hα').act o₂ =
          (LAdicSheaf.CoefficientSheaf.inverseImage f
            (representationSheafCommutantCoefficientSheaf B X (y.map f.hom) ρ hρ α hα)).act o₁ ≫
            φ := by
  have := compactSpace_etaleFundamentalGroup X.1 (y.map f.hom)
  have := compactSpace_etaleFundamentalGroup Y.1 y
  set φ₀ := (etaleFundamentalGroupMap f.hom y).toMonoidHom
  have hφ₀ : Continuous φ₀ := (etaleFundamentalGroupMap f.hom y).continuous
  set ρ' := ρ.comp φ₀
  have hρ' : Continuous ρ' := hρ.comp hφ₀
  set P := representationSheafConj B X (y.map f.hom) ρ hρ
  set P' := representationSheafConj B Y y ρ' hρ'
  have hP : ∀ {Z : B.Scheme} [ConnectedSpace Z.1] (z : GeometricPoint Z.1)
      (τ : EtaleFundamentalGroup Z.1 z →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ) g,
      have := compactSpace_etaleFundamentalGroup Z.1 z
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel τ hτ g).val =
        (representationSheafConj B Z z τ hτ)⁻¹.val * (τ g).val *
          (representationSheafConj B Z z τ hτ).val := fun z τ hτ g => by
    have := compactSpace_etaleFundamentalGroup _ z
    have h := congrArg Units.val (map_integralModel τ hτ g)
    simp only [Units.val_mul] at h
    exact h
  let τ₁ := (integralModel ρ hρ).comp φ₀
  have hτ₁ : Continuous τ₁ := (continuous_integralModel ρ hρ).comp hφ₀
  have hμX := conjIntegralLift_mul_integralModel B X (y.map f.hom) ρ hρ α hα
  have hμ₁ : ∀ s g, conjIntegralLift P α s * (τ₁ g).val = (τ₁ g).val * conjIntegralLift P α s :=
    fun s g => hμX s (φ₀ g)
  let I := representationCoefficientSheafInverseImageIso B f y (integralModel ρ hρ)
    (continuous_integralModel ρ hρ) (conjIntegralLift P α) hμX τ₁ hτ₁ hμ₁ rfl
    (representationSheafCommutantCoefficientSheaf B X (y.map f.hom) ρ hρ α hα) rfl
    (representationCoefficientSheaf B Y y τ₁ hτ₁ (conjIntegralLift P α) hμ₁) rfl
  have hI := representationCoefficientSheafInverseImageIso_hom_act B f y (integralModel ρ hρ)
    (continuous_integralModel ρ hρ) (conjIntegralLift P α) hμX τ₁ hτ₁ hμ₁ rfl
    (representationSheafCommutantCoefficientSheaf B X (y.map f.hom) ρ hρ α hα) rfl
    (representationCoefficientSheaf B Y y τ₁ hτ₁ (conjIntegralLift P α) hμ₁) rfl
  have hM : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ' hρ' g).val =
      (P⁻¹ * P')⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₁ g).val * (P⁻¹ * P').val := by
    intro g
    rw [hP y ρ' hρ' g]
    show _ = _ * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ (φ₀ g)).val * _
    rw [hP (y.map f.hom) ρ hρ (φ₀ g), conj_inv_mul_conj]
    rfl
  have hMμ : ∀ (o₁ : conjIntegralSubring P α) (o₂ : conjIntegralSubring P' α),
      algebraMap _ E o₁ = algebraMap _ E o₂ →
      (P⁻¹ * P')⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P α o₁) *
          (P⁻¹ * P').val =
        (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P' α o₂) := by
    intro o₁ o₂ ho
    have he : (o₁ : E) = (o₂ : E) := ho
    rw [mapMatrix_conjIntegralLift, mapMatrix_conjIntegralLift, conj_inv_mul_conj, he]
  obtain ⟨φ, ψ, N, h₁, h₂, hc⟩ := exists_representationCoefficientSheaf_isogeny_of_conj B Y y hτ₁
    (continuous_integralModel ρ' hρ') (conjIntegralLift P α) (conjIntegralLift P' α) hμ₁
    (conjIntegralLift_mul_integralModel B Y y ρ' hρ' α hα') E (P⁻¹ * P') hM hMμ
  obtain ⟨k₁, k₂⟩ := isogeny_iso_comp I φ ψ (ℓ ^ N) h₁ h₂
  refine ⟨I.hom ≫ φ, ψ ≫ I.inv, N, k₁, k₂, fun o₁ o₂ ho => ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (I.hom ≫ ·) (hc o₁ o₂ ho)).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (hI o₁))).trans
      (Category.assoc _ _ _)))

end Commutant

section RestrictScalars

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
  {m : ℕ} (σ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))
  (hσ' : Continuous (restrictScalarsRep b (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)))

/-- **`f⁻¹ℱ_{Res_b σ}` is isogenous to `ℱ_{Res_b (σ ∘ f_*)}`, compatibly with the actions of the
two integral parts of `E`.** -/
public theorem exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny :
    ∃ (φ : (LAdicSheaf.CoefficientSheaf.inverseImage f
          (restrictScalarsRepCoefficientSheaf B X (y.map f.hom) b σ hσ)).toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B Y y b
          (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) hσ').toLAdicSheaf)
      (ψ : (restrictScalarsRepCoefficientSheaf B Y y b
          (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) hσ').toLAdicSheaf ⟶
        (LAdicSheaf.CoefficientSheaf.inverseImage f
          (restrictScalarsRepCoefficientSheaf B X (y.map f.hom) b σ hσ)).toLAdicSheaf)
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring
          (representationSheafConj B X (y.map f.hom) (restrictScalarsRep b σ) hσ)
          (restrictScalarsScalarAlgHom b m))
        (o₂ : conjIntegralSubring
          (representationSheafConj B Y y
            (restrictScalarsRep b (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)) hσ')
          (restrictScalarsScalarAlgHom b m)),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ (restrictScalarsRepCoefficientSheaf B Y y b
          (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom) hσ').act o₂ =
          (LAdicSheaf.CoefficientSheaf.inverseImage f
            (restrictScalarsRepCoefficientSheaf B X (y.map f.hom) b σ hσ)).act o₁ ≫ φ :=
  exists_inverseImage_representationSheafCommutantCoefficientSheaf_isogeny B f y
    (restrictScalarsRep b σ) hσ (restrictScalarsScalarAlgHom b m)
    (restrictScalarsScalarAlgHom_commute b σ)
    (restrictScalarsScalarAlgHom_commute b (σ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom))

end RestrictScalars

end Stacks.EtaleCohomology

end
