module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCoefficientInverseImageIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationBasePoint

/-!
# The sheaf `ℱ_ρ` with coefficients at two base points

For an isomorphism `t : F_x̄ ≅ F_x̄'` of geometric fibre functors of a connected Noetherian scheme
`X`, with `φ_t : π₁(X, x̄') → π₁(X, x̄)`, the `O`-sheaf of a representation `τ` with an action `μ`
of `O` at `x̄` is the `O`-sheaf of `τ ∘ φ_t` with the same action at `x̄'`
(`Stacks.EtaleCohomology.representationLAdicSheafBasePointIso`, natural in intertwiners). For the
commutant sheaves of `ρ` and `ρ ∘ φ_t`, built from different integral models, this gives an
isogeny compatible with the actions of the two integral parts of `E`. This moves the base point
of `ℱ_σ` in the identification of the fibres of Laumon's families
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.representationCoefficientSheafBasePointIso_hom_act`.
* `Stacks.EtaleCohomology.exists_basePoint_representationSheafCommutantCoefficientSheaf_isogeny`.
* `Stacks.EtaleCohomology.exists_basePoint_restrictScalarsRepCoefficientSheaf_isogeny`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}
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
  [IsNoetherian X.1] (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')

/-- **The isomorphism `ℱ_τ ≅ ℱ_{τ ∘ φ_t}` commutes with the actions of `O`.** -/
public theorem representationCoefficientSheafBasePointIso_hom_act {r : ℕ}
    {τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hτ : Continuous τ) {O : Type}
    [CommRing O] [Algebra ℤ_[ℓ] O] (μ : O →+* Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hμ : ∀ o g, μ o * (τ g).val = (τ g).val * μ o)
    (hμ' : ∀ o g, μ o * ((τ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) g).val =
      ((τ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) g).val * μ o) (o : O) :
    (representationLAdicSheafBasePointIso B X t hτ).hom ≫
        ((representationCoefficientSheaf B X x'
          (τ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
          (hτ.comp (etaleFundamentalGroupBasePointHom t).continuous) μ hμ').act o).asHom =
      ((representationCoefficientSheaf B X x τ hτ μ hμ).act o).asHom ≫
        (representationLAdicSheafBasePointIso B X t hτ).hom :=
  representationLAdicSheafResIso_hom_naturality B X _ _ (etaleFundamentalGroupBasePointHom t)
    (canonicalFiniteLocallyConstantAbelianSheafEquivalenceBasePointInverseIso B X t) hτ hτ (μ o)
    (hμ o)

section Commutant

variable {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
  (hρ : Continuous ρ) {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])
  (hα : ∀ e g, α e * (ρ g).val = (ρ g).val * α e)
  (hα' : ∀ e g, α e * ((ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) g).val =
    ((ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) g).val * α e)

/-- **`ℱ_ρ` at `x̄` is isogenous to `ℱ_{ρ ∘ φ_t}` at `x̄'`, compatibly with the actions of the
integral parts of `E`**, for the commutant sheaves. -/
public theorem exists_basePoint_representationSheafCommutantCoefficientSheaf_isogeny :
    ∃ (φ : (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).toLAdicSheaf ⟶
        (representationSheafCommutantCoefficientSheaf B X x'
          (ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupBasePointHom t).continuous) α hα').toLAdicSheaf)
      (ψ : (representationSheafCommutantCoefficientSheaf B X x'
          (ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupBasePointHom t).continuous) α hα').toLAdicSheaf ⟶
        (representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).toLAdicSheaf)
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring (representationSheafConj B X x ρ hρ) α)
        (o₂ : conjIntegralSubring (representationSheafConj B X x'
          (ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupBasePointHom t).continuous)) α),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ ((representationSheafCommutantCoefficientSheaf B X x'
          (ρ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupBasePointHom t).continuous) α hα').act o₂).asHom =
          ((representationSheafCommutantCoefficientSheaf B X x ρ hρ α hα).act o₁).asHom ≫ φ := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have := compactSpace_etaleFundamentalGroup X.1 x'
  set φ₀ := (etaleFundamentalGroupBasePointHom t).toMonoidHom
  have hφ₀ : Continuous φ₀ := (etaleFundamentalGroupBasePointHom t).continuous
  set ρ' := ρ.comp φ₀
  have hρ' : Continuous ρ' := hρ.comp hφ₀
  set P := representationSheafConj B X x ρ hρ
  set P' := representationSheafConj B X x' ρ' hρ'
  have hP : ∀ (z : GeometricPoint X.1)
      (τ : EtaleFundamentalGroup X.1 z →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ) g,
      have := compactSpace_etaleFundamentalGroup X.1 z
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel τ hτ g).val =
        (representationSheafConj B X z τ hτ)⁻¹.val * (τ g).val *
          (representationSheafConj B X z τ hτ).val := fun z τ hτ g => by
    have := compactSpace_etaleFundamentalGroup X.1 z
    have h := congrArg Units.val (map_integralModel τ hτ g)
    simp only [Units.val_mul] at h
    exact h
  let τ₁ := (integralModel ρ hρ).comp φ₀
  have hτ₁ : Continuous τ₁ := (continuous_integralModel ρ hρ).comp hφ₀
  have hμX := conjIntegralLift_mul_integralModel B X x ρ hρ α hα
  have hμ₁ : ∀ s g, conjIntegralLift P α s * (τ₁ g).val = (τ₁ g).val * conjIntegralLift P α s :=
    fun s g => hμX s (φ₀ g)
  let I := representationLAdicSheafBasePointIso B X t (continuous_integralModel ρ hρ)
  have hI := representationCoefficientSheafBasePointIso_hom_act B X t
    (continuous_integralModel ρ hρ) (conjIntegralLift P α) hμX hμ₁
  have hM : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ' hρ' g).val =
      (P⁻¹ * P')⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₁ g).val * (P⁻¹ * P').val := by
    intro g
    rw [hP x' ρ' hρ' g]
    change _ = _ * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ (φ₀ g)).val * _
    rw [hP x ρ hρ (φ₀ g), conj_inv_mul_conj]
    rfl
  have hMμ : ∀ (o₁ : conjIntegralSubring P α) (o₂ : conjIntegralSubring P' α),
      algebraMap _ E o₁ = algebraMap _ E o₂ →
      (P⁻¹ * P')⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P α o₁) *
          (P⁻¹ * P').val =
        (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (conjIntegralLift P' α o₂) := by
    intro o₁ o₂ ho
    have he : (o₁ : E) = (o₂ : E) := ho
    rw [mapMatrix_conjIntegralLift, mapMatrix_conjIntegralLift, conj_inv_mul_conj, he]
  obtain ⟨φ, ψ, N, h₁, h₂, hc⟩ := exists_representationCoefficientSheaf_isogeny_of_conj B X x' hτ₁
    (continuous_integralModel ρ' hρ') (conjIntegralLift P α) (conjIntegralLift P' α) hμ₁
    (conjIntegralLift_mul_integralModel B X x' ρ' hρ' α hα') E (P⁻¹ * P') hM hMμ
  obtain ⟨k₁, k₂⟩ := isogeny_iso_comp I φ ψ (ℓ ^ N) h₁ h₂
  refine ⟨I.hom ≫ φ, ψ ≫ I.inv, N, k₁, k₂, fun o₁ o₂ ho => ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (I.hom ≫ ·) (hc o₁ o₂ ho)).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ) (hI o₁))).trans
      (Category.assoc _ _ _)))

end Commutant

section RestrictScalars

variable {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
  {m : ℕ} (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))
  (hσ' : Continuous (restrictScalarsRep b
    (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)))

/-- **`ℱ_{Res_b σ}` at `x̄` is isogenous to `ℱ_{Res_b (σ ∘ φ_t)}` at `x̄'`, compatibly with the
actions of the two integral parts of `E`.** -/
public theorem exists_basePoint_restrictScalarsRepCoefficientSheaf_isogeny :
    ∃ (φ : (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B X x' b
          (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) hσ').toLAdicSheaf)
      (ψ : (restrictScalarsRepCoefficientSheaf B X x' b
          (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) hσ').toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf)
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring
          (representationSheafConj B X x (restrictScalarsRep b σ) hσ)
          (restrictScalarsScalarAlgHom b m))
        (o₂ : conjIntegralSubring
          (representationSheafConj B X x'
            (restrictScalarsRep b (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)) hσ')
          (restrictScalarsScalarAlgHom b m)),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ ((restrictScalarsRepCoefficientSheaf B X x' b
          (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom) hσ').act o₂).asHom =
          ((restrictScalarsRepCoefficientSheaf B X x b σ hσ).act o₁).asHom ≫ φ :=
  exists_basePoint_representationSheafCommutantCoefficientSheaf_isogeny B X t
    (restrictScalarsRep b σ) hσ (restrictScalarsScalarAlgHom b m)
    (restrictScalarsScalarAlgHom_commute b σ)
    (restrictScalarsScalarAlgHom_commute b
      (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom))

end RestrictScalars

end Stacks.EtaleCohomology

end
