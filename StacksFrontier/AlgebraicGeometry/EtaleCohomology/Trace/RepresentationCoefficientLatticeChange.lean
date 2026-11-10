module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientIsogenyLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear

/-!
# Changing the integral model of a representation with coefficients, `E`-linearly

Let `τ₁`, `τ₂ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous with `τ₂ = M⁻¹ τ₁ M` over `ℚ_ℓ`, and let
`O₁`, `O₂` act on `ℤ_ℓ^r` through intertwiners `μ₁`, `μ₂` of `τ₁`, `τ₂`, both rings localizing at
`ℓ` to `E`, with `M⁻¹ μ₁(o₁) M = μ₂(o₂)` whenever `o₁` and `o₂` have the same image in `E`. Then
integral multiples `ℓᵇ M⁻¹` and `ℓᵃ M` give an isogeny of the `O`-sheaves `ℱ_{τ₁}`, `ℱ_{τ₂}`
commuting with these pairs of actions
(`Stacks.EtaleCohomology.exists_representationCoefficientSheaf_isogeny_of_conj`), so the
`E`-linear Frobenius characteristic polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` agree.

For the commutant sheaves of `Stacks.EtaleCohomology.representationSheafCommutantCoefficientSheaf`
this applies to two `ℚ_ℓ`-representations `ρ₂ = Q⁻¹ ρ₁ Q` with `Q` commuting with the action `α`
of `E` (`M = P₁⁻¹ Q P₂` for the matrices `Pᵢ` of the integral models); in particular to the sheaves
`ℱ_{Res_b σ}` of two conjugate `E`-linear representations `σ₂ = g⁻¹ σ₁ g`
(`Stacks.EtaleCohomology.charpoly_restrictScalarsRepCoefficientSheaf_eq_of_conj`), where the two
integral parts of `E` differ. This is the lattice change and conjugation step of the
identification of the fibres of Laumon's family in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_representationCoefficientSheaf_isogeny_of_conj`.
* `Stacks.EtaleCohomology.exists_representationSheafCommutantCoefficientSheaf_isogeny_of_conj`.
* `Stacks.EtaleCohomology.exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv`.
* `Stacks.EtaleCohomology.charpoly_restrictScalarsRepCoefficientSheaf_eq_of_conj`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

section General

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] {r : ℕ}
  {τ₁ τ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hτ₁ : Continuous τ₁)
  (hτ₂ : Continuous τ₂) {O₁ O₂ : Type} [CommRing O₁] [Algebra ℤ_[ℓ] O₁] [CommRing O₂]
  [Algebra ℤ_[ℓ] O₂] (μ₁ : O₁ →+* Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (μ₂ : O₂ →+* Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (hμ₁ : ∀ o g, μ₁ o * (τ₁ g).val = (τ₁ g).val * μ₁ o)
  (hμ₂ : ∀ o g, μ₂ o * (τ₂ g).val = (τ₂ g).val * μ₂ o)
  (E : Type) [CommRing E] [Algebra O₁ E] [Algebra O₂ E]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The morphism of an intertwiner between two representations depends only on the matrix. -/
theorem representationLAdicSheafMap_congr₂ {τ τ' : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
    (hτ : Continuous τ) (hτ' : Continuous τ') {A A' : Matrix (Fin r) (Fin r) ℤ_[ℓ]} (h : A = A')
    (hA : ∀ g, A * (τ g).val = (τ' g).val * A) (hA' : ∀ g, A' * (τ g).val = (τ' g).val * A') :
    representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        hτ hτ' A hA =
      representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hτ hτ' A' hA' := by
  subst h
  rfl

/-- **Two integral models conjugate over `ℚ_ℓ`, with compatible actions, give isogenous
`O`-sheaves**: if `τ₂ = M⁻¹ τ₁ M` and `M⁻¹ μ₁(o₁) M = μ₂(o₂)` whenever `o₁`, `o₂` have the same
image in `E`, then `ℓᵇ M⁻¹ : ℱ_{τ₁} → ℱ_{τ₂}` and `ℓᵃ M : ℱ_{τ₂} → ℱ_{τ₁}` (for `a`, `b` making
them integral) are an isogeny commuting with these pairs of actions. -/
public theorem exists_representationCoefficientSheaf_isogeny_of_conj (M : GL (Fin r) ℚ_[ℓ])
    (hM : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₂ g).val =
      M⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₁ g).val * M.val)
    (hMμ : ∀ (o₁ : O₁) (o₂ : O₂), algebraMap O₁ E o₁ = algebraMap O₂ E o₂ →
      M⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (μ₁ o₁) * M.val =
        (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (μ₂ o₂)) :
    ∃ (φ : (representationCoefficientSheaf B X x τ₁ hτ₁ μ₁ hμ₁).toLAdicSheaf ⟶
        (representationCoefficientSheaf B X x τ₂ hτ₂ μ₂ hμ₂).toLAdicSheaf)
      (ψ : (representationCoefficientSheaf B X x τ₂ hτ₂ μ₂ hμ₂).toLAdicSheaf ⟶
        (representationCoefficientSheaf B X x τ₁ hτ₁ μ₁ hμ₁).toLAdicSheaf) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : O₁) (o₂ : O₂), algebraMap O₁ E o₁ = algebraMap O₂ E o₂ →
        φ ≫ ((representationCoefficientSheaf B X x τ₂ hτ₂ μ₂ hμ₂).act o₂).asHom =
          ((representationCoefficientSheaf B X x τ₁ hτ₁ μ₁ hμ₁).act o₁).asHom ≫ φ := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  obtain ⟨a, ha⟩ := exists_isIntegralMatrix_pow_smul M.val
  obtain ⟨b, hb⟩ := exists_isIntegralMatrix_pow_smul M⁻¹.val
  have hMM : M.val * M⁻¹.val = 1 := M.mul_inv
  have hMM' : M⁻¹.val * M.val = 1 := M.inv_mul
  have hτ₁v : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₁ g).val =
      M.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₂ g).val * M⁻¹.val := fun g => by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMM, Matrix.one_mul, Matrix.mul_assoc, hMM,
      Matrix.mul_one]
  let A := ha.lift
  let A' := hb.lift
  have hA : ∀ g, A * (τ₂ g).val = (τ₁ g).val * A := fun g => by
    apply mapMatrix_padicInt_injective
    rw [map_mul, map_mul, IsIntegralMatrix.mapMatrix_lift, hτ₁v, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, hMM', Matrix.mul_one]
  have hA' : ∀ g, A' * (τ₁ g).val = (τ₂ g).val * A' := fun g => by
    apply mapMatrix_padicInt_injective
    rw [map_mul, map_mul, IsIntegralMatrix.mapMatrix_lift, hM, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, hMM, Matrix.mul_one]
  have hAA' : A * A' = (ℓ ^ (a + b)) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hMM, smul_smul, ← pow_add,
      ← Nat.cast_smul_eq_nsmul ℚ_[ℓ], Nat.cast_pow]
  have hA'A : A' * A = (ℓ ^ (a + b)) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hMM', smul_smul, ← pow_add, add_comm b a,
      ← Nat.cast_smul_eq_nsmul ℚ_[ℓ], Nat.cast_pow]
  refine ⟨representationLAdicSheafMap B X x e hτ₁ hτ₂ A' hA',
    representationLAdicSheafMap B X x e hτ₂ hτ₁ A hA, a + b, ?_, ?_, ?_⟩
  · refine (representationLAdicSheafMap_mul B X x e hτ₁ hτ₂ hτ₁ A' hA' A hA).symm.trans ?_
    refine (representationLAdicSheafMap_congr₂ B X x hτ₁ hτ₁ hAA' _ (fun g => by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])).trans ?_
    exact representationLAdicSheafMap_nsmul_one B X x e hτ₁ _ _
  · refine (representationLAdicSheafMap_mul B X x e hτ₂ hτ₁ hτ₂ A hA A' hA').symm.trans ?_
    refine (representationLAdicSheafMap_congr₂ B X x hτ₂ hτ₂ hA'A _ (fun g => by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])).trans ?_
    exact representationLAdicSheafMap_nsmul_one B X x e hτ₂ _ _
  · intro o₁ o₂ ho
    have hmat : μ₂ o₂ * A' = A' * μ₁ o₁ := by
      apply mapMatrix_padicInt_injective
      rw [map_mul, map_mul, IsIntegralMatrix.mapMatrix_lift, ← hMμ o₁ o₂ ho, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hMM, Matrix.mul_one]
    refine (representationLAdicSheafMap_mul B X x e hτ₁ hτ₂ hτ₂ A' hA' (μ₂ o₂)
      (hμ₂ o₂)).symm.trans ?_
    refine (representationLAdicSheafMap_congr₂ B X x hτ₁ hτ₂ hmat _ (fun g => by
      rw [Matrix.mul_assoc, hμ₁ o₁, ← Matrix.mul_assoc, hA' g, Matrix.mul_assoc])).trans ?_
    exact representationLAdicSheafMap_mul B X x e hτ₁ hτ₁ hτ₂ (μ₁ o₁) (hμ₁ o₁) A' hA'

end General

section Commutant

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] {r : ℕ}
  {ρ₁ ρ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]} (hρ₁ : Continuous ρ₁)
  (hρ₂ : Continuous ρ₂) {E : Type} [Field E] [Algebra ℚ_[ℓ] E]
  (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ])
  (hα₁ : ∀ e g, α e * (ρ₁ g).val = (ρ₁ g).val * α e)
  (hα₂ : ∀ e g, α e * (ρ₂ g).val = (ρ₂ g).val * α e)

/-- **The commutant sheaves of two `ℚ_ℓ`-representations conjugate by a matrix commuting with
`α` are isogenous**, compatibly with the actions of the two integral parts of `E`. -/
public theorem exists_representationSheafCommutantCoefficientSheaf_isogeny_of_conj
    (Q : GL (Fin r) ℚ_[ℓ]) (hQ : ∀ g, ρ₂ g = Q⁻¹ * ρ₁ g * Q)
    (hQα : ∀ e, α e * Q.val = Q.val * α e) :
    ∃ (φ : (representationSheafCommutantCoefficientSheaf B X x ρ₁ hρ₁ α hα₁).toLAdicSheaf ⟶
        (representationSheafCommutantCoefficientSheaf B X x ρ₂ hρ₂ α hα₂).toLAdicSheaf)
      (ψ : (representationSheafCommutantCoefficientSheaf B X x ρ₂ hρ₂ α hα₂).toLAdicSheaf ⟶
        (representationSheafCommutantCoefficientSheaf B X x ρ₁ hρ₁ α hα₁).toLAdicSheaf) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring (representationSheafConj B X x ρ₁ hρ₁) α)
        (o₂ : conjIntegralSubring (representationSheafConj B X x ρ₂ hρ₂) α),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ ((representationSheafCommutantCoefficientSheaf B X x ρ₂ hρ₂ α hα₂).act o₂).asHom =
          ((representationSheafCommutantCoefficientSheaf B X x ρ₁ hρ₁ α hα₁).act o₁).asHom ≫ φ := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hP : ∀ (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) g,
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (integralModel ρ hρ g).val =
        (representationSheafConj B X x ρ hρ)⁻¹.val * (ρ g).val *
          (representationSheafConj B X x ρ hρ).val := fun ρ hρ g => by
    have h := congrArg Units.val (map_integralModel ρ hρ g)
    simp only [Units.val_mul] at h
    exact h
  have haux : ∀ (P₁ P₂ : GL (Fin r) ℚ_[ℓ]) (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]),
      (P₁⁻¹ * Q * P₂)⁻¹.val * (P₁⁻¹.val * A * P₁.val) * (P₁⁻¹ * Q * P₂).val =
        P₂⁻¹.val * (Q⁻¹.val * A * Q.val) * P₂.val := fun P₁ P₂ A => by
    simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  refine exists_representationCoefficientSheaf_isogeny_of_conj B X x
    (continuous_integralModel ρ₁ hρ₁) (continuous_integralModel ρ₂ hρ₂) _ _ _ _ E
    ((representationSheafConj B X x ρ₁ hρ₁)⁻¹ * Q * representationSheafConj B X x ρ₂ hρ₂)
    (fun g => ?_) (fun o₁ o₂ ho => ?_)
  · rw [hP ρ₂ hρ₂, hP ρ₁ hρ₁, haux, hQ g]
    simp only [Units.val_mul, Matrix.mul_assoc]
  · have he : (o₁ : E) = (o₂ : E) := ho
    rw [mapMatrix_conjIntegralLift, mapMatrix_conjIntegralLift, ← he, haux,
      Matrix.mul_assoc (Q⁻¹ : GL (Fin r) ℚ_[ℓ]).val, hQα, Units.inv_mul_cancel_left]

end Commutant

section RestrictScalars

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
  {σ₁ σ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E}
  (hσ₁ : Continuous (restrictScalarsRep b σ₁)) (hσ₂ : Continuous (restrictScalarsRep b σ₂))
  (g : GL (Fin m) E) (hg : ∀ γ, σ₂ γ = g⁻¹ * σ₁ γ * g)

include hg in
/-- **The sheaves `ℱ_{Res_b σ}` of two conjugate `E`-linear representations are isogenous**,
compatibly with the actions of the two integral parts of `E`. -/
public theorem exists_restrictScalarsRepCoefficientSheaf_isogeny_of_conj :
    ∃ (φ : (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).toLAdicSheaf)
      (ψ : (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).toLAdicSheaf ⟶
        (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).toLAdicSheaf) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ ∧
      ∀ (o₁ : conjIntegralSubring
          (representationSheafConj B X x (restrictScalarsRep b σ₁) hσ₁)
          (restrictScalarsScalarAlgHom b m))
        (o₂ : conjIntegralSubring
          (representationSheafConj B X x (restrictScalarsRep b σ₂) hσ₂)
          (restrictScalarsScalarAlgHom b m)),
        algebraMap _ E o₁ = algebraMap _ E o₂ →
        φ ≫ ((restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).act o₂).asHom =
          ((restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).act o₁).asHom ≫ φ := by
  refine exists_representationSheafCommutantCoefficientSheaf_isogeny_of_conj B X x hσ₁ hσ₂ _ _ _
    (Units.map (restrictScalarsMonoidHom b m) g) (fun γ => ?_) (fun e => ?_)
  · change Units.map (restrictScalarsMonoidHom b m) (σ₂ γ) = _
    rw [hg γ, map_mul, map_mul, map_inv]
    rfl
  · change restrictScalarsMatrix b (Matrix.scalar (Fin m) e) * restrictScalarsMatrix b g.val =
      restrictScalarsMatrix b g.val * restrictScalarsMatrix b (Matrix.scalar (Fin m) e)
    rw [← restrictScalarsMatrix_mul, ← restrictScalarsMatrix_mul,
      (Matrix.scalar_commute e (fun _ => mul_comm _ _) g.val)]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)

include hg in
/-- **`Hⁱ_c(X_k̄, ℱ_{Res_b σ₁} ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, ℱ_{Res_b σ₂} ⊗ ℚ_ℓ)`, `E`-linearly**, for
conjugate `σ₂ = g⁻¹ σ₁ g`, commuting with `π_X^*`. -/
public theorem exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) :
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).rationalCohomologyModule f j kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).rationalCohomologyModule f j kbar
      i E
    ∃ c : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).toLAdicSheaf i,
      ∀ v, c ((restrictScalarsRepCoefficientSheaf B X x b σ₁
          hσ₁).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard v) =
        (restrictScalarsRepCoefficientSheaf B X x b σ₂
          hσ₂).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard (c v) := by
  obtain ⟨φ, ψ, N, h₁, h₂, hφ⟩ :=
    exists_restrictScalarsRepCoefficientSheaf_isogeny_of_conj B X x b hσ₁ hσ₂ g hg
  exact ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv _ _ f j kbar i E φ ψ N h₁ h₂ hφ,
    LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius _ _ f j kbar i E φ ψ N h₁ h₂
      hφ p q hcard⟩

include hg in
/-- **Conjugate `E`-linear representations have the same `E`-linear Frobenius characteristic
polynomials on `Hⁱ_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`.** -/
public theorem charpoly_restrictScalarsRepCoefficientSheaf_eq_of_conj
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) :
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).rationalCohomologyModule f j kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).rationalCohomologyModule f j kbar
      i E
    ∀ [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b σ₁ hσ₁).toLAdicSheaf i)]
      [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B X x b σ₂ hσ₂).toLAdicSheaf i)],
    ((restrictScalarsRepCoefficientSheaf B X x b σ₁
        hσ₁).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard).charpoly =
      ((restrictScalarsRepCoefficientSheaf B X x b σ₂
        hσ₂).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard).charpoly := by
  obtain ⟨φ, ψ, N, h₁, h₂, hφ⟩ :=
    exists_restrictScalarsRepCoefficientSheaf_isogeny_of_conj B X x b hσ₁ hσ₂ g hg
  exact
    LAdicSheaf.CoefficientSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny
      _ _ f j kbar i E φ ψ N h₁ h₂ hφ p q hcard

end RestrictScalars

end Stacks.EtaleCohomology

end
