module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveSheafBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing

/-!
# The inverse image of `ℱ_ρ` is isogenous to `ℱ_{ρ ∘ f_*}`

For `f : Y ⟶ X` of connected Noetherian schemes, a geometric point `ȳ` of `Y` and a continuous
`ρ : π₁(X, f(ȳ)) → GL_r(ℚ_ℓ)`, the ℓ-adic sheaf `f⁻¹ℱ_ρ` is isogenous to `ℱ_{ρ ∘ f_*}`: both
are built from integral models, `f⁻¹ℱ_ρ` from the restriction of the integral model of `ρ`
(`Stacks.EtaleCohomology.representationLAdicSheafInverseImageIso`) and `ℱ_{ρ ∘ f_*}` from the
integral model of the restriction, and two integral models of the same representation are
conjugate over `ℚ_ℓ`, so integral multiples of the conjugating matrix and of its inverse are
intertwiners whose products are powers of `ℓ`. Isogenous sheaves have the same Frobenius
characteristic polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`.

## Main results

* `exists_representationLAdicSheaf_isogeny_of_conj`: two continuous `ℤ_ℓ`-representations
  conjugate over `ℚ_ℓ` have isogenous sheaves.
* `exists_inverseImage_representationSheaf_isogeny`: `f⁻¹ℱ_ρ` is isogenous to `ℱ_{ρ ∘ f_*}`.
* `LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny`: isogenous
  ℓ-adic sheaves have the same Frobenius characteristic polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### Integral models conjugate over `ℚ_ℓ` give isogenous sheaves -/

section Conj

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **Two continuous `ℤ_ℓ`-representations conjugate over `ℚ_ℓ` have isogenous sheaves**: if
`τ₂ = M⁻¹ τ₁ M` over `ℚ_ℓ`, then `ℓᵇ M⁻¹ : ℱ_{τ₁} → ℱ_{τ₂}` and `ℓᵃ M : ℱ_{τ₂} → ℱ_{τ₁}`, for
`a`, `b` making them integral, have composites multiplication by `ℓᵃ⁺ᵇ`. -/
public theorem exists_representationLAdicSheaf_isogeny_of_conj
    {τ₁ τ₂ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hτ₁ : Continuous τ₁)
    (hτ₂ : Continuous τ₂) (M : GL (Fin r) ℚ_[ℓ])
    (hM : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₂ g).val =
      M⁻¹.val * (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ₁ g).val * M.val) :
    ∃ (φ : representationLAdicSheaf B X x e τ₁ hτ₁ ⟶ representationLAdicSheaf B X x e τ₂ hτ₂)
      (ψ : representationLAdicSheaf B X x e τ₂ hτ₂ ⟶ representationLAdicSheaf B X x e τ₁ hτ₁)
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ := by
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
  have hscal : ∀ (c : ℕ) (Q : Matrix (Fin r) (Fin r) ℚ_[ℓ]), (c : ℚ_[ℓ]) • Q = c • Q :=
    fun c Q => Nat.cast_smul_eq_nsmul ℚ_[ℓ] c Q
  have hAA' : A * A' = (ℓ ^ (a + b)) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hMM, smul_smul, ← pow_add, ← hscal, Nat.cast_pow]
  have hA'A : A' * A = (ℓ ^ (a + b)) • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hMM', smul_smul, ← pow_add, add_comm b a,
      ← hscal, Nat.cast_pow]
  have hcongr : ∀ {τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
      (hτ : Continuous τ) {N N' : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
      (_ : N = N') (hN : ∀ g, N * (τ g).val = (τ g).val * N)
      (hN' : ∀ g, N' * (τ g).val = (τ g).val * N'),
      representationLAdicSheafMap B X x e hτ hτ N hN =
        representationLAdicSheafMap B X x e hτ hτ N' hN' := by
    intro τ hτ N N' h _ _
    subst h
    rfl
  refine ⟨representationLAdicSheafMap B X x e hτ₁ hτ₂ A' hA',
    representationLAdicSheafMap B X x e hτ₂ hτ₁ A hA, a + b, ?_, ?_⟩
  · rw [← representationLAdicSheafMap_mul,
      hcongr hτ₁ hAA' _ (fun g => by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]),
      representationLAdicSheafMap_nsmul_one]
  · rw [← representationLAdicSheafMap_mul,
      hcongr hτ₂ hA'A _ (fun g => by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]),
      representationLAdicSheafMap_nsmul_one]

end Conj

/-! ### The inverse image of `ℱ_ρ` -/

/-- An isogeny precomposed with an isomorphism is an isogeny. -/
public theorem isogeny_iso_comp {C : Type*} [Category* C] [Preadditive C] {F G H : C}
    (I : F ≅ G) (φ : G ⟶ H) (ψ : H ⟶ G) (n : ℕ) (h₁ : φ ≫ ψ = n • 𝟙 G)
    (h₂ : ψ ≫ φ = n • 𝟙 H) :
    (I.hom ≫ φ) ≫ ψ ≫ I.inv = n • 𝟙 F ∧ (ψ ≫ I.inv) ≫ I.hom ≫ φ = n • 𝟙 H := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, reassoc_of% h₁, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, Iso.hom_inv_id]
  · rw [Category.assoc, Iso.inv_hom_id_assoc, h₂]

section InverseImage

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [IsNoetherian Y.1] (y : GeometricPoint Y.1)

/-- **`f⁻¹ℱ_ρ` is isogenous to `ℱ_{ρ ∘ f_*}`** for a continuous `ρ : π₁(X, f(ȳ)) → GL_r(ℚ_ℓ)`. -/
public theorem exists_inverseImage_representationSheaf_isogeny
    (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) :
    ∃ (φ : LAdicSheaf.inverseImage (ℓ := ℓ) f
          (LAdicSheaf.representationSheaf B X (y.map f.hom) ρ hρ) ⟶
        LAdicSheaf.representationSheaf B Y y (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous))
      (ψ : LAdicSheaf.representationSheaf B Y y
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) ⟶
        LAdicSheaf.inverseImage (ℓ := ℓ) f (LAdicSheaf.representationSheaf B X (y.map f.hom) ρ hρ))
      (N : ℕ), φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ := by
  have := compactSpace_etaleFundamentalGroup X.1 (y.map f.hom)
  have := compactSpace_etaleFundamentalGroup Y.1 y
  set φ₀ := (etaleFundamentalGroupMap f.hom y).toMonoidHom
  have hφ₀ : Continuous φ₀ := (etaleFundamentalGroupMap f.hom y).continuous
  set ρ' := ρ.comp φ₀
  have hρ' : Continuous ρ' := hρ.comp hφ₀
  let I := representationLAdicSheafInverseImageIso B f y (integralModel ρ hρ)
    (continuous_integralModel ρ hρ)
  set P := (exists_conj_integral ρ hρ).choose
  set Q := (exists_conj_integral ρ' hρ').choose
  obtain ⟨φ, ψ, N, h₁, h₂⟩ := exists_representationLAdicSheaf_isogeny_of_conj B Y y
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
    (τ₁ := (integralModel ρ hρ).comp φ₀) ((continuous_integralModel ρ hρ).comp hφ₀)
    (continuous_integralModel ρ' hρ') (P⁻¹ * Q)
    (fun g => by
      have key : Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ' hρ' g) = (P⁻¹ * Q)⁻¹ *
            Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
              (integralModel ρ hρ (φ₀ g)) * (P⁻¹ * Q) := by
        rw [map_integralModel, map_integralModel]
        show Q⁻¹ * ρ (φ₀ g) * Q = (P⁻¹ * Q)⁻¹ * (P⁻¹ * ρ (φ₀ g) * P) * (P⁻¹ * Q)
        group
      have h := congrArg Units.val key
      rw [Units.val_mul, Units.val_mul] at h
      exact h)
  exact ⟨I.hom ≫ φ, ψ ≫ I.inv, N, isogeny_iso_comp I φ ψ _ h₁ h₂⟩

end InverseImage

/-! ### Isogeny invariance of the Frobenius characteristic polynomials -/

section Isogeny

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Isogenous ℓ-adic sheaves have the same Frobenius characteristic polynomials on
`Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`.** -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard G
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom.charpoly := by
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
    h₁ h₂ i
  have hcomm := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B X
    ℓ f j kbar φ ψ N h₁ h₂ i
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)
  have hconj : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
      G i).hom = e.toLinearEquiv.conj
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
          i).hom := by
    rw [LinearEquiv.conj_apply]
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
    have := congrArg (fun g => g.hom y) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact this
  rw [hconj, LinearEquiv.charpoly_conj]

/-- Isogenous ℓ-adic sheaves have the same finite dimensionality of `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_isogeny
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i) :=
  LinearEquiv.finiteDimensional
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
      i).toLinearEquiv

end Isogeny

end Stacks.EtaleCohomology

end
