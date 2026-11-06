module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLevelIsogenyCoreAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSheafRestrictScalarsIntegers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsBlockMatrices
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafIntertwinerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheafMapOfHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekBaseChangeIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientRepresentation

/-!
# The representation side of Laumon's level isogeny

Piece (A) of the level isogeny in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
(`Stacks.EtaleCohomology.LaumonFourierRepresentationLevelIsogenyInput`): an `O`-sheaf `G` on a
connected Noetherian `X` is isogenous (`φ, ψ₀`, exponent `N`) to `ℱ_ρ`, `Q ρ₀ P = Res_b τ` with
`P Q = 1`, `Q P = 1`, `Q α(e) P = Res_b(e · 1)` for the action `α` of `E` through `φ, ψ₀`, and
`τ_E = T⁻¹ τ T` is an `O_E`-model of `τ`. Then the level `N'` of `G` and the lisse sheaf of
`(O_E/ℓ^{N'+1})^m` with `π₁` acting through `τ_E`, read as sheaves of `ℤ_ℓ`-modules, are
`ℓᶜ`-isogenous, the isogenies commuting up to `ℓᴺ` with the action of `O`, `c` independent of `N'`.

The isogeny at level `N'` is the level `N'` of the composite `φ ≫ Θ_Q` of morphisms of ℓ-adic
sheaves, followed by the identification of the levels of `ℱ_{Res_β τ_E}` with the lisse sheaves of
`(O_E/ℓ^{N'+1})^m` (`Stacks.EtaleCohomology.padicTowerRestrictScalarsIntegersIso`). Here
`β` is a `ℤ_ℓ`-basis of `O_E`, `Θ_Q` is the morphism of the integral intertwiner
`ℓ^{a} D' Res_b(T⁻¹) Q` of `ρ₀` and `Res_β τ_E`, `D, D'` the change of basis from `b` to `β`
(`Stacks.EtaleCohomology.exists_restrictScalarsMatrix_conj`), and the inverse isogeny is built
from `ℓ^{a'} P Res_b(T) D` and `ψ₀`. The key point is that each map only commutes with the
coefficients up to the bounded power `ℓᴺ`, which is fixed before the level `N'`.

## Main definitions

* `Stacks.EtaleCohomology.padicTowerRestrictScalarsIntegersIso`.

## Main results

* `Stacks.EtaleCohomology.exists_restrictScalarsMatrix_conj`.
* `Stacks.EtaleCohomology.exists_integralIntertwiners`.
* `Stacks.EtaleCohomology.padicTowerRestrictScalarsIntegersIso_smul`.
* `Stacks.EtaleCohomology.exists_levelIsogeny_of_integralIntertwiners`.
* `Stacks.EtaleCohomology.laumonFourierRepresentationLevelIsogenyInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Matrix Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

section BasisChange

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ}

/-- **Restrictions of scalars along two bases are conjugate**: for bases `b`, `b'` of `E` over
`F`, `Res_{b'} M = D' (Res_b M) D` for every square `E`-matrix `M`, with `D D' = D' D = 1`. -/
theorem exists_restrictScalarsMatrix_conj (b b' : Module.Basis (Fin d) F E) (m : ℕ) :
    ∃ D D' : Matrix (Fin (m * d)) (Fin (m * d)) F, D * D' = 1 ∧ D' * D = 1 ∧
      ∀ M : Matrix (Fin m) (Fin m) E,
        restrictScalarsMatrix b' M = D' * restrictScalarsMatrix b M * D := by
  refine ⟨(restrictScalarsPiBasis b m).toMatrix (restrictScalarsPiBasis b' m),
    (restrictScalarsPiBasis b' m).toMatrix (restrictScalarsPiBasis b m),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    fun M => ?_⟩
  rw [restrictScalarsMatrix_eq_toMatrix, restrictScalarsMatrix_eq_toMatrix,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

end BasisChange

section Intertwiners

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A `ℚ_ℓ`-matrix times a power of `ℓ` is the image of a `ℤ_ℓ`-matrix. -/
theorem exists_integral_pow_smul {α β : Type*} [Finite α] [Finite β] (C : Matrix α β ℚ_[ℓ]) :
    ∃ (a : ℕ) (A : Matrix α β ℤ_[ℓ]),
      A.map (PadicInt.Coe.ringHom (p := ℓ)) = ((ℓ : ℚ_[ℓ]) ^ a) • C := by
  obtain ⟨a, ha⟩ := exists_pow_mul_norm_le_one (ℓ := ℓ) C
  exact ⟨a, Matrix.of fun i j => ⟨_, ha i j⟩, by ext i j; rfl⟩

/-- Matrices over `ℤ_ℓ` are determined by their images over `ℚ_ℓ`. -/
theorem map_padicIntCoe_injective {α β : Type*} :
    Function.Injective fun A : Matrix α β ℤ_[ℓ] => A.map (PadicInt.Coe.ringHom (p := ℓ)) :=
  Matrix.map_injective fun _ _ h => PadicInt.ext h

/-- The image over `ℚ_ℓ` of `k • A` is `k` times that of `A`. -/
theorem map_padicIntCoe_nsmul {α β : Type*} (k : ℕ) (A : Matrix α β ℤ_[ℓ]) :
    (k • A).map (PadicInt.Coe.ringHom (p := ℓ)) =
      (k : ℚ_[ℓ]) • A.map (PadicInt.Coe.ringHom (p := ℓ)) := by
  ext i j
  simp [nsmul_eq_mul]

/-- **Integral intertwiners from rational ones**: if `A_Q`, `A_P` are mutually inverse rational
matrices with `A_Q ρ₀(g) = σ₀(g) A_Q` and `A_Q M_i = ℓᴺ S_i A_Q`, then suitable `ℓ`-power
multiples `L_Q`, `L_P` of `A_Q`, `A_P` are integral intertwiners with `L_P L_Q = L_Q L_P = ℓᵏ`,
`L_Q M_i = ℓᴺ S_i L_Q` and `M_i L_P = ℓᴺ L_P S_i`. -/
theorem exists_integralIntertwiners {G ι : Type*} {r n : ℕ}
    (ρ₀ : G → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (σ₀ : G → Matrix (Fin n) (Fin n) ℤ_[ℓ])
    (M : ι → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (S : ι → Matrix (Fin n) (Fin n) ℤ_[ℓ]) (N : ℕ)
    (AQ : Matrix (Fin n) (Fin r) ℚ_[ℓ]) (AP : Matrix (Fin r) (Fin n) ℚ_[ℓ])
    (hPQ : AP * AQ = 1) (hQP : AQ * AP = 1)
    (hρ : ∀ g, AQ * (ρ₀ g).map (PadicInt.Coe.ringHom (p := ℓ)) =
      (σ₀ g).map (PadicInt.Coe.ringHom (p := ℓ)) * AQ)
    (hM : ∀ i, AQ * (M i).map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ N) • ((S i).map (PadicInt.Coe.ringHom (p := ℓ)) * AQ)) :
    ∃ (k : ℕ) (LQ : Matrix (Fin n) (Fin r) ℤ_[ℓ]) (LP : Matrix (Fin r) (Fin n) ℤ_[ℓ]),
      (∀ g, LQ * ρ₀ g = σ₀ g * LQ) ∧ (∀ g, LP * σ₀ g = ρ₀ g * LP) ∧
      LP * LQ = ℓ ^ k • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) ∧
      LQ * LP = ℓ ^ k • (1 : Matrix (Fin n) (Fin n) ℤ_[ℓ]) ∧
      (∀ i, LQ * M i = ℓ ^ N • (S i * LQ)) ∧ (∀ i, M i * LP = ℓ ^ N • (LP * S i)) := by
  have key : ∀ (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]) (B : Matrix (Fin n) (Fin n) ℚ_[ℓ]),
      AQ * A = B * AQ → AP * B = A * AP := fun A B h => by
    calc AP * B = AP * (B * AQ) * AP := by
          rw [Matrix.mul_assoc AP, Matrix.mul_assoc, hQP, Matrix.mul_one]
      _ = A * AP := by rw [← h, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hρ' := fun g => key _ _ (hρ g)
  have hM' := fun i => key _ _ ((hM i).trans (Matrix.smul_mul _ _ _).symm)
  obtain ⟨aQ, LQ, hLQ⟩ := exists_integral_pow_smul AQ
  obtain ⟨aP, LP, hLP⟩ := exists_integral_pow_smul AP
  refine ⟨aQ + aP, LQ, LP, fun g => ?_, fun g => ?_, ?_, ?_, fun i => ?_, fun i => ?_⟩
  all_goals
    apply map_padicIntCoe_injective
    simp only [Matrix.map_mul, map_padicIntCoe_nsmul, hLQ, hLP, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.map_one _ (map_zero _) (map_one _), Nat.cast_pow, smul_smul]
  · rw [hρ]
  · rw [hρ' g]
  · rw [hPQ, ← pow_add, add_comm]
  · rw [hQP, ← pow_add, add_comm]
  · rw [hM, smul_smul, mul_comm]
  · rw [← hM' i, Matrix.mul_smul, smul_smul, mul_comm]

end Intertwiners

section Rational

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d m r : ℕ}
  (b b' : Module.Basis (Fin d) ℚ_[ℓ] E) (D D' : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ])
  (hDD' : D * D' = 1) (hD : ∀ M : Matrix (Fin m) (Fin m) E,
    restrictScalarsMatrix b' M = D' * restrictScalarsMatrix b M * D)
  (P : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Q : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
  (hPQ : P * Q = 1) (T : GL (Fin m) E)

/-- `Res_b T` and `Res_b T⁻¹` are mutually inverse for a unit `T`. -/
private theorem restrictScalarsMatrix_mul_inv_eq_one :
    restrictScalarsMatrix b T.val * restrictScalarsMatrix b (T⁻¹ : GL (Fin m) E).val = 1 ∧
      restrictScalarsMatrix b (T⁻¹ : GL (Fin m) E).val * restrictScalarsMatrix b T.val = 1 := by
  simp only [← restrictScalarsMatrix_mul, Units.mul_inv, Units.inv_mul, restrictScalarsMatrix_one,
    and_self]

include hDD' hD hPQ in
/-- **The rational intertwiner `D' Res_b(T⁻¹) Q`**: if `Q R P = Res_b Y`, then
`D' Res_b(T⁻¹) Q R = Res_{b'}(T⁻¹ Y T) D' Res_b(T⁻¹) Q`. -/
theorem restrictScalarsConj_mul_eq (R : Matrix (Fin r) (Fin r) ℚ_[ℓ])
    (Y : Matrix (Fin m) (Fin m) E) (hY : Q * R * P = restrictScalarsMatrix b Y) :
    D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin m) E).val * Q * R =
      restrictScalarsMatrix b' ((T⁻¹ : GL (Fin m) E).val * Y * T.val) *
        (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin m) E).val * Q) := by
  have hTT := (restrictScalarsMatrix_mul_inv_eq_one b T).1
  have hQR : Q * R = restrictScalarsMatrix b Y * Q := by
    rw [← hY, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  rw [hD, restrictScalarsMatrix_mul, restrictScalarsMatrix_mul]
  simp only [Matrix.mul_assoc]
  rw [hQR, ← Matrix.mul_assoc D D', hDD', Matrix.one_mul,
    ← Matrix.mul_assoc (restrictScalarsMatrix b T.val), hTT, Matrix.one_mul]

end Rational

/-- An endomorphism intertwined by an isomorphism is intertwined by its inverse. -/
theorem comp_inv_eq_inv_comp_of_comp_hom_eq {C : Type*} [Category* C] {Y Z : C} (e : Y ≅ Z)
    {s : Y ⟶ Y} {t : Z ⟶ Z} (h : s ≫ e.hom = e.hom ≫ t) : t ≫ e.inv = e.inv ≫ s := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

section Levels

attribute [local instance] neZero_pow_of_fact_prime

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {D m : ℕ} (β : Module.Basis (Fin D) ℤ_[ℓ] O)
  (τO : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hRes : Continuous (restrictScalarsRepresentation B X x β τO)) (n : ℕ)
  [CharP (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)}) (ℓ ^ (n + 1))]
  [Finite (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)})]
  (h : IsOpen (((GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}))).comp τO).ker :
        Set (EtaleFundamentalGroup X.1 x)))

/-- **The `n`-th level of `ℱ_{Res_β τ}` is the lisse sheaf of `(O/ℓ^{n+1})^m`** with `π₁`
acting through `τ` modulo `ℓ^{n+1}`, both read as sheaves of `ℤ_ℓ`-modules: the level of
`ℱ_{Res_β τ}` is the lisse sheaf of the level module of `Res_β τ`
(`Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso`), which is the lisse sheaf of
`(O/ℓ^{n+1})^m` restricted to `ℤ/ℓ^{n+1}`
(`Stacks.EtaleCohomology.lisseEtaleSheafRestrictScalarsIntegersIso`), and restriction of scalars
along `ℤ_ℓ → ℤ/ℓ^{n+1} → O/ℓ^{n+1}` is restriction along the composite. -/
def padicTowerRestrictScalarsIntegersIso :
    (LAdicSheaf.padicTower B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (restrictScalarsRepresentation B X x β τO) hRes)).obj (op n) ≅
      (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] O)) X.1).obj
        ((lisseEtaleSheaf B X x (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1} (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)})
            ((GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}))).comp
              τO) h)) :=
  padicTowerRepresentationLAdicSheafIso B X x _ hRes n ≪≫
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).mapIso
      (lisseEtaleSheafRestrictScalarsIntegersIso B X x β τO hRes (n + 1) h).symm ≪≫
    (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1))
      (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)}))
      ((Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)})).comp (algebraMap ℤ_[ℓ] O))
      (RingHom.ext fun c => mk_algebraMap_eq_castHom_toZModPow (O := O) (n + 1) c) X.1).app _

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The level identification carries the action of `o ∈ O` through its matrix on `ℱ_{Res_β τ}`
to multiplication by `o`** on the lisse sheaf of `(O/ℓ^{n+1})^m`. -/
theorem padicTowerRestrictScalarsIntegersIso_smul (o : O) :
    (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hRes hRes
        (coefficientScalarRingHom β m o)
        (fun g => coefficientScalarRingHom_commute β m o (τO g).val))).app (op n) ≫
        (padicTowerRestrictScalarsIntegersIso B X x β τO hRes n h).hom =
      (padicTowerRestrictScalarsIntegersIso B X x β τO hRes n h).hom ≫
        (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] O)) X.1).map
          ((etaleModuleSMul X.1 (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}) o)).app _) := by
  have h1 := padicTowerRepresentationLAdicSheafIso_naturality B X x hRes hRes
    (coefficientScalarRingHom β m o) (fun g => coefficientScalarRingHom_commute β m o (τO g).val) n
  have h2 := lisseEtaleSheafRestrictScalarsIntegersIso_smul B X x β τO hRes (n + 1) h o
  have h2' := comp_inv_eq_inv_comp_of_comp_hom_eq _ h2
  have h3 := (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1))
      (ZMod.castHom dvd_rfl (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)}))
      ((Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)})).comp (algebraMap ℤ_[ℓ] O))
      (RingHom.ext fun c => mk_algebraMap_eq_castHom_toZModPow (O := O) (n + 1) c)
        X.1).hom.naturality
    (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}) o •
      𝟙 ((lisseEtaleSheaf B X x (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)})).obj
        (matrixContinuousModule.{u + 1, u + 1} (O ⧸ Ideal.span {(ℓ : O) ^ (n + 1)})
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}))).comp
            τO) h)))
  rw [etaleModuleSMul_app_eq_smul_id]
  simp only [padicTowerRestrictScalarsIntegersIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc, ← Functor.map_comp_assoc, h2', Functor.map_comp_assoc]
  exact congrArg _ (congrArg _ h3)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The inverse of the level identification also carries multiplication by `o` to the action of
`o` through its matrix. -/
theorem padicTowerRestrictScalarsIntegersIso_inv_smul (o : O) :
    (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] O)) X.1).map
          ((etaleModuleSMul X.1 (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (n + 1)}) o)).app _) ≫
        (padicTowerRestrictScalarsIntegersIso B X x β τO hRes n h).inv =
      (padicTowerRestrictScalarsIntegersIso B X x β τO hRes n h).inv ≫
        (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hRes hRes
          (coefficientScalarRingHom β m o)
          (fun g => coefficientScalarRingHom_commute β m o (τO g).val))).app (op n) :=
  comp_inv_eq_inv_comp_of_comp_hom_eq _
    (padicTowerRestrictScalarsIntegersIso_smul B X x β τO hRes n h o)

end Levels

section Calculus

variable {C : Type*} [Category* C] [Preadditive C]

/-- Moving an endomorphism `a` of `G` across `φ ≫ Θ` when `φ ψ₀ = n` and `(ψ₀ a φ) Θ = n Θ σ`. -/
theorem nsmul_comp_comp_eq_of_isogeny {G F F' : C} (φ : G ⟶ F) (ψ₀ : F ⟶ G) {n : ℕ}
    (hφψ : φ ≫ ψ₀ = n • 𝟙 _) (a : G ⟶ G) (Θ : F ⟶ F') (σ : F' ⟶ F')
    (h : (ψ₀ ≫ a ≫ φ) ≫ Θ = n • (Θ ≫ σ)) : n • (a ≫ φ ≫ Θ) = n • ((φ ≫ Θ) ≫ σ) := by
  calc n • (a ≫ φ ≫ Θ) = (n • 𝟙 _) ≫ a ≫ φ ≫ Θ := by
        rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = φ ≫ (ψ₀ ≫ a ≫ φ) ≫ Θ := by rw [← hφψ]; simp only [Category.assoc]
    _ = n • ((φ ≫ Θ) ≫ σ) := by rw [h, Preadditive.comp_nsmul, Category.assoc]

/-- Moving an endomorphism `σ` of `F'` across `Θ' ≫ ψ₀` when `φ ψ₀ = n` and
`n σ Θ' = Θ' (ψ₀ a φ)`. -/
theorem nsmul_comp_comp_eq_of_isogeny' {G F F' : C} (φ : G ⟶ F) (ψ₀ : F ⟶ G) {n : ℕ}
    (hφψ : φ ≫ ψ₀ = n • 𝟙 _) (a : G ⟶ G) (Θ' : F' ⟶ F) (σ : F' ⟶ F')
    (h : n • (σ ≫ Θ') = Θ' ≫ (ψ₀ ≫ a ≫ φ)) : n • (σ ≫ Θ' ≫ ψ₀) = n • ((Θ' ≫ ψ₀) ≫ a) := by
  calc n • (σ ≫ Θ' ≫ ψ₀) = (n • (σ ≫ Θ')) ≫ ψ₀ := by
        rw [Preadditive.nsmul_comp, Category.assoc]
    _ = Θ' ≫ ψ₀ ≫ a ≫ φ ≫ ψ₀ := by rw [h]; simp only [Category.assoc]
    _ = n • ((Θ' ≫ ψ₀) ≫ a) := by
        rw [hφψ]; simp only [Preadditive.comp_nsmul, Category.comp_id, Category.assoc]

/-- Moving endomorphisms across a composite with an intertwining morphism. -/
theorem nsmul_comp_comp_eq_of_comm {X Y Z : C} (aX : X ⟶ X) (f : X ⟶ Y) (aY : Y ⟶ Y)
    (W : Y ⟶ Z) (aZ : Z ⟶ Z) {n : ℕ} (hf : n • (aX ≫ f) = n • (f ≫ aY))
    (hW : aY ≫ W = W ≫ aZ) : n • (aX ≫ f ≫ W) = n • ((f ≫ W) ≫ aZ) := by
  calc n • (aX ≫ f ≫ W) = (n • (aX ≫ f)) ≫ W := by
        rw [Preadditive.nsmul_comp, Category.assoc]
    _ = (n • (f ≫ aY)) ≫ W := by rw [hf]
    _ = n • ((f ≫ W) ≫ aZ) := by rw [Preadditive.nsmul_comp, Category.assoc, hW, Category.assoc]

/-- Moving endomorphisms across an intertwining morphism followed by a composite. -/
theorem nsmul_comp_comp_eq_of_comm' {X Y Z : C} (aZ : Z ⟶ Z) (W : Z ⟶ Y) (aY : Y ⟶ Y)
    (f : Y ⟶ X) (aX : X ⟶ X) {n : ℕ} (hW : aZ ≫ W = W ≫ aY)
    (hf : n • (aY ≫ f) = n • (f ≫ aX)) : n • (aZ ≫ W ≫ f) = n • ((W ≫ f) ≫ aX) := by
  calc n • (aZ ≫ W ≫ f) = W ≫ (n • (aY ≫ f)) := by
        rw [← Category.assoc, hW, Category.assoc, Preadditive.comp_nsmul]
    _ = W ≫ (n • (f ≫ aX)) := by rw [hf]
    _ = n • ((W ≫ f) ≫ aX) := by rw [Preadditive.comp_nsmul, Category.assoc]

/-- Conjugating an `n`-isogeny by an isomorphism, on one side. -/
theorem comp_iso_hom_comp_iso_inv_comp_eq {A Y Z : C} (f : A ⟶ Y) (g : Y ⟶ A) (W : Y ≅ Z) {n : ℕ}
    (h : f ≫ g = n • 𝟙 A) : (f ≫ W.hom) ≫ (W.inv ≫ g) = n • 𝟙 A := by
  rw [Category.assoc, Iso.hom_inv_id_assoc, h]

/-- Conjugating an `n`-isogeny by an isomorphism, on the other side. -/
theorem iso_inv_comp_comp_iso_hom_eq {A Y Z : C} (f : A ⟶ Y) (g : Y ⟶ A) (W : Y ≅ Z) {n : ℕ}
    (h : g ≫ f = n • 𝟙 Y) : (W.inv ≫ g) ≫ (f ≫ W.hom) = n • 𝟙 Z := by
  rw [Category.assoc, ← Category.assoc g, h, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, Iso.inv_hom_id]

end Calculus

section Maps

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}
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
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **`ℱ_{k A} = k ℱ_A`**: the morphism induced by `k • A'` is `k` times that of `A'`. -/
theorem representationLAdicSheafMap_eq_nsmul {A A' : Matrix (Fin r') (Fin r) ℤ_[ℓ]}
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hA' : ∀ g, A' * (ρ g).val = (ρ' g).val * A')
    (k : ℕ) (h : A = k • A') :
    representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      hρ hρ' A hA =
      k • representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A' hA' := by
  subst h
  induction k with
  | zero =>
    refine (representationLAdicSheafMap_eq_of_eq B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' hA
      (fun g => by rw [Matrix.zero_mul, Matrix.mul_zero]) (zero_nsmul A')).trans ?_
    rw [representationLAdicSheafMap_zero, zero_nsmul]
  | succ k ih =>
    refine (representationLAdicSheafMap_eq_of_eq B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' hA
      (fun g => by rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hA' g])
      (succ_nsmul A' k)).trans ?_
    rw [representationLAdicSheafMap_add B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' (k • A') A'
      (fun g => by rw [Matrix.smul_mul, Matrix.mul_smul, hA' g]) hA', ih, succ_nsmul]

/-- **Composing intertwiners**: if `L M_θ = n S L`, then `θ ≫ ℱ_L = n (ℱ_L ≫ ℱ_S)`. -/
theorem comp_representationLAdicSheafMap_eq_nsmul
    (θ : representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
        representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)
    (L : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hL : ∀ g, L * (ρ g).val = (ρ' g).val * L)
    (S : Matrix (Fin r') (Fin r') ℤ_[ℓ]) (hS : ∀ g, S * (ρ' g).val = (ρ' g).val * S) (n : ℕ)
    (h : L * representationLAdicSheafHomMatrix B X x hρ hρ θ = n • (S * L)) :
    θ ≫ representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' L hL =
      n • (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' L hL ≫
        representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ' hρ' S hS) := by
  conv_lhs => rw [eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix B X x hρ hρ θ]
  rw [← representationLAdicSheafMap_mul, ← representationLAdicSheafMap_mul]
  exact representationLAdicSheafMap_eq_nsmul B X x hρ hρ' _ _ n h

/-- **Composing intertwiners**: if `M_θ L = n L S`, then `n (ℱ_S ≫ ℱ_L) = ℱ_L ≫ θ`. -/
theorem nsmul_representationLAdicSheafMap_comp_eq
    (θ : representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
        representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)
    (L : Matrix (Fin r) (Fin r') ℤ_[ℓ]) (hL : ∀ g, L * (ρ' g).val = (ρ g).val * L)
    (S : Matrix (Fin r') (Fin r') ℤ_[ℓ]) (hS : ∀ g, S * (ρ' g).val = (ρ' g).val * S) (n : ℕ)
    (h : representationLAdicSheafHomMatrix B X x hρ hρ θ * L = n • (L * S)) :
    n • (representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ' hρ' S hS ≫
        representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ' hρ L hL) =
      representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ' hρ L hL ≫ θ := by
  conv_rhs => rw [eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix B X x hρ hρ θ]
  rw [← representationLAdicSheafMap_mul, ← representationLAdicSheafMap_mul]
  exact (representationLAdicSheafMap_eq_nsmul B X x hρ' hρ _ _ n h).symm

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- Intertwiners with `L' L = k` induce morphisms composing to `k`. -/
theorem representationLAdicSheafMap_comp_eq_nsmul_id (L : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hL : ∀ g, L * (ρ g).val = (ρ' g).val * L) (L' : Matrix (Fin r) (Fin r') ℤ_[ℓ])
    (hL' : ∀ g, L' * (ρ' g).val = (ρ g).val * L') (k : ℕ)
    (h : L' * L = k • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) :
    representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      hρ hρ' L hL ≫
        representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ' hρ L' hL' =
      k • 𝟙 _ := by
  rw [← representationLAdicSheafMap_mul, representationLAdicSheafMap_eq_nsmul B X x hρ hρ _
    (fun g => by rw [Matrix.one_mul, Matrix.mul_one]) k h, representationLAdicSheafMap_one]

end Maps

section Assembly

attribute [local instance] padicIntAlgebraOfRat neZero_pow_of_fact_prime

/-- The level map of `k (f ≫ g)`. -/
theorem padicTowerMap_app_nsmul_comp {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
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
    [IsNoetherian X.1] [Fact ℓ.Prime] {F₁ F₂ F₃ : LAdicSheaf.{u, u + 1} B X ℓ} (k : ℕ)
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (n : ℕᵒᵖ) :
    (LAdicSheaf.padicTowerMap (k • (f ≫ g))).app n =
      k • ((LAdicSheaf.padicTowerMap f).app n ≫ (LAdicSheaf.padicTowerMap g).app n) := by
  rw [LAdicSheaf.padicTowerMap_nsmul, NatTrans.app_nsmul, LAdicSheaf.padicTowerMap_comp,
    NatTrans.comp_app]

/-- The level maps of an `n`-isogeny of ℓ-adic sheaves form an `n`-isogeny. -/
theorem padicTowerMap_app_comp_eq_nsmul {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
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
    [IsNoetherian X.1] [Fact ℓ.Prime] {F₁ F₂ : LAdicSheaf.{u, u + 1} B X ℓ} (f : F₁ ⟶ F₂)
      (g : F₂ ⟶ F₁) {k : ℕ}
    (h : f ≫ g = k • 𝟙 F₁) (n : ℕᵒᵖ) :
    (LAdicSheaf.padicTowerMap f).app n ≫ (LAdicSheaf.padicTowerMap g).app n = k • 𝟙 _ := by
  rw [← NatTrans.comp_app, ← LAdicSheaf.padicTowerMap_comp, h, LAdicSheaf.padicTowerMap_nsmul,
    LAdicSheaf.padicTowerMap_id, NatTrans.app_nsmul, NatTrans.id_app]

/-- The level maps of morphisms of ℓ-adic sheaves commuting up to `k` commute up to `k`. -/
theorem padicTowerMap_app_nsmul_comp_eq {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
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
    [IsNoetherian X.1] [Fact ℓ.Prime] {F₁ F₂ F₃ F₄ : LAdicSheaf.{u, u + 1} B X ℓ} (a : F₁ ⟶ F₂)
      (f : F₂ ⟶ F₄) (f' : F₁ ⟶ F₃)
    (b : F₃ ⟶ F₄) {k : ℕ} (h : k • (a ≫ f) = k • (f' ≫ b)) (n : ℕᵒᵖ) :
    k • ((LAdicSheaf.padicTowerMap a).app n ≫ (LAdicSheaf.padicTowerMap f).app n) =
      k • ((LAdicSheaf.padicTowerMap f').app n ≫ (LAdicSheaf.padicTowerMap b).app n) := by
  rw [← padicTowerMap_app_nsmul_comp, ← padicTowerMap_app_nsmul_comp, h]

/-- **Level isogenies from an isogeny of ℓ-adic sheaves and level identifications**: an
`ℓᶜ`-isogeny `Φ, Ψ` between `G` and an ℓ-adic sheaf `F'` commuting up to `ℓᵗ` with the actions
`G.act o` and `Σ o'` (for `o`, `o'` with the same image in `E`), and identifications `W_{N'}` of
the levels of `F'` with the lisse sheaves of `(O_E/ℓ^{N'+1})^m` carrying `Σ o'` to multiplication
by `o'`, give the level isogenies of the representation side. -/
theorem exists_levelIsogeny_of_isogenies (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (X : B.Scheme) [ConnectedSpace X.1] [IsNoetherian X.1] (x : GeometricPoint X.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] [Algebra O E]
    (G : LAdicSheaf.CoefficientSheaf B X ℓ O) {mτ : ℕ}
    (τO : EtaleFundamentalGroup X.1 x →* GL (Fin mτ) (integralClosure ℤ_[ℓ] E))
    (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp τO).ker : Set
      (EtaleFundamentalGroup X.1 x)))
    {F' : LAdicSheaf.{u, u + 1} B X ℓ} (Φ : G.toLAdicSheaf ⟶ F') (Ψ : F' ⟶ G.toLAdicSheaf)
    (c t : ℕ) (hΦΨ : Φ ≫ Ψ = ℓ ^ c • 𝟙 _) (hΨΦ : Ψ ≫ Φ = ℓ ^ c • 𝟙 _)
    (act' : integralClosure ℤ_[ℓ] E → (F' ⟶ F'))
    (W : ∀ N' : ℕ, (LAdicSheaf.padicTower B X ℓ F').obj (op N') ≅
      (etaleModuleRestrictScalars
      ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
      (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
      ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
      {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
      (matrixContinuousModule.{u + 1, u + 1}
      (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
      ((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
      (hτO (N' + 1)))))
    (hW : ∀ (N' : ℕ) (o' : integralClosure ℤ_[ℓ] E),
      (LAdicSheaf.padicTowerMap (act' o')).app (op N') ≫ (W N').hom = (W N').hom ≫
        (etaleModuleRestrictScalars
        ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
        (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
        ((etaleModuleSMul X.1 (Ideal.Quotient.mk
        (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
        ((lisseEtaleSheaf B X x
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
        (matrixContinuousModule.{u + 1, u + 1}
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
        ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
        (hτO (N' + 1))))))
    (hΦ : ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E),
      algebraMap O E o = algebraMap (integralClosure ℤ_[ℓ] E) E o' →
        ℓ ^ t • ((G.act o).asHom ≫ Φ) = ℓ ^ t • (Φ ≫ act' o'))
    (hΨ : ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E),
      algebraMap O E o = algebraMap (integralClosure ℤ_[ℓ] E) E o' →
        ℓ ^ t • (act' o' ≫ Ψ) = ℓ ^ t • (Ψ ≫ (G.act o).asHom)) :
    ∃ c t : ℕ, ∀ N' : ℕ,
      ∃ (h : (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N') ⟶
        (etaleModuleRestrictScalars
        ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
        (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
        ((lisseEtaleSheaf B X x
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
        (matrixContinuousModule.{u + 1, u + 1}
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
        ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
        (hτO (N' + 1)))))
        (h' : (etaleModuleRestrictScalars
          ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
          ((lisseEtaleSheaf B X x
          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1}
          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
          ((Matrix.GeneralLinearGroup.map
          (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
          (hτO (N' + 1)))) ⟶ (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N')),
        h ≫ h' = ℓ ^ c • 𝟙 _ ∧ h' ≫ h = ℓ ^ c • 𝟙 _ ∧
        ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E), algebraMap O E o = algebraMap
          (integralClosure ℤ_[ℓ] E) E o' →
          ℓ ^ t • ((LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N') ≫ h) =
            ℓ ^ t • (h ≫ (etaleModuleRestrictScalars
              ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
              (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
              ((etaleModuleSMul X.1
              (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
              ((lisseEtaleSheaf B X x
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
              (matrixContinuousModule.{u + 1, u + 1}
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
              ((Matrix.GeneralLinearGroup.map
              (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
              (hτO (N' + 1)))))) ∧
          ℓ ^ t • ((etaleModuleRestrictScalars
            ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
            (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
            ((etaleModuleSMul X.1
            (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
            ((lisseEtaleSheaf B X x
            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
            (matrixContinuousModule.{u + 1, u + 1}
            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
            ((Matrix.GeneralLinearGroup.map
            (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
            (hτO (N' + 1))))) ≫ h') =
            ℓ ^ t • (h' ≫ (LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N'))
 := by
  refine ⟨c, t, fun N' => ⟨(LAdicSheaf.padicTowerMap Φ).app (op N') ≫ (W N').hom,
    (W N').inv ≫ (LAdicSheaf.padicTowerMap Ψ).app (op N'),
    comp_iso_hom_comp_iso_inv_comp_eq ((LAdicSheaf.padicTowerMap Φ).app (op N'))
      ((LAdicSheaf.padicTowerMap Ψ).app (op N')) (W N')
        (padicTowerMap_app_comp_eq_nsmul Φ Ψ hΦΨ (op N')),
    iso_inv_comp_comp_iso_hom_eq ((LAdicSheaf.padicTowerMap Φ).app (op N'))
      ((LAdicSheaf.padicTowerMap Ψ).app (op N')) (W N')
        (padicTowerMap_app_comp_eq_nsmul Ψ Φ hΨΦ (op N')),
    fun o o' he => ⟨nsmul_comp_comp_eq_of_comm
      ((LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N'))
      ((LAdicSheaf.padicTowerMap Φ).app (op N')) ((LAdicSheaf.padicTowerMap (act' o')).app (op N'))
      (W N').hom ((etaleModuleRestrictScalars
        ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
        (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
        ((etaleModuleSMul X.1 (Ideal.Quotient.mk
        (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
        ((lisseEtaleSheaf B X x
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
        (matrixContinuousModule.{u + 1, u + 1}
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
        ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
        (hτO (N' + 1))))))
        (padicTowerMap_app_nsmul_comp_eq (G.act o).asHom Φ Φ (act' o') (hΦ o o' he)
        (op N'))
      (hW N' o'),
    nsmul_comp_comp_eq_of_comm'
      ((etaleModuleRestrictScalars
      ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
      (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
      ((etaleModuleSMul X.1 (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
      ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸ Ideal.span
      {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
      (matrixContinuousModule.{u + 1, u + 1}
      (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
      ((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
      (hτO (N' + 1)))))) (W N').inv ((LAdicSheaf.padicTowerMap (act' o')).app (op N'))
      ((LAdicSheaf.padicTowerMap Ψ).app (op N'))
      ((LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N'))
      (comp_inv_eq_inv_comp_of_comp_hom_eq (W N') (hW N' o'))
      (padicTowerMap_app_nsmul_comp_eq (act' o') Ψ Ψ (G.act o).asHom (hΨ o o' he) (op N'))⟩⟩⟩

/-- **The representation side from integral intertwiners**: integral intertwiners `L_Q` of
`ρ₀` and `Res_β τ_E`, `L_P` back, with `L_P L_Q = L_Q L_P = ℓᵏ`, carrying the matrix of
`ψ₀ ∘ o ∘ φ` to `ℓᴺ` times the matrix of `o'` (`o`, `o'` with the same image in `E`), give level
isogenies with exponents `c = N + k` and `t = N`. -/
theorem exists_levelIsogeny_of_integralIntertwiners (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (X : B.Scheme) [ConnectedSpace X.1] [IsNoetherian X.1] (x : GeometricPoint X.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] [Algebra O E]
    (G : LAdicSheaf.CoefficientSheaf B X ℓ O) {r : ℕ}
    {ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ₀ : Continuous ρ₀)
    (φ : G.toLAdicSheaf ⟶ representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀)
    (ψ₀ : representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀ ⟶ G.toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ D : ℕ}
    (β : Module.Basis (Fin D) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))
    (τO : EtaleFundamentalGroup X.1 x →* GL (Fin mτ) (integralClosure ℤ_[ℓ] E))
    (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp τO).ker : Set
      (EtaleFundamentalGroup X.1 x)))
    (hRes : Continuous (restrictScalarsRepresentation B X x β τO)) (k : ℕ)
    (LQ : Matrix (Fin (mτ * D)) (Fin r) ℤ_[ℓ]) (LP : Matrix (Fin r) (Fin (mτ * D)) ℤ_[ℓ])
    (hLQ : ∀ g, LQ * (ρ₀ g).val = (restrictScalarsRepresentation B X x β τO g).val * LQ)
    (hLP : ∀ g, LP * (restrictScalarsRepresentation B X x β τO g).val = (ρ₀ g).val * LP)
    (hPQ : LP * LQ = ℓ ^ k • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]))
    (hQP : LQ * LP = ℓ ^ k • (1 : Matrix (Fin (mτ * D)) (Fin (mτ * D)) ℤ_[ℓ]))
    (hMQ : ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E),
      algebraMap O E o = algebraMap (integralClosure ℤ_[ℓ] E) E o' →
        LQ * representationLAdicSheafHomMatrix B X x hρ₀ hρ₀ (ψ₀ ≫ (G.act o).asHom ≫ φ) =
          ℓ ^ N • (coefficientScalarRingHom β mτ o' * LQ))
    (hMP : ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E),
      algebraMap O E o = algebraMap (integralClosure ℤ_[ℓ] E) E o' →
        representationLAdicSheafHomMatrix B X x hρ₀ hρ₀ (ψ₀ ≫ (G.act o).asHom ≫ φ) * LP =
          ℓ ^ N • (LP * coefficientScalarRingHom β mτ o')) :
    ∃ c t : ℕ, ∀ N' : ℕ,
      ∃ (h : (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N') ⟶
        (etaleModuleRestrictScalars
        ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
        (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
        ((lisseEtaleSheaf B X x
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
        (matrixContinuousModule.{u + 1, u + 1}
        (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
        ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
        (hτO (N' + 1)))))
        (h' : (etaleModuleRestrictScalars
          ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
          ((lisseEtaleSheaf B X x
          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1}
          (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
          ((Matrix.GeneralLinearGroup.map
          (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
          (hτO (N' + 1)))) ⟶ (LAdicSheaf.padicTower B X ℓ G.toLAdicSheaf).obj (op N')),
        h ≫ h' = ℓ ^ c • 𝟙 _ ∧ h' ≫ h = ℓ ^ c • 𝟙 _ ∧
        ∀ (o : O) (o' : integralClosure ℤ_[ℓ] E), algebraMap O E o = algebraMap
          (integralClosure ℤ_[ℓ] E) E o' →
          ℓ ^ t • ((LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N') ≫ h) =
            ℓ ^ t • (h ≫ (etaleModuleRestrictScalars
              ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
              (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
              ((etaleModuleSMul X.1
              (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
              ((lisseEtaleSheaf B X x
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
              (matrixContinuousModule.{u + 1, u + 1}
              (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
              ((Matrix.GeneralLinearGroup.map
              (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
              (hτO (N' + 1)))))) ∧
          ℓ ^ t • ((etaleModuleRestrictScalars
            ((Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).comp
            (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
            ((etaleModuleSMul X.1
            (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}) o')).app
            ((lisseEtaleSheaf B X x
            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})).obj
            (matrixContinuousModule.{u + 1, u + 1}
            (integralClosure ℤ_[ℓ] E ⧸ Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)})
            ((Matrix.GeneralLinearGroup.map
            (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (N' + 1)}))).comp τO)
            (hτO (N' + 1))))) ≫ h') =
            ℓ ^ t • (h' ≫ (LAdicSheaf.padicTowerMap (G.act o).asHom).app (op N'))
 :=
  exists_levelIsogeny_of_isogenies B ℓ X x E O G τO hτO
    (φ ≫ representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hRes LQ hLQ)
    (representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      hRes hρ₀ LP hLP ≫ ψ₀) (N + k) N
    (comp_comp_eq_pow_nsmul φ ψ₀ _ _ hφψ
      (representationLAdicSheafMap_comp_eq_nsmul_id B X x hρ₀ hRes LQ hLQ LP hLP _ hPQ))
    ((add_comm k N) ▸ comp_comp_eq_pow_nsmul _ _ ψ₀ φ
      (representationLAdicSheafMap_comp_eq_nsmul_id B X x hRes hρ₀ LP hLP LQ hLQ _ hQP) hψφ)
    (fun o' => representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hRes hRes
      (coefficientScalarRingHom β mτ o')
      (fun g => coefficientScalarRingHom_commute β mτ o' (τO g).val))
    (fun N' => padicTowerRestrictScalarsIntegersIso B X x β τO hRes N' (hτO (N' + 1)))
    (fun N' o' => padicTowerRestrictScalarsIntegersIso_smul B X x β τO hRes N' (hτO (N' + 1)) o')
    (fun o o' he => nsmul_comp_comp_eq_of_isogeny φ ψ₀ hφψ (G.act o).asHom _ _
      (comp_representationLAdicSheafMap_eq_nsmul B X x hρ₀ hRes _ LQ hLQ _ _ _ (hMQ o o' he)))
    (fun o o' he => nsmul_comp_comp_eq_of_isogeny' φ ψ₀ hφψ (G.act o).asHom _ _
      (nsmul_representationLAdicSheafMap_comp_eq B X x hρ₀ hRes _ LP hLP _ _ _ (hMP o o' he)))

/-- **The representation side of Laumon's level isogeny**
(`Stacks.EtaleCohomology.LaumonFourierRepresentationLevelIsogenyInput`), for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): with `β` the basis of `O_E` indexed like
`b`, `D, D'` the change of basis from `Res_b` to `Res_β`, the rational intertwiners
`D' Res_b(T⁻¹) Q` of `ρ₀` and `Res_β τ_E` and `P Res_b(T) D` back are mutually inverse and carry
`α(o)` to the matrix of `o`; their integral multiples
(`Stacks.EtaleCohomology.exists_integralIntertwiners`) give the level isogenies
(`Stacks.EtaleCohomology.exists_levelIsogeny_of_integralIntertwiners`). -/
theorem laumonFourierRepresentationLevelIsogenyInput :
    LaumonFourierRepresentationLevelIsogenyInput.{u} := by
  intro B ℓ _ _ _ _ X _ _ x E _ _ _ d b O _ _ _ _ hOE G r ρ hρ φ ψ₀ N hφψ hψφ mτ τ P Q hPQ hα hτ
    hQP τO T hT hτO
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hRes := continuous_restrictScalarsRepresentation_of_isOpen B X x
    (padicIntegerRingBasisOf b) τO hτO
  have hcoe : ∀ {a c : ℕ} (M : Matrix (Fin a) (Fin c) ℤ_[ℓ]),
      M.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) = M.map (PadicInt.Coe.ringHom (p := ℓ)) := fun _ => rfl
  refine (exists_restrictScalarsMatrix_conj b (padicIntegerRingBasisRatOf b) mτ).elim
    fun D hD => hD.elim fun D' hD' => ?_
  have hTT := (restrictScalarsMatrix_mul_inv_eq_one b T).1
  have hTT' := (restrictScalarsMatrix_mul_inv_eq_one b T).2
  have hPQr : (P * restrictScalarsMatrix b T.val * D) *
      (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q) = 1 := by
    calc _ = P * (restrictScalarsMatrix b T.val * (D * D') *
          restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD'.1, Matrix.mul_one, hTT, Matrix.mul_one, hPQ]
  have hQPr : (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q) *
      (P * restrictScalarsMatrix b T.val * D) = 1 := by
    calc _ = D' * (restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * (Q * P) *
          restrictScalarsMatrix b T.val) * D := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, hTT', Matrix.mul_one, hD'.2.1]
  have hρr : ∀ g, (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q) *
      (integralModel ρ hρ g).val.map (PadicInt.Coe.ringHom (p := ℓ)) =
      (restrictScalarsRepresentation B X x (padicIntegerRingBasisOf b) τO g).val.map
        (PadicInt.Coe.ringHom (p := ℓ)) *
        (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q) := fun g => by
    rw [restrictScalarsConj_mul_eq b (padicIntegerRingBasisRatOf b) D D' hD'.1 hD'.2.2 P Q hPQ T
      ((integralModel ρ hρ g).val.map (PadicInt.Coe.ringHom (p := ℓ))) (τ g).val (hτ g), ← hT g,
        restrictScalarsMatrix_map_padicIntegerRing, hcoe]
    rfl
  have hMr : ∀ i : {p : O × integralClosure ℤ_[ℓ] E // algebraMap O E p.1 = algebraMap
    (integralClosure ℤ_[ℓ] E) E p.2},
      (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q) *
        (representationLAdicSheafHomMatrix B X x (continuous_integralModel ρ hρ)
          (continuous_integralModel ρ hρ) (ψ₀ ≫ (G.act i.1.1).asHom ≫ φ)).map
            (PadicInt.Coe.ringHom (p := ℓ)) =
      ((ℓ : ℚ_[ℓ]) ^ N) • ((coefficientScalarRingHom (padicIntegerRingBasisOf b) mτ i.1.2).map
          (PadicInt.Coe.ringHom (p := ℓ)) *
        (D' * restrictScalarsMatrix b (T⁻¹ : GL (Fin mτ) E).val * Q)) := fun i => by
    have hMα : (representationLAdicSheafHomMatrix B X x (continuous_integralModel ρ hρ)
          (continuous_integralModel ρ hρ) (ψ₀ ≫ (G.act i.1.1).asHom ≫ φ)).map
            (PadicInt.Coe.ringHom (p := ℓ)) = ((ℓ : ℚ_[ℓ]) ^ N) •
          isogenyCoefficientAlgHom B X x G ρ hρ φ ψ₀ N E hφψ hψφ hOE (algebraMap O E i.1.1) := by
      rw [isogenyCoefficientAlgHom_algebraMap,
        smul_inv_smul₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero))]
      rfl
    have hsc : ∀ e : E, (T⁻¹ : GL (Fin mτ) E).val * Matrix.scalar (Fin mτ) e * T.val =
        Matrix.scalar (Fin mτ) e := fun e => by
      rw [Matrix.mul_assoc, (Matrix.scalar_commute e (fun r' => Commute.all e r') T.val).eq,
        ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hmap : Matrix.scalar (Fin mτ) (algebraMap (integralClosure ℤ_[ℓ] E) E i.1.2) =
        (Matrix.scalar (Fin mτ) i.1.2).map (algebraMap (integralClosure ℤ_[ℓ] E) E) := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
    rw [hMα, Matrix.mul_smul, restrictScalarsConj_mul_eq b (padicIntegerRingBasisRatOf b) D D'
      hD'.1 hD'.2.2 P Q hPQ T _ _ (hα _), hsc, i.2, hmap,
        restrictScalarsMatrix_map_padicIntegerRing,
      hcoe]
    rfl
  exact (exists_integralIntertwiners (fun g => (integralModel ρ hρ g).val)
    (fun g => (restrictScalarsRepresentation B X x (padicIntegerRingBasisOf b) τO g).val)
    (fun i : {p : O × integralClosure ℤ_[ℓ] E // algebraMap O E p.1 = algebraMap
      (integralClosure ℤ_[ℓ] E) E p.2} =>
      representationLAdicSheafHomMatrix B X x (continuous_integralModel ρ hρ)
        (continuous_integralModel ρ hρ) (ψ₀ ≫ (G.act i.1.1).asHom ≫ φ))
    (fun i => coefficientScalarRingHom (padicIntegerRingBasisOf b) mτ i.1.2) N _ _ hPQr hQPr hρr
    hMr).elim fun k hk => hk.elim fun LQ hLQ => hLQ.elim fun LP hLP =>
      exists_levelIsogeny_of_integralIntertwiners B ℓ X x E O G (continuous_integralModel ρ hρ) φ ψ₀
        N hφψ hψφ (padicIntegerRingBasisOf b) τO hτO hRes k LQ LP hLP.1 hLP.2.1 hLP.2.2.1
        hLP.2.2.2.1 (fun o o' he => hLP.2.2.2.2.1 ⟨(o, o'), he⟩)
        (fun o o' he => hLP.2.2.2.2.2 ⟨(o, o'), he⟩)

end Assembly

end Stacks.EtaleCohomology

end
