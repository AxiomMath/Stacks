module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientHigherDirectImageStalkLinearIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTorsionFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology

/-!
# Isogeny invariance of `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`, `E`-linearly, across two coefficient rings

Let `F` be an ℓ-adic sheaf with coefficients in a `ℤ_ℓ`-algebra `O` and `F'` one with
coefficients in a `ℤ_ℓ`-algebra `O'`, both rings having the same localization `E = O[1/ℓ] = O'[1/ℓ]`
(for instance two integral parts `O_P`, `O_{P'}` of a finite extension `E` of `ℚ_ℓ` attached to two
integral models of one representation, `Stacks.EtaleCohomology.conjIntegralSubring`). An isogeny
`φ : F ⟶ F'`, `ψ : F' ⟶ F` (both composites multiplication by `ℓᴺ`) commuting with the actions of
every pair `o ∈ O`, `o' ∈ O'` with the same image in `E` induces an `E`-linear isomorphism
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F' ⊗ ℚ_ℓ)` commuting with `π_X^*`: every `e ∈ E` has a multiple
`ℓᵐ e` coming from both `O` and `O'`. Hence the `E`-linear characteristic polynomials of `π_X^*`
agree. This is the lattice change step of the identification of the fibres of Laumon's family in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), where the two sheaves are built from two
integral models of the same `E`-linear representation.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius`.
* `CoefficientSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

namespace LAdicSheaf.CoefficientSheaf

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O O' : Type} [CommRing O] [Algebra ℤ_[ℓ] O] [CommRing O'] [Algebra ℤ_[ℓ] O']
  (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (F' : LAdicSheaf.CoefficientSheaf B X ℓ O')
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E] [Algebra O' E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E] [IsLocalization (Submonoid.powers (ℓ : O')) E]
  (φ : F.toLAdicSheaf ⟶ F'.toLAdicSheaf) (ψ : F'.toLAdicSheaf ⟶ F.toLAdicSheaf) (N : ℕ)
  (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
  (hφ : ∀ (o : O) (o' : O'), algebraMap O E o = algebraMap O' E o' →
    φ ≫ (F'.act o').asHom = (F.act o).asHom ≫ φ)

omit [Fact ℓ.Prime] [Algebra ℚ_[ℓ] E] in
/-- An element of a localization at the powers of `ℓ` has a multiple `ℓᵐ e` in the image. -/
theorem exists_natCast_pow_mul_eq_algebraMap {R : Type} [CommRing R] [Algebra R E]
    [IsLocalization (Submonoid.powers (ℓ : R)) E] (e : E) :
    ∃ (a : ℕ) (o : R), e * (ℓ : E) ^ a = algebraMap R E o := by
  obtain ⟨⟨o, ⟨_, a, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (ℓ : R)) e
  exact ⟨a, o, by simpa only [map_pow, map_natCast] using h⟩

omit [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] [Algebra ℤ_[ℓ] O'] [Algebra ℚ_[ℓ] E] in
/-- An element of `E` has a multiple `ℓᵐ e` coming from both `O` and `O'`. -/
theorem exists_natCast_pow_mul_eq_algebraMap₂ (e : E) :
    ∃ (m : ℕ) (o : O) (o' : O'), e * (ℓ : E) ^ m = algebraMap O E o ∧
      e * (ℓ : E) ^ m = algebraMap O' E o' := by
  obtain ⟨a, o, ho⟩ := exists_natCast_pow_mul_eq_algebraMap (ℓ := ℓ) E (R := O) e
  obtain ⟨b, o', ho'⟩ := exists_natCast_pow_mul_eq_algebraMap (ℓ := ℓ) E (R := O') e
  refine ⟨a + b, o * (ℓ : O) ^ b, o' * (ℓ : O') ^ a, ?_, ?_⟩
  · rw [map_mul, ← ho, pow_add, map_pow, map_natCast, mul_assoc]
  · rw [map_mul, ← ho', pow_add, map_pow, map_natCast, mul_assoc, mul_comm ((ℓ : E) ^ a)]

omit [Algebra ℚ_[ℓ] E] [IsLocalization (Submonoid.powers (ℓ : O)) E]
  [IsLocalization (Submonoid.powers (ℓ : O')) E] in
include hφ in
/-- The map induced by `φ` commutes with the actions of `o ∈ O`, `o' ∈ O'` with the same image
in `E`. -/
theorem rationalIsogeny_rationalIntegralRingHom (o : O) (o' : O')
    (h : algebraMap O E o = algebraMap O' E o')
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).hom (F.rationalIntegralRingHom f j kbar i o v) =
      F'.rationalIntegralRingHom f j kbar i o'
        ((LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
          h₁ h₂ i).hom v) := by
  have key : (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (F.act o).asHom i) ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) =
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (F'.act o').asHom i) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp,
      ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, hφ o o' h]
  exact congrArg (fun t => t.hom v) key

include hφ in
/-- **The map induced by `φ` is `E`-linear.** -/
theorem rationalIsogeny_rationalRingHom (e : E)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).hom (F.rationalRingHom f j kbar i E e v) =
      F'.rationalRingHom f j kbar i E e
        ((LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
          h₁ h₂ i).hom v) := by
  set c := (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
    h₁ h₂ i).hom.hom
  obtain ⟨m, o, o', ho, ho'⟩ := exists_natCast_pow_mul_eq_algebraMap₂ (ℓ := ℓ) E (O := O)
    (O' := O') e
  have hne : ((ℓ ^ m : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hR : ∀ {R : Type} [CommRing R] [Algebra ℤ_[ℓ] R] [Algebra R E]
      [IsLocalization (Submonoid.powers (ℓ : R)) E] (G : LAdicSheaf.CoefficientSheaf B X ℓ R)
      (w : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        G.toLAdicSheaf i),
      G.rationalRingHom f j kbar i E (e * (ℓ : E) ^ m) w =
        (ℓ ^ m : ℕ) • G.rationalRingHom f j kbar i E e w := by
    intro R _ _ _ _ G w
    rw [map_mul, Module.End.mul_apply, map_pow, map_natCast, ← Nat.cast_pow,
      Module.End.natCast_apply, map_nsmul]
  have hmain : (ℓ ^ m : ℕ) • c (F.rationalRingHom f j kbar i E e v) =
      (ℓ ^ m : ℕ) • F'.rationalRingHom f j kbar i E e (c v) := by
    rw [← map_nsmul c, ← hR F v, ← hR F' (c v), ho]
    conv_rhs => rw [ho.symm.trans ho']
    rw [F.rationalRingHom_algebraMap_apply, F'.rationalRingHom_algebraMap_apply]
    exact rationalIsogeny_rationalIntegralRingHom F F' f j kbar i E φ ψ N h₁ h₂ hφ o o'
      (ho.symm.trans ho') v
  have h := congrArg (fun w => ((ℓ ^ m : ℕ) : ℚ_[ℓ])⁻¹ • w) hmain
  simp only [← Nat.cast_smul_eq_nsmul ℚ_[ℓ], smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  exact h

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F' ⊗ ℚ_ℓ)`, `E`-linearly**, induced by an isogeny
commuting with the actions of `O` and `O'`. -/
public def rationalIsogenyLinearEquiv :
    letI := F.rationalCohomologyModule f j kbar i E
    letI := F'.rationalCohomologyModule f j kbar i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F'.toLAdicSheaf i :=
  letI := F.rationalCohomologyModule f j kbar i E
  letI := F'.rationalCohomologyModule f j kbar i E
  let c := (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
    h₁ h₂ i).toLinearEquiv
  { toFun := c
    map_add' := c.map_add
    map_smul' := fun e v => rationalIsogeny_rationalRingHom F F' f j kbar i E φ ψ N h₁ h₂ hφ e v
    invFun := c.symm
    left_inv := c.left_inv
    right_inv := c.right_inv }

public theorem rationalIsogenyLinearEquiv_apply
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    rationalIsogenyLinearEquiv F F' f j kbar i E φ ψ N h₁ h₂ hφ v =
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁
        h₂ i).hom v :=
  rfl

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The `E`-linear isogeny isomorphism commutes with `π_X^*`.** -/
public theorem rationalIsogenyLinearEquiv_frobenius
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    rationalIsogenyLinearEquiv F F' f j kbar i E φ ψ N h₁ h₂ hφ
        (F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard v) =
      F'.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard
        (rationalIsogenyLinearEquiv F F' f j kbar i E φ ψ N h₁ h₂ hφ v) := by
  have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B X ℓ f
    j kbar φ ψ N h₁ h₂ i (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)
  exact (congrArg (fun t => t.hom v) h).symm

include h₁ h₂ hφ in
/-- **Isogenous sheaves with coefficients have the same `E`-linear Frobenius characteristic
polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`**, for an isogeny commuting with the actions of the two
coefficient rings. -/
public theorem charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny :
    letI := F.rationalCohomologyModule f j kbar i E
    letI := F'.rationalCohomologyModule f j kbar i E
    ∀ [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F.toLAdicSheaf i)]
      [Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F'.toLAdicSheaf i)],
    (F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard).charpoly =
      (F'.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard).charpoly := by
  let := F.rationalCohomologyModule f j kbar i E
  let := F'.rationalCohomologyModule f j kbar i E
  intro _ _
  rw [← (rationalIsogenyLinearEquiv F F' f j kbar i E φ ψ N h₁ h₂ hφ).charpoly_conj]
  congr 1
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, rationalIsogenyLinearEquiv_frobenius, LinearEquiv.apply_symm_apply]

end LAdicSheaf.CoefficientSheaf

end Stacks.EtaleCohomology

end
