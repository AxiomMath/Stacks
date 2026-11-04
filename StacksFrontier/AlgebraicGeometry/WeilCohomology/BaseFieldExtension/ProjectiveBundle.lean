module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Coordinates
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.BundleBaseChange

/-!
# DRAFT: axiom (A3) descends along a field extension
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

section Rescale

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R] {M : Type*} [AddCommGroup M]
  [Module K M]

/-- Rescaling the class `ξ` by a nonzero scalar keeps the map `(a_i) ↦ ∑ ξ^i p(a_i)` bijective. -/
theorem bijective_sum_pow_smul {n : ℕ} (ξ : R) (p : M →ₗ[K] R) {c : K} (hc : c ≠ 0)
    (h : Bijective fun a : Fin n → M => ∑ i : Fin n, ξ ^ (i : ℕ) * p (a i)) :
    Bijective fun a : Fin n → M => ∑ i : Fin n, (c • ξ) ^ (i : ℕ) * p (a i) := by
  have key : (fun a : Fin n → M => ∑ i : Fin n, (c • ξ) ^ (i : ℕ) * p (a i)) =
      (fun a : Fin n → M => ∑ i : Fin n, ξ ^ (i : ℕ) * p (a i)) ∘
        fun a i => c ^ (i : ℕ) • a i := by
    funext a
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, map_smul, smul_mul_assoc, mul_smul_comm]
  rw [key]
  exact h.comp (Function.Bijective.piMap (f := fun (i : Fin n) (x : M) => c ^ (i : ℕ) • x) fun i =>
    MulAction.bijective₀ (pow_ne_zero _ hc))

end Rescale

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- The projective bundle formula in coordinates, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`, as a linear map. -/
def bundleFormulaU (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] :
    (Fin (r + 1) → 𝔇.H X) →ₗ[F] 𝔇.H (bundle X E r) :=
  ∑ i : Fin (r + 1), LinearMap.mulLeft F (𝔇.bundleClassU X E r ^ (i : ℕ)) ∘ₗ
    (𝔇.pull (bundleProj X E r)).toLinearMap ∘ₗ LinearMap.proj i

/-- `bundleFormulaU` sends `(a_i)` to `∑ ξ^i ∪ p^*(a_i)`. -/
theorem bundleFormulaU_apply (X : (SmoothProjectiveScheme k).FullSubcategory)
    (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (a : Fin (r + 1) → 𝔇.H X) :
    𝔇.bundleFormulaU X E r a =
      ∑ i : Fin (r + 1), 𝔇.bundleClassU X E r ^ (i : ℕ) * 𝔇.pull (bundleProj X E r) (a i) := by
  simp [bundleFormulaU]

/-- The projective bundle formula is bijective once it is in coordinates. -/
theorem bijective_bundleFormula_of_bijective_bundleFormulaU
    (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    (h : Bijective (𝔇.bundleFormulaU X E r)) : Bijective (𝔇.bundleFormula X E r) := by
  have key : 𝔇.bundleFormula X E r = (𝔇.κ _ 0).symm ∘ 𝔇.bundleFormulaU X E r ∘
      fun a i => 𝔇.κ X (-(i : ℤ)) (a i) := by
    funext a
    apply (𝔇.κ _ 0).injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, bundleFormulaU_apply]
    exact 𝔇.κ_bundleFormula X E r a
  rw [key]
  exact (𝔇.κ _ 0).symm.bijective.comp
    (h.comp (Function.Bijective.piMap (f := fun i : Fin (r + 1) => 𝔇.κ X (-(i : ℤ))) fun i =>
      (𝔇.κ X _).bijective))

/-- Pullback along an isomorphism is bijective. -/
theorem bijective_pull_of_iso {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    Bijective (𝔇.pull e.hom) := by
  refine ⟨fun a b hab => ?_, fun a => ⟨𝔇.pull e.inv a, ?_⟩⟩
  · have h := congrArg (𝔇.pull e.inv) hab
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← 𝔇.pull_comp, e.inv_hom_id, 𝔇.pull_id] at h
  · rw [← AlgHom.comp_apply, ← 𝔇.pull_comp, e.hom_inv_id, 𝔇.pull_id]
    rfl

end FirstChernClassData

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- `v ↦ ψ(1 ⊗ v)`, the comparison `H^*(X) → (H')^*(X_{k'})` as a ring map. -/
def ρ (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.H X →+* 𝔇'.H ((baseChange k k').obj X) :=
  (Φ.iso X).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := F) (A := F') (B := 𝔇.H X)).toRingHom

/-- `ρ` sends `v` to `ψ(1 ⊗ v)`. -/
theorem ρ_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (v : 𝔇.H X) :
    Φ.ρ X v = Φ.iso X (1 ⊗ₜ v) := rfl

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : ((toScheme k).obj X).Modules)
  (r : ℕ) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- The class `c₁^H(𝒪_P(1))`, carried to `𝐏(ℰ_{k'})`, is `u⁻¹` times `c₁^{H'}(𝒪(1))`. -/
theorem pull_ρ_bundleClassU (hA2' : 𝔇'.PullbackAxiom) :
    𝔇'.pull (bundleBaseChangeIso (k' := k') X E r).hom (Φ.ρ _ (𝔇.bundleClassU X E r)) =
      Φ.tateUnit⁻¹ • 𝔇'.bundleClassU ((baseChange k k').obj X) (baseChangeModule X E) r := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  have h1 : Φ.ρ _ (𝔇.bundleClassU X E r) =
      Φ.tateUnit⁻¹ • 𝔇'.κ _ 1 (Φ.twistOne _ (𝔇.bundleClass X E r)) := by
    rw [Φ.κ_twistOne, smul_smul, inv_mul_cancel₀ Φ.tateUnit_ne_zero, one_smul]
    rfl
  rw [h1, map_smul]
  congr 1
  rw [← FirstChernClassData.κ_pullTw]
  unfold FirstChernClassData.bundleClassU FirstChernClassData.bundleClass
  congr 1
  exact (congrArg (𝔇'.pullTw _ 1) (Φ.c₁_comm _ _ _)).trans ((hA2' _ _ _).trans
    (congrArg _ (picardClassOf_eq_of_iso _ _ _ _ _ (bundleBaseChangeTwistIso X E r))))

include Φ in
/-- **Axiom (A3) descends**: if `(H')^*` satisfies the projective bundle formula and `c₁^{H'}` is
compatible with pullbacks, then `H^*` satisfies the projective bundle formula. -/
theorem projectiveBundleAxiom (hA2' : 𝔇'.PullbackAxiom) (hA3' : 𝔇'.ProjectiveBundleAxiom) :
    𝔇.ProjectiveBundleAxiom := by
  intro X E r hE
  apply 𝔇.bijective_bundleFormula_of_bijective_bundleFormulaU
  apply bijective_of_bijective_baseChange F'
  set e := bundleBaseChangeIso (k' := k') X E r
  set X' := (baseChange k k').obj X
  -- the formula for `𝐏(ℰ)_{k'}`, with the carried class
  let U' : (Fin (r + 1) → 𝔇'.H X') →ₗ[F'] 𝔇'.H ((baseChange k k').obj (bundle X E r)) :=
    ∑ i : Fin (r + 1), LinearMap.mulLeft F' (Φ.ρ _ (𝔇.bundleClassU X E r) ^ (i : ℕ)) ∘ₗ
      (𝔇'.pull ((baseChange k k').map (bundleProj X E r))).toLinearMap ∘ₗ LinearMap.proj i
  have hU' : 𝔇'.pull e.hom ∘ U' = fun b : Fin (r + 1) → 𝔇'.H X' =>
      ∑ i : Fin (r + 1), (Φ.tateUnit⁻¹ • 𝔇'.bundleClassU X' (baseChangeModule X E) r) ^ (i : ℕ) *
        𝔇'.pull (bundleProj X' (baseChangeModule X E) r) (b i) := by
    funext b
    simp only [Function.comp_apply, U', LinearMap.sum_apply,
      LinearMap.coe_comp, LinearMap.coe_proj, Function.eval, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← AlgHom.comp_apply, ← 𝔇'.pull_comp, bundleBaseChangeIso_hom_bundleProj]
    exact congrArg₂ _ (congrArg (· ^ (i : ℕ)) (pull_ρ_bundleClassU Φ X E r hA2')) rfl
  have hbU' : Bijective U' := by
    have h := bijective_sum_pow_smul (K := F') _
      (𝔇'.pull (bundleProj X' (baseChangeModule X E) r)).toLinearMap
      (inv_ne_zero Φ.tateUnit_ne_zero)
      (𝔇'.bijective_bundleFormulaU hA3' X' (baseChangeModule X E) r)
    have h' : Bijective (𝔇'.pull e.hom ∘ U') := by rw [hU']; exact h
    exact (Bijective.of_comp_iff' (𝔇'.bijective_pull_of_iso e) _).mp h'
  -- the comparison of the two formulas
  let πX : F' ⊗[F] (Fin (r + 1) → 𝔇.H X) ≃ₗ[F'] (Fin (r + 1) → 𝔇'.H X') :=
    (TensorProduct.piRight F F' F' fun _ : Fin (r + 1) => 𝔇.H X).trans
      (LinearEquiv.piCongrRight fun _ => (Φ.iso X).toLinearEquiv)
  have hcomm : ∀ x, Φ.iso _ ((𝔇.bundleFormulaU X E r).baseChange F' x) = U' (πX x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, iso_tmul, FirstChernClassData.bundleFormulaU_apply,
        ← ρ_apply, map_sum]
      simp only [πX, U', LinearEquiv.trans_apply, TensorProduct.piRight_apply,
        TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
        AlgEquiv.toLinearEquiv_apply, LinearMap.sum_apply, LinearMap.coe_comp,
        LinearMap.coe_proj, Function.comp_apply, Function.eval, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, map_mul, map_pow, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [iso_tmul, map_smul, mul_smul_comm, ρ_apply, ρ_apply, Φ.iso_natural]
    | add x y hx hy => simp only [map_add, hx, hy]
  have : (𝔇.bundleFormulaU X E r).baseChange F' = (Φ.iso _).symm ∘ U' ∘ πX := by
    funext x
    simp [← hcomm]
  rw [this]
  exact (Φ.iso _).symm.bijective.comp (hbU'.comp πX.bijective)

end FieldExtensionComparison

end Stacks.WeilCohomology
