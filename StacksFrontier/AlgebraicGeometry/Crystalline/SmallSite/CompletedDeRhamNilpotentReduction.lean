module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsData
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection

/-!
# Completed de Rham complexes when `p` is nilpotent

When `p` is nilpotent in a ring `D`, say `p^k = 0`, the ideal `(p)^k` kills every `D`-module, so
every `D`-module is `p`-adically complete and the completed tensor product `M ⊗̂_D X` is the
uncompleted one `M ⊗_D X`.  This module uses this to compare the completed de Rham complex
`M ⊗^∧_D Ω^*_D` of a module with integrable connection with an uncompleted de Rham complex
`N ⊗_{R'} ⋀^* Ω'` along a ring map `θ : D → R'`, a semilinear map `λ : M → N` and semilinear maps
of forms `Θ_a : Ω^a_D → ⋀^a Ω'`.

## Main definitions

* `Crystalline.reduceTensor` — the map `M ⊗̂_D X → N ⊗_{R'} Y`, `m ⊗ x ↦ λ m ⊗ Φ x`, for `p`
  nilpotent in `D`.
* `Crystalline.ringDeRhamComplex` — the cochain complex `N ⊗_{R'} ⋀^* Ω'` with a given
  differential.
* `Crystalline.FormsData.ConnModule.reduceComplexHom` — the morphism of complexes
  `M ⊗^∧_D Ω^*_D → N ⊗_{R'} ⋀^* Ω'` given by the `reduceTensor`s.

## Main results

* `Crystalline.isAdicComplete_of_pow_eq_zero` — every module is `p`-adically complete when `p`
  is nilpotent.
* `Crystalline.bijective_reduceTensor` — `reduceTensor` is bijective when `θ`, `λ` and `Φ` are.
* `Crystalline.FormsData.ConnModule.reduceTensor_differential` — the `reduceTensor`s intertwine
  the differential of `M ⊗^∧_D Ω^*_D` with a differential `δ` given by the de Rham formula
  `δ(n ⊗ ω) = ∇(n) ∧ ω + n ⊗ dω` for a connection on `N` compatible with `∇` on `M`.
* `Crystalline.FormsData.ConnModule.isIso_reduceComplexHom` — the morphism of complexes is an
  isomorphism when `θ`, `λ` and every `Θ_a` are bijective.

Nothing here constructs the differential `δ`, the connection on `N` or proves that `δ` squares
to zero: these are data and hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

section Nilpotent

variable {p : ℕ} {D : Type*} [CommRing D]

/-- **If `p^k = 0` in `D`, then `(p)^k` kills every `D`-module.** -/
theorem pAdicIdeal_pow_smul_top_eq_bot {k : ℕ} (hk : (p : D) ^ k = 0) (X : Type*)
    [AddCommGroup X] [Module D X] :
    (pAdicIdeal (A := D) p) ^ k • (⊤ : Submodule D X) = ⊥ := by
  rw [pAdicIdeal, Ideal.span_singleton_pow, hk, Ideal.span_singleton_eq_bot.mpr rfl,
    Submodule.bot_smul]

/-- **When `p` is nilpotent in `D`, every `D`-module is `p`-adically complete.** -/
theorem isAdicComplete_of_pow_eq_zero (hpk : ∃ k : ℕ, (p : D) ^ k = 0) (X : Type*)
    [AddCommGroup X] [Module D X] : IsAdicComplete (pAdicIdeal (A := D) p) X := by
  obtain ⟨k, hk⟩ := hpk
  have hbot := pAdicIdeal_pow_smul_top_eq_bot hk X
  have hle : ∀ n, k ≤ n → (pAdicIdeal (A := D) p) ^ n • (⊤ : Submodule D X) = ⊥ := fun n hn ↦
    eq_bot_iff.mpr (hbot ▸ Submodule.smul_mono_left (Ideal.pow_le_pow_right hn))
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ⟨f k, fun n ↦ ?_⟩ }
  · have := hx k
    rwa [SModEq, hbot, Submodule.Quotient.eq, sub_zero, Submodule.mem_bot] at this
  · rcases le_total n k with h | h
    · exact hf h
    · have := hf h
      rw [SModEq, hbot, Submodule.Quotient.eq, Submodule.mem_bot, sub_eq_zero] at this
      rw [this]

/-- **When `p` is nilpotent in `D`, every `D`-module is its own `p`-adic completion**: the map
`AdicCompletion.of` is a linear equivalence. -/
def ofLinearEquivOfPowEqZero (hpk : ∃ k : ℕ, (p : D) ^ k = 0) (X : Type*) [AddCommGroup X]
    [Module D X] : X ≃ₗ[D] AdicCompletion (pAdicIdeal (A := D) p) X :=
  haveI := isAdicComplete_of_pow_eq_zero hpk X
  AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D) p) X

/-- The equivalence `ofLinearEquivOfPowEqZero` is `AdicCompletion.of`. -/
@[simp] theorem ofLinearEquivOfPowEqZero_apply (hpk : ∃ k : ℕ, (p : D) ^ k = 0) (X : Type*)
    [AddCommGroup X] [Module D X] (x : X) :
    ofLinearEquivOfPowEqZero hpk X x = AdicCompletion.of (pAdicIdeal (A := D) p) X x :=
  rfl

/-- **Two additive maps out of a completed tensor product agree as soon as they agree on pure
tensors**, when `p` is nilpotent in `D` (the target is arbitrary). -/
theorem completedTensor_addMonoidHom_ext_of_pow_eq_zero (hpk : ∃ k : ℕ, (p : D) ^ k = 0)
    {X M Z : Type*} [AddCommGroup X] [Module D X] [AddCommGroup M] [Module D M] [AddCommGroup Z]
    {f g : CompletedTensor p D X M →+ Z}
    (h : ∀ (m : M) (x : X), f (toCompletedTensor p D X M (m ⊗ₜ x)) =
      g (toCompletedTensor p D X M (m ⊗ₜ x))) : f = g := by
  refine AddMonoidHom.ext fun z ↦ ?_
  obtain ⟨t, rfl⟩ := (ofLinearEquivOfPowEqZero hpk (M ⊗[D] X)).surjective z
  rw [ofLinearEquivOfPowEqZero_apply]
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul m x => exact h m x
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Nilpotent

section Reduce

variable {p : ℕ} {D : Type*} [CommRing D] {R' : Type*} [CommRing R'] (θ : D →+* R')
  (hpk : ∃ k : ℕ, (p : D) ^ k = 0)
  {M X : Type*} [AddCommGroup M] [Module D M] [AddCommGroup X] [Module D X]
  {N Y : Type*} [AddCommGroup N] [Module R' N] [AddCommGroup Y] [Module R' Y]

/-- The bi-additive map `(m, x) ↦ λ m ⊗ Φ x` of two semilinear maps. -/
def reducePair (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) : M →+ X →+ N ⊗[R'] Y :=
  AddMonoidHom.mk' (fun m ↦ (TensorProduct.mk R' N Y (lam m)).toAddMonoidHom.comp
      Φ.toAddMonoidHom)
    (fun m m' ↦ AddMonoidHom.ext fun x ↦ by
      simp)

/-- The value of `reducePair` at `m` and `x` is `λ m ⊗ Φ x`. -/
@[simp] theorem reducePair_apply (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) (m : M) (x : X) :
    reducePair θ lam Φ m x = lam m ⊗ₜ Φ x := rfl

/-- **The uncompleted reduction** `M ⊗_D X → N ⊗_{R'} Y`, `m ⊗ x ↦ λ m ⊗ Φ x`: balanced since
`λ` and `Φ` are semilinear over the same ring map. -/
def reduceRaw (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) : (M ⊗[D] X) →+ N ⊗[R'] Y :=
  TensorProduct.liftAddHom (reducePair θ lam Φ) fun r m x ↦ by
    simp only [reducePair_apply, map_smulₛₗ, TensorProduct.smul_tmul]

/-- The uncompleted reduction on a pure tensor. -/
@[simp] theorem reduceRaw_tmul (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) (m : M) (x : X) :
    reduceRaw θ lam Φ (m ⊗ₜ x) = lam m ⊗ₜ Φ x := rfl

/-- **The reduction of a completed tensor product when `p` is nilpotent**:
`M ⊗̂_D X → N ⊗_{R'} Y`, `m ⊗ x ↦ λ m ⊗ Φ x`.  When `p` is nilpotent in `D` the completion
`M ⊗̂_D X` is `M ⊗_D X`, and this is the uncompleted reduction `reduceRaw` composed with the
inverse of `AdicCompletion.of`. -/
def reduceTensor (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) :
    CompletedTensor p D X M →+ N ⊗[R'] Y :=
  (reduceRaw θ lam Φ).comp (ofLinearEquivOfPowEqZero hpk (M ⊗[D] X)).symm.toAddMonoidHom

/-- **`reduceTensor` on a pure tensor**: `m ⊗ x ↦ λ m ⊗ Φ x`. -/
@[simp] theorem reduceTensor_of_tmul (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) (m : M) (x : X) :
    reduceTensor θ hpk lam Φ (toCompletedTensor p D X M (m ⊗ₜ x)) = lam m ⊗ₜ Φ x := by
  change reduceRaw θ lam Φ ((ofLinearEquivOfPowEqZero hpk (M ⊗[D] X)).symm
    (ofLinearEquivOfPowEqZero hpk (M ⊗[D] X) (m ⊗ₜ x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The inverse of a bijective semilinear map is semilinear over the inverse ring map, in the
form needed for balancing: `λ⁻¹ (θ s • n) = s • λ⁻¹ n`. -/
theorem symm_ofBijective_smul (lam : M →ₛₗ[θ] N) (hlam : Function.Bijective lam) (s : D)
    (n : N) :
    (AddEquiv.ofBijective (lam : M →+ N) hlam).symm (θ s • n) =
      s • (AddEquiv.ofBijective (lam : M →+ N) hlam).symm n := by
  apply (AddEquiv.ofBijective (lam : M →+ N) hlam).injective
  simp only [AddEquiv.apply_symm_apply]
  change θ s • n = lam (s • (AddEquiv.ofBijective (lam : M →+ N) hlam).symm n)
  rw [map_smulₛₗ]
  congr 1
  exact ((AddEquiv.ofBijective (lam : M →+ N) hlam).apply_symm_apply n).symm

/-- **The uncompleted reduction is bijective** when `θ`, `λ` and `Φ` are: its inverse is the
reduction along the inverse maps. -/
theorem bijective_reduceRaw (hθ : Function.Bijective θ) (lam : M →ₛₗ[θ] N)
    (hlam : Function.Bijective lam) (Φ : X →ₛₗ[θ] Y) (hΦ : Function.Bijective Φ) :
    Function.Bijective (reduceRaw θ lam Φ) := by
  set eL := AddEquiv.ofBijective (lam : M →+ N) hlam
  set eΦ := AddEquiv.ofBijective (Φ : X →+ Y) hΦ
  let pair : N →+ Y →+ M ⊗[D] X :=
    AddMonoidHom.mk' (fun n ↦ (TensorProduct.mk D M X (eL.symm n)).toAddMonoidHom.comp
        eΦ.symm.toAddMonoidHom)
      (fun n n' ↦ AddMonoidHom.ext fun y ↦ by simp)
  let inv : (N ⊗[R'] Y) →+ M ⊗[D] X := TensorProduct.liftAddHom pair fun r n y ↦ by
    obtain ⟨s, rfl⟩ := hθ.2 r
    change eL.symm (θ s • n) ⊗ₜ eΦ.symm y = eL.symm n ⊗ₜ eΦ.symm (θ s • y)
    rw [symm_ofBijective_smul θ lam hlam, symm_ofBijective_smul θ Φ hΦ, TensorProduct.smul_tmul]
  have hinv : ∀ n y, inv (n ⊗ₜ y) = eL.symm n ⊗ₜ eΦ.symm y := fun _ _ ↦ rfl
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, fun t ↦ ?_, fun t ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m x =>
      rw [reduceRaw_tmul, hinv]
      exact congrArg₂ (· ⊗ₜ ·) (eL.symm_apply_apply m) (eΦ.symm_apply_apply x)
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  · induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul n y =>
      rw [hinv, reduceRaw_tmul]
      exact congrArg₂ (· ⊗ₜ ·) (eL.apply_symm_apply n) (eΦ.apply_symm_apply y)
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **`reduceTensor` is bijective** when `θ`, `λ` and `Φ` are. -/
theorem bijective_reduceTensor (hθ : Function.Bijective θ) (lam : M →ₛₗ[θ] N)
    (hlam : Function.Bijective lam) (Φ : X →ₛₗ[θ] Y) (hΦ : Function.Bijective Φ) :
    Function.Bijective (reduceTensor θ hpk lam Φ) :=
  (bijective_reduceRaw θ hθ lam hlam Φ hΦ).comp
    (ofLinearEquivOfPowEqZero hpk (M ⊗[D] X)).symm.bijective

end Reduce

section RingDeRham

variable {R' : Type u} [CommRing R'] {Ω' : Type u} [AddCommGroup Ω'] [Module R' Ω']
  {N' : Type u} [AddCommGroup N'] [Module R' N']

/-- **The de Rham complex `N ⊗_{R'} ⋀^* Ω'`** with a given differential `δ` squaring to zero. -/
def ringDeRhamComplex (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun a ↦ AddCommGrpCat.of (N' ⊗[R'] ⋀[R']^a Ω'))
    (fun a ↦ AddCommGrpCat.ofHom (δ a))
    (fun a ↦ AddCommGrpCat.ext fun x ↦ DFunLike.congr_fun (hδsq a) x)

/-- The degree-`a` term of `ringDeRhamComplex` is `N ⊗_{R'} ⋀^a Ω'`. -/
theorem ringDeRhamComplex_X (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) (a : ℕ) :
    (ringDeRhamComplex δ hδsq).X a = AddCommGrpCat.of (N' ⊗[R'] ⋀[R']^a Ω') :=
  rfl

/-- The differential of `ringDeRhamComplex` is `δ`. -/
theorem ringDeRhamComplex_d (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) (a : ℕ) :
    (ringDeRhamComplex δ hδsq).d a (a + 1) = AddCommGrpCat.ofHom (δ a) :=
  CochainComplex.of_d (fun a ↦ AddCommGrpCat.of (N' ⊗[R'] ⋀[R']^a Ω'))
    (fun a ↦ AddCommGrpCat.ofHom (δ a)) a

end RingDeRham

namespace FormsData.ConnModule

variable {p : ℕ} {R : FormsData.{u} p} (M : ConnModule R)
  {R' : Type u} [CommRing R'] {Ω' : Type u} [AddCommGroup Ω'] [Module R' Ω']
  {N' : Type u} [AddCommGroup N'] [Module R' N']
  (θ : R.ring →+* R') (hpk : ∃ k : ℕ, (p : R.ring) ^ k = 0)

/-- **`reduceTensor` intertwines left wedging by a form**: the reduction of `m ⊗ (η ∧ ω)` is
`λ m ⊗ (Θ₁ η ∧ Θ ω)`. -/
theorem reduceTensor_wedgeMap (Θ1 : R.Om 1 →ₛₗ[θ] Ω') (Θ : ∀ a, R.Om a →ₛₗ[θ] ⋀[R']^a Ω')
    (hwedge : ∀ a (ω : R.Om a) (η : R.Om 1),
      Θ (a + 1) (R.wedge a ω η) = leftWedge a (Θ1 η) (Θ a ω))
    (lam : M.carrier →ₛₗ[θ] N') (a : ℕ) (ω : R.Om a)
    (z : CompletedTensor p R.ring (R.Om 1) M.carrier) :
    reduceTensor θ hpk lam (Θ (a + 1))
        (CompletedDeRham.wedgeMap p R.ring R.Om R.wedge M.carrier a ω z) =
      TensorProduct.map LinearMap.id ((leftWedge a).flip (Θ a ω))
        (reduceTensor θ hpk lam Θ1 z) := by
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero hpk
    (f := (reduceTensor θ hpk lam (Θ (a + 1))).comp
      (CompletedDeRham.wedgeMap p R.ring R.Om R.wedge M.carrier a ω).toAddMonoidHom)
    (g := (TensorProduct.map LinearMap.id ((leftWedge a).flip (Θ a ω))).toAddMonoidHom.comp
      (reduceTensor θ hpk lam Θ1)) fun m η ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        CompletedDeRham.wedgeMap_of_tmul, reduceTensor_of_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearMap.flip_apply, hwedge]
  exact DFunLike.congr_fun h z

/-- **The reductions intertwine the differentials**: if `∇'` on `N` is compatible with `∇` on `M`
(`∇' (λ m) = (λ ⊗ Θ₁)(∇ m)`), the forms with the wedge and the differentials, and `δ` is given by
the de Rham formula `δ(n ⊗ ω) = ∇'(n) ∧ ω + n ⊗ dω`, then the reduction of the differential of
`M ⊗^∧_D Ω^*_D` is `δ` of the reduction. -/
theorem reduceTensor_differential (Θ1 : R.Om 1 →ₛₗ[θ] Ω') (Θ : ∀ a, R.Om a →ₛₗ[θ] ⋀[R']^a Ω')
    (hwedge : ∀ a (ω : R.Om a) (η : R.Om 1),
      Θ (a + 1) (R.wedge a ω η) = leftWedge a (Θ1 η) (Θ a ω))
    (dK : ∀ a, (⋀[R']^a Ω') →+ ⋀[R']^(a + 1) Ω')
    (hd : ∀ a ω, Θ (a + 1) (R.deRham a ω) = dK a (Θ a ω))
    (lam : M.carrier →ₛₗ[θ] N') (nablaK : N' →+ N' ⊗[R'] Ω')
    (hnabla : ∀ m, nablaK (lam m) = reduceTensor θ hpk lam Θ1 (M.nabla m))
    (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδ : ∀ a n ω, δ a (n ⊗ₜ ω) =
      TensorProduct.map LinearMap.id ((leftWedge a).flip ω) (nablaK n) + n ⊗ₜ dK a ω)
    (a : ℕ) (x : CompletedTensor p R.ring (R.Om a) M.carrier) :
    reduceTensor θ hpk lam (Θ (a + 1))
        (CompletedDeRham.differential p R.ring R.Om R.wedge R.deRham M.carrier M.nabla
          R.isGradedLeibniz a x) =
      δ a (reduceTensor θ hpk lam (Θ a) x) := by
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero hpk
    (f := (reduceTensor θ hpk lam (Θ (a + 1))).comp
      (CompletedDeRham.differential p R.ring R.Om R.wedge R.deRham M.carrier M.nabla
        R.isGradedLeibniz a))
    (g := (δ a).comp (reduceTensor θ hpk lam (Θ a))) fun m ω ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply,
        CompletedDeRham.differential_of_tmul, map_add, reduceTensor_of_tmul, hδ, hnabla, hd,
        reduceTensor_wedgeMap M θ hpk Θ1 Θ hwedge lam]
  exact DFunLike.congr_fun h x

/-- **The reduction morphism of complexes** `M ⊗^∧_D Ω^*_D → N ⊗_{R'} ⋀^* Ω'` when `p` is
nilpotent in `D`: in degree `a` the map `m ⊗ ω ↦ λ m ⊗ Θ_a ω`. -/
def reduceComplexHom (Θ1 : R.Om 1 →ₛₗ[θ] Ω') (Θ : ∀ a, R.Om a →ₛₗ[θ] ⋀[R']^a Ω')
    (hwedge : ∀ a (ω : R.Om a) (η : R.Om 1),
      Θ (a + 1) (R.wedge a ω η) = leftWedge a (Θ1 η) (Θ a ω))
    (dK : ∀ a, (⋀[R']^a Ω') →+ ⋀[R']^(a + 1) Ω')
    (hd : ∀ a ω, Θ (a + 1) (R.deRham a ω) = dK a (Θ a ω))
    (lam : M.carrier →ₛₗ[θ] N') (nablaK : N' →+ N' ⊗[R'] Ω')
    (hnabla : ∀ m, nablaK (lam m) = reduceTensor θ hpk lam Θ1 (M.nabla m))
    (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδ : ∀ a n ω, δ a (n ⊗ₜ ω) =
      TensorProduct.map LinearMap.id ((leftWedge a).flip ω) (nablaK n) + n ⊗ₜ dK a ω)
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) :
    M.complex ⟶ ringDeRhamComplex δ hδsq :=
  { f := fun a ↦ AddCommGrpCat.ofHom (reduceTensor θ hpk lam (Θ a))
    comm' := by
      rintro a _ rfl
      have h1 : M.complex.d a (a + 1) = AddCommGrpCat.ofHom (CompletedDeRham.differential p
          R.ring R.Om R.wedge R.deRham M.carrier M.nabla R.isGradedLeibniz a) :=
        CompletedDeRham.complex_d _ _ _ _ _ _ _ _ _ a
      rw [h1, ringDeRhamComplex_d]
      exact AddCommGrpCat.ext fun x ↦
        (reduceTensor_differential M θ hpk Θ1 Θ hwedge dK hd lam nablaK hnabla δ hδ a x).symm }

/-- The degree-`a` component of the reduction morphism is `reduceTensor θ hpk λ Θ_a`. -/
@[simp] theorem reduceComplexHom_f (Θ1 : R.Om 1 →ₛₗ[θ] Ω') (Θ : ∀ a, R.Om a →ₛₗ[θ] ⋀[R']^a Ω')
    (hwedge : ∀ a (ω : R.Om a) (η : R.Om 1),
      Θ (a + 1) (R.wedge a ω η) = leftWedge a (Θ1 η) (Θ a ω))
    (dK : ∀ a, (⋀[R']^a Ω') →+ ⋀[R']^(a + 1) Ω')
    (hd : ∀ a ω, Θ (a + 1) (R.deRham a ω) = dK a (Θ a ω))
    (lam : M.carrier →ₛₗ[θ] N') (nablaK : N' →+ N' ⊗[R'] Ω')
    (hnabla : ∀ m, nablaK (lam m) = reduceTensor θ hpk lam Θ1 (M.nabla m))
    (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδ : ∀ a n ω, δ a (n ⊗ₜ ω) =
      TensorProduct.map LinearMap.id ((leftWedge a).flip ω) (nablaK n) + n ⊗ₜ dK a ω)
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) (a : ℕ) :
    (M.reduceComplexHom θ hpk Θ1 Θ hwedge dK hd lam nablaK hnabla δ hδ hδsq).f a =
      AddCommGrpCat.ofHom (reduceTensor θ hpk lam (Θ a)) :=
  rfl

/-- **The reduction morphism is an isomorphism** when `θ`, `λ` and every `Θ_a` are bijective. -/
theorem isIso_reduceComplexHom (Θ1 : R.Om 1 →ₛₗ[θ] Ω') (Θ : ∀ a, R.Om a →ₛₗ[θ] ⋀[R']^a Ω')
    (hwedge : ∀ a (ω : R.Om a) (η : R.Om 1),
      Θ (a + 1) (R.wedge a ω η) = leftWedge a (Θ1 η) (Θ a ω))
    (dK : ∀ a, (⋀[R']^a Ω') →+ ⋀[R']^(a + 1) Ω')
    (hd : ∀ a ω, Θ (a + 1) (R.deRham a ω) = dK a (Θ a ω))
    (lam : M.carrier →ₛₗ[θ] N') (nablaK : N' →+ N' ⊗[R'] Ω')
    (hnabla : ∀ m, nablaK (lam m) = reduceTensor θ hpk lam Θ1 (M.nabla m))
    (δ : ∀ a, (N' ⊗[R'] ⋀[R']^a Ω') →+ N' ⊗[R'] ⋀[R']^(a + 1) Ω')
    (hδ : ∀ a n ω, δ a (n ⊗ₜ ω) =
      TensorProduct.map LinearMap.id ((leftWedge a).flip ω) (nablaK n) + n ⊗ₜ dK a ω)
    (hδsq : ∀ a, (δ (a + 1)).comp (δ a) = 0) (hθ : Function.Bijective θ)
    (hlam : Function.Bijective lam) (hΘ : ∀ a, Function.Bijective (Θ a)) :
    IsIso (M.reduceComplexHom θ hpk Θ1 Θ hwedge dK hd lam nablaK hnabla δ hδ hδsq) := by
  have : ∀ a : ℕ,
      IsIso ((M.reduceComplexHom θ hpk Θ1 Θ hwedge dK hd lam nablaK hnabla δ hδ hδsq).f a) :=
    fun a ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_reduceTensor θ hpk hθ lam hlam (Θ a) (hΘ a))
  exact HomologicalComplex.Hom.isIso_of_components _

end FormsData.ConnModule

end Crystalline
