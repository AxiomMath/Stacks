module

public import StacksFrontier.RingTheory.SerreIntersection.DiagonalTor
public import StacksFrontier.RingTheory.Flat.LocalCriterion
public import StacksFrontier.Homology.Tor.Presentation

/-!
# Flatness of a base change through the second ring map
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.SerreIntersection

section Flatness

variable {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] (α β : R →+* B) (ψ : B →+* R)
  (hψα : ∀ r, ψ (α r) = r) (hker : RingHom.ker ψ ≤ Ideal.map β (maximalIdeal R))

/-- For a `B`-module `P` viewed as an `R`-module through `β`, multiplication by an element of
`β(𝔪) B` carries `P` into `𝔪 P`. -/
theorem smul_mem_smul_top_of_mem_map {P : Type u} [AddCommGroup P] [Module B P] {z : B}
    (hz : z ∈ Ideal.map β (maximalIdeal R)) (y : Twist β P) :
    z • y ∈ (maximalIdeal R) • (⊤ : Submodule R (Twist β P)) := by
  induction hz using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add x x' _ _ hx hx' =>
    rw [add_smul]
    exact Submodule.add_mem _ (hx y) (hx' y)
  | smul b x _ hx =>
    rw [smul_eq_mul, mul_comm, mul_smul]
    exact hx (b • y)

/-- The contraction along `ψ`, on the twist of the base change along `β`. -/
def contractT (X : Type u) [AddCommGroup X] [Module R X] : Twist β (Ext α X) →+ X where
  toFun y := contract α ψ hψα X y
  map_zero' := map_zero (contract α ψ hψα X)
  map_add' x y := map_add (contract α ψ hψα X) x y

omit [IsLocalRing R] in
/-- The contraction `contractT` is semilinear along `ψ`:
`contractT (b • y) = ψ b • contractT y`. -/
theorem contractT_smul {X : Type u} [AddCommGroup X] [Module R X] (b : B)
    (y : Twist β (Ext α X)) : contractT α β ψ hψα X (b • y) = ψ b • contractT α β ψ hψα X y :=
  contract_smul α ψ hψα X b y

/-- The contraction carries `𝔪 · (B ⊗_{R, α} X)` (twisted along `β`) into `I X`, for an ideal `I`
containing `ψ (β 𝔪)`. -/
theorem contract_mem_smul_top_of_mem_smul_top (I : Ideal R)
    (hI : ∀ r ∈ maximalIdeal R, ψ (β r) ∈ I) {X : Type u} [AddCommGroup X] [Module R X]
    {y : Twist β (Ext α X)} (hy : y ∈ (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α X)))) :
    contractT α β ψ hψα X y ∈ I • (⊤ : Submodule R X) := by
  refine Submodule.smul_induction_on hy (fun r hr y _ => ?_) (fun x y hx hy => ?_)
  · change contractT α β ψ hψα X (β r • y) ∈ _
    rw [contractT_smul]
    exact Submodule.smul_mem_smul (hI r hr) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- `1 ⊗ I X` lies in `𝔪 · (B ⊗_{R, α} X)` (twisted along `β`) when `α I ⊆ β(𝔪) B`. -/
theorem mk_one_tmul_mem_smul_top (I : Ideal R)
    (hIα : ∀ r ∈ I, α r ∈ Ideal.map β (maximalIdeal R)) {X : Type u} [AddCommGroup X]
    [Module R X] {x : X} (hx : x ∈ I • (⊤ : Submodule R X)) :
    Twist.mk β (Twist.mk α (1 : B) ⊗ₜ x : Ext α X) ∈
      (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α X))) := by
  refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · have h : (Twist.mk α (1 : B) ⊗ₜ (r • x) : Ext α X) =
        α r • (Twist.mk α (1 : B) ⊗ₜ x : Ext α X) := by
      rw [← TensorProduct.smul_tmul, Twist.rsmul_mk, TensorProduct.smul_tmul', Twist.smul_mk]
    rw [h]
    exact smul_mem_smul_top_of_mem_map β (hIα r hr) _
  · rw [TensorProduct.tmul_add, ← Twist.mk_add]
    exact Submodule.add_mem _ hx hy

include hker in
/-- When `ker ψ ⊆ β(𝔪) B`, every `y ∈ B ⊗_{R, α} X` is congruent to `1 ⊗ contract y` modulo
`𝔪 · (B ⊗_{R, α} X)` (twisted along `β`). -/
theorem sub_mem_smul_top {X : Type u} [AddCommGroup X] [Module R X] (y : Ext α X) :
    Twist.mk β y - Twist.mk β (Twist.mk α (1 : B) ⊗ₜ contract α ψ hψα X y : Ext α X) ∈
      (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α X))) := by
  induction y using TensorProduct.inductionOn with
  | tmul b x =>
    obtain ⟨b, rfl⟩ : ∃ b' : B, Twist.mk α b' = b := ⟨b, rfl⟩
    have hb : b - α (ψ b) ∈ Ideal.map β (maximalIdeal R) :=
      hker (by rw [RingHom.mem_ker, map_sub, hψα, sub_self])
    have heq : Twist.mk β (Twist.mk α b ⊗ₜ x : Ext α X) -
        Twist.mk β (Twist.mk α (1 : B) ⊗ₜ contract α ψ hψα X (Twist.mk α b ⊗ₜ x) : Ext α X) =
        (b - α (ψ b)) • Twist.mk β (Twist.mk α (1 : B) ⊗ₜ x : Ext α X) := by
      rw [contract_tmul, ← TensorProduct.smul_tmul, Twist.rsmul_mk, smul_eq_mul, mul_one,
        sub_smul, Twist.smul_mk, Twist.smul_mk, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        Twist.smul_mk, Twist.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    rw [heq]
    exact smul_mem_smul_top_of_mem_map β hb _
  | add y y' hy hy' =>
    have : Twist.mk β (y + y') - Twist.mk β (Twist.mk α (1 : B) ⊗ₜ
        contract α ψ hψα X (y + y') : Ext α X) =
        (Twist.mk β y - Twist.mk β (Twist.mk α (1 : B) ⊗ₜ contract α ψ hψα X y : Ext α X)) +
        (Twist.mk β y' - Twist.mk β (Twist.mk α (1 : B) ⊗ₜ contract α ψ hψα X y' : Ext α X)) := by
      rw [map_add, TensorProduct.tmul_add, ← Twist.mk_add, ← Twist.mk_add]
      abel
    rw [this]
    exact Submodule.add_mem _ hy hy'

omit [IsLocalRing R] in
/-- The contraction `contractT` is natural in `X`: it commutes with the maps induced by an
`R`-linear map `f : X₁ → X₂`. -/
theorem contractT_twistMap {X₁ X₂ : Type u} [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂]
    [Module R X₂] (f : X₁ →ₗ[R] X₂) (y : Twist β (Ext α X₁)) :
    contractT α β ψ hψα X₂ (twistMap β (extMap α f) y) = f (contractT α β ψ hψα X₁ y) :=
  contract_extMap α ψ hψα f y

/-- The residue field as the quotient by the maximal ideal, `R`-linearly. -/
def residueFieldEquivQuotient : ResidueField R ≃ₗ[R] R ⧸ maximalIdeal R where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [CommRing B] in
/-- The identification `κ ⊗_R Y ≃ Y / 𝔪 Y` sends `1 ⊗ y` to the class of `y`. -/
theorem quotTensor_residueField_one_tmul {Y : Type u} [AddCommGroup Y] [Module R Y] (y : Y) :
    ((TensorProduct.congr (residueFieldEquivQuotient (R := R)) (LinearEquiv.refl R Y)).trans
      (TensorProduct.quotTensorEquivQuotSMul Y (maximalIdeal R))) ((1 : ResidueField R) ⊗ₜ y) =
      Submodule.Quotient.mk y := by
  rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _

include hψα hker in
/-- Base change along `α` followed by restriction along `β` is injective on maps after reduction
modulo the maximal ideal of `R`, for maps `f` which are injective modulo an ideal `I` (that is,
`f⁻¹(I X₂) = I X₁`) with `ψ (β 𝔪) ⊆ I` and `α I ⊆ β(𝔪) B`: through the contraction along `ψ`,
`κ ⊗_{R, β} (B ⊗_{R, α} X)` is a quotient of `X / I X`. For `I = 0` this is the case of a
retraction `ψ` with kernel `β(𝔪) B`, where `κ ⊗_{R, β} (B ⊗_{R, α} X) = X`. -/
theorem lTensor_residueField_twistMap_injective_of_smul_top (I : Ideal R)
    (hI : ∀ r ∈ maximalIdeal R, ψ (β r) ∈ I)
    (hIα : ∀ r ∈ I, α r ∈ Ideal.map β (maximalIdeal R)) {X₁ X₂ : Type u} [AddCommGroup X₁]
    [Module R X₁] [AddCommGroup X₂] [Module R X₂] (f : X₁ →ₗ[R] X₂)
    (hf : ∀ x, f x ∈ I • (⊤ : Submodule R X₂) → x ∈ I • (⊤ : Submodule R X₁)) :
    Function.Injective (LinearMap.lTensor (ResidueField R) (twistMap β (extMap α f))) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  let e₁ := (TensorProduct.congr (residueFieldEquivQuotient (R := R))
    (LinearEquiv.refl R (Twist β (Ext α X₁)))).trans
    (TensorProduct.quotTensorEquivQuotSMul (Twist β (Ext α X₁)) (maximalIdeal R))
  let e₂ := (TensorProduct.congr (residueFieldEquivQuotient (R := R))
    (LinearEquiv.refl R (Twist β (Ext α X₂)))).trans
    (TensorProduct.quotTensorEquivQuotSMul (Twist β (Ext α X₂)) (maximalIdeal R))
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e₁ t)
  have ht' : t = (1 : ResidueField R) ⊗ₜ y := by
    apply e₁.injective
    rw [← hy]
    exact (quotTensor_residueField_one_tmul y).symm
  have h2 : Submodule.Quotient.mk (p := (maximalIdeal R) • (⊤ : Submodule R
      (Twist β (Ext α X₂)))) (twistMap β (extMap α f) y) = 0 := by
    have := congrArg e₂ ht
    rw [ht', LinearMap.lTensor_tmul, map_zero] at this
    rw [← this]
    exact (quotTensor_residueField_one_tmul _).symm
  rw [Submodule.Quotient.mk_eq_zero] at h2
  have h3 : contractT α β ψ hψα X₁ y ∈ I • (⊤ : Submodule R X₁) := by
    apply hf
    rw [← contractT_twistMap]
    exact contract_mem_smul_top_of_mem_smul_top α β ψ hψα I hI h2
  have h4 : y - Twist.mk β (Twist.mk α (1 : B) ⊗ₜ contractT α β ψ hψα X₁ y : Ext α X₁) ∈
      (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α X₁))) :=
    sub_mem_smul_top α β ψ hψα hker y
  have h5 : y ∈ (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α X₁))) := by
    have := Submodule.add_mem _ h4 (mk_one_tmul_mem_smul_top α β I hIα h3)
    rwa [sub_add_cancel] at this
  rw [ht']
  apply e₁.injective
  rw [map_zero, quotTensor_residueField_one_tmul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr h5

end Flatness

section Assembly

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B)

/-- The base change along `α` of a finite free module, twisted along `β`, is a finite product
of copies of `B` twisted along `β`. -/
def twistExtPiEquiv (j : ℕ) : Twist β (Ext α (Fin j → R)) ≃ₗ[R] (Fin j → Twist β B) :=
  (Twist.congr (piScalarRightOver (B := B) (Twist α B) (Fin j))).trans
    { toFun v := v
      invFun v := v
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }

/-- If `B` is flat over `R` through `β`, then so is the base change `B ⊗_{R, α} R^j` of a finite
free module. -/
theorem flat_twist_ext_pi [Module.Flat R (Twist β B)] (j : ℕ) :
    Module.Flat R (Twist β (Ext α (Fin j → R))) := by
  classical
  have : Module.Flat R (Π₀ _ : Fin j, Twist β B) := inferInstance
  exact Module.Flat.of_linearEquiv
    ((twistExtPiEquiv α β j).trans DFinsupp.linearEquivFunOnFintype.symm)

/-- The base change `B ⊗_{R, α} M` of a finite `R`-module `M` is a finite `B`-module. -/
theorem finite_ext (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite B (Ext α M) := by
  obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' R M
  have : Module.Finite B (Ext α (Fin j → R)) := by
    have : Module.Finite B (Fin j → Twist α B) := by
      have : Module.Finite B (Twist α B) := Module.Finite.equiv (Twist.of α B)
      infer_instance
    exact Module.Finite.equiv (piScalarRightOver (B := B) (Twist α B) (Fin j)).symm
  exact Module.Finite.of_surjective (extMap α p) (LinearMap.lTensor_surjective _ hp)

/-- **Tor independence of the two base changes.** Let `α, β : R → B` be flat local maps of
Noetherian local rings, let `ψ : B → R` be a retraction of `α` whose kernel lies in `β(𝔪) B`, and
let `I ⊆ R` be an ideal with `ψ (β 𝔪) ⊆ I` and `α I ⊆ β(𝔪) B`. Then for every finite `R`-module
`M` whose finite free covers `R^j → M` have kernels `K` with `K ∩ I R^j = I K` the base change
`B ⊗_{R, α} M` is flat over `R` through `β`. By the local criterion (Stacks 00MK) it suffices
that `Tor₁^R(κ, B ⊗_{R, α} M)` vanishes; along a finite free cover of `M` the long exact sequence
reduces this to the injectivity of `κ ⊗_{R, β} (B ⊗_{R, α} -)` on the cover, which the
contraction along `ψ` reduces to the injectivity of `K / I K → R^j / I R^j`. -/
theorem flat_twist_ext_of_smul_top [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing B]
    [IsNoetherianRing B] [IsLocalHom β] [Module.Flat R (Twist α B)] [Module.Flat R (Twist β B)]
    (ψ : B →+* R) (hψα : ∀ r, ψ (α r) = r)
    (hker : RingHom.ker ψ ≤ Ideal.map β (maximalIdeal R)) (I : Ideal R)
    (hI : ∀ r ∈ maximalIdeal R, ψ (β r) ∈ I)
    (hIα : ∀ r ∈ I, α r ∈ Ideal.map β (maximalIdeal R))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ (j : ℕ) (p : (Fin j → R) →ₗ[R] M) (x : LinearMap.ker p),
      (x : Fin j → R) ∈ I • (⊤ : Submodule R (Fin j → R)) →
        x ∈ I • (⊤ : Submodule R (LinearMap.ker p))) :
    Module.Flat R (Twist β (Ext α M)) := by
  obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' R M
  let g₁ := twistMap β (extMap α (LinearMap.ker p).subtype)
  let g₂ := twistMap β (extMap α p)
  have hexact : Function.Exact g₁ g₂ :=
    lTensor_exact (Twist α B) (LinearMap.exact_subtype_ker_map p) hp
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom g₁) (ModuleCat.ofHom g₂) (by
      ext x
      exact hexact.apply_apply_eq_zero x)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact _ hexact
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))
    (LinearMap.lTensor_surjective _ hp)
  have : Module.Flat R S.X₂ := flat_twist_ext_pi α β j
  let κ := ModuleCat.of R (ResidueField R)
  have hex := Stacks.Tor.Tor'_composableArrows_exact_second hS κ 0
  have h2 : IsZero (((Tor' (ModuleCat.{u} R) 1).obj κ).obj S.X₂) :=
    Stacks.Tor.isZero_Tor'_succ_obj_of_flat _ _ 0
  have hδmono : Mono (Stacks.Tor.Tor'δSecond hS κ 0) :=
    (hex.exact' 1 2 3).mono_g (h2.eq_of_src _ _)
  have hmono0 : Mono (((Tor' (ModuleCat.{u} R) 0).obj κ).map S.f) := by
    have hw : Mono (κ ◁ S.f) := by
      rw [ModuleCat.mono_iff_injective]
      exact lTensor_residueField_twistMap_injective_of_smul_top α β ψ hψα hker I hI hIα _
        (hM j p)
    have hnat := fromLeftDerivedZero_natural ((tensoringRight (ModuleCat.{u} R)).map S.f) κ
    have hw' : Mono (((tensoringRight (ModuleCat.{u} R)).map S.f).app κ) := hw
    have h3 : Mono ((NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map S.f) 0).app κ ≫
        ((tensoringRight (ModuleCat.{u} R)).obj S.X₂).fromLeftDerivedZero.app κ) := by
      rw [hnat]
      exact mono_comp _ _
    have h4 : Mono (((Tor' (ModuleCat.{u} R) 0).obj κ).map S.f ≫
        ((tensoringRight (ModuleCat.{u} R)).obj S.X₂).fromLeftDerivedZero.app κ) := h3
    exact mono_of_mono _ (((tensoringRight (ModuleCat.{u} R)).obj S.X₂).fromLeftDerivedZero.app κ)
  have hδzero : Stacks.Tor.Tor'δSecond hS κ 0 = 0 := by
    rw [← cancel_mono (((Tor' (ModuleCat.{u} R) 0).obj κ).map S.f), zero_comp]
    exact hex.toIsComplex.zero 2
  have hTor : IsZero (((Tor' (ModuleCat.{u} R) 1).obj κ).obj S.X₃) :=
    IsZero.of_mono_eq_zero _ hδzero
  let : Algebra R B := β.toAlgebra
  have : IsLocalHom (algebraMap R B) := ‹IsLocalHom β›
  have : IsScalarTower R B (Twist β (Ext α M)) :=
    ⟨fun r b y => by
      change (β r * b) • y = β r • b • y
      rw [mul_smul]⟩
  have : Module.Finite B (Ext α M) := finite_ext α M
  have : Module.Finite B (Twist β (Ext α M)) := Module.Finite.equiv (Twist.of β (Ext α M))
  exact Module.Flat.of_isZero_Tor'_one_residueField B (Twist β (Ext α M)) hTor

/-- **Tor independence of the two base changes**, for a retraction `ψ : B → R` of `α` whose
kernel is generated by the image under `β` of the maximal ideal of `R`: for every finite
`R`-module `M` the base change `B ⊗_{R, α} M` is flat over `R` through `β`. This is
`flat_twist_ext_of_smul_top` with `I = 0`. -/
theorem flat_twist_ext [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom β] [Module.Flat R (Twist α B)] [Module.Flat R (Twist β B)] (ψ : B →+* R)
    (hψα : ∀ r, ψ (α r) = r) (hker : RingHom.ker ψ = Ideal.map β (maximalIdeal R))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Flat R (Twist β (Ext α M)) := by
  refine flat_twist_ext_of_smul_top α β ψ hψα hker.le ⊥ (fun r hr => ?_) (fun r hr => ?_) M
    (fun j p x hx => ?_)
  · rw [Ideal.mem_bot]
    exact RingHom.mem_ker.mp (hker ▸ Ideal.mem_map_of_mem β hr)
  · rw [Ideal.mem_bot.mp hr, map_zero]
    exact Submodule.zero_mem _
  · rw [Submodule.bot_smul, Submodule.mem_bot] at hx ⊢
    exact Subtype.ext hx

end Assembly

end Stacks.SerreIntersection
