module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

/-!
# Flatness of quotient modules and intersections of ideals

Let `R` be a commutative ring, `M` an `R`-module and `I₁, I₂` ideals of `R`. If `M / I₁ M` is flat
over `R / I₁` and `M / I₂ M` is flat over `R / I₂`, then `M / (I₁ ⊓ I₂) M` is flat over
`R / (I₁ ⊓ I₂)`.

## Main results

* `Module.Flat.of_inf_eq_bot`: if `I₁ ⊓ I₂ = ⊥`, `M / I₁ M` is flat over `R / I₁` and `M / I₂ M` is
  flat over `R / I₂`, then `M` is flat over `R`.
* `Module.Flat.quotient_inf`: if `M / I₁ M` is flat over `R / I₁` and `M / I₂ M` is flat over
  `R / I₂`, then `M / (I₁ ⊓ I₂) M` is flat over `R / (I₁ ⊓ I₂)`.
-/

@[expose] public section

open scoped TensorProduct

/-- Let `M ⧸ I • ⊤` be flat over `R ⧸ I` and let `g : N → R ⧸ I` be an injective `R ⧸ I`-linear
map. Then `rTensor M g : N ⊗[R] M → (R ⧸ I) ⊗[R] M` is injective. -/
lemma Module.Flat.rTensor_restrictScalars_injective {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) {N : Type*} [AddCommGroup N]
    [Module (R ⧸ I) N] [Module R N] [IsScalarTower R (R ⧸ I) N] (g : N →ₗ[R ⧸ I] (R ⧸ I))
    (hg : Function.Injective g) :
    Function.Injective (LinearMap.rTensor M (g.restrictScalars R)) := by
  let e : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul M I)
  let G : N ⊗[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) :=
    (TensorProduct.lid (R ⧸ I) _).toLinearMap ∘ₗ LinearMap.rTensor _ g
  let Φ : N ⊗[R] M ≃ₗ[R ⧸ I] N ⊗[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) N M).symm.trans
      (LinearEquiv.lTensor N e)
  have key : ((TensorProduct.quotTensorEquivQuotSMul M I) ∘
        (LinearMap.rTensor M (g.restrictScalars R)))
      = (G ∘ Φ) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add a b ha hb =>
        simp only [Function.comp_apply, map_add] at *
        rw [ha, hb]
    | tmul n m =>
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (g n)
        simp only [Function.comp_apply, LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply]
        rw [← hr, TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
        show _ = G (Φ (n ⊗ₜ[R] m))
        simp only [Φ, LinearEquiv.trans_apply,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul]
        change _ = G (n ⊗ₜ[R ⧸ I] (e ((1 : R ⧸ I) ⊗ₜ[R] m)))
        have he1 : e ((1 : R ⧸ I) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
          change (TensorProduct.quotTensorEquivQuotSMul M I) ((1 : R ⧸ I) ⊗ₜ[R] m) = _
          rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
            one_smul]
        rw [he1]
        simp only [G, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
          TensorProduct.lid_tmul]
        rw [← hr]
        rfl
  refine Function.Injective.of_comp (f := TensorProduct.quotTensorEquivQuotSMul M I) ?_
  rw [key]
  exact ((TensorProduct.lid (R ⧸ I) _).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap g hg)).comp Φ.injective

/-- Let `M ⧸ I • ⊤` be flat over `R ⧸ I`, let `N` be killed by `I` and let `f : N → R ⧸ I` be an
injective `R`-linear map. Then `rTensor M f` is injective. -/
lemma Module.Flat.rTensor_injective_of_isTorsionBySet {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) {N : Type*} [AddCommGroup N]
    [Module R N] (hN : Module.IsTorsionBySet R N (I : Set R)) (f : N →ₗ[R] (R ⧸ I))
    (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor M f) := by
  let : Module (R ⧸ I) N := hN.module
  have : IsScalarTower R (R ⧸ I) N := hN.isScalarTower
  let g : N →ₗ[R ⧸ I] (R ⧸ I) :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective f
  have hg : g.restrictScalars R = f := by
    ext x
    simp [g, LinearMap.extendScalarsOfSurjective_apply]
  rw [← hg]
  exact Module.Flat.rTensor_restrictScalars_injective I hflat g fun a b hab => hf <| by
    rw [← hg]
    exact hab

/-- If `I₁ ⊓ I₂ = ⊥`, `M ⧸ I₁ • ⊤` is flat over `R ⧸ I₁` and `M ⧸ I₂ • ⊤` is flat over `R ⧸ I₂`,
then for every ideal `J` of `R` the map `J ⊗[R] M → R ⊗[R] M` is injective. -/
lemma Module.Flat.rTensor_subtype_injective_of_inf_eq_bot {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I₁ I₂ : Ideal R) (hcap : I₁ ⊓ I₂ = ⊥)
    (h₁ : Module.Flat (R ⧸ I₁) (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • (⊤ : Submodule R M)))) (J : Ideal R) :
    Function.Injective (LinearMap.rTensor M J.subtype) := by
  let P : Submodule R ↥J := Submodule.comap J.subtype I₁
  have hann2 : Module.IsTorsionBySet R ↥P (I₂ : Set R) := by
    intro x a
    ext
    change (a : R) • ((x : ↥J) : R) = 0
    have : (a : R) • ((x : ↥J) : R) ∈ I₁ ⊓ I₂ :=
      ⟨Ideal.mul_mem_left _ _ x.2, Ideal.mul_mem_right _ _ a.2⟩
    simpa [hcap] using this
  let f₂ : ↥P →ₗ[R] (R ⧸ I₂) := (Algebra.linearMap R (R ⧸ I₂)).comp (J.subtype.comp P.subtype)
  have hf₂inj : Function.Injective f₂ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : ((x : ↥J) : R) ∈ I₁ ⊓ I₂ := ⟨x.2, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩
    rw [hcap] at this
    exact Subtype.ext (Subtype.ext this)
  let ψ : ↥J →ₗ[R] (R ⧸ I₁) := (Algebra.linearMap R (R ⧸ I₁)).comp J.subtype
  have hker : P = LinearMap.ker ψ := by
    ext x
    change ((x : R)) ∈ I₁ ↔ Ideal.Quotient.mk I₁ (x : R) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  let νmap : (↥J ⧸ P) →ₗ[R] (R ⧸ I₁) := P.liftQ ψ hker.le
  have hann1 : Module.IsTorsionBySet R (↥J ⧸ P) (I₁ : Set R) := by
    intro x a
    obtain ⟨y, rfl⟩ := P.mkQ_surjective x
    change (a : R) • (P.mkQ y) = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change ((a : R) • (y : R)) ∈ I₁
    exact Ideal.mul_mem_right _ _ a.2
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
  have hstepa : LinearMap.rTensor M P.mkQ ξ = 0 := by
    apply Module.Flat.rTensor_injective_of_isTorsionBySet I₁ h₁ hann1 νmap
      (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' P ψ hker))
    rw [← LinearMap.rTensor_comp_apply, P.liftQ_mkQ ψ hker.le, LinearMap.rTensor_comp_apply, hξ,
      map_zero, map_zero]
  obtain ⟨η, hη⟩ :=
    (_root_.rTensor_exact M (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective ξ).mp hstepa
  have hη0 : η = 0 := by
    apply Module.Flat.rTensor_injective_of_isTorsionBySet I₂ h₂ hann2 f₂ hf₂inj
    rw [LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply, hη, hξ, map_zero, map_zero]
  rw [← hη, hη0, map_zero]

/-- If `I₁ ⊓ I₂ = ⊥`, `M ⧸ I₁ • ⊤` is flat over `R ⧸ I₁` and `M ⧸ I₂ • ⊤` is flat over `R ⧸ I₂`,
then `M` is flat over `R`. -/
lemma Module.Flat.of_inf_eq_bot {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I₁ I₂ : Ideal R) (hcap : I₁ ⊓ I₂ = ⊥)
    (h₁ : Module.Flat (R ⧸ I₁) (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
    Module.Flat R M :=
  (Module.Flat.iff_rTensor_injective').2
    (Module.Flat.rTensor_subtype_injective_of_inf_eq_bot I₁ I₂ hcap h₁ h₂)

/-- The images of `I₁` and `I₂` in `R ⧸ (I₁ ⊓ I₂)` have trivial intersection. -/
lemma Ideal.map_mk_inf_map_mk_eq_bot {R : Type*} [CommRing R] (I₁ I₂ : Ideal R) :
    (Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₁) ⊓
      (Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₂) = ⊥ := by
  refine eq_bot_iff.2 fun x ⟨hx1, hx2⟩ => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [SetLike.mem_coe, Ideal.mem_quotient_iff_mem_sup] at hx1 hx2
  rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  rw [sup_eq_left.mpr inf_le_left] at hx1
  rw [sup_eq_left.mpr inf_le_right] at hx2
  exact ⟨hx1, hx2⟩

/-- For ideals `J`, `K` of `R`, the `R`-submodule of `M ⧸ J • ⊤` underlying `K̄ • ⊤`, where `K̄` is
the image of `K` in `R ⧸ J`, is the image of `K • ⊤`. -/
lemma Submodule.restrictScalars_map_smul_top_eq_map_mkQ {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (J K : Ideal R) :
    Submodule.restrictScalars R
        ((Ideal.map (Ideal.Quotient.mk J) K) •
          (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))))
      = Submodule.map (Submodule.mkQ (J • (⊤ : Submodule R M))) (K • (⊤ : Submodule R M)) := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    refine Submodule.smul_induction_on hz ?_ fun _ _ => Submodule.add_mem _
    intro q hq x hx
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
    obtain ⟨y, rfl⟩ := (J • (⊤ : Submodule R M)).mkQ_surjective x
    exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hr hx)
  · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
    intro r hr y _
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr)
      (Submodule.mem_top : (J • (⊤ : Submodule R M)).mkQ y ∈ (⊤ : Submodule (R ⧸ J) _))

/-- Let `J ≤ K` be ideals of `R`. If `M ⧸ K • ⊤` is flat over `R ⧸ K`, then, writing `K̄` for the
image of `K` in `R ⧸ J`, the module `(M ⧸ J • ⊤) ⧸ K̄ • ⊤` is flat over `(R ⧸ J) ⧸ K̄`. -/
lemma Module.Flat.quotientQuotient_of_le {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (J K : Ideal R) (hK : J ≤ K)
    (hK' : Module.Flat (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M)))) :
    Module.Flat ((R ⧸ J) ⧸ (Ideal.map (Ideal.Quotient.mk J) K))
      ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
        ((Ideal.map (Ideal.Quotient.mk J) K) •
          (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))))) := by
  let α := DoubleQuot.quotQuotEquivQuotOfLE hK
  let β := Submodule.quotientQuotientEquivQuotient (J • (⊤ : Submodule R M))
    (K • (⊤ : Submodule R M)) (Submodule.smul_mono hK le_rfl)
  let γ := Submodule.quotEquivOfEq _ _
    (Submodule.restrictScalars_map_smul_top_eq_map_mkQ (M := M) J K).symm
  let δ := Submodule.Quotient.restrictScalarsEquiv R
      ((Ideal.map (Ideal.Quotient.mk J) K) • (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R
          M)))))
  let ψ : ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
        ((Ideal.map (Ideal.Quotient.mk J) K) • (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R
            M))))))
      ≃+ (M ⧸ (K • (⊤ : Submodule R M))) :=
    δ.symm.toAddEquiv.trans (γ.symm.toAddEquiv.trans β.toAddEquiv)
  have hψ : ∀ (a : (R ⧸ J) ⧸ (Ideal.map (Ideal.Quotient.mk J) K))
      (m : (M ⧸ (J • (⊤ : Submodule R M))) ⧸
        ((Ideal.map (Ideal.Quotient.mk J) K) • (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R
            M)))))),
      ψ (a • m) = α a • ψ m := by
    intro a m
    obtain ⟨ā, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ ā
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a'
    rfl
  set A := (R ⧸ J) ⧸ (Ideal.map (Ideal.Quotient.mk J) K)
  set B := R ⧸ K
  let : Algebra A B := (α.toRingHom).toAlgebra
  let : Module A (M ⧸ (K • (⊤ : Submodule R M))) := Module.compHom _ α.toRingHom
  have : IsScalarTower A B (M ⧸ (K • (⊤ : Submodule R M))) :=
    ⟨fun a b n => mul_smul (α a) b n⟩
  have : Module.Flat A B := RingHom.Flat.of_bijective (f := α.toRingHom) α.bijective
  have : Module.Flat A (M ⧸ (K • (⊤ : Submodule R M))) := Module.Flat.trans A B _
  let ψ' : ((M ⧸ (J • (⊤ : Submodule R M))) ⧸
        ((Ideal.map (Ideal.Quotient.mk J) K) • (⊤ : Submodule (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R
            M))))))
      ≃ₗ[A] (M ⧸ (K • (⊤ : Submodule R M))) :=
    { ψ with
      map_smul' := hψ }
  exact Module.Flat.of_linearEquiv ψ'

/-- **Stacks 0522**.
If `M ⧸ I₁ • ⊤` is flat over `R ⧸ I₁` and `M ⧸ I₂ • ⊤` is flat over `R ⧸ I₂`, then
`M ⧸ (I₁ ⊓ I₂) • ⊤` is flat over `R ⧸ (I₁ ⊓ I₂)`. -/
@[stacks 0522]
theorem Module.Flat.quotient_inf {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (I₁ I₂ : Ideal R)
    (h₁ : Module.Flat (R ⧸ I₁) (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (h₂ : Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
    Module.Flat (R ⧸ (I₁ ⊓ I₂)) (M ⧸ ((I₁ ⊓ I₂) • (⊤ : Submodule R M))) :=
  Module.Flat.of_inf_eq_bot
    (Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₁)
    (Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₂)
    (Ideal.map_mk_inf_map_mk_eq_bot I₁ I₂)
    (Module.Flat.quotientQuotient_of_le (I₁ ⊓ I₂) I₁ inf_le_left h₁)
    (Module.Flat.quotientQuotient_of_le (I₁ ⊓ I₂) I₂ inf_le_right h₂)
