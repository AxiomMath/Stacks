module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExactLocal
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange

/-!
# The equalizer sequence over a Noetherian algebra

Let `p₁ p₂ : C → D` be two maps of flat `A`-algebras with `C` and `C ⊗_A C` Noetherian, and let
`M` be a `C`-module. This file proves that the equalizer sequence
`0 → M ⊗_A A → M ⊗_A C → M ⊗_A D` of `AlgHom.EqualizerTensorExact` is exact as soon as it is
exact for the residue field `κ(Q)` of every associated prime `Q` of `M`
(`AlgHom.EqualizerTensorExact.of_associatedPrimes`).

The multiplication `M ⊗_A C → M` splits the sequence (`AlgHom.tensorSMul`), so exactness says
that an element `x` of `M ⊗_A C` killed by `p₁ - p₂` and by the multiplication is zero. Such an
element is carried to zero in `L ⊗_A C` for every `C`-module `L` on which the sequence is
exact, in particular for `L = (M/Qⁿ M)_Q` with `Q` associated to `M`, by
`AlgHom.EqualizerTensorExact.of_smul_eq_bot`. Reading `M ⊗_A C` as the module `E ⊗_C M` over
`E = C ⊗_A C`, this says that `s x ∈ Qⁿ (E ⊗_C M)` for some `s ∉ Q`, for every associated prime
`Q` and every `n`; the Artin–Rees lemma over the Noetherian ring `E`, applied at an associated
prime of `E x`, then forces `x = 0` (`Module.eq_zero_of_forall_associatedPrimes_smul_mem`).
-/

@[expose] public section

open TensorProduct

/-! ### A Krull-type criterion for vanishing in a flat base change -/

namespace Module

variable {R E M : Type*} [CommRing R] [CommRing E] [Algebra R E] [IsNoetherianRing R]
  [IsNoetherianRing E] [Module.Flat R E] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Vanishing in a flat Noetherian base change.** Let `R → E` be a flat map of Noetherian rings
and `M` a finite `R`-module. An element `y` of `E ⊗_R M` such that, for every associated prime
`Q` of `M` and every `n`, some `s ∉ Q` has `s • y ∈ Qⁿ (E ⊗_R M)`, is zero. -/
theorem eq_zero_of_forall_associatedPrimes_smul_mem (y : E ⊗[R] M)
    (h : ∀ Q ∈ associatedPrimes R M, ∀ n : ℕ,
      ∃ s ∉ Q, s • y ∈ (Q ^ n • ⊤ : Submodule R (E ⊗[R] M))) : y = 0 := by
  by_contra hy
  let P : Submodule E (E ⊗[R] M) := Submodule.span E {y}
  have : Nontrivial P := by
    refine ⟨⟨⟨y, Submodule.mem_span_singleton_self y⟩, 0, fun h => hy ?_⟩⟩
    simpa using congrArg Subtype.val h
  obtain ⟨𝔓, h𝔓⟩ := associatedPrimes.nonempty E P
  obtain ⟨h𝔓p, ⟨z, hzP⟩, hz⟩ := (isAssociatedPrime_iff (I := 𝔓) (M := P)).mp h𝔓
  have hann (e : E) : e ∈ 𝔓 ↔ e • z = 0 := by
    rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set Q : Ideal R := 𝔓.comap (algebraMap R E)
  have hQ : Q ∈ associatedPrimes R M := by
    refine Stacks.AssociatedPrimes.FlatBaseChange.associatedPrimes_tensorProduct_subset_of_flat
      (P := E) ?_
    refine (isAssociatedPrime_iff (I := Q) (M := E ⊗[R] M)).mpr ⟨Ideal.comap_isPrime _ _, z, ?_⟩
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Ideal.mem_comap, hann,
      algebraMap_smul]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔓 (Submodule.span E {z})
  obtain ⟨s, hsQ, hs⟩ := h Q hQ (c + 1)
  obtain ⟨e₀, he₀⟩ := Submodule.mem_span_singleton.mp hzP
  have hle : (Q ^ (c + 1) • ⊤ : Submodule R (E ⊗[R] M)) ≤
      ((𝔓 ^ (c + 1) • ⊤ : Submodule E (E ⊗[R] M))).restrictScalars R := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul E r n]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    have : (Q ^ (c + 1)).map (algebraMap R E) ≤ 𝔓 ^ (c + 1) := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono Ideal.map_comap_le _
    exact this (Ideal.mem_map_of_mem _ hr)
  have h1 : s • z ∈ (𝔓 ^ (c + 1) • ⊤ : Submodule E (E ⊗[R] M)) ⊓ Submodule.span E {z} := by
    refine ⟨?_, ?_⟩
    · rw [← he₀, smul_comm]
      exact Submodule.smul_mem _ _ (hle hs)
    · rw [← algebraMap_smul E s z]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  rw [hc (c + 1) (Nat.le_succ c), Nat.add_sub_cancel_left, pow_one] at h1
  have h2 : s • z ∈ 𝔓 • Submodule.span E {z} :=
    Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨p, hp, hpz⟩ := Submodule.mem_smul_span_singleton.mp h2
  have h3 : algebraMap R E s - p ∈ 𝔓 := by
    rw [hann, sub_smul, algebraMap_smul, hpz, sub_self]
  exact hsQ (Ideal.mem_comap.mpr (by simpa using 𝔓.add_mem h3 hp))

end Module

namespace AlgHom

variable {A C D : Type*} [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
  {p₁ p₂ : C →ₐ[A] D}

/-! ### The splitting by the multiplication map -/

section Splitting

variable (A C) (M : Type*) [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]

/-- The multiplication `M ⊗_A C → M`, `m ⊗ c ↦ c • m`, of a `C`-module `M`. -/
noncomputable def tensorSMul : M ⊗[A] C →ₗ[A] M :=
  TensorProduct.lift (LinearMap.mk₂ A (fun (m : M) (c : C) => c • m)
    (fun (m₁ m₂ : M) (c : C) => smul_add c m₁ m₂)
    (fun (a : A) (m : M) (c : C) => smul_comm c a m)
    (fun (m : M) (c₁ c₂ : C) => add_smul c₁ c₂ m)
    (fun (a : A) (m : M) (c : C) => smul_assoc a c m))

variable {A C M}

/-- The multiplication `tensorSMul` sends `m ⊗ c` to `c • m`. -/
@[simp]
theorem tensorSMul_tmul (m : M) (c : C) : tensorSMul A C M (m ⊗ₜ c) = c • m := rfl

/-- The multiplication splits the first map of the sequence. -/
theorem tensorSMul_lTensor_linearMap (w : M ⊗[A] A) :
    tensorSMul A C M ((Algebra.linearMap A C).lTensor M w) = TensorProduct.rid A M w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul m a => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The multiplication is natural in `C`-linear maps. -/
theorem tensorSMul_rTensor {M' : Type*} [AddCommGroup M'] [Module A M'] [Module C M']
    [IsScalarTower A C M'] (φ : M →ₗ[C] M') (x : M ⊗[A] C) :
    tensorSMul A C M' ((φ.restrictScalars A).rTensor C x) = φ (tensorSMul A C M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- For a `C`-module `M`, the sequence is exact exactly when an element of `M ⊗_A C` killed by
`p₁ - p₂` and by the multiplication is zero. -/
theorem equalizerTensorExact_iff_of_module :
    EqualizerTensorExact p₁ p₂ M ↔ ∀ x : M ⊗[A] C,
      (p₁.toLinearMap - p₂.toLinearMap).lTensor M x = 0 → tensorSMul A C M x = 0 → x = 0 := by
  refine ⟨fun h x hδ hμ => ?_, fun h => ⟨fun w₁ w₂ hw => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩⟩
  · obtain ⟨w, rfl⟩ := (h.2 x).mp hδ
    rw [tensorSMul_lTensor_linearMap] at hμ
    rw [(TensorProduct.rid A M).injective (hμ.trans (map_zero _).symm), map_zero]
  · have := congrArg (tensorSMul A C M) hw
    rw [tensorSMul_lTensor_linearMap, tensorSMul_lTensor_linearMap] at this
    exact (TensorProduct.rid A M).injective this
  · set w := (TensorProduct.rid A M).symm (tensorSMul A C M x)
    refine ⟨w, (sub_eq_zero.mp (h _ ?_ ?_)).symm⟩
    · rw [map_sub, hx, lTensor_sub_lTensor_linearMap, sub_self]
    · rw [map_sub, tensorSMul_lTensor_linearMap, LinearEquiv.apply_symm_apply, sub_self]
  · rintro ⟨w, rfl⟩
    exact lTensor_sub_lTensor_linearMap w

end Splitting

/-! ### Associated primes -/

section Noetherian

/-- The image of a `Qⁿ`-multiple under `m ↦ e ⊗ m` is a `Qⁿ`-multiple. -/
theorem _root_.TensorProduct.tmul_mem_smul_top {R E M : Type*} [CommRing R] [AddCommGroup E]
    [Module R E] [AddCommGroup M] [Module R M] (I : Ideal R) (e : E) {m : M}
    (hm : m ∈ (I • ⊤ : Submodule R M)) : e ⊗ₜ m ∈ (I • ⊤ : Submodule R (E ⊗[R] M)) :=
  Submodule.smul_induction_on hm
    (fun r hr n _ => by rw [tmul_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top)
    (fun x y hx hy => by rw [tmul_add]; exact add_mem hx hy)

/-- If `y ∈ E ⊗_R M` dies in `E ⊗_R (M/QⁿM)_Q` for a flat `R`-module `E`, then `s y ∈ Qⁿ (E ⊗ M)`
for some `s ∉ Q`. -/
theorem _root_.TensorProduct.exists_smul_mem_of_lTensor_eq_zero {R E M : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [Module.Flat R E] [AddCommGroup M] [Module R M]
    (Q : Ideal R) [Q.IsPrime] (n : ℕ) (y : E ⊗[R] M)
    (hy : ((LocalizedModule.mkLinearMap Q.primeCompl (M ⧸ (Q ^ n • ⊤ : Submodule R M))) ∘ₗ
      (Q ^ n • ⊤ : Submodule R M).mkQ).lTensor E y = 0) :
    ∃ s ∉ Q, s • y ∈ (Q ^ n • ⊤ : Submodule R (E ⊗[R] M)) := by
  set φ := (LocalizedModule.mkLinearMap Q.primeCompl (M ⧸ (Q ^ n • ⊤ : Submodule R M))) ∘ₗ
      (Q ^ n • ⊤ : Submodule R M).mkQ
  have hex : Function.Exact ((LinearMap.ker φ).subtype.lTensor E) (φ.lTensor E) :=
    Module.Flat.lTensor_exact E (LinearMap.exact_subtype_ker_map φ)
  obtain ⟨w, rfl⟩ := (hex y).mp hy
  clear hy
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, (Ideal.ne_top_iff_one Q).mp Ideal.IsPrime.ne_top', by simp⟩
  | tmul e m =>
    have hm : φ m = 0 := m.2
    rw [LinearMap.comp_apply,
      IsLocalizedModule.eq_zero_iff Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl _)]
      at hm
    obtain ⟨⟨s, hs⟩, hsm⟩ := hm
    refine ⟨s, hs, ?_⟩
    have : s • (m : M) ∈ (Q ^ n • ⊤ : Submodule R M) := by
      rwa [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hsm
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← tmul_smul]
    exact TensorProduct.tmul_mem_smul_top _ e this
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, h₁⟩ := h₁
    obtain ⟨s₂, hs₂, h₂⟩ := h₂
    refine ⟨s₁ * s₂, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hs₁ hs₂, ?_⟩
    rw [map_add, smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ s₂ h₁
    · rw [mul_smul]
      exact Submodule.smul_mem _ s₁ h₂

/-- Reading `M ⊗_A C` as the module `(C ⊗_A C) ⊗_C M` over `C ⊗_A C`. -/
private noncomputable def tensorCancelEquiv {M : Type*} [AddCommGroup M] [Module A M] [Module C M]
    [IsScalarTower A C M] : M ⊗[A] C ≃ₗ[C] (C ⊗[A] C) ⊗[C] M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A C C M C).symm ≪≫ₗ
    TensorProduct.comm C M (C ⊗[A] C)

variable [Module.Flat A C] [Module.Flat A D] [IsNoetherianRing C] [IsNoetherianRing (C ⊗[A] C)]
  {M : Type*} [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]

/-- The finite case of `AlgHom.EqualizerTensorExact.of_associatedPrimes`. -/
theorem EqualizerTensorExact.of_associatedPrimes_of_finite [Module.Finite C M]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Q ∈ associatedPrimes C M →
      EqualizerTensorExact p₁ p₂ (Ideal.ResidueField Q)) :
    EqualizerTensorExact p₁ p₂ M := by
  rw [equalizerTensorExact_iff_of_module]
  intro x hδ hμ
  suffices hΦ : tensorCancelEquiv (A := A) x = 0 by simpa using hΦ
  refine Module.eq_zero_of_forall_associatedPrimes_smul_mem (R := C) (E := C ⊗[A] C)
    (tensorCancelEquiv (A := A) x) fun Q hQ n => ?_
  have : Q.IsPrime := hQ.isPrime
  apply TensorProduct.exists_smul_mem_of_lTensor_eq_zero
  set L := LocalizedModule Q.primeCompl (M ⧸ (Q ^ n • ⊤ : Submodule C M))
  set φ : M →ₗ[C] L := (LocalizedModule.mkLinearMap Q.primeCompl _) ∘ₗ
    (Q ^ n • ⊤ : Submodule C M).mkQ
  have hkill : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ n •
      (⊤ : Submodule (Localization.AtPrime Q) L) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, eq_bot_iff,
      Submodule.smul_le]
    intro r hr ℓ _
    have hle : (Q ^ n).map (algebraMap C (Localization.AtPrime Q)) ≤
        Module.annihilator (Localization.AtPrime Q) L := by
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, Module.mem_annihilator]
      intro ℓ
      rw [algebraMap_smul]
      induction ℓ using LocalizedModule.induction_on with
      | h m s =>
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [LocalizedModule.smul'_mk, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hq Submodule.mem_top),
          LocalizedModule.zero_mk]
    rw [Submodule.mem_bot]
    exact Module.mem_annihilator.mp (hle hr) ℓ
  have hL : EqualizerTensorExact p₁ p₂ L := (h Q hQ).of_smul_eq_bot n L hkill
  have hx : (φ.restrictScalars A).rTensor C x = 0 :=
    (equalizerTensorExact_iff_of_module.mp hL) _
      (by rw [← rTensor_lTensor_apply, hδ, map_zero])
      (by rw [tensorSMul_rTensor, hμ, map_zero])
  have hnat (z : M ⊗[A] C) : φ.lTensor (C ⊗[A] C) (tensorCancelEquiv (A := A) z) =
      tensorCancelEquiv (A := A) ((φ.restrictScalars A).rTensor C z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  rw [hnat, hx, map_zero]

omit [Module.Flat A C] [IsNoetherianRing C] [IsNoetherianRing (C ⊗[A] C)] in
/-- Every element of `M ⊗_A C` comes from `M' ⊗_A C` for a finitely generated `C`-submodule
`M'` of `M`. -/
theorem exists_fg_rTensor_eq (x : M ⊗[A] C) : ∃ M' : Submodule C M, M'.FG ∧
    ∃ x' : M' ⊗[A] C, (M'.subtype.restrictScalars A).rTensor C x' = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Submodule.fg_bot, 0, map_zero _⟩
  | tmul m c =>
    exact ⟨C ∙ m, Submodule.fg_span_singleton m,
      (⟨m, Submodule.mem_span_singleton_self m⟩ : C ∙ m) ⊗ₜ c, rfl⟩
  | add x y hx hy =>
    obtain ⟨M₁, h₁, x₁, rfl⟩ := hx
    obtain ⟨M₂, h₂, x₂, rfl⟩ := hy
    refine ⟨M₁ ⊔ M₂, h₁.sup h₂,
      ((Submodule.inclusion le_sup_left).restrictScalars A).rTensor C x₁ +
        ((Submodule.inclusion le_sup_right).restrictScalars A).rTensor C x₂, ?_⟩
    rw [map_add, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    rfl

/-- **The equalizer sequence over a Noetherian algebra.** Let `p₁ p₂ : C → D` be two maps of
flat `A`-algebras with `C` and `C ⊗_A C` Noetherian, and let `M` be a `C`-module. If the
sequence is exact for the residue field of every associated prime of `M`, it is exact
for `M`. -/
theorem EqualizerTensorExact.of_associatedPrimes
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Q ∈ associatedPrimes C M →
      EqualizerTensorExact p₁ p₂ (Ideal.ResidueField Q)) :
    EqualizerTensorExact p₁ p₂ M := by
  rw [equalizerTensorExact_iff_of_module]
  intro x hδ hμ
  obtain ⟨M', hM', x', rfl⟩ := exists_fg_rTensor_eq x
  have : Module.Finite C M' := Module.Finite.iff_fg.mpr hM'
  have hgood : EqualizerTensorExact p₁ p₂ M' :=
    EqualizerTensorExact.of_associatedPrimes_of_finite fun Q _ hQ =>
      h Q (associatedPrimes.subset_of_injective (f := M'.subtype) Subtype.val_injective hQ)
  rw [(equalizerTensorExact_iff_of_module.mp hgood) x' ?_ ?_, map_zero]
  · apply Module.Flat.rTensor_preserves_injective_linearMap (M := D)
      (M'.subtype.restrictScalars A) Subtype.val_injective
    rw [rTensor_lTensor_apply, hδ, map_zero]
  · apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← M'.subtype_apply, ← tensorSMul_rTensor, hμ]

end Noetherian

end AlgHom
