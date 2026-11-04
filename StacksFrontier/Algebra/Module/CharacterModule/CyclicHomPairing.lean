module

public import StacksFrontier.Algebra.Module.CharacterModule.Finite
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# `Hom(A, M)^∨ = Hom(M, A)` for a finite cyclic group `A` of order `n` and `n M = 0`

Let `A` be a finite cyclic group of order `n` and `M` a finite abelian group killed by `n`. Every
endomorphism of `A` is multiplication by a unique scalar `e ∈ ℤ/n`
(`Stacks.CharacterModule.cyclicEndScalar`), and composition followed by `ℤ/n ⊂ ℚ/ℤ`,
`e ↦ e/n`, is a perfect pairing

`Hom(A, M) × Hom(M, A) → End(A) = ℤ/n ⊂ ℚ/ℤ`,

so `ψ ↦ (φ ↦ ψ ∘ φ)` identifies `Hom(M, A)` with the character group of `Hom(A, M)`
(`Stacks.CharacterModule.cyclicHomPairing_bijective`). No generator of `A` is chosen: the scalar
of an endomorphism does not depend on one. For `A = μ_n` this is the identification
`M(-1)^∨ = Hom(M, μ_n)` of the Tate twist `M(-1) = Hom(μ_n, M)` with the twisted dual.

## Main definitions

* `Stacks.CharacterModule.cyclicEndScalar`: `End(A) → ℤ/n`.
* `Stacks.CharacterModule.zmodToRatCircle`: `ℤ/n → ℚ/ℤ`, `e ↦ e/n`.
* `Stacks.CharacterModule.cyclicHomPairing`: `Hom(M, A) → Hom(Hom(A, M), ℚ/ℤ)`.
-/

@[expose] public noncomputable section

namespace Stacks.CharacterModule

section Scalar

variable {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n] [hcyc : IsAddCyclic A]
  (hA : Nat.card A = n)

omit hcyc in
include hA in
/-- Every element of `A` is killed by `n`. -/
theorem nsmul_eq_zero_of_natCard (a : A) : n • a = 0 := by
  have : Finite A := Nat.finite_of_card_ne_zero (hA ▸ NeZero.ne n)
  rw [← hA]
  exact card_nsmul_eq_zero'

/-- The chosen isomorphism `ℤ/n ≅ A`, used only to prove properties of the scalar. -/
def cyclicZModEquiv : ZMod n ≃+ A :=
  zmodAddEquivOfGenerator hcyc.exists_generator.choose_spec hA

/-- **The scalar of an endomorphism of a cyclic group of order `n`**: the unique `e ∈ ℤ/n` with
`f = e • id`. -/
def cyclicEndScalar (f : A →+ A) : ZMod n :=
  (cyclicZModEquiv hA).symm (f (cyclicZModEquiv hA 1))

/-- An additive map out of `ℤ/n` sends `x` to `x.val` times the image of `1`. -/
private theorem val_nsmul_map_one {F N : Type*} [AddMonoid N] [FunLike F (ZMod n) N]
    [AddMonoidHomClass F (ZMod n) N] (f : F) (x : ZMod n) : x.val • f 1 = f x := by
  rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- `f` is multiplication by its scalar. -/
theorem cyclicEndScalar_spec (f : A →+ A) (a : A) : f a = (cyclicEndScalar hA f).val • a := by
  set ι := cyclicZModEquiv hA
  obtain ⟨x, rfl⟩ := ι.surjective a
  have hfx : f (ι x) = x.val • f (ι 1) := by
    rw [← val_nsmul_map_one ι x, map_nsmul]
  have hf1 : f (ι 1) = (cyclicEndScalar hA f).val • ι 1 := by
    rw [cyclicEndScalar, val_nsmul_map_one, AddEquiv.apply_symm_apply]
  rw [hfx, hf1, smul_comm, val_nsmul_map_one]

/-- The scalar is unique. -/
theorem cyclicEndScalar_eq_of_forall (f : A →+ A) (e : ZMod n) (h : ∀ a, f a = e.val • a) :
    cyclicEndScalar hA f = e := by
  rw [cyclicEndScalar, h, val_nsmul_map_one, AddEquiv.symm_apply_apply]

/-- The scalar is additive. -/
def cyclicEndScalarHom : (A →+ A) →+ ZMod n where
  toFun := cyclicEndScalar hA
  map_zero' := cyclicEndScalar_eq_of_forall hA 0 0 fun a ↦ by simp
  map_add' f g := cyclicEndScalar_eq_of_forall hA (f + g) _ fun a ↦ by
    rw [AddMonoidHom.add_apply, cyclicEndScalar_spec hA f, cyclicEndScalar_spec hA g, ← add_nsmul]
    have hmod : (cyclicEndScalar hA f).val + (cyclicEndScalar hA g).val ≡
        (cyclicEndScalar hA f + cyclicEndScalar hA g).val [MOD n] := by
      rw [ZMod.val_add]
      exact (Nat.mod_modEq _ _).symm
    exact nsmul_eq_nsmul_of_modEq hA hmod a
where
  nsmul_eq_nsmul_of_modEq (hA : Nat.card A = n) {i j : ℕ} (hij : i ≡ j [MOD n]) (a : A) :
      i • a = j • a := by
    rw [← Nat.mod_add_div i n, ← Nat.mod_add_div j n, hij, add_nsmul, add_nsmul, mul_nsmul,
      mul_nsmul, nsmul_eq_zero_of_natCard hA, nsmul_zero, nsmul_zero]

/-- The scalar is invariant under conjugation. -/
theorem cyclicEndScalar_conj (f : A →+ A) (σ σ' : A →+ A) (hσ : ∀ a, σ (σ' a) = a) :
    cyclicEndScalar hA (σ.comp (f.comp σ')) = cyclicEndScalar hA f :=
  cyclicEndScalar_eq_of_forall hA _ _ fun a ↦ by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, cyclicEndScalar_spec hA f, map_nsmul, hσ]

/-- The scalar of a nonzero endomorphism is nonzero. -/
theorem cyclicEndScalar_ne_zero {f : A →+ A} (hf : f ≠ 0) : cyclicEndScalar hA f ≠ 0 := by
  intro h0
  apply hf
  ext a
  rw [cyclicEndScalar_spec hA f, h0, ZMod.val_zero, zero_nsmul, AddMonoidHom.zero_apply]

end Scalar

section Circle

variable (n : ℕ) [NeZero n]

/-- **`ℤ/n ⊂ ℚ/ℤ`**, `e ↦ e/n`. -/
def zmodToRatCircle : ZMod n →+ AddCircle (1 : ℚ) :=
  ZMod.lift n ⟨zmultiplesHom (AddCircle (1 : ℚ)) ((1 / n : ℚ) : AddCircle (1 : ℚ)), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← AddCircle.coe_nsmul, nsmul_eq_mul,
      mul_one_div_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)), AddCircle.coe_period]⟩

/-- The image of `k ∈ ℕ` under `ℤ/n → ℚ/ℤ` is `k/n`. -/
theorem zmodToRatCircle_natCast (k : ℕ) :
    zmodToRatCircle n k = ((k / n : ℚ) : AddCircle (1 : ℚ)) := by
  rw [show ((k : ℕ) : ZMod n) = ((k : ℤ) : ZMod n) by simp, zmodToRatCircle, ZMod.lift_coe,
    zmultiplesHom_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast, mul_one_div]

/-- The map `ℤ/n → ℚ/ℤ`, `e ↦ e/n`, is injective. -/
theorem zmodToRatCircle_injective : Function.Injective (zmodToRatCircle n) := by
  rw [injective_iff_map_eq_zero]
  intro e he
  rw [← ZMod.natCast_zmod_val e, zmodToRatCircle_natCast, AddCircle.coe_eq_zero_iff] at he
  obtain ⟨m, hm⟩ := he
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hlt : (e.val : ℚ) / n < 1 := (div_lt_one hn).mpr (by exact_mod_cast ZMod.val_lt e)
  have hge : (0 : ℚ) ≤ (e.val : ℚ) / n := by positivity
  rw [zsmul_eq_mul, mul_one] at hm
  have hm0 : m = 0 := by
    have h₁ : m < 1 := by exact_mod_cast (hm ▸ hlt : (m : ℚ) < 1)
    have h₀ : 0 ≤ m := by exact_mod_cast (hm ▸ hge : (0 : ℚ) ≤ m)
    omega
  rw [hm0, Int.cast_zero, eq_comm, div_eq_zero_iff] at hm
  rcases hm with hk | hk
  · rw [← ZMod.natCast_zmod_val e, show e.val = 0 by exact_mod_cast hk, Nat.cast_zero]
  · exact absurd hk hn.ne'

/-- The elements of `ℚ/ℤ` killed by `n` are the image of `ℤ/n`. -/
theorem exists_zmodToRatCircle_eq {x : AddCircle (1 : ℚ)} (hx : n • x = 0) :
    ∃ e : ZMod n, zmodToRatCircle n e = x := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  change n • ((q : ℚ) : AddCircle (1 : ℚ)) = 0 at hx
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod n), ?_⟩
  rw [zmodToRatCircle, ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul]
  show ((m • (1 / n : ℚ) : ℚ) : AddCircle (1 : ℚ)) = ((q : ℚ) : AddCircle (1 : ℚ))
  congr 1
  rw [zsmul_eq_mul, mul_one] at hm
  rw [zsmul_eq_mul, hm, nsmul_eq_mul, mul_one_div]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))

end Circle

section Pairing

variable {A : Type*} [AddCommGroup A] {M : Type*} [AddCommGroup M] {n : ℕ} [NeZero n]
  [IsAddCyclic A] (hA : Nat.card A = n)

/-- The pairing `φ ↦ (ψ ∘ φ)/n` of `Hom(A, M)` against a fixed `ψ ∈ Hom(M, A)`. -/
def cyclicHomPairingFun (ψ : M →+ A) : (A →+ M) →+ AddCircle (1 : ℚ) :=
  (zmodToRatCircle n).comp ((cyclicEndScalarHom hA).comp (AddMonoidHom.compHom ψ))

/-- The value of the pairing at `φ` is the image in `ℚ/ℤ` of the scalar of `ψ ∘ φ`. -/
theorem cyclicHomPairingFun_apply (ψ : M →+ A) (φ : A →+ M) :
    cyclicHomPairingFun hA ψ φ = zmodToRatCircle n (cyclicEndScalar hA (ψ.comp φ)) :=
  rfl

/-- **The pairing `Hom(M, A) → Hom(Hom(A, M), ℚ/ℤ)`**, `ψ ↦ (φ ↦ (ψ ∘ φ)/n)`. -/
def cyclicHomPairing : (M →+ A) →+ CharacterModule (A →+ M) where
  toFun ψ := cyclicHomPairingFun hA ψ
  map_zero' := AddMonoidHom.ext fun φ ↦ by
    change zmodToRatCircle n (cyclicEndScalarHom hA ((0 : M →+ A).comp φ)) = 0
    rw [AddMonoidHom.zero_comp, map_zero, map_zero]
  map_add' ψ ψ' := AddMonoidHom.ext fun φ ↦ by
    change zmodToRatCircle n (cyclicEndScalarHom hA ((ψ + ψ').comp φ)) =
      zmodToRatCircle n (cyclicEndScalarHom hA (ψ.comp φ)) +
        zmodToRatCircle n (cyclicEndScalarHom hA (ψ'.comp φ))
    rw [AddMonoidHom.add_comp, map_add, map_add]

/-- The character `cyclicHomPairing hA ψ` sends `φ` to the image in `ℚ/ℤ` of the scalar of
`ψ ∘ φ`. -/
theorem cyclicHomPairing_apply (ψ : M →+ A) (φ : A →+ M) :
    (cyclicHomPairing hA ψ : (A →+ M) →+ AddCircle (1 : ℚ)) φ =
      zmodToRatCircle n (cyclicEndScalar hA (ψ.comp φ)) :=
  rfl

variable (hM : ∀ m : M, n • m = 0)

omit [NeZero n] in
include hM in
/-- For `m ∈ M` there is `φ : A → M` sending the chosen generator to `m`. -/
theorem exists_hom_apply_generator (m : M) :
    ∃ φ : A →+ M, φ (cyclicZModEquiv hA 1) = m :=
  ⟨(ZMod.lift n ⟨zmultiplesHom M m, by rw [zmultiplesHom_apply, natCast_zsmul, hM]⟩).comp
      (cyclicZModEquiv hA).symm.toAddMonoidHom, by
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply,
      show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by simp, ZMod.lift_coe, zmultiplesHom_apply,
      one_zsmul]⟩

include hM in
/-- The pairing `Hom(M, A) → Hom(Hom(A, M), ℚ/ℤ)` is injective when `n M = 0`. -/
theorem cyclicHomPairing_injective : Function.Injective (cyclicHomPairing hA (M := M)) := by
  rw [injective_iff_map_eq_zero]
  intro ψ hψ
  by_contra hne
  obtain ⟨m, hm⟩ := not_forall.mp fun h : ∀ m, ψ m = 0 ↦ hne (AddMonoidHom.ext h)
  obtain ⟨φ, hφ⟩ := exists_hom_apply_generator hA hM m
  have hcomp : ψ.comp φ ≠ 0 := fun h ↦ hm (by
    rw [← hφ, ← AddMonoidHom.comp_apply, h, AddMonoidHom.zero_apply])
  have h0 := DFunLike.congr_fun hψ φ
  rw [cyclicHomPairing_apply] at h0
  exact cyclicEndScalar_ne_zero hA hcomp
    ((zmodToRatCircle_injective n) (h0.trans (map_zero _).symm))

include hM in
/-- **`Hom(M, A) ≅ Hom(A, M)^∨`** for `A` cyclic of order `n` and `M` finite killed by `n`. -/
theorem cyclicHomPairing_bijective [Finite M] :
    Function.Bijective (cyclicHomPairing hA (M := M)) := by
  have : Finite A := Nat.finite_of_card_ne_zero (hA ▸ NeZero.ne n)
  have : Finite (A →+ M) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (M →+ A) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (M →+ ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  refine (cyclicHomPairing_injective hA hM).bijective_of_nat_card_le ?_
  -- `#Hom(A, M)^∨ = #Hom(A, M) ≤ #M = #M^∨ ≤ #Hom(M, ℤ/n) = #Hom(M, A)`.
  have h1 : Nat.card (A →+ M) ≤ Nat.card M :=
    Nat.card_le_card_of_injective (fun φ ↦ φ (cyclicZModEquiv hA 1)) fun φ φ' h ↦ by
      change φ (cyclicZModEquiv hA 1) = φ' (cyclicZModEquiv hA 1) at h
      ext a
      obtain ⟨x, rfl⟩ := (cyclicZModEquiv hA).surjective a
      rw [← val_nsmul_map_one (cyclicZModEquiv hA) x, map_nsmul, map_nsmul, h]
  have h2 : Nat.card (CharacterModule M) ≤ Nat.card (M →+ ZMod n) := by
    refine Nat.card_le_card_of_surjective (fun ψ ↦ (zmodToRatCircle n).comp ψ) fun c ↦ ?_
    have hc : ∀ m, ∃ e : ZMod n, zmodToRatCircle n e = c m := fun m ↦
      exists_zmodToRatCircle_eq n (by rw [← map_nsmul, hM, map_zero])
    choose ψ hψ using hc
    refine ⟨{ toFun := ψ
              map_zero' := zmodToRatCircle_injective n (by
                rw [hψ, map_zero (zmodToRatCircle n), map_zero c])
              map_add' := fun a b ↦ zmodToRatCircle_injective n (by
                rw [hψ, map_add (zmodToRatCircle n), hψ, hψ, map_add c]) },
      AddMonoidHom.ext fun m ↦ hψ m⟩
  rw [CharacterModule.natCard_eq]
  calc Nat.card (A →+ M) ≤ Nat.card M := h1
    _ = Nat.card (CharacterModule M) := (CharacterModule.natCard_eq M).symm
    _ ≤ Nat.card (M →+ ZMod n) := h2
    _ = Nat.card (M →+ A) :=
      Nat.card_congr (AddEquiv.addMonoidHomCongrRightEquiv (cyclicZModEquiv hA))

end Pairing

end Stacks.CharacterModule

end
