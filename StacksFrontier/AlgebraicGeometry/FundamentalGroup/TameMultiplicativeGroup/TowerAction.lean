module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.DeckProperties

/-!
# The action of `Ẑ^{(q)} ⋊ Ẑ` on ring maps with values in the Kummer tower

The base point `k₀^{(m)} : 𝔽_{m!}[X]_X → Ω` is injective, and `γ ∈ Γ = Ẑ^{(q)} ⋊ Ẑ` acts on its
image by `τ_γ = k₀^{(m)} ∘ deck_m(γ) ∘ (k₀^{(m)})⁻¹`. These maps are compatible along the tower
(the transitions commute with the deck action), multiplicative in `γ`, and fix the image of the
base map `k[x]_x → Ω`. So `γ` acts on every ring map `ψ : C → Ω` with values in the image of some
base point, by `ψ ↦ τ_γ ∘ ψ`, independently of the layer.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.tau`: `τ_γ` on the image of `k₀^{(m)}`.
* `AlgebraicGeometry.TameMultiplicativeGroup.IsTowerValued`: `ψ` takes values in some image.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerAct`: the action `ψ ↦ τ_γ ∘ ψ`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k] [Fintype k]

/-- `𝔽_{m!}[X]_X` is isomorphic to the image of its base point. -/
def rangeEquiv (m : ℕ) : Ring (towerField k m) ≃+* (towerPoint k m).range :=
  RingEquiv.ofBijective (towerPoint k m).rangeRestrict
    ⟨fun _ _ h ↦ towerPoint_injective k m (congrArg Subtype.val h),
      (towerPoint k m).rangeRestrict_surjective⟩

/-- The base point sends the preimage of `ω` under `rangeEquiv` back to `ω`. -/
theorem towerPoint_rangeEquiv_symm (m : ℕ) (ω : (towerPoint k m).range) :
    towerPoint k m ((rangeEquiv k m).symm ω) = ω :=
  congrArg Subtype.val ((rangeEquiv k m).apply_symm_apply ω)

/-- **The action `τ_γ = k₀ ∘ deck(γ) ∘ k₀⁻¹`** of `γ` on the image of the `m`-th base point. -/
def tau (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) :
    (towerPoint k m).range →+* Omega k :=
  (towerPoint k m).comp ((deck k m γ).toRingHom.comp (rangeEquiv k m).symm.toRingHom)

/-- If `ω = k₀^{(m)}(z)`, then `τ_γ(ω) = k₀^{(m)}(deck_m(γ)(z))`. -/
theorem tau_eq {m : ℕ} (γ : Gamma (inverseCharacter (Fintype.card k))) {ω : Omega k}
    (hω : ω ∈ (towerPoint k m).range) {z : Ring (towerField k m)} (hz : towerPoint k m z = ω) :
    tau k m γ ⟨ω, hω⟩ = towerPoint k m (deck k m γ z) := by
  have h : (⟨ω, hω⟩ : (towerPoint k m).range) = rangeEquiv k m z := Subtype.ext hz.symm
  change towerPoint k m (deck k m γ ((rangeEquiv k m).symm ⟨ω, hω⟩)) = _
  rw [h, RingEquiv.symm_apply_apply]

/-- `τ_γ` maps the image of `k₀^{(m)}` into itself. -/
theorem tau_mem (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ω : (towerPoint k m).range) : tau k m γ ω ∈ (towerPoint k m).range :=
  ⟨_, rfl⟩

/-- **`τ_γ` is compatible with the transitions.** -/
theorem tau_succ (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) {ω : Omega k}
    (h : ω ∈ (towerPoint k m).range) :
    tau k (m + 1) γ ⟨ω, range_towerPoint_le k m h⟩ = tau k m γ ⟨ω, h⟩ := by
  obtain ⟨z, hz⟩ := id h
  rw [tau_eq k γ _ ((towerPoint_transition k m z).trans hz), tau_eq k γ h hz,
    ← towerTransition_deck, towerPoint_transition]

/-- For `m ≤ m'`, `τ_γ` at layer `m'` agrees with `τ_γ` at layer `m` on the image of `k₀^{(m)}`. -/
theorem tau_of_le {m m' : ℕ} (hle : m ≤ m') (γ : Gamma (inverseCharacter (Fintype.card k)))
    {ω : Omega k} (h : ω ∈ (towerPoint k m).range) :
    tau k m' γ ⟨ω, range_towerPoint_mono k hle h⟩ = tau k m γ ⟨ω, h⟩ := by
  induction hle with
  | refl => rfl
  | step hle ih => exact (tau_succ k _ γ (range_towerPoint_mono k hle h)).trans ih

/-- `τ_{γγ'} = τ_γ ∘ τ_{γ'}` on the image of `k₀^{(m)}`. -/
theorem tau_mul (m : ℕ) (γ γ' : Gamma (inverseCharacter (Fintype.card k)))
    (ω : (towerPoint k m).range) :
    tau k m (γ * γ') ω = tau k m γ ⟨tau k m γ' ω, tau_mem k m γ' ω⟩ := by
  rcases ω with ⟨_, z, rfl⟩
  have h := Set.mem_range_self (f := towerPoint k m) z
  rw [tau_eq k _ h rfl, tau_eq k γ _ (tau_eq k γ' h rfl).symm, map_mul]
  rfl

/-- `τ_1` is the identity on the image of `k₀^{(m)}`. -/
theorem tau_one (m : ℕ) (ω : (towerPoint k m).range) : tau k m 1 ω = ω := by
  rcases ω with ⟨_, z, rfl⟩
  simp [tau_eq k _ (Set.mem_range_self z) rfl]

/-- `τ_γ` fixes the image of the base map `k[x]_x → Ω`. -/
theorem tau_baseHom (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) (z : Ring k)
    (h : baseHom k z ∈ (towerPoint k m).range) : tau k m γ ⟨baseHom k z, h⟩ = baseHom k z := by
  rw [tau_eq k γ h (towerPoint_kummerMap k m z), deck_kummerMap, towerPoint_kummerMap]

/-- If `deck_m(γ) = deck_m(γ')`, then `τ_γ = τ_{γ'}` on the image of `k₀^{(m)}`. -/
theorem tau_congr (m : ℕ) {γ γ' : Gamma (inverseCharacter (Fintype.card k))}
    (h : deck k m γ = deck k m γ') (ω : (towerPoint k m).range) : tau k m γ ω = tau k m γ' ω := by
  rw [tau, tau, h]

section Act

variable {k} {C : Type*} [CommRing C]

/-- A ring map `C → Ω` **with values in the Kummer tower**: in the image of some base point. -/
def IsTowerValued (ψ : C →+* Omega k) : Prop :=
  ∃ m, ∀ c, ψ c ∈ (towerPoint k m).range

variable (k) in
/-- The action of `γ` at the layer `m`: `τ_γ ∘ ψ`. -/
def actAt (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (hm : ∀ c, ψ c ∈ (towerPoint k m).range) : C →+* Omega k :=
  (tau k m γ).comp (ψ.codRestrict _ hm)

/-- The action of `γ` at layer `m` sends `ψ` to `c ↦ τ_γ(ψ c)`. -/
theorem actAt_apply (m : ℕ) (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (hm : ∀ c, ψ c ∈ (towerPoint k m).range) (c : C) :
    actAt k m γ ψ hm c = tau k m γ ⟨ψ c, hm c⟩ := rfl

/-- For `m ≤ m'`, the action of `γ` at layer `m'` agrees with the action at layer `m`. -/
theorem actAt_of_le {m m' : ℕ} (hle : m ≤ m') (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ψ : C →+* Omega k) (hm : ∀ c, ψ c ∈ (towerPoint k m).range) :
    actAt k m' γ ψ (fun c ↦ range_towerPoint_mono k hle (hm c)) = actAt k m γ ψ hm :=
  RingHom.ext fun c ↦ tau_of_le k hle γ (hm c)

/-- The action of `γ` on `ψ` is the same at any two layers containing the values of `ψ`. -/
theorem actAt_eq {m m' : ℕ} (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (hm : ∀ c, ψ c ∈ (towerPoint k m).range) (hm' : ∀ c, ψ c ∈ (towerPoint k m').range) :
    actAt k m γ ψ hm = actAt k m' γ ψ hm' :=
  (actAt_of_le (le_max_left m m') γ ψ hm).symm.trans (actAt_of_le (le_max_right m m') γ ψ hm')

/-- **The action of `γ ∈ Γ` on ring maps with values in the Kummer tower**, `ψ ↦ τ_γ ∘ ψ`. -/
def towerAct (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (h : IsTowerValued ψ) : C →+* Omega k :=
  actAt k h.choose γ ψ h.choose_spec

/-- `towerAct γ ψ` is the action at any layer `m` containing the values of `ψ`. -/
theorem towerAct_eq {m : ℕ} (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (h : IsTowerValued ψ) (hm : ∀ c, ψ c ∈ (towerPoint k m).range) :
    towerAct γ ψ h = actAt k m γ ψ hm :=
  actAt_eq γ ψ _ hm

/-- Pointwise form of `towerAct_eq`: `towerAct γ ψ c = τ_γ(ψ c)` at any layer `m`. -/
private theorem towerAct_apply {m : ℕ} (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ψ : C →+* Omega k) (h : IsTowerValued ψ) (hm : ∀ c, ψ c ∈ (towerPoint k m).range) (c : C) :
    towerAct γ ψ h c = tau k m γ ⟨ψ c, hm c⟩ :=
  RingHom.congr_fun (towerAct_eq γ ψ h hm) c

/-- `towerAct γ ψ` depends only on `ψ`, not on the proof that it is tower-valued. -/
theorem towerAct_eq_of_eq (γ : Gamma (inverseCharacter (Fintype.card k))) {ψ ψ' : C →+* Omega k}
    (h : IsTowerValued ψ) (h' : IsTowerValued ψ') (e : ψ = ψ') :
    towerAct γ ψ h = towerAct γ ψ' h' := by
  subst e
  rfl

/-- `towerAct γ ψ` takes values in the same image of a base point as `ψ`. -/
theorem towerAct_mem (γ : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (h : IsTowerValued ψ) (c : C) : towerAct γ ψ h c ∈ (towerPoint k h.choose).range :=
  tau_mem k _ γ _

/-- `towerAct γ ψ` takes values in the Kummer tower. -/
theorem isTowerValued_towerAct (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ψ : C →+* Omega k) (h : IsTowerValued ψ) : IsTowerValued (towerAct γ ψ h) :=
  ⟨h.choose, towerAct_mem γ ψ h⟩

/-- The action is multiplicative: `γγ'` acts as `γ` after `γ'`. -/
theorem towerAct_mul (γ γ' : Gamma (inverseCharacter (Fintype.card k))) (ψ : C →+* Omega k)
    (h : IsTowerValued ψ) :
    towerAct (γ * γ') ψ h = towerAct γ (towerAct γ' ψ h) (isTowerValued_towerAct γ' ψ h) := by
  ext c
  rw [towerAct_apply _ _ _ h.choose_spec, towerAct_apply _ _ _ (towerAct_mem γ' ψ h),
    tau_mul]
  rfl

/-- The identity of `Γ` acts trivially. -/
theorem towerAct_one (ψ : C →+* Omega k) (h : IsTowerValued ψ) : towerAct 1 ψ h = ψ := by
  ext c
  rw [towerAct_apply _ _ _ h.choose_spec, tau_one]

/-- The action commutes with precomposition: `γ · (ψ ∘ g) = (γ · ψ) ∘ g`. -/
theorem towerAct_comp {C' : Type*} [CommRing C'] (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ψ : C →+* Omega k) (h : IsTowerValued ψ) (g : C' →+* C) (h' : IsTowerValued (ψ.comp g)) :
    towerAct γ (ψ.comp g) h' = (towerAct γ ψ h).comp g := by
  rw [towerAct_eq _ _ _ (fun c ↦ h.choose_spec (g c)), towerAct_eq _ _ _ h.choose_spec]
  rfl

/-- If `ψ ∘ φ` is the base map `k[x]_x → Ω`, then so is `(γ · ψ) ∘ φ`. -/
theorem towerAct_comp_eq_baseHom (γ : Gamma (inverseCharacter (Fintype.card k)))
    (ψ : C →+* Omega k) (h : IsTowerValued ψ) (φ : Ring k →+* C) (hφ : ψ.comp φ = baseHom k) :
    (towerAct γ ψ h).comp φ = baseHom k := by
  ext z
  have hz : ψ (φ z) = baseHom k z := RingHom.congr_fun hφ z
  rw [RingHom.comp_apply, towerAct_apply _ _ _ h.choose_spec]
  have hmem : baseHom k z ∈ (towerPoint k h.choose).range := hz ▸ h.choose_spec (φ z)
  have : (⟨ψ (φ z), h.choose_spec (φ z)⟩ : (towerPoint k h.choose).range) = ⟨baseHom k z, hmem⟩ :=
    Subtype.ext hz
  rw [this, tau_baseHom]

/-- If `deck_m(γ) = deck_m(γ')` and `ψ` takes values in the image of `k₀^{(m)}`, then `γ` and `γ'`
act equally on `ψ`. -/
theorem towerAct_congr {m : ℕ} {γ γ' : Gamma (inverseCharacter (Fintype.card k))}
    (hγ : deck k m γ = deck k m γ') (ψ : C →+* Omega k) (h : IsTowerValued ψ)
    (hm : ∀ c, ψ c ∈ (towerPoint k m).range) : towerAct γ ψ h = towerAct γ' ψ h := by
  ext c
  rw [towerAct_apply _ _ _ hm, towerAct_apply _ _ _ hm, tau_congr k m hγ]

end Act

end AlgebraicGeometry.TameMultiplicativeGroup

end
