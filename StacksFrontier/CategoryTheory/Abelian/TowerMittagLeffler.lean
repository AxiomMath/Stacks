module

public import StacksFrontier.CategoryTheory.Abelian.ScalarQuotientTower
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Towers with a Verschiebung, and the Mittag-Leffler property of `R^q f_!` of an ℓ-adic sheaf

Let `C` be an abelian category and `ℓ : ℕ`. A *Verschiebung* on a tower `T : ℕᵒᵖ ⥤ C` is a family
of maps `v n : Tₙ ⟶ Tₙ₊₁` whose composites with the transition maps `t : Tₙ₊₁ ⟶ Tₙ`, in either
order, are multiplication by `ℓ`. The levels `Fₙ` of an ℓ-adic sheaf carry one, and so does any
tower obtained from them by an additive functor, for instance `n ↦ R^q f_! Fₙ`.

For an ℓ-adic sheaf with flat levels, the sequences `0 → F_a → F_{a+b+1} → F_b → 0` (the first map
the iterated Verschiebung, the second the transition) are exact, and the long exact sequences of
`R^q f_!` give, for the towers `Tₙ = R^q f_! Fₙ` and `Sₙ = R^{q+1} f_! Fₙ`, exact sequences

`T_a → T_{a+b+1} → T_b --δ--> S_a → S_{a+b+1} → S_b`,

natural in `a`. This file proves, from these exact sequences (`CategoryTheory.LAdicTower.LESData`)
and the single hypothesis that `S₀` is a Noetherian object, that `T` satisfies the Mittag-Leffler
condition with a uniform shift (`CategoryTheory.LAdicTower.LESData.mittagLeffler`), and that the
stable images `Hₙ = Im(T_{n+β+1} ⟶ Tₙ)` then form a strict ℓ-adic tower: each transition
`Hₙ₊₁ ⟶ Hₙ` is the quotient by `ℓⁿ⁺¹`
(`CategoryTheory.LAdicTower.LESData.stableImageTransition_isCokernel`). The stable image tower
and `T` are isomorphic as pro-objects (`stableImageι`, `stableImageRetraction`). This is the
ℓ-adic sheaf `R^q f_! F` of the Leray step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves.

The uniform shift `β` is the index at which the ascending chain of kernels of the iterated
Verschiebung out of `S₀` stabilises; an induction on the level transports the stabilisation to
every level of `S` (`CategoryTheory.LAdicTower.LESData.verschiebung_kernel_stable`).

## Main definitions

* `CategoryTheory.LAdicTower.verschiebungMap`: the iterated Verschiebung `T_a ⟶ T_b`, `a ≤ b`.
* `CategoryTheory.LAdicTower.LESData`: the exact sequences above.
* `CategoryTheory.LAdicTower.LESData.stableImageTower`: the tower of stable images.

## Main results

* `CategoryTheory.LAdicTower.LESData.mittagLeffler`.
* `CategoryTheory.LAdicTower.LESData.stableImageTransition_isCokernel`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Preadditive Opposite

namespace CategoryTheory.LAdicTower

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Iterated Verschiebung -/

section Verschiebung

variable [Abelian C] (T : ℕᵒᵖ ⥤ C) (v : ∀ n, towerObj T n ⟶ towerObj T (n + 1))

/-- The iterated Verschiebung `T_a ⟶ T_b` for `a ≤ b`. -/
def verschiebungMap {a b : ℕ} (h : a ≤ b) : towerObj T a ⟶ towerObj T b :=
  (Functor.ofSequence (X := fun n => towerObj T n) v).map (homOfLE h)

omit [Abelian C] in
/-- The iterated Verschiebung `T_a ⟶ T_a` is the identity. -/
@[simp]
theorem verschiebungMap_self (a : ℕ) : verschiebungMap T v (le_refl a) = 𝟙 _ :=
  (Functor.ofSequence (X := fun n => towerObj T n) v).map_id a

omit [Abelian C] in
/-- The iterated Verschiebungs `T_a ⟶ T_b ⟶ T_c` compose to the iterated Verschiebung
`T_a ⟶ T_c`. -/
@[reassoc (attr := simp)]
theorem verschiebungMap_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    verschiebungMap T v hab ≫ verschiebungMap T v hbc = verschiebungMap T v (hab.trans hbc) :=
  ((Functor.ofSequence (X := fun n => towerObj T n) v).map_comp _ _).symm

omit [Abelian C] in
/-- The iterated Verschiebung `T_a ⟶ T_{a+1}` is `v a`. -/
theorem verschiebungMap_succ (a : ℕ) : verschiebungMap T v (Nat.le_succ a) = v a :=
  Functor.ofSequence_map_homOfLE_succ _ a

omit [Abelian C] in
/-- The iterated Verschiebung one step further. -/
theorem verschiebungMap_le_succ {a b : ℕ} (h : a ≤ b) :
    verschiebungMap T v (h.trans (Nat.le_succ b)) = verschiebungMap T v h ≫ v b := by
  rw [← verschiebungMap_comp T v h (Nat.le_succ b), verschiebungMap_succ]

/-- `v` is a Verschiebung for multiplication by `ℓ`: both composites with the transition maps
are multiplication by `ℓ`. -/
structure IsVerschiebung (ℓ : ℕ) : Prop where
  v_t : ∀ n, v n ≫ towerMap T (Nat.le_succ n) = ℓ • 𝟙 _
  t_v : ∀ n, towerMap T (Nat.le_succ n) ≫ v n = ℓ • 𝟙 _

variable {T v} {ℓ : ℕ} (hv : IsVerschiebung T v ℓ)
include hv

/-- One transition step commutes with the iterated Verschiebung. -/
theorem IsVerschiebung.t_verschiebungMap {a b : ℕ} (h : a ≤ b) :
    towerMap T (Nat.le_succ a) ≫ verschiebungMap T v h =
      verschiebungMap T v (Nat.succ_le_succ h) ≫ towerMap T (Nat.le_succ b) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [verschiebungMap_le_succ T v hab, reassoc_of% ih, hv.t_v b,
      show Nat.succ_le_succ (hab.trans (Nat.le_succ b)) = (Nat.succ_le_succ hab).trans
        (Nat.le_succ (b + 1)) from rfl, verschiebungMap_le_succ T v (Nat.succ_le_succ hab),
      Category.assoc, hv.v_t (b + 1)]

/-- **Transitions commute with the iterated Verschiebung**: for `c ≤ a`, `d ≤ b` with
`a - c = b - d`, the square `T_a ⟶ T_c ⟶ T_d`, `T_a ⟶ T_b ⟶ T_d` commutes. -/
theorem IsVerschiebung.towerMap_verschiebungMap {a b c d : ℕ} (hca : c ≤ a) (hdb : d ≤ b)
    (hcd : c ≤ d) (hab : a ≤ b) (h : a + d = b + c) :
    towerMap T hca ≫ verschiebungMap T v hcd = verschiebungMap T v hab ≫ towerMap T hdb := by
  obtain ⟨j, rfl⟩ : ∃ j, a = c + j := ⟨a - c, by omega⟩
  obtain rfl : b = d + j := by omega
  induction j with
  | zero =>
    change towerMap T (le_refl c) ≫ verschiebungMap T v hcd =
      verschiebungMap T v hcd ≫ towerMap T (le_refl d)
    rw [towerMap_self, towerMap_self, Category.id_comp, Category.comp_id]
  | succ j ih =>
    rw [← towerMap_comp T (Nat.le_add_right c j) (Nat.le_succ (c + j)), Category.assoc,
      ih (Nat.le_add_right c j) (Nat.le_add_right d j) (by omega) (by omega),
      reassoc_of% hv.t_verschiebungMap (show c + j ≤ d + j by omega),
      towerMap_comp]

/-- The iterated Verschiebung followed by the transition is multiplication by `ℓ^(b - a)`. -/
theorem IsVerschiebung.verschiebungMap_towerMap {a b : ℕ} (h : a ≤ b) :
    verschiebungMap T v h ≫ towerMap T h = ℓ ^ (b - a) • 𝟙 _ := by
  induction b, h using Nat.le_induction with
  | base => simpa using towerMap_self T a
  | succ b hab ih =>
    rw [verschiebungMap_le_succ T v hab, ← towerMap_comp T hab (Nat.le_succ b), Category.assoc,
      reassoc_of% hv.v_t b, nsmul_comp, Category.id_comp, comp_nsmul, ih, smul_smul]
    rw [Nat.succ_sub hab, pow_succ, Nat.mul_comm]

/-- The transition followed by the iterated Verschiebung is multiplication by `ℓ^(b - a)`. -/
theorem IsVerschiebung.towerMap_verschiebungMap_self {a b : ℕ} (h : a ≤ b) :
    towerMap T h ≫ verschiebungMap T v h = ℓ ^ (b - a) • 𝟙 _ := by
  induction b, h using Nat.le_induction with
  | base => simpa using towerMap_self T a
  | succ b hab ih =>
    rw [verschiebungMap_le_succ T v hab, ← towerMap_comp T hab (Nat.le_succ b), Category.assoc,
      reassoc_of% ih, nsmul_comp, Category.id_comp, comp_nsmul, hv.t_v b, smul_smul]
    rw [Nat.succ_sub hab, pow_succ]

end Verschiebung

/-! ### The exact sequences of `R^q` and `R^{q+1}` -/

section LES

variable [Abelian C]

/-- **The exact sequences of `R^q f_!` and `R^{q+1} f_!` on the levels of a flat ℓ-adic sheaf**,
abstractly: towers `T`, `S` with Verschiebungs and connecting maps `δ a b : T_b ⟶ S_a` such that,
for `m = a + b + 1`,
`T_a → T_m → T_b → S_a → S_m → S_b` is exact at `T_m`, `T_b`, `S_a` and `S_m`, with `δ` natural
in `a`. Exactness is phrased up to refinements. -/
structure LESData (T S : ℕᵒᵖ ⥤ C) (ℓ : ℕ) where
  /-- The Verschiebung of `T`. -/
  vT : ∀ n, towerObj T n ⟶ towerObj T (n + 1)
  /-- The Verschiebung of `S`. -/
  vS : ∀ n, towerObj S n ⟶ towerObj S (n + 1)
  /-- `vT` is a Verschiebung for multiplication by `ℓ`. -/
  hvT : IsVerschiebung T vT ℓ
  /-- `vS` is a Verschiebung for multiplication by `ℓ`. -/
  hvS : IsVerschiebung S vS ℓ
  /-- The connecting maps. -/
  δ : ∀ a b, towerObj T b ⟶ towerObj S a
  /-- Exactness of `T_a → T_m → T_b` at `T_m`. -/
  exactT : ∀ (a b m : ℕ) (hm : a + b + 1 = m) ⦃X : C⦄ (x : X ⟶ towerObj T m),
    x ≫ towerMap T (show b ≤ m by omega) = 0 → ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π)
      (y : X' ⟶ towerObj T a), π ≫ x = y ≫ verschiebungMap T vT (show a ≤ m by omega)
  /-- Exactness of `S_a → S_m → S_b` at `S_m`. -/
  exactS : ∀ (a b m : ℕ) (hm : a + b + 1 = m) ⦃X : C⦄ (x : X ⟶ towerObj S m),
    x ≫ towerMap S (show b ≤ m by omega) = 0 → ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π)
      (y : X' ⟶ towerObj S a), π ≫ x = y ≫ verschiebungMap S vS (show a ≤ m by omega)
  /-- `T_m → T_b → S_a` is a complex. -/
  towerMap_δ : ∀ (a b m : ℕ) (hm : a + b + 1 = m),
    towerMap T (show b ≤ m by omega) ≫ δ a b = 0
  /-- Exactness of `T_m → T_b → S_a` at `T_b`. -/
  exactδ : ∀ (a b m : ℕ) (hm : a + b + 1 = m) ⦃X : C⦄ (x : X ⟶ towerObj T b),
    x ≫ δ a b = 0 → ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π)
      (y : X' ⟶ towerObj T m), π ≫ x = y ≫ towerMap T (show b ≤ m by omega)
  /-- `T_b → S_a → S_m` is a complex. -/
  δ_verschiebungMap : ∀ (a b m : ℕ) (hm : a + b + 1 = m),
    δ a b ≫ verschiebungMap S vS (show a ≤ m by omega) = 0
  /-- Naturality of `δ` in `a`. -/
  δ_towerMap : ∀ a b, δ (a + 1) b ≫ towerMap S (Nat.le_succ a) = δ a b

/-- If `k • 𝟙 Y = 0`, then `f : X ⟶ Y` kills `k • 𝟙 X`. -/
private theorem nsmul_id_comp_eq_zero {X Y : C} (f : X ⟶ Y) {k : ℕ} (h : k • 𝟙 Y = 0) :
    (k • 𝟙 X) ≫ f = 0 := by
  rw [nsmul_comp, Category.id_comp, ← Category.comp_id f, ← comp_nsmul, h, comp_zero]

namespace LESData

variable {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ} (D : LESData T S ℓ)

/-- For `c ≤ a`, the connecting map `δ a b` followed by the transition `S_a ⟶ S_c` is `δ c b`. -/
theorem δ_towerMap_le (b : ℕ) {c a : ℕ} (h : c ≤ a) :
    D.δ a b ≫ towerMap S h = D.δ c b := by
  induction a, h using Nat.le_induction with
  | base => simp only [show towerMap S _ = 𝟙 _ from towerMap_self S c, Category.comp_id]
  | succ a hca ih =>
    rw [← towerMap_comp S hca (Nat.le_succ a), ← Category.assoc, D.δ_towerMap, ih]

/-- The ascending chain of kernels of the iterated Verschiebung out of `S₀`. -/
def kernelChain : ℕ →o Subobject (towerObj S 0) where
  toFun b := kernelSubobject (verschiebungMap S D.vS (Nat.zero_le (b + 1)))
  monotone' b b' h := by
    have e := verschiebungMap_comp S D.vS (Nat.zero_le (b + 1)) (show b + 1 ≤ b' + 1 by omega)
    simpa only [e] using kernelSubobject_comp_le
      (verschiebungMap S D.vS (Nat.zero_le (b + 1)))
      (verschiebungMap S D.vS (show b + 1 ≤ b' + 1 by omega))

/-- **Uniform stabilisation of the kernels of the iterated Verschiebung on `S`**: if `S₀` is a
Noetherian object there is `β` such that at every level `a`, a generalized element killed by
`v^(b+1)` for some `b ≥ β` is already killed by `v^(β+1)`. -/
theorem verschiebung_kernel_stable [IsNoetherianObject (towerObj S 0)] :
    ∃ β : ℕ, ∀ (a b m m' : ℕ) (_ : β ≤ b) (hm : a + b + 1 = m) (hm' : a + β + 1 = m')
      ⦃X : C⦄ (x : X ⟶ towerObj S a),
      x ≫ verschiebungMap S D.vS (show a ≤ m by omega) = 0 →
        x ≫ verschiebungMap S D.vS (show a ≤ m' by omega) = 0 := by
  obtain ⟨β, hβ⟩ := monotone_chain_condition_of_isNoetherianObject D.kernelChain
  have base : ∀ (b : ℕ) (_ : β ≤ b) ⦃X : C⦄ (x : X ⟶ towerObj S 0),
      x ≫ verschiebungMap S D.vS (Nat.zero_le (b + 1)) = 0 →
        x ≫ verschiebungMap S D.vS (Nat.zero_le (β + 1)) = 0 := by
    intro b hb X x hx
    have h1 : (kernelSubobject (verschiebungMap S D.vS (Nat.zero_le (b + 1)))).Factors x :=
      (kernelSubobject_factors_iff _ x).2 hx
    have e : D.kernelChain β = D.kernelChain b := hβ b hb
    change (D.kernelChain b).Factors x at h1
    rw [← e] at h1
    exact (kernelSubobject_factors_iff _ x).1 h1
  refine ⟨β, fun a => ?_⟩
  induction a with
  | zero =>
    intro b m m' hb hm hm' X x hx
    obtain rfl : m = b + 1 := by omega
    obtain rfl : m' = β + 1 := by omega
    exact base b hb x hx
  | succ a ih =>
    intro b m m' hb hm hm' X x hx
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m' = m₁ + 1 := ⟨m' - 1, by omega⟩
    have h1 : (x ≫ towerMap S (Nat.le_succ a)) ≫
        verschiebungMap S D.vS (show a ≤ m₀ by omega) = 0 := by
      rw [Category.assoc, D.hvS.t_verschiebungMap (show a ≤ m₀ by omega), ← Category.assoc, hx,
        zero_comp]
    have h2 := ih b m₀ m₁ hb (by omega) (by omega) _ h1
    have h3 : (x ≫ verschiebungMap S D.vS (show a + 1 ≤ m₁ + 1 by omega)) ≫
        towerMap S (Nat.le_succ m₁) = 0 := by
      rw [Category.assoc, ← D.hvS.t_verschiebungMap (show a ≤ m₁ by omega), ← Category.assoc]
      exact h2
    obtain ⟨X', π, hπ, z, hz⟩ := D.exactS 0 m₁ (m₁ + 1) (by omega) _ h3
    have h4 : z ≫ verschiebungMap S D.vS (Nat.zero_le (m₀ + 1)) = 0 := by
      rw [← verschiebungMap_comp S D.vS (show 0 ≤ m₁ + 1 by omega)
        (show m₁ + 1 ≤ m₀ + 1 by omega), ← Category.assoc, ← hz, Category.assoc,
        Category.assoc, verschiebungMap_comp, hx, comp_zero]
    have h5 := base m₀ (by omega) z h4
    have h6 : π ≫ (x ≫ verschiebungMap S D.vS (show a + 1 ≤ m₁ + 1 by omega)) = 0 := by
      rw [hz, ← verschiebungMap_comp S D.vS (show 0 ≤ β + 1 by omega)
        (show β + 1 ≤ m₁ + 1 by omega), ← Category.assoc, h5, zero_comp]
    exact (cancel_epi π).1 (by rw [h6, comp_zero])

/-- The uniform shift of the Mittag-Leffler condition. -/
def shift [IsNoetherianObject (towerObj S 0)] : ℕ := D.verschiebung_kernel_stable.choose

/-- At every level `a`, a generalized element of `S_a` killed by `v^(b+1)` for some
`b ≥ CategoryTheory.LAdicTower.LESData.shift` is killed by `v^(shift+1)`. -/
theorem shift_spec [IsNoetherianObject (towerObj S 0)] :
    ∀ (a b m m' : ℕ) (_ : D.shift ≤ b) (hm : a + b + 1 = m) (hm' : a + D.shift + 1 = m')
      ⦃X : C⦄ (x : X ⟶ towerObj S a),
      x ≫ verschiebungMap S D.vS (show a ≤ m by omega) = 0 →
        x ≫ verschiebungMap S D.vS (show a ≤ m' by omega) = 0 :=
  D.verschiebung_kernel_stable.choose_spec

variable [IsNoetherianObject (towerObj S 0)]

omit [IsNoetherianObject (towerObj S 0)] in
/-- The Mittag-Leffler condition for any `β` with the stabilisation property of
`CategoryTheory.LAdicTower.LESData.shift`. -/
theorem mittagLeffler_of_stable (β : ℕ)
    (hβ : ∀ (a b m m' : ℕ) (_ : β ≤ b) (hm : a + b + 1 = m) (hm' : a + β + 1 = m')
      ⦃X : C⦄ (x : X ⟶ towerObj S a),
      x ≫ verschiebungMap S D.vS (show a ≤ m by omega) = 0 →
        x ≫ verschiebungMap S D.vS (show a ≤ m' by omega) = 0)
    (n m : ℕ) (hm : n + β + 1 ≤ m) ⦃X : C⦄ (x : X ⟶ towerObj T (n + β + 1)) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (y : X' ⟶ towerObj T m),
      π ≫ x ≫ towerMap T (show n ≤ n + β + 1 by omega) =
        y ≫ towerMap T (show n ≤ m by omega) := by
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst h
    exact ⟨X, 𝟙 X, inferInstance, x, Category.id_comp _⟩
  obtain ⟨c, rfl⟩ : ∃ c, m = c + β + 1 + n + 1 := ⟨m - n - β - 2, by omega⟩
  have h1 : (x ≫ towerMap T (show n ≤ n + β + 1 by omega)) ≫ D.δ (c + β + 1) n ≫
      verschiebungMap S D.vS (show c + β + 1 ≤ c + β + 1 + n + 1 by omega) = 0 := by
    rw [D.δ_verschiebungMap (c + β + 1) n (c + β + 1 + n + 1) rfl, comp_zero]
  have h2 : ((x ≫ towerMap T (show n ≤ n + β + 1 by omega)) ≫ D.δ (c + β + 1) n) ≫
      towerMap S (show β ≤ c + β + 1 by omega) = 0 := by
    rw [Category.assoc, D.δ_towerMap_le n (show β ≤ c + β + 1 by omega), Category.assoc,
      D.towerMap_δ β n (n + β + 1) (by omega), comp_zero]
  obtain ⟨X₁, π₁, hπ₁, z, hz⟩ := D.exactS c β (c + β + 1) rfl _ h2
  have h3 : z ≫ verschiebungMap S D.vS (show c ≤ c + β + 1 + n + 1 by omega) = 0 := by
    rw [← verschiebungMap_comp S D.vS (show c ≤ c + β + 1 by omega)
      (show c + β + 1 ≤ c + β + 1 + n + 1 by omega), ← Category.assoc, ← hz]
    simp only [Category.assoc] at h1 ⊢
    rw [h1, comp_zero]
  have h4 := hβ c (β + n + 1) _ (c + β + 1) (by omega) (by omega) rfl z h3
  obtain ⟨X₂, π₂, hπ₂, y, hy⟩ := D.exactδ (c + β + 1) n (c + β + 1 + n + 1) rfl
    (π₁ ≫ x ≫ towerMap T (show n ≤ n + β + 1 by omega))
    (by rw [Category.assoc, hz, h4])
  exact ⟨X₂, π₂ ≫ π₁, inferInstance, y, by simpa only [Category.assoc] using hy⟩

/-- **The Mittag-Leffler condition with a uniform shift**: a generalized element of `Tₙ` which
lifts to `T_{n+β+1}` lifts, up to refinement, to every `T_m` with `m ≥ n + β + 1`. -/
theorem mittagLeffler (n m : ℕ) (hm : n + D.shift + 1 ≤ m) ⦃X : C⦄
    (x : X ⟶ towerObj T (n + D.shift + 1)) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (y : X' ⟶ towerObj T m),
      π ≫ x ≫ towerMap T (show n ≤ n + D.shift + 1 by omega) =
        y ≫ towerMap T (show n ≤ m by omega) :=
  D.mittagLeffler_of_stable D.shift D.shift_spec n m hm x

/-! ### The tower of stable images -/

/-- The stable image `Hₙ = Im(T_{n+β+1} ⟶ Tₙ)`, as a subobject of `Tₙ`. -/
def stableImageSub (n : ℕ) : Subobject (towerObj T n) :=
  imageSubobject (towerMap T (show n ≤ n + D.shift + 1 by omega))

/-- The square inducing the transition `Hₙ₊₁ ⟶ Hₙ`. -/
def stableImageSquare (n : ℕ) :
    Arrow.mk (towerMap T (show n + 1 ≤ n + 1 + D.shift + 1 by omega)) ⟶
      Arrow.mk (towerMap T (show n ≤ n + D.shift + 1 by omega)) :=
  Arrow.homMk (towerMap T (show n + D.shift + 1 ≤ n + 1 + D.shift + 1 by omega))
    (towerMap T (Nat.le_succ n)) (by simp only [Arrow.mk_hom, towerMap_comp])

/-- The transition `Hₙ₊₁ ⟶ Hₙ` of the stable images. -/
def stableImageTransition (n : ℕ) :
    (D.stableImageSub (n + 1) : C) ⟶ (D.stableImageSub n : C) :=
  imageSubobjectMap (D.stableImageSquare n)

/-- The transition `Hₙ₊₁ ⟶ Hₙ` followed by the inclusion `Hₙ ⟶ Tₙ` is the inclusion
`Hₙ₊₁ ⟶ Tₙ₊₁` followed by the transition `Tₙ₊₁ ⟶ Tₙ`. -/
@[reassoc (attr := simp)]
theorem stableImageTransition_arrow (n : ℕ) :
    D.stableImageTransition n ≫ (D.stableImageSub n).arrow =
      (D.stableImageSub (n + 1)).arrow ≫ towerMap T (Nat.le_succ n) :=
  imageSubobjectMap_arrow _

/-- **The tower of stable images** `n ↦ Hₙ`. -/
def stableImageTower : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n => (D.stableImageSub n : C)) D.stableImageTransition

/-- The transition `Hₙ₊₁ ⟶ Hₙ` of the stable image tower is `stableImageTransition n`. -/
theorem stableImageTower_map_succ (n : ℕ) :
    towerMap D.stableImageTower (Nat.le_succ n) = D.stableImageTransition n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The inclusion `Hₙ ⟶ Tₙ` of the stable images, a map of towers. -/
def stableImageι : D.stableImageTower ⟶ T :=
  NatTrans.ofOpSequence (fun n => (D.stableImageSub n).arrow) (fun n => by
    rw [show D.stableImageTower.map (homOfLE (n.le_add_right 1)).op =
      D.stableImageTransition n from Functor.ofOpSequence_map_homOfLE_succ _ n]
    exact D.stableImageTransition_arrow n)

/-- The component of the inclusion at `n` is the arrow of the subobject `Hₙ` of `Tₙ`. -/
theorem stableImageι_app (n : ℕ) : D.stableImageι.app (op n) = (D.stableImageSub n).arrow := rfl

/-- Each component `Hₙ ⟶ Tₙ` of the inclusion is a monomorphism. -/
instance (n : ℕ) : Mono (D.stableImageι.app (op n)) :=
  (inferInstance : Mono (D.stableImageSub n).arrow)

/-- The transition of the stable images commutes with the inclusions. -/
@[reassoc]
theorem towerMap_stableImageι {n n' : ℕ} (h : n ≤ n') :
    towerMap D.stableImageTower h ≫ D.stableImageι.app (op n) =
      D.stableImageι.app (op n') ≫ towerMap T h :=
  D.stableImageι.naturality (homOfLE h).op

/-- The corestriction `T_{n+β+1} ⟶ Hₙ` of the transition. -/
def stableImageRetraction (n : ℕ) :
    towerObj T (n + D.shift + 1) ⟶ towerObj D.stableImageTower n :=
  factorThruImageSubobject (towerMap T (show n ≤ n + D.shift + 1 by omega))

/-- The corestriction `T_{n+β+1} ⟶ Hₙ` is an epimorphism. -/
instance (n : ℕ) : Epi (D.stableImageRetraction n) :=
  (inferInstance : Epi (factorThruImageSubobject (towerMap T (show n ≤ n + D.shift + 1 by omega))))

/-- The corestriction `T_{n+β+1} ⟶ Hₙ` followed by the inclusion `Hₙ ⟶ Tₙ` is the transition
`T_{n+β+1} ⟶ Tₙ`. -/
@[reassoc (attr := simp)]
theorem stableImageRetraction_ι (n : ℕ) :
    D.stableImageRetraction n ≫ D.stableImageι.app (op n) =
      towerMap T (show n ≤ n + D.shift + 1 by omega) :=
  imageSubobject_arrow_comp _

/-- The transitions of the stable images are epimorphisms. -/
theorem stableImageTransition_epi (n : ℕ) : Epi (towerMap D.stableImageTower (Nat.le_succ n)) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro X x
  obtain ⟨X₁, π₁, hπ₁, w, hw⟩ := surjective_up_to_refinements_of_epi (D.stableImageRetraction n) x
  obtain ⟨X₂, π₂, hπ₂, y, hy⟩ := D.mittagLeffler n (n + 1 + D.shift + 1) (by omega) w
  refine ⟨X₂, π₂ ≫ π₁, inferInstance, y ≫ D.stableImageRetraction (n + 1), ?_⟩
  rw [← cancel_mono (D.stableImageι.app (op n))]
  simp only [Category.assoc, D.towerMap_stableImageι, stableImageRetraction_ι_assoc, towerMap_comp]
  rw [← hy, ← stableImageRetraction_ι, reassoc_of% hw]

/-- The level `n` of `T` is killed by `ℓⁿ⁺¹`, hence so is the stable image. -/
theorem stableImage_annihilated (hT : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj T n) = 0) (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 (towerObj D.stableImageTower n) = 0 :=
  (cancel_mono (D.stableImageι.app (op n))).1
    (by rw [zero_comp, nsmul_id_comp_eq_zero _ (hT n)])

/-- **The kernel of `Hₙ₊₁ ⟶ Hₙ` is `ℓⁿ⁺¹ Hₙ₊₁`**, up to refinements. -/
theorem stableImageTransition_exact (n : ℕ) ⦃X : C⦄
    (x : X ⟶ towerObj D.stableImageTower (n + 1))
    (hx : x ≫ towerMap D.stableImageTower (Nat.le_succ n) = 0) :
    ∃ (X' : C) (π : X' ⟶ X) (_ : Epi π) (z : X' ⟶ towerObj D.stableImageTower (n + 1)),
      π ≫ x = z ≫ (ℓ ^ (n + 1) • 𝟙 _) := by
  obtain ⟨X₁, π₁, hπ₁, w, hw⟩ :=
    surjective_up_to_refinements_of_epi (D.stableImageRetraction (n + 1)) x
  have hw0 : w ≫ towerMap T (show n ≤ n + 1 + D.shift + 1 by omega) = 0 := by
    have : w ≫ towerMap T (show n ≤ n + 1 + D.shift + 1 by omega) =
        π₁ ≫ x ≫ towerMap D.stableImageTower (Nat.le_succ n) ≫ D.stableImageι.app (op n) := by
      rw [D.towerMap_stableImageι, reassoc_of% hw, stableImageRetraction_ι_assoc, towerMap_comp]
    rw [this, reassoc_of% hx, zero_comp, comp_zero]
  obtain ⟨X₂, π₂, hπ₂, y', hy'⟩ :=
    D.exactT (0 + D.shift + 1) n (n + 1 + D.shift + 1) (by omega) w hw0
  obtain ⟨X₃, π₃, hπ₃, y'', hy''⟩ := D.mittagLeffler 0 (n + 1 + D.shift + 1) (by omega) y'
  refine ⟨X₃, π₃ ≫ π₂ ≫ π₁, inferInstance, y'' ≫ D.stableImageRetraction (n + 1), ?_⟩
  rw [← cancel_mono (D.stableImageι.app (op (n + 1)))]
  have key : towerMap T (show 0 ≤ 0 + D.shift + 1 by omega) ≫
      verschiebungMap T D.vT (show 0 ≤ n + 1 by omega) =
        verschiebungMap T D.vT (show 0 + D.shift + 1 ≤ n + 1 + D.shift + 1 by omega) ≫
          towerMap T (show n + 1 ≤ n + 1 + D.shift + 1 by omega) :=
    D.hvT.towerMap_verschiebungMap _ _ _ _ (by omega)
  have key2 := D.hvT.towerMap_verschiebungMap_self (show 0 ≤ n + 1 by omega)
  simp only [Nat.sub_zero] at key2
  rw [Category.assoc (π₃ ≫ π₂ ≫ π₁), Category.assoc (y'' ≫ D.stableImageRetraction (n + 1))]
  calc (π₃ ≫ π₂ ≫ π₁) ≫ x ≫ D.stableImageι.app (op (n + 1))
      = π₃ ≫ (π₂ ≫ w) ≫ towerMap T (show n + 1 ≤ n + 1 + D.shift + 1 by omega) := by
        rw [Category.assoc, Category.assoc, reassoc_of% hw, stableImageRetraction_ι,
          Category.assoc]
    _ = π₃ ≫ y' ≫ towerMap T (show 0 ≤ 0 + D.shift + 1 by omega) ≫
          verschiebungMap T D.vT (show 0 ≤ n + 1 by omega) := by
        rw [hy', key, Category.assoc]
    _ = y'' ≫ towerMap T (show n + 1 ≤ n + 1 + D.shift + 1 by omega) ≫ (ℓ ^ (n + 1) • 𝟙 _) := by
        rw [← Category.assoc π₃, ← Category.assoc, Category.assoc π₃, hy'', Category.assoc,
          ← towerMap_comp T (show 0 ≤ n + 1 by omega)
            (show n + 1 ≤ n + 1 + D.shift + 1 by omega), Category.assoc, key2]
    _ = (y'' ≫ D.stableImageRetraction (n + 1)) ≫ (ℓ ^ (n + 1) • 𝟙 _) ≫
          D.stableImageι.app (op (n + 1)) := by
        simp only [comp_nsmul, nsmul_comp, Category.id_comp, Category.comp_id,
          stableImageRetraction_ι, Category.assoc]

/-- When the levels of `T` are killed by the powers of `ℓ`, multiplication by `ℓⁿ⁺¹` on `Hₙ₊₁`
followed by the transition `Hₙ₊₁ ⟶ Hₙ` is zero. -/
theorem stableImage_condition (hT : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj T n) = 0) (n : ℕ) :
    (ℓ ^ (n + 1) • 𝟙 (towerObj D.stableImageTower (n + 1))) ≫
      towerMap D.stableImageTower (Nat.le_succ n) = 0 := by
  rw [nsmul_id_comp_eq_zero _ (D.stableImage_annihilated hT n)]

/-- **The stable images form a strict ℓ-adic tower**: when the levels of `T` are killed by the
powers of `ℓ`, each transition `Hₙ₊₁ ⟶ Hₙ` exhibits `Hₙ` as the quotient of `Hₙ₊₁` by `ℓⁿ⁺¹`. -/
def stableImageTransition_isCokernel (hT : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj T n) = 0) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ _ (D.stableImage_condition hT n)) := by
  let Sc := ShortComplex.mk _ _ (D.stableImage_condition hT n)
  have hSc : Sc.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    exact fun _ x hx => D.stableImageTransition_exact n x hx
  haveI : Epi Sc.g := D.stableImageTransition_epi n
  exact hSc.gIsCokernel

/-- The corestrictions are natural. -/
theorem towerMap_stableImageRetraction {n n' : ℕ} (h : n ≤ n') :
    towerMap T (show n + D.shift + 1 ≤ n' + D.shift + 1 by omega) ≫ D.stableImageRetraction n =
      D.stableImageRetraction n' ≫ towerMap D.stableImageTower h := by
  rw [← cancel_mono (D.stableImageι.app (op n)), Category.assoc, Category.assoc,
    stableImageRetraction_ι, D.towerMap_stableImageι, stableImageRetraction_ι_assoc,
    towerMap_comp, towerMap_comp]

/-- The inclusion followed by the corestriction is the transition of the stable images. -/
theorem stableImageι_stableImageRetraction (n : ℕ) :
    D.stableImageι.app (op (n + D.shift + 1)) ≫ D.stableImageRetraction n =
      towerMap D.stableImageTower (show n ≤ n + D.shift + 1 by omega) := by
  rw [← cancel_mono (D.stableImageι.app (op n)), Category.assoc, stableImageRetraction_ι,
    D.towerMap_stableImageι]

end LESData

end LES

/-! ### Limits along a pro-isomorphism of towers -/

section ProIso

variable {D : Type*} [Category* D]

/-- **Pro-isomorphic towers have isomorphic limits**: a map of towers `f : A ⟶ B` together with
maps `g n : B_{N n} ⟶ Aₙ` which are inverse to `f` up to the transition maps induces an
isomorphism of limits. -/
theorem isIso_limMap_of_proInverse {A B : ℕᵒᵖ ⥤ D} [HasLimit A] [HasLimit B] (f : A ⟶ B)
    (N : ℕ → ℕ) (hN : ∀ n, n ≤ N n) (hNm : Monotone N)
    (g : ∀ n, towerObj B (N n) ⟶ towerObj A n)
    (hg : ∀ n n' (h : n ≤ n'), towerMap B (hNm h) ≫ g n = g n' ≫ towerMap A h)
    (hfg : ∀ n, g n ≫ f.app (op n) = towerMap B (hN n))
    (hgf : ∀ n, f.app (op (N n)) ≫ g n = towerMap A (hN n)) :
    IsIso (limMap f) := by
  let c : Cone A :=
    { pt := limit B
      π :=
        { app := fun j => limit.π B (op (N j.unop)) ≫ g j.unop
          naturality := fun j j' u => by
            have h : j'.unop ≤ j.unop := leOfHom u.unop
            obtain rfl : u = (homOfLE h).op := rfl
            dsimp
            rw [Category.id_comp, Category.assoc]
            change _ = _ ≫ g j.unop ≫ towerMap A h
            rw [← hg _ _ h, ← Category.assoc]
            exact congrArg (· ≫ g j'.unop) (limit.w B (homOfLE (hNm h)).op).symm } }
  refine ⟨⟨limit.lift A c, limit.hom_ext fun j => ?_, limit.hom_ext fun j => ?_⟩⟩
  · rw [Category.assoc, limit.lift_π, Category.id_comp]
    dsimp [c]
    rw [limMap_π_assoc, hgf]
    exact limit.w A (homOfLE (hN j.unop)).op
  · rw [Category.assoc, limMap_π, limit.lift_π_assoc, Category.id_comp]
    dsimp [c]
    rw [Category.assoc, hfg]
    exact limit.w B (homOfLE (hN j.unop)).op

end ProIso

end CategoryTheory.LAdicTower
