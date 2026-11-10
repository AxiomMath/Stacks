module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite
public import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Additive characters of `A / K` and their duality with `K`

Let `K` be a function field over a finite field `k` of characteristic `p`, with adele ring `A`,
and let `Λ` be a field. An *adelic character* is an additive character `ψ : A → Λ` which is
trivial on `K` and on one of the lattices `A(D) = {a | ord_v a_v ≥ -D(v)}`; these are the
continuous characters of the compact group `A / K` (the lattices `A(D)` form a basis of
neighbourhoods of `0`). For `ξ ∈ K` the character `a ↦ ψ(ξ a)` is again adelic.

We prove the duality theorem: if `ψ` is a nontrivial adelic character, every adelic character is
`a ↦ ψ(ξ a)` for exactly one `ξ ∈ K`. That is, `ξ ↦ ψ(ξ ·)` identifies `K` with the group of
continuous characters of `A / K`. When `Λ` contains the `p`-th roots of unity a nontrivial adelic
character exists. Finally, a nontrivial adelic character has a greatest lattice on which it is
trivial: there is a divisor `W` with `ψ(A(D)) = 1 ↔ D ≤ W` (the divisor of `ψ`, which is a
canonical divisor of `K`).

The duality theorem is proved by counting, with Riemann–Roch in the cardinality form
`ℓ(D) / h¹(D) = N(D) · ℓ(0) / h¹(0)`: if `χ` were not of the form `ψ(ξ ·)`, then for every
divisor `B` the characters `ψ(ξ ·) χ(η ·)` with `ξ ∈ L(D_ψ + B)` and `η ∈ L(D_χ + B)` would be
distinct characters of `A / (K + A(-B))`, so `ℓ(D_ψ + B) ℓ(D_χ + B) ≤ h¹(-B)`; the left side
grows like `N(B)²` and the right side like `N(B)`.

These are the additive characters of the Fourier–Whittaker expansion of cusp forms, the first
step of the converse theorem route to Stacks Tag 03VU.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.IsAdelicChar` — `ψ` is trivial on `K` and on some `A(D)`.
* `Stacks.Adeles.GlobalFunctionField.liftChar` — the character of `G ⧸ H` induced by a
  character of `G` trivial on `H`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.existsUnique_eq_mulShift` — duality: every adelic
  character is `ψ(ξ ·)` for a unique `ξ ∈ K`.
* `Stacks.Adeles.GlobalFunctionField.exists_isAdelicChar_ne_one` — a nontrivial adelic
  character exists when `Λ` has enough `p`-th roots of unity.
* `Stacks.Adeles.GlobalFunctionField.exists_forall_trivial_iff_le` — the greatest lattice
  `A(W)` on which a nontrivial adelic character is trivial.

## References

* A. Weil, *Basic Number Theory*, Chapter IV, §2 and Chapter VI.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section FiniteGroup

variable {G : Type*} [AddCommGroup G] {Λ : Type*} [Field Λ]

/-- The character of `G ⧸ H` induced by a character `θ` of `G` trivial on `H`. -/
public def liftChar (H : AddSubgroup G) (θ : AddChar G Λ) (hθ : ∀ a ∈ H, θ a = 1) :
    AddChar (G ⧸ H) Λ where
  toFun g := Quotient.liftOn' g θ fun a b hab => by
    rw [QuotientAddGroup.leftRel_apply] at hab
    rw [← mul_one (θ a), ← hθ _ hab, ← AddChar.map_add_eq_mul, add_neg_cancel_left]
  map_zero_eq_one' := θ.map_zero_eq_one
  map_add_eq_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    exact θ.map_add_eq_mul a b

/-- `liftChar H θ hθ` evaluates on the class of `a` to `θ a`. -/
@[simp]
public theorem liftChar_mk (H : AddSubgroup G) (θ : AddChar G Λ) (hθ : ∀ a ∈ H, θ a = 1)
    (a : G) : liftChar H θ hθ (a : G ⧸ H) = θ a := rfl

/-- A finite group has finitely many `Λ`-valued characters (Dedekind's independence of
characters). -/
public theorem finite_addChar [Finite G] : Finite (AddChar G Λ) := by
  have := Fintype.ofFinite G
  have : Finite (Multiplicative G →* Λ) :=
    (linearIndependent_monoidHom (Multiplicative G) Λ).finite
  exact Finite.of_equiv _ AddChar.toMonoidHomEquiv.symm

/-- A finite group `G` has at most `#G` characters with values in a field. -/
public theorem natCard_addChar_le [Finite G] : Nat.card (AddChar G Λ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  have hli := linearIndependent_monoidHom (Multiplicative G) Λ
  have : Finite (Multiplicative G →* Λ) := hli.finite
  have := Fintype.ofFinite (Multiplicative G →* Λ)
  rw [Nat.card_congr AddChar.toMonoidHomEquiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_multiplicative] at this

/-- The characters of `G` trivial on `H` inject into the characters of `G ⧸ H`. -/
public theorem liftChar_injective (H : AddSubgroup G) :
    Function.Injective fun θ : {θ : AddChar G Λ // ∀ a ∈ H, θ a = 1} => liftChar H θ.1 θ.2 := by
  intro θ θ' h
  apply Subtype.ext
  ext a
  exact DFunLike.congr_fun h (a : G ⧸ H)

/-- A subgroup `H` of finite index has finitely many characters of `G` trivial on it. -/
public theorem finite_trivialOn (H : AddSubgroup G) [Finite (G ⧸ H)] :
    Finite {θ : AddChar G Λ // ∀ a ∈ H, θ a = 1} := by
  have := finite_addChar (G := G ⧸ H) (Λ := Λ)
  exact Finite.of_injective _ (liftChar_injective H)

/-- The characters of `G` trivial on a subgroup `H` of finite index are at most `[G : H]` in
number. -/
public theorem natCard_trivialOn_le_index (H : AddSubgroup G) [Finite (G ⧸ H)] :
    Nat.card {θ : AddChar G Λ // ∀ a ∈ H, θ a = 1} ≤ H.index := by
  have := finite_addChar (G := G ⧸ H) (Λ := Λ)
  calc _ ≤ Nat.card (AddChar (G ⧸ H) Λ) := Nat.card_le_card_of_injective _ (liftChar_injective H)
    _ ≤ Nat.card (G ⧸ H) := natCard_addChar_le
    _ = H.index := rfl

/-- The character `b ↦ φ(b mod H)` of `G` defined by a homomorphism `φ` from `G ⧸ H` to `Λˣ`. -/
public def charOfHom (H : AddSubgroup G) (φ : Multiplicative (G ⧸ H) →* Λˣ) : AddChar G Λ where
  toFun b := (φ (Multiplicative.ofAdd (b : G ⧸ H)) : Λ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' b b' := by
    rw [QuotientAddGroup.mk_add, ofAdd_add, map_mul, Units.val_mul]

/-- `charOfHom H φ` sends `b` to `φ(b mod H)`. -/
public theorem charOfHom_apply (H : AddSubgroup G) (φ : Multiplicative (G ⧸ H) →* Λˣ) (b : G) :
    charOfHom H φ b = φ (Multiplicative.ofAdd (b : G ⧸ H)) := rfl

/-- The character `charOfHom H φ` is trivial on `H`. -/
public theorem charOfHom_eq_one_of_mem (H : AddSubgroup G) (φ : Multiplicative (G ⧸ H) →* Λˣ)
    {b : G} (hb : b ∈ H) : charOfHom H φ b = 1 := by
  rw [charOfHom_apply, (QuotientAddGroup.eq_zero_iff b).2 hb, ofAdd_zero, map_one, Units.val_one]

/-- Distinct homomorphisms `G ⧸ H → Λˣ` give distinct characters `charOfHom H φ`. -/
public theorem charOfHom_injective (H : AddSubgroup G) :
    Function.Injective (charOfHom (Λ := Λ) H) := by
  intro φ φ' h
  refine MonoidHom.ext fun g => Units.ext ?_
  induction g using Multiplicative.rec with | ofAdd g => ?_
  induction g using QuotientAddGroup.induction_on with | H b => ?_
  exact DFunLike.congr_fun h b

end FiniteGroup

section KFree

variable {K : Type u} [Field K]

open scoped Classical in
/-- `A(D ⊔ D') = A(D) + A(D')`: an adele in `A(D ⊔ D')` is the sum of its components at the
places where `D' > D`, which lie in `A(D')`, and of the rest, which lies in `A(D)`. -/
public theorem adeleLattice_sup_le (D D' : Place K →₀ ℤ) :
    adeleLattice K (D ⊔ D') ≤ adeleLattice K D ⊔ adeleLattice K D' := by
  intro a ha
  set T := (D ⊔ D' - D).support
  set z : AdeleRing K := ∑ v ∈ T, singleAdele v (a v)
  have hz : ∀ w, z w = if w ∈ T then a w else 0 := by
    intro w
    rw [show z w = ∑ v ∈ T, singleAdele v (a v) w from map_sum (evalAt K w) _ T]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun v _ hv => singleAdele_apply_ne (Ne.symm hv) _)
        (fun h => absurd hw h), singleAdele_apply_self]
    · exact Finset.sum_eq_zero fun v hv => singleAdele_apply_ne (fun h : w = v => hw (h ▸ hv)) _
  have hT : ∀ w, w ∈ T ↔ D w < D' w := by
    intro w
    simp only [T, Finsupp.mem_support_iff, Finsupp.coe_sub, Pi.sub_apply, Finsupp.sup_apply]
    omega
  have hz' : z ∈ adeleLattice K D' := by
    intro w
    rw [hz w]
    split_ifs with hw
    · have := ha w
      rwa [Finsupp.sup_apply, max_eq_right ((hT w).1 hw).le] at this
    · exact (w.ball _).zero_mem
  have hr : a - z ∈ adeleLattice K D := by
    intro w
    change a w - z w ∈ _
    rw [hz w]
    split_ifs with hw
    · rw [sub_self]
      exact (w.ball _).zero_mem
    · have := ha w
      rw [Finsupp.sup_apply, max_eq_left (not_lt.1 fun h => hw ((hT w).2 h))] at this
      rwa [sub_zero]
  have := AddSubgroup.add_mem_sup hr hz'
  rwa [sub_add_cancel] at this

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

variable (K) in
/-- An *adelic character*: an additive character `ψ : A → Λ` trivial on `K` and on some lattice
`A(D)`, that is, a continuous character of `A / K`. -/
public def IsAdelicChar (ψ : AddChar (AdeleRing K) Λ) : Prop :=
  (∀ κ : K, ψ (diag k K κ) = 1) ∧ ∃ D : Place K →₀ ℤ, ∀ a ∈ adeleLattice K D, ψ a = 1

/-- A character trivial on `K` and on `A(D)` is trivial on `K + A(D)`. -/
public theorem apply_eq_one_of_mem_sup {ψ : AddChar (AdeleRing K) Λ}
    (hK : ∀ κ : K, ψ (diag k K κ) = 1) {D : Place K →₀ ℤ}
    (hD : ∀ a ∈ adeleLattice K D, ψ a = 1) {a : AdeleRing K}
    (ha : a ∈ principal k K ⊔ adeleLattice K D) : ψ a = 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 ha
  obtain ⟨κ, rfl⟩ := (mem_principal k).1 hy
  rw [AddChar.map_add_eq_mul, hK κ, hD z hz, one_mul]

/-- `L(E) · A(F) ⊆ A(E + F)`. -/
public theorem diag_mul_mem_adeleLattice {E F : Place K →₀ ℤ} {ξ : K}
    (hξ : diag k K ξ ∈ adeleLattice K E) {a : AdeleRing K} (ha : a ∈ adeleLattice K F) :
    diag k K ξ * a ∈ adeleLattice K (E + F) := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · rw [map_zero, zero_mul]
    exact AddSubgroup.zero_mem _
  rcases (diag_mem_adeleLattice_iff k).1 hξ with h | h
  · exact absurd h hξ0
  have hle : F ≤ E + F + principalDivisor k K ξ := fun v => by
    have := h v
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
    omega
  have := (mul_mem_adeleLattice_iff k hξ0 (D := E + F + principalDivisor k K ξ)).2
    (adeleLattice_mono k hle ha)
  rwa [add_sub_cancel_right] at this

/-- The shift `a ↦ ψ(ξ a)` of an adelic character by `ξ ∈ K` is adelic. -/
public theorem IsAdelicChar.mulShift {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ)
    (ξ : K) : IsAdelicChar k K (ψ.mulShift (diag k K ξ)) := by
  obtain ⟨h1, D, hD⟩ := hψ
  refine ⟨fun κ => by rw [AddChar.mulShift_apply, ← (diag k K).map_mul]; exact h1 _, ?_⟩
  rcases eq_or_ne ξ 0 with rfl | hξ
  · exact ⟨0, fun a _ => by simp⟩
  · refine ⟨D + principalDivisor k K ξ, fun a ha => ?_⟩
    rw [AddChar.mulShift_apply]
    apply hD
    have := (mul_mem_adeleLattice_iff k hξ (D := D + principalDivisor k K ξ)).2 ha
    rwa [add_sub_cancel_right] at this

/-- For a nontrivial character `ψ`, the shift `ψ(ξ ·)` is trivial only for `ξ = 0`. -/
public theorem mulShift_diag_eq_one_iff {ψ : AddChar (AdeleRing K) Λ} (hψ : ψ ≠ 1) {ξ : K} :
    ψ.mulShift (diag k K ξ) = 1 ↔ ξ = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero, AddChar.mulShift_zero]⟩
  by_contra hξ
  apply hψ
  ext a
  have := DFunLike.congr_fun h (diag k K ξ⁻¹ * a)
  rw [AddChar.mulShift_apply, ← mul_assoc, ← (diag k K).map_mul, mul_inv_cancel₀ hξ, map_one,
    one_mul] at this
  simpa using this

/-- A shift of `ψ` by an element of `L(D + B)` is trivial on `K + A(-B)` when `ψ` is trivial on
`K` and on `A(D)`. -/
public theorem mulShift_apply_eq_one {ψ : AddChar (AdeleRing K) Λ}
    (hK : ∀ κ : K, ψ (diag k K κ) = 1) {D B : Place K →₀ ℤ}
    (hD : ∀ a ∈ adeleLattice K D, ψ a = 1) {x : AdeleRing K}
    (hx : x ∈ principal k K ⊓ adeleLattice K (D + B)) {a : AdeleRing K}
    (ha : a ∈ principal k K ⊔ adeleLattice K (-B)) : ψ.mulShift x a = 1 := by
  obtain ⟨ξ, rfl⟩ := (mem_principal k).1 (AddSubgroup.mem_inf.1 hx).1
  refine apply_eq_one_of_mem_sup k (fun κ => ?_) (fun a ha => ?_) ha
  · rw [AddChar.mulShift_apply, ← (diag k K).map_mul]
    exact hK _
  · rw [AddChar.mulShift_apply]
    apply hD
    have := diag_mul_mem_adeleLattice k (AddSubgroup.mem_inf.1 hx).2 ha
    rwa [add_neg_cancel_right] at this

/-- The counting inequality behind duality: if `χ` is not a shift of `ψ`, then
`ℓ(D_ψ + B) · ℓ(D_χ + B) ≤ h¹(-B)` for every divisor `B`. -/
public theorem ell_mul_ell_le_hOne {ψ χ : AddChar (AdeleRing K) Λ}
    (hψK : ∀ κ : K, ψ (diag k K κ) = 1) {Dψ : Place K →₀ ℤ}
    (hDψ : ∀ a ∈ adeleLattice K Dψ, ψ a = 1) (hψ1 : ψ ≠ 1)
    (hχK : ∀ κ : K, χ (diag k K κ) = 1) {Dχ : Place K →₀ ℤ}
    (hDχ : ∀ a ∈ adeleLattice K Dχ, χ a = 1)
    (hno : ∀ ξ : K, χ ≠ ψ.mulShift (diag k K ξ)) (B : Place K →₀ ℤ) :
    ell k K (Dψ + B) * ell k K (Dχ + B) ≤ hOne k K (-B) := by
  set H := principal k K ⊔ adeleLattice K (-B)
  have : Finite (AdeleRing K ⧸ H) := finite_quotient_principal_sup_adeleLattice k (-B)
  have := finite_trivialOn (Λ := Λ) H
  let Φ : ↥(principal k K ⊓ adeleLattice K (Dψ + B)) × ↥(principal k K ⊓ adeleLattice K (Dχ + B)) →
      {θ : AddChar (AdeleRing K) Λ // ∀ a ∈ H, θ a = 1} := fun p =>
    ⟨ψ.mulShift p.1 * χ.mulShift p.2, fun a ha => by
      rw [AddChar.mul_apply, mulShift_apply_eq_one k hψK hDψ p.1.2 ha,
        mulShift_apply_eq_one k hχK hDχ p.2.2 ha, one_mul]⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    have h0 : ψ.mulShift x * χ.mulShift y = ψ.mulShift x' * χ.mulShift y' :=
      congrArg Subtype.val h
    have h1 : ψ.mulShift (x - x') = χ.mulShift (y' - y) := by
      have e1 : ψ.mulShift (x - x') = ψ.mulShift x / ψ.mulShift x' := by
        rw [eq_div_iff_mul_eq', AddChar.mulShift_mul, sub_add_cancel]
      have e2 : χ.mulShift (y' - y) = χ.mulShift y' / χ.mulShift y := by
        rw [eq_div_iff_mul_eq', AddChar.mulShift_mul, sub_add_cancel]
      rw [e1, e2, div_eq_div_iff_mul_eq_mul, h0, mul_comm]
    obtain ⟨ξ, hξ⟩ := (mem_principal k).1 (AddSubgroup.sub_mem _ (AddSubgroup.mem_inf.1 hx).1
      (AddSubgroup.mem_inf.1 hx').1)
    obtain ⟨η, hη⟩ := (mem_principal k).1 (AddSubgroup.sub_mem _ (AddSubgroup.mem_inf.1 hy').1
      (AddSubgroup.mem_inf.1 hy).1)
    rcases eq_or_ne η 0 with rfl | hη0
    · rw [map_zero] at hη
      rw [← hη, AddChar.mulShift_zero, ← hξ, mulShift_diag_eq_one_iff k hψ1] at h1
      rw [h1, map_zero] at hξ
      obtain rfl : x = x' := sub_eq_zero.1 hξ.symm
      obtain rfl : y = y' := (sub_eq_zero.1 hη.symm).symm
      rfl
    · exfalso
      apply hno (ξ * η⁻¹)
      ext a
      have := DFunLike.congr_fun h1 (diag k K η⁻¹ * a)
      rw [← hξ, ← hη, AddChar.mulShift_apply, AddChar.mulShift_apply, ← mul_assoc, ← mul_assoc,
        ← (diag k K).map_mul, ← (diag k K).map_mul, mul_inv_cancel₀ hη0, map_one, one_mul] at this
      rw [AddChar.mulShift_apply]
      exact this.symm
  have := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at this
  exact this.trans (natCard_trivialOn_le_index H)

/-- There is a divisor whose norm exceeds any given bound (and `1`). -/
private theorem exists_one_lt_divNorm_gt (k : Type u) [Field k] [Finite k] {K : Type u}
    [Field K] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] (M : ℚ) :
    ∃ B : Place K →₀ ℤ, 1 < divNorm K B ∧ M < divNorm K B := by
  set v₀ := basePlace k K
  have hq : (1 : ℚ) < v₀.resCard := by exact_mod_cast one_lt_resCard k v₀
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 M) hq
  have hNB : divNorm K ((n + 1) • Finsupp.single v₀ 1) = (v₀.resCard : ℚ) ^ (n + 1) := by
    rw [divNorm_nsmul k, divNorm_single, zpow_one]
  have h : max 1 M < divNorm K ((n + 1) • Finsupp.single v₀ 1) := by
    rw [hNB, pow_succ (v₀.resCard : ℚ) n]
    exact hn.trans_le (le_mul_of_one_le_right (by positivity) hq.le)
  exact ⟨_, (le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩

/-- **Duality for the adelic characters of a function field.** If `ψ` is a nontrivial adelic
character, every adelic character `χ` is `a ↦ ψ(ξ a)` for one and only one `ξ ∈ K`. -/
public theorem existsUnique_eq_mulShift {ψ χ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) (hχ : IsAdelicChar k K χ) :
    ∃! ξ : K, χ = ψ.mulShift (diag k K ξ) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · by_contra hno
    push Not at hno
    obtain ⟨hψK, Dψ, hDψ⟩ := hψ
    obtain ⟨hχK, Dχ, hDχ⟩ := hχ
    set c : ℚ := ell k K 0 / hOne k K 0
    have hc : 0 < c := chi_zero_pos k
    have ha := divNorm_pos k Dψ
    have hb := divNorm_pos k Dχ
    obtain ⟨B, hX1, hXn⟩ :=
      exists_one_lt_divNorm_gt k (K := K) (1 / (c ^ 3 * divNorm K Dψ * divNorm K Dχ))
    obtain ⟨X, hXdef⟩ : ∃ X, divNorm K B = X := ⟨_, rfl⟩
    rw [hXdef] at hX1 hXn
    have hX0 : 0 < X := zero_lt_one.trans hX1
    -- `h¹(-B) = N(B) / c`
    have hNmB : divNorm K (-B) = X⁻¹ := by rw [divNorm_neg k B, hXdef]
    have hellmB : ell k K (-B) = 1 :=
      ell_eq_one_of_divNorm_lt_one k (by rw [hNmB]; exact inv_lt_one_of_one_lt₀ hX1)
    have hRR := ell_div_hOne k (-B)
    rw [hellmB, hNmB, Nat.cast_one] at hRR
    have hh : (hOne k K (-B) : ℚ) = X / c := by
      rw [one_div, inv_eq_iff_eq_inv, mul_inv, inv_inv] at hRR
      rw [hRR, ← div_eq_mul_inv]
    -- `ℓ(D + B) ≥ N(D) N(B) c`
    have h1 := divNorm_mul_chi_le_ell k (Dψ + B)
    have h2 := divNorm_mul_chi_le_ell k (Dχ + B)
    rw [divNorm_add k, hXdef] at h1 h2
    have key : ((ell k K (Dψ + B) * ell k K (Dχ + B) : ℕ) : ℚ) ≤ hOne k K (-B) := by
      exact_mod_cast ell_mul_ell_le_hOne k hψK hDψ hψ1 hχK hDχ hno B
    rw [Nat.cast_mul, hh] at key
    have hprod : divNorm K Dψ * X * c * (divNorm K Dχ * X * c) ≤ X / c :=
      (mul_le_mul h1 h2 (by positivity) (by positivity)).trans key
    have hfin : c ^ 3 * divNorm K Dψ * divNorm K Dχ * X ≤ 1 := by
      rw [le_div_iff₀ hc] at hprod
      have : c ^ 3 * divNorm K Dψ * divNorm K Dχ * X * X ≤ 1 * X := by nlinarith
      exact le_of_mul_le_mul_right this hX0
    rw [div_lt_iff₀ (by positivity)] at hXn
    linarith
  · intro ξ ξ' h h'
    have h0 : ψ.mulShift (diag k K (ξ - ξ')) = 1 := by
      have e : ψ.mulShift (diag k K (ξ - ξ')) * ψ.mulShift (diag k K ξ') =
          ψ.mulShift (diag k K ξ) := by
        rw [AddChar.mulShift_mul, ← map_add, sub_add_cancel]
      rwa [← h, ← h', mul_eq_right] at e
    exact sub_eq_zero.1 ((mulShift_diag_eq_one_iff k hψ1).1 h0)

/-- The adeles are killed by the characteristic `p` of `k`. -/
private theorem ringChar_nsmul_adele (a : AdeleRing K) : ringChar k • a = 0 := by
  have hK : ((ringChar k : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap k K), ringChar.Nat.cast_ringChar, map_zero]
  rw [nsmul_eq_mul, ← map_natCast (diag k K), hK, map_zero, zero_mul]

/-- The quotients of `A` have exponent dividing `p`. -/
public theorem exponent_dvd_ringChar (H : AddSubgroup (AdeleRing K)) :
    Monoid.exponent (Multiplicative (AdeleRing K ⧸ H)) ∣ ringChar k := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  induction g using Multiplicative.rec with | ofAdd g => ?_
  induction g using QuotientAddGroup.induction_on with | H b => ?_
  rw [← ofAdd_nsmul, ← QuotientAddGroup.mk_nsmul, ringChar_nsmul_adele k b]
  rfl

/-- A point `b ∉ K + A(D)` is detected by an adelic character trivial on `K + A(D)`, when `Λ` has
enough `p`-th roots of unity. -/
public theorem exists_charOfHom_apply_ne_one [HasEnoughRootsOfUnity Λ (ringChar k)]
    {D : Place K →₀ ℤ} {b : AdeleRing K} (hb : b ∉ principal k K ⊔ adeleLattice K D) :
    ∃ φ : Multiplicative (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) →* Λˣ,
      IsAdelicChar k K (charOfHom _ φ) ∧ charOfHom _ φ b ≠ 1 := by
  have : NeZero (ringChar k) := ⟨CharP.char_ne_zero_of_finite k (ringChar k)⟩
  set H := principal k K ⊔ adeleLattice K D
  have : Finite (AdeleRing K ⧸ H) := finite_quotient_principal_sup_adeleLattice k D
  have hg : Multiplicative.ofAdd (b : AdeleRing K ⧸ H) ≠ 1 := by
    rwa [Ne, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, QuotientAddGroup.eq_zero_iff]
  have := HasEnoughRootsOfUnity.of_dvd Λ (exponent_dvd_ringChar k H)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (Multiplicative (AdeleRing K ⧸ H)) Λ hg
  refine ⟨φ, ⟨fun κ => charOfHom_eq_one_of_mem H φ
    (AddSubgroup.mem_sup_left ((mem_principal k).2 ⟨κ, rfl⟩)),
    D, fun a ha => charOfHom_eq_one_of_mem H φ (AddSubgroup.mem_sup_right ha)⟩, fun h => hφ ?_⟩
  rw [charOfHom_apply] at h
  exact Units.val_eq_one.1 h

/-- **A nontrivial adelic character exists** when `Λ` has enough `p`-th roots of unity, `p` the
characteristic of `k` (for instance, `Λ` algebraically closed of characteristic `≠ p`). -/
public theorem exists_isAdelicChar_ne_one [HasEnoughRootsOfUnity Λ (ringChar k)] :
    ∃ ψ : AddChar (AdeleRing K) Λ, IsAdelicChar k K ψ ∧ ψ ≠ 1 := by
  set c : ℚ := ell k K 0 / hOne k K 0
  have hc : 0 < c := chi_zero_pos k
  obtain ⟨B, -, hXc⟩ := exists_one_lt_divNorm_gt k (K := K) c
  set H := principal k K ⊔ adeleLattice K (-B)
  -- `h¹(-B) ≥ N(B) / c > 1`
  have hidx : 1 < H.index := by
    have hRR := ell_div_hOne k (-B)
    rw [divNorm_neg k] at hRR
    have hl : (1 : ℚ) ≤ ell k K (-B) := by exact_mod_cast ell_pos k (-B)
    have hh0 : (0 : ℚ) < hOne k K (-B) := by exact_mod_cast Nat.pos_of_ne_zero (hOne_ne_zero k _)
    have hX0 : 0 < divNorm K B := divNorm_pos k B
    have : (1 : ℚ) < hOne k K (-B) := by
      have e : (ell k K (-B) : ℚ) = (divNorm K B)⁻¹ * c * hOne k K (-B) := by
        rwa [div_eq_iff hh0.ne'] at hRR
      by_contra hle
      push Not at hle
      have : (ell k K (-B) : ℚ) < 1 := by
        rw [e]
        calc (divNorm K B)⁻¹ * c * hOne k K (-B) ≤ (divNorm K B)⁻¹ * c * 1 := by gcongr
          _ < 1 := by rwa [mul_one, inv_mul_lt_iff₀ hX0, mul_one]
      linarith
    exact_mod_cast this
  have hne : H ≠ ⊤ := fun h => by simp [h] at hidx
  obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt hne.lt_top
  obtain ⟨φ, hφ, ha'⟩ := exists_charOfHom_apply_ne_one k (Λ := Λ) ha
  exact ⟨charOfHom _ φ, hφ, fun h => ha' (by rw [h, AddChar.one_apply])⟩

/-- **Characters of `A / (K + A(D))` separate points.** If `ψ` is a nontrivial adelic character
and `b ∉ K + A(D)`, some shift `ψ(ξ ·)` trivial on `A(D)` is nontrivial at `b`. -/
public theorem exists_mulShift_apply_ne_one [HasEnoughRootsOfUnity Λ (ringChar k)]
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) {D : Place K →₀ ℤ}
    {b : AdeleRing K} (hb : b ∉ principal k K ⊔ adeleLattice K D) :
    ∃ ξ : K, (∀ a ∈ adeleLattice K D, ψ (diag k K ξ * a) = 1) ∧ ψ (diag k K ξ * b) ≠ 1 := by
  obtain ⟨φ, hθ, hb'⟩ := exists_charOfHom_apply_ne_one k (Λ := Λ) hb
  obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_mulShift k hψ hψ1 hθ
  refine ⟨ξ, fun a ha => ?_, ?_⟩
  · rw [← AddChar.mulShift_apply, ← hξ]
    exact charOfHom_eq_one_of_mem _ φ (AddSubgroup.mem_sup_right ha)
  · rwa [← AddChar.mulShift_apply, ← hξ]

/-- **The divisor of a nontrivial adelic character.** There is a greatest lattice `A(W)` on which
a nontrivial adelic character `ψ` is trivial: `ψ` is trivial on `A(D)` exactly when `D ≤ W`. -/
public theorem exists_forall_trivial_iff_le {ψ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) :
    ∃ W : Place K →₀ ℤ, ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) ↔ D ≤ W := by
  classical
  obtain ⟨hK, D₀, hD₀⟩ := hψ
  set S : (Place K →₀ ℤ) → Prop := fun D => ∀ a ∈ adeleLattice K D, ψ a = 1
  have hsup : ∀ D D', S D → S D' → S (D ⊔ D') := by
    intro D D' hD hD' a ha
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 (adeleLattice_sup_le D D' ha)
    rw [AddChar.map_add_eq_mul, hD y hy, hD' z hz, one_mul]
  obtain ⟨M₀, hM₀⟩ := exists_sup_adeleLattice_eq_top k (K := K)
  have hbd : ∀ D, S D → divNorm K D < M₀ := by
    intro D hD
    by_contra hle
    push Not at hle
    exact hψ1 <| DFunLike.ext _ _ fun a =>
      apply_eq_one_of_mem_sup k hK hD (by rw [hM₀ D hle]; exact AddSubgroup.mem_top a)
  set F := {E : Place K →₀ ℤ | 0 ≤ E ∧ divNorm K E ≤ M₀ / divNorm K D₀ ∧ S (D₀ + E)}
  have hF : F.Finite := (finite_setOf_nonneg_divNorm_le k (M₀ / divNorm K D₀)).subset
    fun E hE => ⟨hE.1, hE.2.1⟩
  have hF0 : (0 : Place K →₀ ℤ) ∈ F := by
    refine ⟨le_rfl, ?_, by simpa using hD₀⟩
    rw [divNorm_zero, le_div_iff₀ (divNorm_pos k D₀), one_mul]
    exact (hbd D₀ hD₀).le
  have hne : hF.toFinset.Nonempty := ⟨0, hF.mem_toFinset.2 hF0⟩
  refine ⟨D₀ + hF.toFinset.sup' hne id, fun D => ⟨fun hD => ?_, fun hle a ha => ?_⟩⟩
  · -- `D ≤ D ⊔ D₀ = D₀ + E` with `E ∈ F`
    set E := D ⊔ D₀ - D₀
    have hE : E ∈ F := by
      have hS : S (D₀ + E) := by
        rw [add_sub_cancel]
        exact hsup D D₀ hD hD₀
      refine ⟨sub_nonneg.2 le_sup_right, ?_, hS⟩
      rw [le_div_iff₀ (divNorm_pos k D₀), mul_comm, ← divNorm_add k]
      exact (hbd _ hS).le
    calc D ≤ D ⊔ D₀ := le_sup_left
      _ = D₀ + E := (add_sub_cancel _ _).symm
      _ ≤ D₀ + hF.toFinset.sup' hne id := by
        gcongr
        exact Finset.le_sup' id (hF.mem_toFinset.2 hE)
  · -- `A(D) ⊆ A(W)` and `ψ` is trivial on `A(W)`
    have hW : S (D₀ + hF.toFinset.sup' hne id) := by
      refine Finset.sup'_induction hne id (p := fun E => S (D₀ + E)) (fun E₁ h₁ E₂ h₂ => ?_)
        fun E hE => (hF.mem_toFinset.1 hE).2.2
      rw [add_sup]
      exact hsup _ _ h₁ h₂
    exact hW a (adeleLattice_mono k hle ha)

end Stacks.Adeles.GlobalFunctionField

end
