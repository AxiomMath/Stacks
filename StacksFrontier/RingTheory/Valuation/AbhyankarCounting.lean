module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import StacksFrontier.RingTheory.HilbertSamuel.DimensionTheorem
import StacksFrontier.RingTheory.HilbertSamuel.Function

/-!
# Abhyankar's inequality: monomials of independent value and the counting step

Let `V` be a valuation ring and `x₁, …, x_r ∈ V`. The values `v(x₁), …, v(x_r)` in the value
group of `V` are `ℤ`-linearly independent exactly when distinct monomials `x^α`, `x^β`
(`α, β ∈ ℕ^r`) are never associated in `V`, i.e. never have the same value. This file records
that condition, `Stacks.Abhyankar.MonomialIndependent`, which mentions no value group and no
fraction field, and proves the *counting step* of Abhyankar's inequality.

The counting step is the archimedean case of the bound `r ≤ dim B` for a Noetherian local ring
`B` with a local homomorphism `φ : B → V`: if `f₁, …, f_d` is a system of parameters of `B` and
every `φ(f_j)` has, up to a power, a value larger than every `v(φ(xᵢ))`, then `r ≤ d`. The
monomials `x^α` with all exponents at most `k` have pairwise distinct values, all of them
smaller than the values of the elements of `Q = (f₁^N, …, f_d^N)` for `N` linear in `k`; the
ideals `φ⁻¹(φ(x^α) V) + Q` are then `(k + 1)^r` pairwise comparable and pairwise distinct ideals
containing `Q`, so `(k + 1)^r ≤ length(B/Q) + 1`, while `length(B/Q) ≤ N^d length(B/(f))`
grows like `k^d`.

## Main definitions

* `Stacks.Abhyankar.monom`: the monomial `∏ i, x i ^ α i`.
* `Stacks.Abhyankar.MonomialIndependent`: distinct monomials in `x` are never associated.

## Main results

* `Stacks.Abhyankar.length_quotient_sup_span_image_pow_le`: for a finite set `s` of elements of
  a commutative ring, `length(B/(I + (s^N))) ≤ N^{#s} length(B/(I + (s)))`.
* `Stacks.Abhyankar.card_le_length_add_one`: a finite family of pairwise comparable submodules
  has at most `length + 1` members.
* `Stacks.Abhyankar.card_le_card_of_forall_exists_pow_eq_mul`: the counting step.

## References

* S. Abhyankar, *On the valuations centered in a local domain*, Amer. J. Math. 78 (1956),
  Theorem 1.
* O. Zariski, P. Samuel, *Commutative Algebra*, vol. II, Appendix 2.
-/

@[expose] public section

namespace Stacks.Abhyankar

open IsLocalRing

section Monomial

variable {V : Type*} [CommRing V] {ι : Type*} [Fintype ι]

/-- The monomial `x^α = ∏ i, x i ^ α i` of a finite family `x` with exponent vector `α`. -/
def monom (x : ι → V) (α : ι → ℕ) : V := ∏ i, x i ^ α i

theorem monom_zero (x : ι → V) : monom x 0 = 1 := by
  simp [monom]

theorem monom_add (x : ι → V) (α β : ι → ℕ) : monom x (α + β) = monom x α * monom x β := by
  simp [monom, pow_add, Finset.prod_mul_distrib]

theorem map_monom {W : Type*} [CommRing W] (f : V →+* W) (x : ι → V) (α : ι → ℕ) :
    f (monom x α) = monom (f ∘ x) α := by
  simp [monom, map_prod, map_pow]

/-- The family `x` has *independent values*: two monomials `x^α`, `x^β` are associated only when
`α = β`. For `V` a valuation ring this says exactly that the values of the `x i` are nonzero and
`ℤ`-linearly independent in the value group. -/
def MonomialIndependent (x : ι → V) : Prop :=
  ∀ α β : ι → ℕ, Associated (monom x α) (monom x β) → α = β

theorem MonomialIndependent.ne_zero {x : ι → V} (hx : MonomialIndependent x)
    (i : ι) : x i ≠ 0 := by
  classical
  intro h0
  have h1 : monom x (Pi.single i 1) = 0 := by
    rw [monom, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])]
  have h2 : monom x (Pi.single i 2) = 0 := by
    rw [monom, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])]
  have := congrFun (hx (Pi.single i 1) (Pi.single i 2) (by rw [h1, h2])) i
  simp at this

theorem MonomialIndependent.monom_ne_zero [IsDomain V] {x : ι → V}
    (hx : MonomialIndependent x) (α : ι → ℕ) : monom x α ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx.ne_zero i)

end Monomial

section Length

variable {B : Type*} [CommRing B]

/-- `length(B/(I + (f^N))) ≤ N · length(B/(I + (f)))` for `N ≥ 1`: the successive quotients of
`B/(I + (f^N))` by the powers of `f` are quotients of `B/(I + (f))`. -/
theorem length_quotient_sup_span_pow_le (I : Ideal B) (f : B) {N : ℕ} (hN : 1 ≤ N) :
    Module.length B (B ⧸ (I ⊔ Ideal.span {f ^ N})) ≤
      N * Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  induction N, hN using Nat.le_induction with
  | base => rw [pow_one, Nat.cast_one, one_mul]
  | succ N hN ih =>
    have hAB : ∀ b ∈ I ⊔ Ideal.span {f}, f ^ N * b ∈ I ⊔ Ideal.span {f ^ (N + 1)} := by
      intro b hb
      obtain ⟨i, hi, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      rw [mul_add]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hi))
        (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨r, by ring⟩))
    have h := Stacks.HilbertSamuel.DimensionTheorem.length_quotient_le_add (f ^ N)
      (I ⊔ Ideal.span {f ^ (N + 1)}) (I ⊔ Ideal.span {f}) hAB
    have hsup : I ⊔ Ideal.span {f ^ (N + 1)} ⊔ Ideal.span {f ^ N} = I ⊔ Ideal.span {f ^ N} := by
      have hle : Ideal.span {f ^ (N + 1)} ≤ Ideal.span {f ^ N} := by
        rw [Ideal.span_singleton_le_span_singleton, pow_succ]
        exact dvd_mul_right _ _
      rw [sup_assoc, sup_eq_right.mpr hle]
    rw [hsup] at h
    refine h.trans ?_
    push_cast
    calc Module.length B (B ⧸ (I ⊔ Ideal.span {f})) +
          Module.length B (B ⧸ (I ⊔ Ideal.span {f ^ N}))
        ≤ Module.length B (B ⧸ (I ⊔ Ideal.span {f})) +
          N * Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := add_le_add le_rfl ih
      _ = (N + 1) * Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by ring

/-- `length(B/(I + (s^N))) ≤ N^{#s} · length(B/(I + (s)))` for a finite set `s` and `N ≥ 1`,
where `s^N` is the set of `N`-th powers of the elements of `s`. -/
theorem length_quotient_sup_span_image_pow_le [DecidableEq B] (s : Finset B) (I : Ideal B)
    {N : ℕ} (hN : 1 ≤ N) :
    Module.length B (B ⧸ (I ⊔ Ideal.span (s.image (· ^ N) : Set B))) ≤
      N ^ s.card * Module.length B (B ⧸ (I ⊔ Ideal.span (s : Set B))) := by
  induction s using Finset.induction_on generalizing I with
  | empty =>
    simp only [Finset.image_empty, Finset.card_empty, pow_zero, one_mul]
    exact le_rfl
  | insert a t hat ih =>
    rw [Finset.image_insert, Finset.coe_insert, Finset.coe_insert, Ideal.span_insert,
      Ideal.span_insert, Finset.card_insert_of_notMem hat]
    have e3 : (I ⊔ Ideal.span (t : Set B)) ⊔ Ideal.span {a} =
        I ⊔ (Ideal.span {a} ⊔ Ideal.span (t : Set B)) := by
      rw [sup_assoc, sup_comm (Ideal.span (t : Set B))]
    rw [← sup_assoc]
    refine (ih (I ⊔ Ideal.span {a ^ N})).trans ?_
    rw [sup_right_comm]
    have h2 := length_quotient_sup_span_pow_le (I ⊔ Ideal.span (t : Set B)) a hN
    rw [e3] at h2
    calc (N : ℕ∞) ^ t.card * Module.length B (B ⧸ (I ⊔ Ideal.span (t : Set B) ⊔
          Ideal.span {a ^ N}))
        ≤ (N : ℕ∞) ^ t.card * (N * Module.length B (B ⧸ (I ⊔ (Ideal.span {a} ⊔
          Ideal.span (t : Set B))))) := mul_le_mul_right h2 _
      _ = (N : ℕ∞) ^ (t.card + 1) * Module.length B (B ⧸ (I ⊔ (Ideal.span {a} ⊔
          Ideal.span (t : Set B)))) := by ring

end Length

section Chain

/-- A finite set `F` of pairwise comparable elements, all strictly below `a`, has at most
`height a` elements. -/
theorem card_le_height_of_pairwise_comparable {α : Type*} [PartialOrder α] (F : Finset α)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a ≤ b ∨ b ≤ a) (a : α) (ha : ∀ b ∈ F, b < a) :
    (F.card : ℕ∞) ≤ Order.height a := by
  classical
  induction F using Finset.strongInduction generalizing a with
  | H F ih =>
    rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨m, hm⟩ := Finset.exists_maximal hne
    have hmF : m ∈ F := hm.prop
    have hlt : ∀ b ∈ F.erase m, b < m := by
      intro b hb
      obtain ⟨hbm, hbF⟩ := Finset.mem_erase.mp hb
      rcases hF b hbF m hmF with h | h
      · exact lt_of_le_of_ne h hbm
      · exact absurd (le_antisymm h (hm.2 hbF h)) (Ne.symm hbm)
    have h1 := ih (F.erase m) (Finset.erase_ssubset hmF)
      (fun b hb c hc => hF b (Finset.mem_of_mem_erase hb) c (Finset.mem_of_mem_erase hc)) m hlt
    have h2 := Order.height_add_one_le (ha m hmF)
    rw [← Finset.card_erase_add_one hmF]
    push_cast
    calc ((F.erase m).card : ℕ∞) + 1 ≤ Order.height m + 1 := by gcongr
      _ ≤ Order.height a := h2

/-- A finite set of pairwise comparable submodules of `M` has at most `length M + 1` members. -/
theorem card_le_length_add_one {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (F : Finset (Submodule R M)) (hF : ∀ a ∈ F, ∀ b ∈ F, a ≤ b ∨ b ≤ a) :
    (F.card : ℕ∞) ≤ Module.length R M + 1 := by
  classical
  have h := card_le_height_of_pairwise_comparable (F.erase ⊤)
    (fun a ha b hb => hF a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)) ⊤
    (fun b hb => lt_top_iff_ne_top.mpr (Finset.ne_of_mem_erase hb))
  rw [Module.length_eq_height]
  have hc : F.card ≤ (F.erase ⊤).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := F) (a := ⊤)
    omega
  calc (F.card : ℕ∞) ≤ ((F.erase ⊤).card + 1 : ℕ) := by exact_mod_cast hc
    _ ≤ Order.height (⊤ : Submodule R M) + 1 := by
        push_cast
        gcongr

end Chain

section Counting

variable {B : Type*} [CommRing B] {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- A power of an element whose `M`-th power is a strict multiple of `y` stays one. -/
private theorem exists_pow_eq_mul_of_le {g y : V} {M M' : ℕ} (hMM' : M ≤ M')
    (h : ∃ c ∈ maximalIdeal V, g ^ M = y * c) : ∃ c ∈ maximalIdeal V, g ^ M' = y * c := by
  obtain ⟨c, hc, hgc⟩ := h
  refine ⟨c * g ^ (M' - M), Ideal.mul_mem_right _ _ hc, ?_⟩
  rw [← mul_assoc, ← hgc, ← pow_add, Nat.add_sub_cancel' hMM']

/-- **The counting step of Abhyankar's inequality.** Let `B` be a Noetherian local ring, `φ` a
local homomorphism from `B` to a valuation ring `V`, `x : ι → B` a finite family whose images
have independent values, and `s` a finite set whose span has radical the maximal ideal of `B`.
If each `φ(f)`, `f ∈ s`, has a power that is a strict multiple of each `φ(x i)` (the values of
the `x i` are bounded by multiples of those of the `f`), then `#ι ≤ #s`. -/
theorem card_le_card_of_forall_exists_pow_eq_mul [IsNoetherianRing B] [IsLocalRing B]
    (φ : B →+* V) [IsLocalHom φ] {ι : Type*} [Fintype ι] (x : ι → B)
    (hx : MonomialIndependent (φ ∘ x)) (s : Finset B)
    (hs : (Ideal.span (s : Set B)).radical = maximalIdeal B)
    (harch : ∀ i, ∀ f ∈ s, ∃ M : ℕ, ∃ c ∈ maximalIdeal V, φ f ^ M = φ (x i) * c) :
    Fintype.card ι ≤ s.card := by
  classical
  -- A uniform exponent.
  choose! Mf hMf using harch
  set M : ℕ := ∑ i, ∑ f ∈ s, Mf i f with hM
  have hunif : ∀ i, ∀ f ∈ s, ∃ c ∈ maximalIdeal V, φ f ^ M = φ (x i) * c := by
    intro i f hf
    refine exists_pow_eq_mul_of_le ?_ (hMf i f hf)
    calc Mf i f ≤ ∑ f' ∈ s, Mf i f' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf
      _ ≤ M := Finset.single_le_sum (f := fun i => ∑ f' ∈ s, Mf i f')
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  -- The elements of `s` lie in the maximal ideal.
  have hsm : ∀ f ∈ s, φ f ∈ maximalIdeal V := by
    intro f hf
    have : f ∈ maximalIdeal B := hs ▸ Ideal.le_radical (Ideal.subset_span hf)
    exact map_nonunit φ f this
  -- The length of `B ⧸ (s)` is finite.
  obtain ⟨L, hL⟩ : ∃ L : ℕ, Module.length B (B ⧸ Ideal.span (s : Set B)) = L := by
    have h := HilbertSamuel.length_quotient_lt_top (Ideal.span (s : Set B)) hs B 0
    rw [zero_add, pow_one, Ideal.smul_top_eq_self] at h
    exact ⟨_, (ENat.natCast_toNat h.ne).symm⟩
  set r := Fintype.card ι
  set d := s.card
  by_contra hrd
  push Not at hrd
  -- The parameters of the contradiction.
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = (M * r + 1) ^ d * L := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = A + 1 := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = M * (r * k) + 1 := ⟨_, rfl⟩
  set Q : Ideal B := Ideal.span (s.image (· ^ N) : Set B)
  -- Every element of `Q` maps to a strict multiple of every monomial of the box.
  have hQ : ∀ α : ι → Fin (k + 1), ∀ q ∈ Q, ∃ c ∈ maximalIdeal V,
      φ q = φ (monom x (fun i => (α i : ℕ))) * c := by
    intro α q hq
    set y := φ (monom x (fun i => (α i : ℕ))) with hy
    have hle : Q ≤ Ideal.comap φ (Ideal.span {y} * maximalIdeal V) := by
      rw [Ideal.span_le]
      intro q hq
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
      rw [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_span_singleton_mul]
      have hsum : ∑ i, (α i : ℕ) ≤ r * k := by
        calc ∑ i, (α i : ℕ) ≤ ∑ _i : ι, k := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (α i).2
          _ = r * k := by simp [r]
      choose c hc hgc using fun i => hunif i f hf
      refine ⟨(∏ i, c i ^ (α i : ℕ)) * φ f ^ (M * (r * k - ∑ i, (α i : ℕ)) + 1),
        Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hsm f hf) _ (Nat.succ_pos _)), ?_⟩
      have hN : N = M * ∑ i, (α i : ℕ) + (M * (r * k - ∑ i, (α i : ℕ)) + 1) := by
        rw [hNdef, ← add_assoc, ← mul_add, Nat.add_sub_cancel' hsum]
      have key : φ f ^ (M * ∑ i, (α i : ℕ)) = ∏ i, (φ (x i) * c i) ^ (α i : ℕ) := by
        rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun i _ => by rw [hgc i]
      rw [map_pow, hN, pow_add (φ f) (M * ∑ i, (α i : ℕ)), key, hy, map_monom, monom]
      simp only [mul_pow, Finset.prod_mul_distrib, Function.comp_apply]
      ring
    exact Ideal.mem_span_singleton_mul.mp (hle hq) |>.imp fun c hc => ⟨hc.1, hc.2.symm⟩
  -- The ideals `φ⁻¹(φ(x^α) V)`, pushed to `B ⧸ Q`.
  let J : (ι → Fin (k + 1)) → Submodule B (B ⧸ Q) := fun α =>
    Submodule.map (Submodule.mkQ (Q : Submodule B B))
      (Ideal.comap φ (Ideal.span {φ (monom x (fun i => (α i : ℕ)))}) : Submodule B B)
  have hmono : ∀ α β, φ (monom x (fun i => (β i : ℕ))) ∣ φ (monom x (fun i => (α i : ℕ))) →
      J α ≤ J β := fun α β h =>
    Submodule.map_mono (Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.mpr h))
  have hJcomp : ∀ α β, J α ≤ J β ∨ J β ≤ J α := fun α β =>
    (ValuationRing.dvd_total _ _).imp (hmono α β) (hmono β α)
  -- If `J α ≤ J β` then `φ(x^β)` divides `φ(x^α)`.
  have hJdvd : ∀ α β, J α ≤ J β →
      φ (monom x (fun i => (β i : ℕ))) ∣ φ (monom x (fun i => (α i : ℕ))) := by
    intro α β hαβ
    have hmem : monom x (fun i => (α i : ℕ)) ∈ (Q : Submodule B B) ⊔
        (Ideal.comap φ (Ideal.span {φ (monom x (fun i => (β i : ℕ)))}) : Submodule B B) := by
      rw [← Submodule.comap_map_mkQ]
      refine hαβ (Submodule.mem_map_of_mem ?_)
      exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
    obtain ⟨q, hq, w, hw, hqw⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, hc, hqc⟩ := hQ α q hq
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hw)
    have hunit : IsUnit (1 - c) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c hc
    have h1 : φ (monom x (fun i => (α i : ℕ))) = φ q + φ w := by rw [← map_add, hqw]
    have : φ (monom x (fun i => (α i : ℕ))) * (1 - c) =
        φ (monom x (fun i => (β i : ℕ))) * e := by
      calc φ (monom x (fun i => (α i : ℕ))) * (1 - c)
          = φ (monom x (fun i => (α i : ℕ))) - φ (monom x (fun i => (α i : ℕ))) * c := by ring
        _ = φ (monom x (fun i => (α i : ℕ))) - φ q := by rw [hqc]
        _ = φ w := by rw [h1]; ring
        _ = φ (monom x (fun i => (β i : ℕ))) * e := by rw [← he]; ring
    obtain ⟨u, hu⟩ := hunit
    refine ⟨e * ↑u⁻¹, ?_⟩
    calc φ (monom x (fun i => (α i : ℕ))) = φ (monom x (fun i => (α i : ℕ))) * (1 - c) *
          ↑u⁻¹ := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [this, mul_assoc]
  have hJinj : Function.Injective J := by
    intro α β hαβ
    have h := hx (fun i => (α i : ℕ)) (fun i => (β i : ℕ)) (associated_of_dvd_dvd
      (by rw [← map_monom, ← map_monom]; exact hJdvd β α hαβ.ge)
      (by rw [← map_monom, ← map_monom]; exact hJdvd α β hαβ.le))
    funext i
    exact Fin.ext (congrFun h i)
  -- Lower bound: `(k + 1)^r` comparable distinct submodules.
  have hlow : ((k + 1) ^ r : ℕ∞) ≤ Module.length B (B ⧸ Q) + 1 := by
    have h := card_le_length_add_one (Finset.univ.image J) (by
      intro a ha b hb
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hb
      exact hJcomp α β)
    rw [Finset.card_image_of_injective _ hJinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin] at h
    exact_mod_cast h
  -- Upper bound: `length(B ⧸ Q) ≤ N^d L`.
  have hup : Module.length B (B ⧸ Q) ≤ N ^ d * L := by
    have h := length_quotient_sup_span_image_pow_le s ⊥ (N := N)
      (by rw [hNdef]; exact Nat.le_add_left 1 _)
    rw [bot_sup_eq, bot_sup_eq, hL] at h
    exact h
  have hnat : (k + 1) ^ r ≤ N ^ d * L + 1 := by
    have : ((k + 1) ^ r : ℕ∞) ≤ N ^ d * L + 1 := hlow.trans (by gcongr)
    exact_mod_cast this
  -- The contradiction: `(k + 1)^r` outgrows `N^d L + 1`.
  have hNk : N ≤ (M * r + 1) * (k + 1) := by
    rw [hNdef]; nlinarith
  have hpow : (k + 1) ^ (d + 1) ≤ (k + 1) ^ r :=
    Nat.pow_le_pow_right (by omega) hrd
  have hNd : N ^ d * L ≤ A * (k + 1) ^ d := by
    calc N ^ d * L ≤ ((M * r + 1) * (k + 1)) ^ d * L :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNk d)
      _ = A * (k + 1) ^ d := by rw [hA, mul_pow]; ring
  have hP : 1 ≤ (k + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have key : (k + 1) ^ d * (k + 1) ≤ A * (k + 1) ^ d + 1 := by
    calc (k + 1) ^ d * (k + 1) = (k + 1) ^ (d + 1) := by ring
      _ ≤ _ := hpow.trans (hnat.trans (by omega))
  have : (k + 1) ^ d * (k + 1) = A * (k + 1) ^ d + 2 * (k + 1) ^ d := by
    rw [hk]; ring
  omega

end Counting

end Stacks.Abhyankar
