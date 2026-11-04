module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Filtration
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ideals of an adic completion lying between an extended ideal and its torsion

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `A^∧` the `I`-adic completion. This file
records the commutative algebra the proof of **Stacks 0GHE** uses to glue an ideal of `A` out
of an ideal `K ⊆ A^∧` and an ideal `N ⊆ A` that agree up to `I`-power torsion.

## Main results

* `Ideal.eq_zero_of_forall_mem_pow_of_pow_mul_eq_zero`: in a Noetherian ring an element lying
  in every power of `I` and annihilated by a power of `I` is zero (Krull's intersection
  theorem).
* `Ideal.map_colon_le_of_flat_adicCompletion`: an element `x ∈ A^∧` with `I^k x ⊆ N A^∧` lies
  in `(N : I^k) A^∧`, because colon ideals by finitely generated ideals commute with the flat
  base change `A → A^∧`.
* `Ideal.exists_map_adicCompletion_eq`: if `N A^∧ ⊆ K` and `I^k K ⊆ N A^∧`, then
  `K = J A^∧` for an ideal `J` of `A` with `N ⊆ J` and `I^k J ⊆ N`.
-/

@[expose] public section

open TensorProduct

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- **Krull.** In a Noetherian ring, an element lying in every power of an ideal `I` and
annihilated by a power of `I` is zero: by Krull's intersection theorem `x = r x` for some
`r ∈ I`, hence `x = r ^ k x = 0`. -/
theorem eq_zero_of_forall_mem_pow_of_pow_mul_eq_zero [IsNoetherianRing A] (I : Ideal A) {x : A}
    (hx : ∀ n, x ∈ I ^ n) {k : ℕ} (hk : ∀ y ∈ I ^ k, y * x = 0) : x = 0 := by
  have hmem : x ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule A A) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx i
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I x).1 hmem
  rw [smul_eq_mul] at hr
  have hpow : ∀ m : ℕ, (r : A) ^ m * x = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hr, ih]
  rw [← hpow k]
  exact hk _ (Ideal.pow_mem_pow r.2 k)

section Flat

variable {B : Type u} [CommRing B] [Algebra A B] [Module.Flat A B]

/-- `a` annihilates the class of `b` in `A ⧸ N` iff `a * b ∈ N`. -/
private theorem mem_torsionOf_quotient_mk_iff (N : Ideal A) (a b : A) :
    a ∈ Ideal.torsionOf A (A ⧸ N) (Ideal.Quotient.mk N b) ↔ a * b ∈ N := by
  rw [Ideal.mem_torsionOf_iff, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The annihilator of the class of `1` in `A ⧸ N` is `N`. -/
theorem torsionOf_quotient_mk_one (N : Ideal A) :
    Ideal.torsionOf A (A ⧸ N) (Ideal.Quotient.mk N 1) = N := by
  ext a
  rw [mem_torsionOf_quotient_mk_iff, mul_one]

/-- **Colon ideals by finitely generated ideals commute with flat base change.** For a flat
`A`-algebra `B`, ideals `N, L ⊆ A` with `L` finitely generated, and `x ∈ B` with
`L x ⊆ N B`, the element `x` lies in `(N : L) B`. -/
theorem mem_map_colon_of_flat (N L : Ideal A) (hL : L.FG) {x : B}
    (hx : ∀ y ∈ L, algebraMap A B y * x ∈ N.map (algebraMap A B)) :
    x ∈ (N.colon (L : Set A)).map (algebraMap A B) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  have hP : N.colon (L : Set A) = ⨅ j, Ideal.torsionOf A (A ⧸ N) (Ideal.Quotient.mk N (g j)) := by
    ext a
    rw [Submodule.mem_colon, Submodule.mem_iInf]
    constructor
    · intro h j
      rw [mem_torsionOf_quotient_mk_iff]
      exact h _ (hg ▸ Submodule.subset_span ⟨j, rfl⟩)
    · intro h p hp
      rw [← hg] at hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨j, rfl⟩ := hp
        exact (mem_torsionOf_quotient_mk_iff N a _).1 (h j)
      | zero => simp
      | add p q _ _ hp hq =>
        rw [smul_add]
        exact N.add_mem hp hq
      | smul r p _ hp =>
        rw [smul_comm]
        exact N.smul_mem r hp
  rw [hP, Ideal.map_iInf_of_flat, Submodule.mem_iInf]
  intro j
  rw [ann_extension_eq_ann_baseChange_elem, Ideal.mem_torsionOf_iff]
  have h1 : ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk N (g j)) =
      algebraMap A B (g j) • ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk N 1) := by
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
  have h2 : x * algebraMap A B (g j) ∈ Ideal.torsionOf B (B ⊗[A] (A ⧸ N))
      ((1 : B) ⊗ₜ[A] Ideal.Quotient.mk N 1) := by
    rw [← ann_extension_eq_ann_baseChange_elem, torsionOf_quotient_mk_one, mul_comm]
    exact hx _ (hg ▸ Submodule.subset_span ⟨j, rfl⟩)
  rw [h1, smul_smul]
  rwa [Ideal.mem_torsionOf_iff] at h2

end Flat

variable [IsNoetherianRing A] (I : Ideal A)

local notation "Â" => AdicCompletion I A

/-- Every element of `A^∧` is congruent modulo `I ^ k A^∧` to the image of an element of `A`. -/
theorem exists_sub_algebraMap_mem_map_pow (c : Â) (k : ℕ) :
    ∃ a : A, c - algebraMap A Â a ∈ (I ^ k).map (algebraMap A Â) := by
  obtain ⟨a, ha⟩ := (I ^ k • (⊤ : Submodule A A)).mkQ_surjective (AdicCompletion.eval I A k c)
  refine ⟨a, ?_⟩
  have h : c - algebraMap A Â a ∈ (I ^ k • ⊤ : Submodule A Â) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
      map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of,
      Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]
  rwa [Ideal.smul_top_eq_map] at h

/-- **The ideal of `A` cut out by an ideal of `A^∧` between `N A^∧` and its `I`-power
torsion.** Let `N ⊆ A` and `K ⊆ A^∧` be ideals with `N A^∧ ⊆ K` and `I^k K ⊆ N A^∧`. Then
`K = J A^∧` for an ideal `J ⊆ A` with `N ⊆ J` and `I^k J ⊆ N`, namely the elements of the
colon ideal `(N : I^k)` whose image lies in `K`. -/
theorem exists_map_adicCompletion_eq (N : Ideal A) (K : Ideal Â) (k : ℕ)
    (hN : N.map (algebraMap A Â) ≤ K)
    (hK : (I ^ k).map (algebraMap A Â) * K ≤ N.map (algebraMap A Â)) :
    ∃ J : Ideal A, N ≤ J ∧ I ^ k * J ≤ N ∧ J.map (algebraMap A Â) = K := by
  let P : Ideal A := N.colon ((I ^ k : Ideal A) : Set A)
  have hNP : N ≤ P := fun a ha => Submodule.mem_colon.2 fun p _ => N.mul_mem_right p ha
  have hIP : I ^ k * P ≤ N := by
    rw [Ideal.mul_le]
    intro r hr a ha
    rw [mul_comm]
    exact (Submodule.mem_colon).1 ha r hr
  let J : Ideal A := P ⊓ K.comap (algebraMap A Â)
  have hNJ : N ≤ J := le_inf hNP (Ideal.map_le_iff_le_comap.1 hN)
  refine ⟨J, hNJ, (Ideal.mul_mono_right inf_le_left).trans hIP, le_antisymm
    (Ideal.map_le_iff_le_comap.2 inf_le_right) ?_⟩
  -- every element of `P A^∧` is the image of an element of `P` modulo `N A^∧`
  have hdecomp : ∀ y ∈ P.map (algebraMap A Â),
      ∃ p ∈ P, y - algebraMap A Â p ∈ N.map (algebraMap A Â) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨p, hp, by simp⟩
    | zero => exact ⟨0, P.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, hp, hyp⟩ := hy
      obtain ⟨q, hq, hzq⟩ := hz
      refine ⟨p + q, P.add_mem hp hq, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hyp hzq
    | smul c y _ hy =>
      obtain ⟨p, hp, hyp⟩ := hy
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map_pow I c k
      refine ⟨a * p, P.mul_mem_left a hp, ?_⟩
      have heq : c • y - algebraMap A Â (a * p) =
          c * (y - algebraMap A Â p) + (c - algebraMap A Â a) * algebraMap A Â p := by
        rw [smul_eq_mul, map_mul, mul_sub, sub_mul]
        abel
      rw [heq]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ c hyp) ?_
      have hmem : (c - algebraMap A Â a) * algebraMap A Â p ∈
          (I ^ k).map (algebraMap A Â) * P.map (algebraMap A Â) :=
        Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ hp)
      rw [← Ideal.map_mul] at hmem
      exact Ideal.map_mono hIP hmem
  intro x hx
  have hxP : x ∈ P.map (algebraMap A Â) := by
    refine mem_map_colon_of_flat N (I ^ k) (I ^ k).fg_of_isNoetherianRing fun y hy => ?_
    exact hK (Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hy) hx)
  obtain ⟨p, hp, hxp⟩ := hdecomp x hxP
  have hpK : p ∈ K.comap (algebraMap A Â) := by
    rw [Ideal.mem_comap]
    have := K.sub_mem hx (hN hxp)
    rwa [sub_sub_cancel] at this
  rw [← add_sub_cancel (algebraMap A Â p) x]
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ ⟨hp, hpK⟩) (Ideal.map_mono hNJ hxp)

/-- **Ideals of `A^∧` are closed.** For a Noetherian ring `A`, every ideal `K` of the `I`-adic
completion is the intersection of the ideals `K + I ^ (n + 1) A^∧`: by Krull's intersection
theorem in `A^∧ ⧸ K` an element of the intersection is killed by some `1 - r` with `r ∈ I A^∧`,
which is a unit because `A^∧` is `I A^∧`-adically complete. -/
@[sga "3 VIIB 5.5.2" "partial"]
theorem iInf_sup_map_pow_eq [IsNoetherianRing Â] (K : Ideal Â) :
    ⨅ n : ℕ, (K ⊔ (I ^ (n + 1)).map (algebraMap A Â)) = K := by
  refine le_antisymm (fun x hx => ?_) (le_iInf fun _ => le_sup_left)
  let I' := I.map (algebraMap A Â)
  have : IsAdicComplete I' Â := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have hmem : Submodule.Quotient.mk (p := K) x ∈ (⨅ i : ℕ, I' ^ i • ⊤ : Submodule Â (Â ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have hx' := (Submodule.mem_iInf _).1 hx i
      rw [Ideal.map_pow] at hx'
      obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.1 hx'
      rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hk, zero_add]
      have : Submodule.Quotient.mk (p := K) y = y • Submodule.Quotient.mk (p := K) (1 : Â) := by
        rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem_smul hy Submodule.mem_top
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I' _).1 hmem
  have hunit : IsUnit (1 - (r : Â)) := by
    simpa [sub_eq_add_neg, mul_comm, add_comm] using
      Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot I' r.2) (-1)
  have h1 : (1 - (r : Â)) * x ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero, sub_mul, one_mul, Submodule.Quotient.mk_sub,
      ← smul_eq_mul, Submodule.Quotient.mk_smul, hr, sub_self]
  exact (K.unit_mul_mem_iff_mem hunit).1 h1

end Ideal
