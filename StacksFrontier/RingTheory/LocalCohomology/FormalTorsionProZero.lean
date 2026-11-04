module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# Torsion at the closed point of a formal module is pro-zero

Let `(B, 𝔪)` be a Noetherian local ring, `J ⊆ 𝔪` an ideal and `P` a finite module over the
`J`-adic completion `B^∧`, complete for the `J`-adic topology. Consider a decreasing filtration
`Λ₀ ⊇ Λ₁ ⊇ ⋯` of `P` by `B`-submodules with `J^{k+1} P ⊆ Λ_k` and `Λ_k = Λ_{k+1} + J^{k+1} P`,
that is, a compatible system of submodules `Λ_k / J^{k+1}P` of the levels `P / J^{k+1} P` with
surjective transitions, annihilated by a fixed power of `J`. Its intersection `H = ⋂ Λ_k`
satisfies `Λ_k = H + J^{k+1} P`, so the quotients `P / Λ_k` are the levels of the formal module
`P / H`.

This file proves that the inverse system of the `𝔪`-power torsion of the levels `P / Λ_k` is
pro-zero, given two conditions on `P / H`:

* it has depth at least one, in the uniform form that an element killed by `𝔪` modulo `Λ_{k+c}`
  lies in `Λ_k`;
* no nonmaximal prime `𝔓` of `B^∧` with `V(𝔓) ∩ V(J B^∧) = {𝔪 B^∧}` is an associated prime of
  `P`.

The second condition is the depth hypothesis of Stacks, Tag 0EJE at the completed stalk.

The proof is the following. The `𝔪`-power torsion of a level `P / Λ_m` has finite length, so the
images of the torsion of the higher levels stabilize, and the stable images form a system with
surjective transitions. Lifting a compatible family of stable elements produces an element `z` of
`P` which is `𝔪`-power torsion modulo every `Λ_k`. Such an element lies in `H`: otherwise an
associated prime `𝔓 = Ann(w)` of the submodule of such elements modulo `H` satisfies, by
Artin–Rees, `𝔪^e ⊆ 𝔓 + J B^∧`, so `V(𝔓) ∩ V(J B^∧)` is the closed point; the depth condition
excludes `𝔓 = 𝔪 B^∧`, and otherwise multiplying `w` by an element of a power of `J` outside `𝔓`
(which kills `H`) shows that `𝔓` is an associated prime of `P` itself.

## Main results

* `Stacks.LocalCohomology.FormalFiltration.mem_iff_exists_mem_iInf` — `Λ_k = H + J^{k+1} P`.
* `Stacks.LocalCohomology.FormalFiltration.mem_iInf_of_forall_exists_pow_smul_mem` — an element
  which is `𝔪`-power torsion modulo every `Λ_k` lies in `H`.
* `Stacks.LocalCohomology.FormalFiltration.exists_forall_pow_smul_mem_imp_mem` — the
  pro-vanishing of the `𝔪`-power torsion.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public section

open IsLocalRing Submodule

universe u

namespace Stacks.LocalCohomology

variable {B : Type u} [CommRing B] (J : Ideal B)
  {P : Type u} [AddCommGroup P] [Module B P] [Module (AdicCompletion J B) P]
  [IsScalarTower B (AdicCompletion J B) P]

/-- The `B`-submodule `J ^ n P` of a module over the completion has the same elements as the
`B^∧`-submodule `(J B^∧) ^ n P`. -/
theorem mem_pow_smul_top_iff_mem_map_pow_smul_top (n : ℕ) (p : P) :
    p ∈ (J.map (algebraMap B (AdicCompletion J B))) ^ n •
        (⊤ : Submodule (AdicCompletion J B) P) ↔
      p ∈ J ^ n • (⊤ : Submodule B P) := by
  rw [← Ideal.map_pow]
  have h := Ideal.smul_restrictScalars (J ^ n) (⊤ : Submodule (AdicCompletion J B) P)
  rw [Submodule.restrictScalars_top] at h
  rw [← h]
  rfl

/-- The structure of a compatible system of submodules of the levels of a formal module: a
decreasing filtration `Λ` of `P` with `J ^ (k+1) P ⊆ Λ k` and `Λ k = Λ (k+1) + J ^ (k+1) P`. -/
structure FormalFiltration (Λ : ℕ → Submodule B P) : Prop where
  pow_smul_top_le : ∀ k, J ^ (k + 1) • (⊤ : Submodule B P) ≤ Λ k
  eq_sup : ∀ k, Λ k = Λ (k + 1) ⊔ J ^ (k + 1) • (⊤ : Submodule B P)

omit [Module (AdicCompletion J B) P] [IsScalarTower B (AdicCompletion J B) P] in
/-- The submodules `J ^ n P` decrease as `n` increases. -/
theorem pow_smul_top_mono {m n : ℕ} (h : m ≤ n) :
    J ^ n • (⊤ : Submodule B P) ≤ J ^ m • (⊤ : Submodule B P) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

omit [Module (AdicCompletion J B) P] [IsScalarTower B (AdicCompletion J B) P] in
/-- **Lifting along a filtration with surjective transitions.** If `A i ⊆ A (i+1) + J ^ (k+i+1) P`
for all `i`, every element of `A 0` is congruent modulo `J ^ (k+1) P` to an element `z` of the
complete module `P` which is congruent modulo `J ^ (k+i+1) P` to an element of `A i`, for
every `i`. -/
theorem exists_limit [IsPrecomplete J P] (A : ℕ → Submodule B P) (k : ℕ)
    (hA : ∀ i, A i ≤ A (i + 1) ⊔ J ^ (k + i + 1) • (⊤ : Submodule B P)) {p : P}
    (hp : p ∈ A 0) :
    ∃ z : P, (∀ i, ∃ x ∈ A i, z - x ∈ J ^ (k + i + 1) • (⊤ : Submodule B P)) ∧
      p - z ∈ J ^ (k + 1) • (⊤ : Submodule B P) := by
  have step : ∀ i (x : P), x ∈ A i →
      ∃ x' ∈ A (i + 1), x - x' ∈ J ^ (k + i + 1) • (⊤ : Submodule B P) := by
    intro i x hx
    obtain ⟨y, hy, ε, hε, rfl⟩ := Submodule.mem_sup.mp (hA i hx)
    exact ⟨y, hy, by simpa using hε⟩
  choose g hg hg' using step
  let f : ∀ i, A i := fun i =>
    Nat.rec (motive := fun i => A i) ⟨p, hp⟩ (fun i x => ⟨g i x x.2, hg i x x.2⟩) i
  have hf : ∀ i, (f i : P) - f (i + 1) ∈ J ^ (k + i + 1) • (⊤ : Submodule B P) := fun i =>
    hg' i (f i) (f i).2
  have hdiff : ∀ i j, (f i : P) - f (i + j) ∈ J ^ (k + i + 1) • (⊤ : Submodule B P) := by
    intro i j
    induction j with
    | zero => simp
    | succ j ih =>
      have : (f i : P) - f (i + (j + 1)) =
          ((f i : P) - f (i + j)) + ((f (i + j) : P) - f (i + j + 1)) := by
        rw [← add_assoc]
        abel
      rw [this]
      exact add_mem ih (pow_smul_top_mono J (P := P) (by omega) (hf (i + j)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := J) inferInstance (f := fun i => (f i : P))
    (by
      intro m n hmn
      rw [SModEq.sub_mem]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact pow_smul_top_mono J (P := P) (by omega) (hdiff m j))
  have hLi : ∀ i, L - f i ∈ J ^ (k + i + 1) • (⊤ : Submodule B P) := by
    intro i
    have h1 := SModEq.sub_mem.mp (hL (k + i + 1))
    have h2 := hdiff i (k + 1)
    rw [show k + i + 1 = i + (k + 1) by omega] at h1 h2 ⊢
    have : L - f i = -((f (i + (k + 1)) : P) - L) + -((f i : P) - f (i + (k + 1))) := by
      abel
    rw [this]
    exact add_mem (neg_mem h1) (neg_mem h2)
  refine ⟨L, fun i => ⟨f i, (f i).2, hLi i⟩, ?_⟩
  rw [← neg_sub]
  exact neg_mem (hLi 0)

namespace FormalFiltration

variable {J} {Λ : ℕ → Submodule B P} (hΛ : FormalFiltration J Λ)
include hΛ

omit [Module (AdicCompletion J B) P] [IsScalarTower B (AdicCompletion J B) P] in
/-- The filtration `Λ` is decreasing. -/
theorem antitone : _root_.Antitone Λ :=
  antitone_nat_of_succ_le fun k => (hΛ.eq_sup k).symm ▸ le_sup_left

/-- Each member of the filtration is stable under the completion. -/
theorem smul_mem (hJ : J.FG) (a : AdicCompletion J B) {k : ℕ} {p : P} (hp : p ∈ Λ k) :
    a • p ∈ Λ k := by
  obtain ⟨b, hb⟩ := Stacks.Coherent.completion_exists_approximation J hJ a (k + 1)
  simpa using add_mem (Λ k |>.smul_mem b hp)
    (hΛ.pow_smul_top_le k (Stacks.Coherent.completion_smul_difference_mem J hb p))

/-- The filtration as `B^∧`-submodules. -/
def toCompletion (hJ : J.FG) (k : ℕ) : Submodule (AdicCompletion J B) P where
  carrier := Λ k
  add_mem' := (Λ k).add_mem
  zero_mem' := (Λ k).zero_mem
  smul_mem' a _ hp := hΛ.smul_mem hJ a hp

omit [Module (AdicCompletion J B) P] [IsScalarTower B (AdicCompletion J B) P] in
/-- **Every member of the filtration is the intersection plus an ideal-power multiple.** -/
theorem mem_iff_exists_mem_iInf [IsPrecomplete J P] (k : ℕ) (p : P) :
    p ∈ Λ k ↔ ∃ h ∈ ⨅ j, Λ j, p - h ∈ J ^ (k + 1) • (⊤ : Submodule B P) := by
  constructor
  · intro hp
    obtain ⟨z, hz, hpz⟩ := exists_limit J (fun i => Λ (k + i)) k
      (fun i => by rw [show k + (i + 1) = k + i + 1 by omega, ← hΛ.eq_sup (k + i)])
      (p := p) (by simpa using hp)
    refine ⟨z, Submodule.mem_iInf _ |>.mpr fun j => ?_, hpz⟩
    obtain ⟨x, hx, hzx⟩ := hz j
    rw [← sub_add_cancel z x]
    exact add_mem (hΛ.pow_smul_top_le j (pow_smul_top_mono J (P := P) (by omega) hzx))
      (hΛ.antitone (by omega) hx)
  · rintro ⟨h, hh, hph⟩
    rw [← sub_add_cancel p h]
    exact add_mem (hΛ.pow_smul_top_le k hph) (Submodule.mem_iInf _ |>.mp hh k)

omit [Module (AdicCompletion J B) P] [IsScalarTower B (AdicCompletion J B) P] hΛ in
/-- **A power of `J` kills the intersection** as soon as it kills every level. -/
theorem smul_eq_zero_of_mem_iInf [IsHausdorff J P] {c : ℕ}
    (hc : ∀ k, ∀ p ∈ Λ k, ∀ a ∈ J ^ c, a • p ∈ J ^ (k + 1) • (⊤ : Submodule B P))
    {h : P} (hh : h ∈ ⨅ j, Λ j) {a : B} (ha : a ∈ J ^ c) : a • h = 0 := by
  apply IsHausdorff.haus (I := J) inferInstance
  intro n
  rw [SModEq.zero]
  cases n with
  | zero => simp
  | succ n => exact hc n h (Submodule.mem_iInf _ |>.mp hh n) a ha

variable [IsNoetherianRing B] [IsLocalRing B] [Module.Finite (AdicCompletion J B) P]
  [IsAdicComplete J P]

/-- The `B^∧`-submodule of elements which are `𝔪`-power torsion modulo `Λ k`. -/
private def mTorsionMod (hΛ : FormalFiltration J Λ) (hJ : J.FG) (k : ℕ) :
    Submodule (AdicCompletion J B) P where
  carrier := {p | ∃ e, ∀ a ∈ maximalIdeal B ^ e, a • p ∈ Λ k}
  add_mem' := by
    intro x z ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    refine ⟨max e₁ e₂, fun a ha => ?_⟩
    rw [smul_add]
    exact add_mem (he₁ a (Ideal.pow_le_pow_right (le_max_left _ _) ha))
      (he₂ a (Ideal.pow_le_pow_right (le_max_right _ _) ha))
  zero_mem' := ⟨0, fun a _ => by simp⟩
  smul_mem' := by
    intro a' z ⟨e, he⟩
    refine ⟨e, fun a ha => ?_⟩
    rw [smul_comm]
    exact hΛ.smul_mem hJ a' (he a ha)

/-- **An element which is `𝔪`-power torsion modulo every member of the filtration lies in their
intersection**, under the two conditions on the formal module `P / ⋂ Λ`. -/
theorem mem_iInf_of_forall_exists_pow_smul_mem (hJ : J ≤ maximalIdeal B)
    (hc : ∃ c, ∀ k, ∀ p ∈ Λ k, ∀ a ∈ J ^ c, a • p ∈ J ^ (k + 1) • (⊤ : Submodule B P))
    (hD : ∃ d, ∀ k (p : P), (∀ a ∈ maximalIdeal B, a • p ∈ Λ (k + d)) → p ∈ Λ k)
    (h6 : ∀ 𝔓 : Ideal (AdicCompletion J B), 𝔓.IsPrime →
      𝔓 ≠ (maximalIdeal B).map (algebraMap B (AdicCompletion J B)) →
      (∀ Q : Ideal (AdicCompletion J B), Q.IsPrime → 𝔓 ≤ Q →
        J.map (algebraMap B (AdicCompletion J B)) ≤ Q →
        Q = (maximalIdeal B).map (algebraMap B (AdicCompletion J B))) →
      𝔓 ∉ associatedPrimes (AdicCompletion J B) P)
    (y : P) (hy : ∀ k, ∃ e, ∀ a ∈ maximalIdeal B ^ e, a • y ∈ Λ k) : y ∈ ⨅ k, Λ k := by
  classical
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing J
  set C := AdicCompletion J B
  set 𝔪C := (maximalIdeal B).map (algebraMap B C)
  have h𝔪C : 𝔪C.IsMaximal :=
    AdicCompletion.isMaximal_map_of_le J (maximalIdeal B) hJ hJfg
  let H : Submodule C P := ⨅ k, hΛ.toCompletion hJfg k
  have hmemH : ∀ p : P, p ∈ H ↔ ∀ k, p ∈ Λ k := fun p => Submodule.mem_iInf _
  have hHi : ∀ p : P, p ∈ H ↔ p ∈ ⨅ k, Λ k := fun p => (hmemH p).trans (Submodule.mem_iInf _).symm
  let L : Submodule C P := ⨅ k, mTorsionMod hΛ hJfg k
  by_contra hyH
  let N := P ⧸ H
  let L'' : Submodule C N := L.map H.mkQ
  have hx0 : (⟨H.mkQ y, Submodule.mem_map_of_mem (Submodule.mem_iInf _ |>.mpr hy)⟩ : L'') ≠ 0 := by
    intro h0
    apply hyH
    have := congrArg Subtype.val h0
    exact (hHi y).mp ((Submodule.Quotient.mk_eq_zero H).mp this)
  obtain ⟨𝔓, h𝔓, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing C _ hx0
  obtain ⟨h𝔓prime, w, hw⟩ := (isAssociatedPrime_iff).mp h𝔓
  obtain ⟨y₁, hy₁L, hy₁w⟩ := Submodule.mem_map.mp w.2
  have hann : ∀ a : C, a ∈ 𝔓 ↔ a • y₁ ∈ H := by
    intro a
    rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      change a • (w : N) = 0 at h'
      rw [← hy₁w, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
      exact h'
    · intro h
      apply Subtype.ext
      show a • (w : N) = 0
      rw [← hy₁w, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
  -- the fibre condition `V(𝔓) ∩ V(J C) = {𝔪 C}`, by Artin–Rees
  have hfib : ∀ Q : Ideal C, Q.IsPrime → 𝔓 ≤ Q → J.map (algebraMap B C) ≤ Q → Q = 𝔪C := by
    intro Q hQ h𝔓Q hJQ
    obtain ⟨c₀, hc₀⟩ := Ideal.exists_pow_inf_eq_pow_smul (J.map (algebraMap B C))
      (Submodule.span C {H.mkQ y₁})
    obtain ⟨e, he⟩ := (Submodule.mem_iInf _ |>.mp hy₁L) c₀
    have hmem : ∀ a ∈ maximalIdeal B ^ e, algebraMap B C a ∈ 𝔓 ⊔ J.map (algebraMap B C) := by
      intro a ha
      obtain ⟨h, hh, hah⟩ := (hΛ.mem_iff_exists_mem_iInf c₀ (a • y₁)).mp (he a ha)
      have h1 : algebraMap B C a • H.mkQ y₁ ∈
          (J.map (algebraMap B C)) ^ (c₀ + 1) • (⊤ : Submodule C N) := by
        have : algebraMap B C a • H.mkQ y₁ = H.mkQ (a • y₁ - h) := by
          rw [map_sub, Submodule.mkQ_apply H h,
            (Submodule.Quotient.mk_eq_zero H).mpr ((hHi h).mpr hh), sub_zero,
            ← algebraMap_smul C a y₁, map_smul]
        rw [this]
        have hah' := (mem_pow_smul_top_iff_mem_map_pow_smul_top J (c₀ + 1) _).mpr hah
        have := Submodule.mem_map_of_mem (f := H.mkQ) hah'
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
        exact this
      have h2 : algebraMap B C a • H.mkQ y₁ ∈ Submodule.span C {H.mkQ y₁} :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have h3 := hc₀ (c₀ + 1) (by omega) ▸ Submodule.mem_inf.mpr ⟨h1, h2⟩
      rw [Nat.add_sub_cancel_left, pow_one] at h3
      have h4 : algebraMap B C a • H.mkQ y₁ ∈
          J.map (algebraMap B C) • Submodule.span C {H.mkQ y₁} :=
        Submodule.smul_mono le_rfl inf_le_right h3
      obtain ⟨j, hj, hjy⟩ := Submodule.mem_smul_span_singleton.mp h4
      have : algebraMap B C a - j ∈ 𝔓 := by
        rw [hann, sub_smul]
        rw [← map_smul, ← map_smul] at hjy
        have := (Submodule.Quotient.eq H).mp hjy
        rw [← neg_mem_iff, neg_sub] at this
        simpa [algebraMap_smul] using this
      have : algebraMap B C a = (algebraMap B C a - j) + j := by abel
      rw [this]
      exact add_mem (Submodule.mem_sup_left ‹_›) (Submodule.mem_sup_right hj)
    have hle : maximalIdeal B ≤ Q.comap (algebraMap B C) := by
      intro b hb
      have := hmem (b ^ e) (Ideal.pow_mem_pow hb e)
      rw [map_pow] at this
      exact hQ.mem_of_pow_mem e (sup_le h𝔓Q hJQ this)
    have h𝔪Q : 𝔪C ≤ Q := Ideal.map_le_iff_le_comap.mpr hle
    exact (h𝔪C.eq_of_le hQ.ne_top h𝔪Q).symm
  by_cases h𝔓𝔪 : 𝔓 = 𝔪C
  · -- depth: an element killed by `𝔪` modulo `H` lies in `H`
    obtain ⟨d, hd⟩ := hD
    have hy₁Λ : ∀ k, y₁ ∈ Λ k := by
      intro k
      apply hd k y₁
      intro a ha
      have h1 : algebraMap B C a ∈ 𝔓 := by
        rw [h𝔓𝔪]
        exact Ideal.mem_map_of_mem _ ha
      have h2 := (hann _).mp h1
      rw [algebraMap_smul] at h2
      exact (hmemH _).mp h2 (k + d)
    have h1 : (1 : C) ∈ 𝔓 := (hann 1).mpr (by rw [one_smul]; exact (hmemH y₁).mpr hy₁Λ)
    exact h𝔓prime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · have hnot := h6 𝔓 h𝔓prime h𝔓𝔪 hfib
    obtain ⟨c, hc⟩ := hc
    have hJ𝔓 : ¬ (J.map (algebraMap B C)) ^ c ≤ 𝔓 := by
      intro h
      exact h𝔓𝔪 (hfib 𝔓 h𝔓prime le_rfl (h𝔓prime.le_of_pow_le h))
    obtain ⟨f, hf, hf𝔓⟩ := Set.not_subset.mp hJ𝔓
    have hJcH : ∀ f' ∈ (J.map (algebraMap B C)) ^ c, ∀ h ∈ H, f' • h = 0 := by
      intro f' hf' h hh
      rw [← Ideal.map_pow] at hf'
      induction hf' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        rw [algebraMap_smul]
        exact smul_eq_zero_of_mem_iInf hc ((hHi h).mp hh) ha
      | zero => simp
      | add x z _ _ hx hz => rw [add_smul, hx, hz, add_zero]
      | smul r x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]
    have hfH : ∀ h ∈ H, f • h = 0 := hJcH f hf
    apply hnot
    refine (isAssociatedPrime_iff).mpr ⟨h𝔓prime, f • y₁, ?_⟩
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro hr
      rw [smul_comm]
      exact hfH _ ((hann r).mp hr)
    · intro hr
      have : (r * f) ∈ 𝔓 := (hann _).mpr (by rw [mul_smul, hr]; exact H.zero_mem)
      exact (h𝔓prime.mem_or_mem this).resolve_right hf𝔓

/-- **The `𝔪`-power torsion of the levels `P / Λ_k` is pro-zero**: for every `m` there is an
`m₂ ≥ m` such that an element which is `𝔪`-power torsion modulo `Λ m₂` lies in `Λ m`. -/
theorem exists_forall_pow_smul_mem_imp_mem (hJ : J ≤ maximalIdeal B)
    (hc : ∃ c, ∀ k, ∀ p ∈ Λ k, ∀ a ∈ J ^ c, a • p ∈ J ^ (k + 1) • (⊤ : Submodule B P))
    (hD : ∃ d, ∀ k (p : P), (∀ a ∈ maximalIdeal B, a • p ∈ Λ (k + d)) → p ∈ Λ k)
    (h6 : ∀ 𝔓 : Ideal (AdicCompletion J B), 𝔓.IsPrime →
      𝔓 ≠ (maximalIdeal B).map (algebraMap B (AdicCompletion J B)) →
      (∀ Q : Ideal (AdicCompletion J B), Q.IsPrime → 𝔓 ≤ Q →
        J.map (algebraMap B (AdicCompletion J B)) ≤ Q →
        Q = (maximalIdeal B).map (algebraMap B (AdicCompletion J B))) →
      𝔓 ∉ associatedPrimes (AdicCompletion J B) P)
    (m : ℕ) :
    ∃ m₂, m ≤ m₂ ∧ ∀ p : P, (∃ e, ∀ a ∈ maximalIdeal B ^ e, a • p ∈ Λ m₂) → p ∈ Λ m := by
  classical
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing J
  set C := AdicCompletion J B
  let Λc : ℕ → Submodule C P := fun k => hΛ.toCompletion hJfg k
  have hΛc : ∀ k (p : P), p ∈ Λc k ↔ p ∈ Λ k := fun _ _ => Iff.rfl
  let W : ℕ → Submodule C P := mTorsionMod hΛ hJfg
  have hW : ∀ k (p : P), p ∈ W k ↔ ∃ e, ∀ a ∈ maximalIdeal B ^ e, a • p ∈ Λ k :=
    fun _ _ => Iff.rfl
  have hWanti : ∀ {k k'}, k ≤ k' → W k' ≤ W k := by
    intro k k' hkk' p hp
    obtain ⟨e, he⟩ := hp
    exact ⟨e, fun a ha => hΛ.antitone hkk' (he a ha)⟩
  have hΛW : ∀ k, Λc k ≤ W k := fun k p hp => ⟨0, fun a _ => (Λ k).smul_mem a hp⟩
  -- the 𝔪-power torsion modulo `Λ j` is annihilated by a fixed power of `𝔪`
  have hbound : ∀ j, ∃ e₀, ∀ a ∈ maximalIdeal B ^ e₀, ∀ p ∈ W j, a • p ∈ Λ j := by
    intro j
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (W j) : (W j).FG)
    choose! e he using fun x (hx : x ∈ s) =>
      (hW j x).mp (hs ▸ Submodule.subset_span hx)
    refine ⟨s.sup e, fun a ha p hp => ?_⟩
    rw [← hs] at hp
    induction hp using Submodule.span_induction with
    | mem x hx => exact he x hx a (Ideal.pow_le_pow_right (Finset.le_sup hx) ha)
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
    | smul r x _ hx => rw [smul_comm]; exact hΛ.smul_mem hJfg r hx
  -- stabilization of the images of the higher torsion, by finite length
  have hstab : ∀ j, ∃ n, ∀ n', n ≤ n' → W (j + n') ⊔ Λc j = W (j + n) ⊔ Λc j := by
    intro j
    obtain ⟨e₀, he₀⟩ := hbound j
    let V := ↥(W j) ⧸ (Λc j).comap (W j).subtype
    let 𝔫 : Ideal C := (maximalIdeal B ^ (e₀ + 1)).map (algebraMap B C)
    have hV : Module.IsTorsionBySet C V 𝔫 := by
      intro v a
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
      obtain ⟨a, ha⟩ := a
      show a • Submodule.Quotient.mk x = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      show a • (x : P) ∈ Λ j
      induction ha using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨b, hb, rfl⟩ := hb
        rw [algebraMap_smul]
        exact he₀ b (Ideal.pow_le_pow_right (Nat.le_succ e₀) hb) x x.2
      | zero => simp
      | add b b' _ _ hb hb' => rw [add_smul]; exact add_mem hb hb'
      | smul r b _ hb => rw [smul_eq_mul, mul_smul]; exact hΛ.smul_mem hJfg r hb
    have : IsLocalRing C :=
      Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal J hJ
    have hmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C :=
      IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le J (maximalIdeal B) hJ hJfg)
    have hart : IsArtinianRing (C ⧸ 𝔫) := by
      refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
        ⟨⟨inferInstance, ?_⟩, fun q hq _ => ?_⟩
      · rw [← hmax]
        exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero e₀))
      · have h1 : (maximalIdeal B).map (algebraMap B C) ^ (e₀ + 1) ≤ q := by
          rw [← Ideal.map_pow]
          exact hq.2
        rw [hmax] at h1
        have := hq.1
        exact this.le_of_pow_le h1
    let : Module (C ⧸ 𝔫) V := hV.module
    have : IsScalarTower C (C ⧸ 𝔫) V := hV.isScalarTower
    have : Module.Finite C V := inferInstance
    have : Module.Finite (C ⧸ 𝔫) V := Module.Finite.of_restrictScalars_finite C _ _
    have : IsArtinian (C ⧸ 𝔫) V := inferInstance
    have : IsArtinian C V :=
      isArtinian_of_surjective_algebraMap (R := C ⧸ 𝔫) (M := V) Ideal.Quotient.mk_surjective
    let img : Submodule C P → Submodule C V := fun S =>
      (S.comap (W j).subtype).map ((Λc j).comap (W j).subtype).mkQ
    have himg_inj : ∀ S₁ S₂ : Submodule C P, Λc j ≤ S₁ → S₁ ≤ W j → Λc j ≤ S₂ → S₂ ≤ W j →
        img S₁ ≤ img S₂ → S₁ ≤ S₂ := by
      intro S₁ S₂ _ hS₁ hS₂ _ himg x hx
      have hx' : (⟨x, hS₁ hx⟩ : W j) ∈ S₁.comap (W j).subtype := hx
      obtain ⟨x', hx', hxx'⟩ := Submodule.mem_map.mp (himg (Submodule.mem_map_of_mem hx'))
      have hdiff := (Submodule.Quotient.eq _).mp hxx'
      have : x = (x' : P) - ((x' : P) - x) := by abel
      rw [this]
      exact sub_mem hx' (hS₂ hdiff)
    let g : ℕ →o (Submodule C V)ᵒᵈ :=
      ⟨fun n => OrderDual.toDual (img (W (j + n) ⊔ Λc j)), by
        intro n n' hnn'
        show img (W (j + n') ⊔ Λc j) ≤ img (W (j + n) ⊔ Λc j)
        exact Submodule.map_mono (Submodule.comap_mono
          (sup_le_sup_right (hWanti (by omega)) _))⟩
    obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes g
    refine ⟨n, fun n' hnn' => ?_⟩
    have hgeq : img (W (j + n) ⊔ Λc j) = img (W (j + n') ⊔ Λc j) := hn n' hnn'
    have hle₁ : ∀ n'', W (j + n'') ⊔ Λc j ≤ W j := fun n'' =>
      sup_le (hWanti (by omega)) (hΛW j)
    exact le_antisymm
      (himg_inj _ _ le_sup_right (hle₁ n') le_sup_right (hle₁ n) hgeq.symm.le)
      (himg_inj _ _ le_sup_right (hle₁ n) le_sup_right (hle₁ n') hgeq.le)
  choose μ hμ using hstab
  let S : ℕ → Submodule C P := fun j => W (j + μ j) ⊔ Λc j
  have hS : ∀ j m₂, j + μ j ≤ m₂ → W m₂ ⊔ Λc j = S j := by
    intro j m₂ hm₂
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hm₂
    rw [show j + μ j + n' = j + (μ j + n') by omega]
    exact hμ j _ (by omega)
  have hSW : ∀ j, S j ≤ W j := fun j => sup_le (hWanti (by omega)) (hΛW j)
  have hML : ∀ j, (S j).restrictScalars B ≤
      (S (j + 1)).restrictScalars B ⊔ J ^ (j + 1) • (⊤ : Submodule B P) := by
    intro j p hp
    let m₂ := max (j + μ j) (j + 1 + μ (j + 1))
    rw [Submodule.restrictScalars_mem, ← hS j m₂ (le_max_left _ _)] at hp
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hp
    have hy' : y ∈ Λ (j + 1) ⊔ J ^ (j + 1) • (⊤ : Submodule B P) := hΛ.eq_sup j ▸ hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy'
    rw [← add_assoc]
    refine Submodule.add_mem_sup ?_ hy₂
    rw [Submodule.restrictScalars_mem, ← hS (j + 1) m₂ (le_max_right _ _)]
    exact Submodule.add_mem_sup hx hy₁
  have hSΛ : ∀ j, ∀ p ∈ S j, p ∈ Λ j := by
    intro j p hp
    obtain ⟨z, hz, hpz⟩ := exists_limit J (fun i => (S (j + i)).restrictScalars B) j
      (fun i => by
        have := hML (j + i)
        rwa [show j + i + 1 = j + (i + 1) by omega] at this ⊢) (p := p) (by simpa using hp)
    have hzL : ∀ k, ∃ e, ∀ a ∈ maximalIdeal B ^ e, a • z ∈ Λ k := by
      intro k
      obtain ⟨x, hx, hzx⟩ := hz k
      have hxW : x ∈ W (j + k) := hSW (j + k) hx
      have hzW : z ∈ W (j + k) := by
        have : z = x + (z - x) := by abel
        rw [this]
        exact add_mem hxW (hΛW _ (hΛ.pow_smul_top_le _ hzx))
      exact hWanti (by omega : k ≤ j + k) hzW
    have hzH := hΛ.mem_iInf_of_forall_exists_pow_smul_mem hJ hc hD h6 z hzL
    exact (hΛ.mem_iff_exists_mem_iInf j p).mpr ⟨z, hzH, hpz⟩
  exact ⟨m + μ m, Nat.le_add_right _ _, fun p hp => hSΛ m p (Submodule.mem_sup_left hp)⟩

end FormalFiltration

end Stacks.LocalCohomology

end
