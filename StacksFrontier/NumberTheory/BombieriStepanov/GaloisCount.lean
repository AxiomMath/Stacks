module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Finiteness.Quotient

/-!
# The Frobenius-twisted primes of a Galois extension

Let `S/R` be a finite extension of domains with Galois group `G` (`IsGaloisGroup G R S`), and let
`p` be a maximal ideal of `R` with finite residue field. For `Q = #(R/p) ^ j` and `σ ∈ G`, call a
prime `P` of `S` over `p` *`σ`-twisted* when `σ x ≡ x ^ Q (mod P)` for every `x ∈ S`. This is
the condition counted by the twisted Bombieri–Stepanov bound, and the counting identity of the
lower bound of the Riemann hypothesis is

`|G| ≤ ∑_{P | p} f_P · #{σ : P is σ-twisted}`.

The Frobenius `x ↦ x ^ Q` of `S/P` is an automorphism over `R/p`; the decomposition group of `P`
surjects onto those automorphisms (`Ideal.Quotient.stabilizerHom_surjective`), so some `σ₀` makes
`P` twisted, and then so does every element of the coset `σ₀ · I_P` of the inertia group. Since
`|I_P| = e_P` and `∑_{P | p} e_P f_P = |G|`, the identity follows.

## Main definitions

* `Stacks.BombieriStepanov.frobSet`: the `σ` for which `P` is `σ`-twisted.

## Main results

* `Stacks.BombieriStepanov.natCard_inertia_le_natCard_frobSet`: `|I_P| ≤ #frobSet P Q`.
* `Stacks.BombieriStepanov.natCard_le_sum_inertiaDeg_mul_natCard_frobSet`: the counting identity.
* `Stacks.BombieriStepanov.natCard_frobSet_le_natCard_inertia`: the twisting elements form at most
  one coset of the inertia group.
-/

@[expose] public noncomputable section

open Ideal

namespace Stacks.BombieriStepanov

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- The `σ ∈ G` for which the prime `P` is `σ`-twisted: `σ x - x ^ Q ∈ P` for every `x`. -/
def frobSet (P : Ideal S) (Q : ℕ) : Set G := {σ | ∀ x : S, σ • x - x ^ Q ∈ P}

/-- **Some coset of the inertia group consists of twisting elements.** For a prime `P` over a
maximal ideal `p` with finite residue field and `Q = #(R/p) ^ j`, the inertia group of `P` injects
into the set of `σ` for which `P` is `σ`-twisted. -/
theorem natCard_inertia_le_natCard_frobSet [Module.Finite R S] (p : Ideal R) [p.IsMaximal]
    [Finite (R ⧸ p)] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (j : ℕ) :
    Nat.card (P.inertia G) ≤ Nat.card (frobSet G P (Nat.card (R ⧸ p) ^ j)) := by
  classical
  have : Algebra.IsInvariant R S G := IsGaloisGroup.isInvariant
  have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite (R ⧸ p) (S ⧸ P) := module_finite_of_liesOver P p
  have : Finite (S ⧸ P) := Module.finite_of_finite (R ⧸ p)
  let : Fintype (R ⧸ p) := Fintype.ofFinite _
  -- the `Q`-power Frobenius of `S ⧸ P` over `R ⧸ p`
  set φ : (S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P) := FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ P) ^ j
  have hφ : ∀ y : S ⧸ P, φ y = y ^ (Nat.card (R ⧸ p) ^ j) := by
    intro y
    have h := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (R ⧸ p) (S ⧸ P) j) y
    rw [Nat.card_eq_fintype_card, ← h]
    simp only [φ, AlgEquiv.coe_pow]
  obtain ⟨σ₀, hσ₀⟩ := Ideal.Quotient.stabilizerHom_surjective G p P φ
  refine Nat.card_le_card_of_injective (fun τ => ⟨(σ₀ : G) * τ, fun x => ?_⟩) ?_
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, mul_smul, map_pow, ← hφ, ← hσ₀,
      Ideal.Quotient.stabilizerHom_apply, sub_eq_zero]
    have hτ : Ideal.Quotient.mk P ((τ : G) • x) = Ideal.Quotient.mk P x :=
      Ideal.Quotient.eq.2 ((AddSubgroup.mem_inertia).1 τ.2 x)
    have h := congrArg (Ideal.Quotient.stabilizerHom P p G σ₀) hτ
    rwa [Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.stabilizerHom_apply] at h
  · intro τ τ' h
    have := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel this)

/-- **The counting identity of the twisted primes.** For a maximal ideal `p` of `R` with finite
residue field and `Q = #(R/p) ^ j`,
`|G| ≤ ∑_{P | p} f_P · #{σ ∈ G : σ x ≡ x ^ Q (mod P) for all x}`. -/
theorem natCard_le_sum_inertiaDeg_mul_natCard_frobSet [IsDomain R] [IsDomain S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsMaximal] [Finite (R ⧸ p)]
    [Fintype (p.primesOver S)] (j : ℕ) :
    Nat.card G ≤ ∑ P : p.primesOver S,
      P.1.inertiaDeg R * Nat.card (frobSet G P.1 (Nat.card (R ⧸ p) ^ j)) := by
  rw [← sum_ramification_inertia_eq_card (S := S) (p := p) (G := G)]
  refine Finset.sum_le_sum fun P _ => ?_
  have := P.2.1
  have := P.2.2
  have : PerfectField p.ResidueField := inferInstance
  rw [mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  rw [← ramificationIdxIn_eq_ramificationIdx p P.1 G,
    ← card_inertia_eq_ramificationIdxIn (G := G) p P.1]
  exact natCard_inertia_le_natCard_frobSet G p P.1 j

/-- **Two twisting elements differ by inertia.** If `σ₀` and `σ` both make the maximal ideal `P`
twisted, then `σ₀⁻¹ σ` lies in the inertia group of `P`; so the twisting elements form at most one
coset of the inertia group. Here `G` is any group acting on `S` by ring automorphisms. -/
theorem natCard_frobSet_le_natCard_inertia {G : Type*} [Group G] [Finite G] [MulSemiringAction G S]
    (P : Ideal S) [P.IsMaximal] (Q : ℕ) (hQ : Q ≠ 0) :
    Nat.card (frobSet G P Q) ≤ Nat.card (P.inertia G) := by
  classical
  rcases (frobSet G P Q).eq_empty_or_nonempty with h | ⟨σ₀, hσ₀⟩
  · rw [h]
    simp
  -- `σ₀` stabilizes `P`
  have hle : ∀ y ∈ P, σ₀ • y ∈ P := by
    intro y hy
    have h := hσ₀ y
    have hyQ : y ^ Q ∈ P := Ideal.pow_mem_of_mem P hy Q (Nat.pos_of_ne_zero hQ)
    simpa using P.add_mem h hyQ
  have hJ : P = Ideal.comap (MulSemiringAction.toRingHom G S σ₀) P := by
    refine (inferInstance : P.IsMaximal).eq_of_le ?_ fun y hy => hle y hy
    intro htop
    have h1 : (1 : S) ∈ Ideal.comap (MulSemiringAction.toRingHom G S σ₀) P :=
      htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).2 h1)
  have hinv : ∀ y ∈ P, σ₀⁻¹ • y ∈ P := by
    intro y hy
    have : σ₀⁻¹ • y ∈ Ideal.comap (MulSemiringAction.toRingHom G S σ₀) P := by
      rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply, smul_inv_smul]
      exact hy
    rwa [← hJ] at this
  refine Nat.card_le_card_of_injective (fun σ => ⟨σ₀⁻¹ * σ.1, fun x => ?_⟩) ?_
  · have h : σ.1 • x - σ₀ • x ∈ P := by
      have := P.sub_mem (σ.2 x) (hσ₀ x)
      simpa using this
    have h' := hinv _ h
    simpa [mul_smul, smul_sub] using h'
  · intro σ σ' h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))

end Stacks.BombieriStepanov

end
