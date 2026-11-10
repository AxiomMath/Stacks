module

public import StacksFrontier.CategoryTheory.Trace.Sorites.TwistedRestrictionTrace
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# A group-ring trace with vanishing conjugacy traces dies at a lower level

Let `ℓ` be a prime, `A = ℤ/ℓⁿ`, `G` a finite group and `T ∈ A[G]^♮` an element all of whose
conjugacy traces `κ_g(T) = ∑_{k ∈ G} T(k⁻¹ g k)` vanish. Writing `T` as the class of
`∑_h x_h h`, the conjugacy trace at `g` is `#Z_G(g)` times the sum of the coefficients `x_h` over
the conjugacy class of `g`; so each of these class sums is divisible by `ℓ^{n - v}`, where `ℓ^v`
is the `ℓ`-part of `#G`. Hence every additive map out of `A[G]^♮` into a group killed by `ℓ^m`
vanishes on `T` once `n ≥ m + v`.

This is the last step of the argument of Steps 7 to 9 of the proof of [Stacks, Tag 03UG]: there
`T` is the trace of `π^*` on `RΓ_c(U_k̄, f_* A)` over `A[G]`, its conjugacy traces are the traces
of `(g⁻¹π_V)^*` on `RΓ_c(V_k̄, A)` (which vanish by Step 9), and the additive map is the one
induced by the change of coefficients to `Λ`, which is killed by `ℓ^m`.

## Main results

* `MulAction.sum_smul_eq_card_stabilizer_nsmul`: `∑_{k ∈ G} f(k • b)` is `#Stab(b)` times the
  sum of `f` over the orbit of `b`.
* `Stacks.Trace.map_eq_zero_of_conjugacyTrace_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.FilteredDerived
open scoped MonoidAlgebra BigOperators

universe u v

namespace MulAction

/-- **Summing over a group through an orbit.** For a finite group acting on a type,
`∑_{k ∈ G} f(k • b)` is `#Stab(b)` times the sum of `f` over the orbit of `b`. -/
theorem sum_smul_eq_card_stabilizer_nsmul {G : Type u} [Group G] [Fintype G] {X : Type v}
    [MulAction G X] (b : X) [Fintype (orbit G b)] {M : Type*} [AddCommMonoid M] (f : X → M) :
    ∑ k : G, f (k • b) = Nat.card (stabilizer G b) • ∑ o : orbit G b, f o := by
  classical
  let φ : G → orbit G b := fun k => ⟨k • b, mem_orbit b k⟩
  have hφ : ∀ k, f (k • b) = f (φ k : X) := fun _ => rfl
  simp_rw [hφ]
  rw [← Finset.sum_fiberwise Finset.univ φ (fun k => f (φ k : X)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hfib : (Finset.univ.filter fun k => φ k = o).card = Nat.card (stabilizer G b) := by
    obtain ⟨_, ⟨k₀, rfl⟩⟩ := o
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun k => ⟨k₀⁻¹ * k, ?_⟩
        invFun := fun s => ⟨k₀ * s, ?_⟩
        left_inv := fun k => by ext; simp
        right_inv := fun s => by ext; simp }
    · have hk := (Finset.mem_filter.1 k.2).2
      have hk' : k.1 • b = k₀ • b := congrArg Subtype.val hk
      rw [mem_stabilizer_iff, mul_smul, hk', inv_smul_smul]
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Subtype.ext ?_⟩
      change (k₀ * s) • b = k₀ • b
      rw [mul_smul, mem_stabilizer_iff.1 s.2]
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.sum_const,
    hfib]

end MulAction

namespace Stacks.Trace

/-- Over a commutative ring the additive commutator quotient is the ring itself. -/
theorem eq_zero_of_additiveCommutatorQuotientMk_eq_zero {A : Type u} [CommRing A] {a : A}
    (h : additiveCommutatorQuotientMk A a = 0) : a = 0 := by
  have hbot : additiveCommutatorSubgroup A = ⊥ := by
    refine AddSubgroup.closure_eq_bot_iff.2 ?_
    rintro _ ⟨x, y, rfl⟩
    rw [mul_comm, sub_self]
    rfl
  have hmem : a ∈ additiveCommutatorSubgroup A := (QuotientAddGroup.eq_zero_iff a).1 h
  rw [hbot] at hmem
  exact hmem

variable {ℓ n m : ℕ} [Fact ℓ.Prime] (G : Type v) [Group G] [Fintype G]

omit [Fintype G] in
/-- The class of `single h 1` in `A[G]^♮` depends only on the conjugacy class of `h`. -/
theorem additiveCommutatorQuotientMk_single_conj (A : Type u) [Ring A] (h k : G) :
    additiveCommutatorQuotientMk A[G] (MonoidAlgebra.single (k⁻¹ * h * k) (1 : A)) =
      additiveCommutatorQuotientMk A[G] (MonoidAlgebra.single h (1 : A)) := by
  have e : MonoidAlgebra.single (k⁻¹ * h * k) (1 : A) =
      MonoidAlgebra.single k⁻¹ (1 : A) * (MonoidAlgebra.single h 1 * MonoidAlgebra.single k 1) := by
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
      mul_assoc]
  rw [e, additiveCommutatorQuotientMk_mul_comm, mul_assoc, MonoidAlgebra.single_mul_single,
    MonoidAlgebra.single_mul_single, mul_one, mul_one, mul_inv_cancel, mul_one]

/-- **A group-ring trace whose conjugacy traces vanish dies under every additive map into a group
killed by `ℓ^m`**, over `A = ℤ/ℓⁿ` with `n ≥ m + v` for every `ℓ^v` dividing `#G`. -/
theorem map_eq_zero_of_conjugacyTrace_eq_zero
    (T : AdditiveCommutatorQuotient (ZMod (ℓ ^ n))[G])
    (hT : ∀ g : G, conjugacyTrace (ZMod (ℓ ^ n)) G g T = 0)
    {M : Type*} [AddCommGroup M] (Ψ : AdditiveCommutatorQuotient (ZMod (ℓ ^ n))[G] →+ M)
    (hM : ∀ y : M, (ℓ ^ m) • y = 0) (hn : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card G → m + v ≤ n) :
    Ψ T = 0 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  set A := ZMod (ℓ ^ n)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective T
  change Ψ (additiveCommutatorQuotientMk A[G] x) = 0
  let X : G → ℕ := fun h => (x.coeff h).val
  let y : G → M := fun h => Ψ (additiveCommutatorQuotientMk A[G] (MonoidAlgebra.single h 1))
  have hy : ∀ h k : G, y (k⁻¹ * h * k) = y h := fun h k => by
    simp only [y, additiveCommutatorQuotientMk_single_conj]
  -- `Ψ(T) = ∑_h X_h • y_h`
  have hsum : Ψ (additiveCommutatorQuotientMk A[G] x) = ∑ h, X h • y h := by
    have hx : x = ∑ h, MonoidAlgebra.single h (x.coeff h) := by
      ext g
      simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]
    rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have e : MonoidAlgebra.single h (x.coeff h) = X h • MonoidAlgebra.single h (1 : A) := by
      rw [MonoidAlgebra.smul_single, nsmul_one, ZMod.natCast_zmod_val]
    rw [e, map_nsmul, map_nsmul]
  -- every class sum is divisible by `ℓ^m`
  have hclass : ∀ g : G, ℓ ^ m ∣ ∑ o : MulAction.orbit (ConjAct G) g, X o := by
    intro g
    have h0 := hT g
    rw [show (QuotientAddGroup.mk x : AdditiveCommutatorQuotient A[G]) =
      additiveCommutatorQuotientMk A[G] x from rfl, conjugacyTrace_mk] at h0
    have h1 := eq_zero_of_additiveCommutatorQuotientMk_eq_zero h0
    have h2 : ((∑ k : G, X (k⁻¹ * g * k) : ℕ) : A) = 0 := by
      rw [← h1, Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => ZMod.natCast_zmod_val _
    rw [ZMod.natCast_eq_zero_iff] at h2
    -- `∑_k X(k⁻¹gk) = #Z · (class sum)`
    have h3 : ∑ k : G, X (k⁻¹ * g * k) =
        Nat.card (MulAction.stabilizer (ConjAct G) g) •
          ∑ o : MulAction.orbit (ConjAct G) g, X o := by
      rw [← MulAction.sum_smul_eq_card_stabilizer_nsmul g X]
      exact Fintype.sum_equiv ((Equiv.inv G).trans ConjAct.toConjAct.toEquiv) _ _
        (fun k => by simp [ConjAct.smul_def])
    rw [h3, smul_eq_mul] at h2
    obtain ⟨v, u, hu, hGu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Fintype.card_ne_zero (α := G)) ℓ
      hℓ.ne_one
    have hZ : Nat.card (MulAction.stabilizer (ConjAct G) g) ∣ Fintype.card G := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_congr ConjAct.ofConjAct.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h4 : ℓ ^ n ∣ ℓ ^ v * (u * ∑ o : MulAction.orbit (ConjAct G) g, X o) := by
      rw [← mul_assoc, ← hGu]
      exact h2.trans (Nat.mul_dvd_mul_right hZ _)
    have hcop : Nat.Coprime (ℓ ^ n) u :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hu)
    have h5 : ℓ ^ n ∣ ℓ ^ v * ∑ o : MulAction.orbit (ConjAct G) g, X o := by
      rw [mul_left_comm] at h4
      exact hcop.dvd_of_dvd_mul_left h4
    have hmv := hn v ⟨u, hGu⟩
    have h6 : ℓ ^ v * ℓ ^ m ∣ ℓ ^ v * ∑ o : MulAction.orbit (ConjAct G) g, X o := by
      rw [← pow_add]
      exact (pow_dvd_pow ℓ (by omega)).trans h5
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ.pos v) h6
  rw [hsum, ← Finset.sum_fiberwise Finset.univ
    (fun h => (Quotient.mk'' h : MulAction.orbitRel.Quotient (ConjAct G) G)) _]
  refine Finset.sum_eq_zero fun ω _ => ?_
  induction ω using Quotient.inductionOn' with
  | h g =>
  have hmem : ∀ h : G, h ∈ Finset.univ.filter (fun h : G =>
      (Quotient.mk'' h : MulAction.orbitRel.Quotient (ConjAct G) G) = Quotient.mk'' g) ↔
        h ∈ MulAction.orbit (ConjAct G) g := fun h => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq'',
      MulAction.orbitRel_apply]
  have hfib : ∀ h ∈ Finset.univ.filter (fun h : G =>
      (Quotient.mk'' h : MulAction.orbitRel.Quotient (ConjAct G) G) = Quotient.mk'' g),
        X h • y h = X h • y g := fun h hh => by
    obtain ⟨c, rfl⟩ := (hmem h).1 hh
    congr 1
    change y (c • g) = y g
    rw [ConjAct.smul_def]
    simpa using hy g (ConjAct.ofConjAct c)⁻¹
  rw [Finset.sum_congr rfl hfib, ← Finset.sum_smul, Finset.sum_subtype _ hmem X]
  · obtain ⟨t, ht⟩ := hclass g
    rw [ht, mul_comm, mul_smul, hM, smul_zero]

end Stacks.Trace
