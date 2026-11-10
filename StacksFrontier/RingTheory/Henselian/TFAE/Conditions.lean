module

import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Characterisations of henselian local rings: the conditions and the étale cycle

This file begins the proof of Lemma 04GG, the equivalence of thirteen conditions on a local ring
`(R, 𝔪, κ)`; the statement, the list of the conditions and the plan of the proof are in the module
docstring of `StacksFrontier.RingTheory.Henselian.TFAE.Factorization`, which assembles them into
`HenselianLocalRing.TFAE_factorization_etale_quasiFinite`.

Here the thirteen conditions are stated as the private reducible abbreviations `Item1`, …,
`Item13`. The file then proves the implications that are restrictions or specialisations
(2 ⇒ 1, 8 ⇒ 7, 4 ⇒ 3, 5 ⇒ 3, 10 ⇒ 9, 6 ⇒ 4 and 6 ⇒ 5), collects the lemmas on reduction to the
residue field and on splitting off a factor of a finite algebra that the later implications share
— among them `exists_isRoot_of_sub_mem`, the common last step of 3 ⇒ 1, 9 ⇒ 1 and 13 ⇒ 1 — and
closes the étale cycle `1 → 8 → 7 → 1`.

## Main results

* `Stacks.Henselian.Characterizations.finite_of_ringEquiv_pi_local`: a module-finite algebra over
  a local ring which is a product of local rings has only finitely many factors.

## References

* [StacksProject 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

universe u

@[expose] public section

namespace Stacks.Henselian.Characterizations

open Polynomial IsLocalRing TensorProduct

variable (R : Type u) [CommRing R] [IsLocalRing R]
/-! ### The thirteen conditions -/

/-- Item (1) of 04GG: `R` is henselian. -/
private abbrev Item1 : Prop := HenselianLocalRing R

/-- Item (2) of 04GG: every simple root of `f̄` in `κ`, for an arbitrary `f ∈ R[T]`, lifts to a
root of `f` in `R`. -/
private abbrev Item2 : Prop :=
  ∀ f : R[X], ∀ a₀ : ResidueField R, aeval a₀ f = 0 → aeval a₀ (derivative f) ≠ 0 →
    ∃ a : R, f.IsRoot a ∧ residue R a = a₀

/-- Item (3) of 04GG: a coprime factorisation of `f̄` lifts to a factorisation of `f`, for monic
`f`. -/
private abbrev Item3 : Prop :=
  ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
    IsCoprime g₀ h₀ →
    ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀

/-- Item (4) of 04GG: item (3) with the degree of the first factor preserved. -/
private abbrev Item4 : Prop :=
  ∀ f : R[X], f.Monic → ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
    IsCoprime g₀ h₀ →
    ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.degree = g₀.degree

/-- Item (5) of 04GG: item (3) for arbitrary, not necessarily monic, `f`. -/
private abbrev Item5 : Prop :=
  ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], f.map (residue R) = g₀ * h₀ →
    IsCoprime g₀ h₀ →
    ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀

/-- Item (6) of 04GG: item (5) with the degree of the first factor preserved; the source's tacit
`g₀ ≠ 0`, without which the item holds only for fields, is carried explicitly. -/
private abbrev Item6 : Prop :=
  ∀ f : R[X], ∀ g₀ h₀ : (ResidueField R)[X], g₀ ≠ 0 → f.map (residue R) = g₀ * h₀ →
    IsCoprime g₀ h₀ →
    ∃ g h : R[X], f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ ∧
      g.degree = g₀.degree

/-- Item (7) of 04GG: an étale `R`-algebra with a prime over `𝔪` whose residue field is `κ`
admits a retraction. -/
private abbrev Item7 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
    ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
    Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      (q.over_def _)) → Nonempty (S →ₐ[R] R)

/-- Item (8) of 04GG: the retraction of item (7) exists and is unique once pinned by
`τ⁻¹(𝔪) = q`. -/
private abbrev Item8 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.Etale R S →
    ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
    Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) q (Algebra.ofId R S)
      (q.over_def _)) → ∃! τ : S →ₐ[R] R, (maximalIdeal R).comap (τ : S →+* R) = q

/-- Item (9) of 04GG: every finite `R`-algebra is a product of local rings. -/
private abbrev Item9 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
    ∃ (ι : Type u) (A : ι → Type u) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsLocalRing (A i)),
      Nonempty (S ≃+* ∀ i, A i)

/-- Item (10) of 04GG: every finite `R`-algebra is a finite product of local rings. -/
private abbrev Item10 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Module.Finite R S →
    ∃ (ι : Type u) (_ : Finite ι) (A : ι → Type u) (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, IsLocalRing (A i)), Nonempty (S ≃+* ∀ i, A i)

/-- Item (11) of 04GG: a finite type `R`-algebra is `A × B` with `A` finite over `R` and `B`
quasi-finite over `R` at no prime over `𝔪`. -/
private abbrev Item11 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
      (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
      ∀ q : Ideal B, ∀ [q.IsPrime], q.LiesOver (maximalIdeal R) →
        ¬ Algebra.QuasiFiniteAt R q

/-- Item (12) of 04GG: a finite type `R`-algebra is `A × B` with `A` finite over `R` and every
irreducible component of `Spec(κ ⊗_R B)` of dimension `≥ 1`. -/
private abbrev Item12 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
      (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
      ∀ p ∈ minimalPrimes (ResidueField R ⊗[R] B),
        1 ≤ ringKrullDim ((ResidueField R ⊗[R] B) ⧸ p)

/-- Item (13) of 04GG: a quasi-finite `R`-algebra is `A × B` with `A` finite over `R` and
`κ ⊗_R B = 0`. -/
private abbrev Item13 : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
    Algebra.QuasiFinite R S →
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra R A) (_ : Algebra R B)
      (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
      Subsingleton (ResidueField R ⊗[R] B)

/-! ### The easy implications -/

/-- 2 ⇒ 1: in (2) all polynomials are considered and in (1) only the monic ones. -/
private theorem item2_imp_item1 : Item2 R → Item1 R := fun H =>
  ((HenselianLocalRing.TFAE R).out 2 1).mp fun f _ a₀ h₁ h₂ => H f a₀ h₁ h₂

/-- 8 ⇒ 7: forget the uniqueness and the pinning of the retraction. -/
private theorem item8_imp_item7 : Item8 R → Item7 R := by
  intro H S _ _ hE q _ _ hb
  obtain ⟨τ, -, -⟩ := H S hE q hb
  exact ⟨τ⟩

/-- 4 ⇒ 3: forget the control of the degree. -/
private theorem item4_imp_item3 : Item4 R → Item3 R := by
  intro H f hf g₀ h₀ he hc
  obtain ⟨g, h, h₁, h₂, h₃, -⟩ := H f hf g₀ h₀ he hc
  exact ⟨g, h, h₁, h₂, h₃⟩

/-- 5 ⇒ 3: in (5) all polynomials are considered and in (3) only the monic ones. -/
private theorem item5_imp_item3 : Item5 R → Item3 R := fun H f _ => H f

omit [IsLocalRing R] in
/-- 10 ⇒ 9: forget the finiteness of the index type. -/
private theorem item10_imp_item9 : Item10 R → Item9 R := by
  intro H S _ _ hS
  obtain ⟨ι, -, A, hc, hl, he⟩ := H S hS
  exact ⟨ι, A, hc, hl, he⟩

/-- 6 ⇒ 4: in (6) all polynomials are considered and in (4) only the monic ones, for which the
side condition `g₀ ≠ 0` of (6) is automatic since `f̄` is then monic. -/
private theorem item6_imp_item4 : Item6 R → Item4 R := by
  intro H f hf g₀ h₀ he hc
  have hfm : (f.map (residue R)).Monic := hf.map _
  refine H f g₀ h₀ ?_ he hc
  rintro rfl
  rw [zero_mul] at he
  exact hfm.ne_zero he

/-- 6 ⇒ 5: forget the control of the degree; the side condition `g₀ ≠ 0` of (6) is only a
restriction when `f̄ = 0`, and there a factorisation with `g = 0` is produced by hand from a unit
of `R` lifting the constant `h₀`. -/
private theorem item6_imp_item5 : Item6 R → Item5 R := by
  intro H f g₀ h₀ he hc
  rcases eq_or_ne g₀ 0 with rfl | hg₀
  · rw [zero_mul] at he
    rw [isCoprime_zero_left] at hc
    obtain ⟨c, hcu, rfl⟩ := Polynomial.isUnit_iff.mp hc
    obtain ⟨b, hbc⟩ : ∃ b : R, residue R b = c := Ideal.Quotient.mk_surjective c
    have hb : IsUnit b := by
      rw [← notMem_maximalIdeal]
      intro hmem
      refine hcu.ne_zero ?_
      rw [← hbc]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    have hu : (↑hb.unit⁻¹ : R) * b = 1 := by
      have h := hb.unit.inv_mul
      rwa [hb.unit_spec] at h
    refine ⟨C (↑hb.unit⁻¹ : R) * f, C b, ?_, ?_, ?_⟩
    · calc f = C ((↑hb.unit⁻¹ : R) * b) * f := by rw [hu, map_one, one_mul]
        _ = C (↑hb.unit⁻¹ : R) * f * C b := by rw [C_mul]; ring
    · rw [Polynomial.map_mul, he, mul_zero]
    · rw [Polynomial.map_C, hbc]
  · obtain ⟨g, h, h₁, h₂, h₃, -⟩ := H f g₀ h₀ hg₀ he hc
    exact ⟨g, h, h₁, h₂, h₃⟩

/-! ### Reduction to the residue field -/

/-- Evaluating the reduction `p̄ ∈ κ[X]` at a point of `κ` is `Polynomial.aeval` of `p` there. -/
private lemma aeval_eq_eval_map (p : R[X]) (x : ResidueField R) :
    aeval x p = (p.map (residue R)).eval x := by
  rw [aeval_def, IsLocalRing.ResidueField.algebraMap_eq, Polynomial.eval₂_eq_eval_map]

/-- Reduction commutes with evaluation at a point of `R`: `p̄(r̄) = p(r)‾`. -/
private lemma eval_map_residue (p : R[X]) (r : R) :
    (p.map (residue R)).eval (residue R r) = residue R (p.eval r) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- Coefficients of a polynomial whose reduction vanishes lie in `𝔪`. -/
private lemma coeff_mem_maximalIdeal_of_map_eq_zero {p : R[X]} (hp : p.map (residue R) = 0)
    (n : ℕ) : p.coeff n ∈ maximalIdeal R := by
  have h : (p.map (residue R)).coeff n = 0 := by rw [hp]; simp
  rw [Polynomial.coeff_map] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- Dividing the reduction of `f` by a simple root: a lift `h ∈ R[X]` of `f̄ / (X - a₀)`, together
with the factorisation, the coprimality of the two factors and the value `h̄(a₀) = f̄'(a₀)`. -/
private lemma exists_lift_divByMonic (f : R[X]) (a₀ : ResidueField R) (h₁ : aeval a₀ f = 0)
    (h₂ : aeval a₀ (derivative f) ≠ 0) :
    ∃ h : R[X], f.map (residue R) = (X - C a₀) * h.map (residue R) ∧
      IsCoprime (X - C a₀ : (ResidueField R)[X]) (h.map (residue R)) ∧
      (h.map (residue R)).eval a₀ = aeval a₀ (derivative f) := by
  obtain ⟨h, hh⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective
    (f.map (residue R) /ₘ (X - C a₀))
  have hderiv : Polynomial.eval a₀ (derivative (f.map (residue R))) = aeval a₀ (derivative f) := by
    rw [Polynomial.derivative_map, ← aeval_eq_eval_map]
  have hfac : f.map (residue R) = (X - C a₀) * h.map (residue R) := by
    rw [hh]
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr (by
      rw [Polynomial.IsRoot.def, ← aeval_eq_eval_map]; exact h₁)).symm
  refine ⟨h, hfac, ?_, ?_⟩
  · rw [hh]
    exact Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero _ a₀ (by rw [hderiv]; exact h₂)
  · rw [← hderiv, hfac, Polynomial.derivative_mul]
    simp

/-! ### Splitting off a factor of a finite algebra -/

omit [IsLocalRing R] in
/-- The left factor of an `R`-algebra decomposition `S ≃ₐ[R] A × B` is a direct summand of `S` as
an `R`-module: the inclusion `A → S` and the projection `S → A` compose to the identity. -/
private lemma fst_comp_inl_eq_id {S A B : Type*} [CommRing S] [Algebra R S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (Ψ : S ≃ₐ[R] A × B) :
    (LinearMap.fst R A B ∘ₗ Ψ.toLinearEquiv.toLinearMap) ∘ₗ
      (Ψ.symm.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inl R A B) = LinearMap.id := by
  ext x
  simp

omit [IsLocalRing R] in
/-- A factor of a projective module is projective. -/
private lemma projective_of_algEquiv_prod {S A B : Type*} [CommRing S] [Algebra R S]
    [Module.Projective R S] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (Ψ : S ≃ₐ[R] A × B) : Module.Projective R A :=
  Module.Projective.of_split _ _ (fst_comp_inl_eq_id R Ψ)

omit [IsLocalRing R] in
/-- A factor of a flat module is flat. -/
private lemma flat_of_algEquiv_prod {S A B : Type*} [CommRing S] [Algebra R S]
    [Module.Flat R S] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (Ψ : S ≃ₐ[R] A × B) : Module.Flat R A :=
  Module.Flat.of_retract _ _ (fst_comp_inl_eq_id R Ψ)

omit [IsLocalRing R] in
/-- **Chinese remainder theorem for a pair of elements with zero product.** If `γ δ : S` satisfy
`γ δ = 0` and generate the unit ideal, then `e = u γ` is an idempotent with `(γ) = (e)` and
`(δ) = (1 - e)`, and `S` is the product of the two quotients. -/
private lemma nonempty_algEquiv_quotient_prod {S : Type*} [CommRing S] [Algebra R S]
    (γ δ u v : S) (hγδ : γ * δ = 0) (huv : u * γ + v * δ = 1) :
    Nonempty (S ≃ₐ[R] (S ⧸ Ideal.span ({γ} : Set S)) × (S ⧸ Ideal.span ({δ} : Set S))) := by
  classical
  have hγe : γ * (u * γ) = γ := by linear_combination γ * huv - v * hγδ
  have heI : (u * γ) ∈ Ideal.span ({γ} : Set S) := Ideal.mem_span_singleton'.mpr ⟨u, rfl⟩
  have h1eJ : (1 - u * γ) ∈ Ideal.span ({δ} : Set S) :=
    Ideal.mem_span_singleton'.mpr ⟨v, by linear_combination huv⟩
  let Φ : S →ₐ[R] (S ⧸ Ideal.span ({γ} : Set S)) × (S ⧸ Ideal.span ({δ} : Set S)) :=
    (Ideal.Quotient.mkₐ R _).prod (Ideal.Quotient.mkₐ R _)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : x ∈ Ideal.span ({γ} : Set S) := by
      have hfst := congrArg Prod.fst hx
      simpa [Φ, Ideal.Quotient.eq_zero_iff_mem] using hfst
    have h2 : x ∈ Ideal.span ({δ} : Set S) := by
      have hsnd := congrArg Prod.snd hx
      simpa [Φ, Ideal.Quotient.eq_zero_iff_mem] using hsnd
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h2
    have e1 : x * (u * γ) = x := by rw [← hc]; linear_combination c * hγe
    have e2 : x * (u * γ) = 0 := by rw [← hd]; linear_combination u * d * hγδ
    rw [← e1, e2]
  have hsurj : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨(1 - u * γ) * A + (u * γ) * B, ?_⟩
    have h1 : (Ideal.Quotient.mk (Ideal.span ({γ} : Set S))) (u * γ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr heI
    have h2' : (Ideal.Quotient.mk (Ideal.span ({δ} : Set S))) (u * γ) = 1 := by
      have h2 : (Ideal.Quotient.mk (Ideal.span ({δ} : Set S))) (1 - u * γ) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr h1eJ
      rw [map_sub, map_one, sub_eq_zero] at h2
      exact h2.symm
    apply Prod.ext <;> simp [Φ, Ideal.Quotient.mkₐ_eq_mk, h1, h2', sub_mul]
  exact ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

omit [IsLocalRing R] in
/-- A polynomial all of whose coefficients lie in `I` takes values in `I A`. -/
private lemma aeval_mem_map {A : Type*} [CommRing A] [Algebra R A] (x : A) (I : Ideal R)
    (p : R[X]) (hp : ∀ n, p.coeff n ∈ I) :
    aeval x p ∈ Ideal.map (algebraMap R A) I := by
  have h := Ideal.mem_map_of_mem ((aeval x : R[X] →ₐ[R] A) : R[X] →+* A)
    (Ideal.mem_map_C_iff.mpr hp)
  rwa [Ideal.map_map, show ((aeval x : R[X] →ₐ[R] A) : R[X] →+* A).comp
    (C : R →+* R[X]) = algebraMap R A from by ext r; simp] at h

omit [IsLocalRing R] in
/-- Evaluation respects congruence modulo an ideal: if `y ≡ b` modulo `J` then
`q(y) ≡ q(b)` modulo `J`. -/
private lemma aeval_sub_mem {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A) (q : R[X])
    (y : A) (b : R) (hy : y - algebraMap R A b ∈ J) :
    aeval y q - algebraMap R A (q.eval b) ∈ J := by
  have hq : (Ideal.Quotient.mk J) y = (Ideal.Quotient.mk J) (algebraMap R A b) := by
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  calc (Ideal.Quotient.mk J) (aeval y q)
      = aeval ((Ideal.Quotient.mk J) y) q := by
        rw [← Ideal.Quotient.mkₐ_eq_mk R J, Polynomial.aeval_algHom_apply]
    _ = aeval ((Ideal.Quotient.mk J) (algebraMap R A b)) q := by rw [hq]
    _ = (Ideal.Quotient.mk J) (algebraMap R A (q.eval b)) := by
        rw [← Ideal.Quotient.mkₐ_eq_mk R J, Polynomial.aeval_algHom_apply, Polynomial.aeval_def,
          Polynomial.eval₂_at_apply]

omit [IsLocalRing R] in
/-- Cancelling a factor congruent to a unit scalar: if `z G ≡ σ` and `G ≡ τ` modulo `J` with `τ` a
unit of `R`, then `z ≡ σ τ⁻¹` modulo `J`. -/
private lemma exists_sub_mem_of_mul_sub_mem {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A)
    (z G : A) (σ τ : R) (hτ : IsUnit τ) (h1 : z * G - algebraMap R A σ ∈ J)
    (h2 : G - algebraMap R A τ ∈ J) : ∃ r : R, z - algebraMap R A r ∈ J := by
  refine ⟨σ * ↑hτ.unit⁻¹, ?_⟩
  have key : z * algebraMap R A τ - algebraMap R A σ ∈ J := by
    rw [show z * algebraMap R A τ - algebraMap R A σ
        = (z * G - algebraMap R A σ) - z * (G - algebraMap R A τ) by ring]
    exact sub_mem h1 (J.mul_mem_left _ h2)
  have htτ : algebraMap R A (↑hτ.unit⁻¹ : R) * algebraMap R A τ = 1 := by
    rw [← map_mul, mul_comm, hτ.mul_val_inv, map_one]
  have hid : z - algebraMap R A (σ * ↑hτ.unit⁻¹)
      = algebraMap R A (↑hτ.unit⁻¹ : R) * (z * algebraMap R A τ - algebraMap R A σ) := by
    rw [map_mul]
    linear_combination (-z) * htτ
  rw [hid]
  exact J.mul_mem_left _ key

/-- **Nakayama.** A submodule of a finite module over a local ring which is everything modulo `𝔪`
is everything. -/
@[ega "III 7.6.11" "partial"]
private lemma eq_top_of_sup_smul_top {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M)
    (h : ∀ x : M, x ∈ N ⊔ (maximalIdeal R) • (⊤ : Submodule R M)) : N = ⊤ :=
  top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    ((IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge) (fun x _ => h x))

/-- If `A` is generated over `R` by an element `x` congruent to a scalar modulo `𝔪 A`, then every
element of `A` is congruent to a scalar modulo `𝔪 A`. -/
private lemma exists_sub_mem_map_maximalIdeal {A : Type*} [CommRing A] [Algebra R A] (x : A)
    (hgen : Function.Surjective (aeval x : R[X] →ₐ[R] A)) (b : R)
    (hx : x - algebraMap R A b ∈ Ideal.map (algebraMap R A) (maximalIdeal R)) (y : A) :
    ∃ r : R, y - algebraMap R A r ∈ Ideal.map (algebraMap R A) (maximalIdeal R) := by
  set J := Ideal.map (algebraMap R A) (maximalIdeal R)
  have hpow : ∀ k : ℕ, ∃ r : R, x ^ k - algebraMap R A r ∈ J := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ n ih =>
        obtain ⟨r, hr⟩ := ih
        refine ⟨b * r, ?_⟩
        rw [show x ^ (n + 1) - algebraMap R A (b * r)
            = (x - algebraMap R A b) * x ^ n + algebraMap R A b * (x ^ n - algebraMap R A r) by
          rw [map_mul]
          ring]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hr)
  obtain ⟨p, rfl⟩ := hgen y
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨r, hr⟩ := hp
      obtain ⟨s, hs⟩ := hq
      refine ⟨r + s, ?_⟩
      rw [show (aeval x) (p + q) - algebraMap R A (r + s)
          = ((aeval x) p - algebraMap R A r) + ((aeval x) q - algebraMap R A s) by
        rw [map_add, map_add]
        ring]
      exact Ideal.add_mem _ hr hs
  | monomial n r₀ =>
      obtain ⟨r, hr⟩ := hpow n
      refine ⟨r₀ * r, ?_⟩
      rw [show (aeval x) (Polynomial.monomial n r₀) - algebraMap R A (r₀ * r)
          = algebraMap R A r₀ * (x ^ n - algebraMap R A r) by
        simp only [Polynomial.aeval_monomial, map_mul]
        ring]
      exact Ideal.mul_mem_left _ _ hr

/-- **A finite free algebra of rank one is `R`.** Over a local ring, a nontrivial finite free
algebra all of whose elements are scalars modulo `𝔪` has bijective structure map. -/
private lemma bijective_algebraMap_of_free (A : Type*) [CommRing A] [Nontrivial A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A]
    (h : ∀ y : A, ∃ r : R, y - algebraMap R A r ∈ Ideal.map (algebraMap R A) (maximalIdeal R)) :
    Function.Bijective (algebraMap R A) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    let b := Module.Free.chooseBasis R A
    obtain ⟨i⟩ := (inferInstance : Nonempty (Module.Free.ChooseBasisIndex R A))
    have h1 : r • b i = 0 := by rw [Algebra.smul_def, hr, zero_mul]
    simpa [b] using congrArg (fun c => c i) (congrArg b.repr h1)
  · have key : LinearMap.range (Algebra.linearMap R A) = ⊤ := by
      refine eq_top_of_sup_smul_top R _ (fun y => ?_)
      obtain ⟨r, hr⟩ := h y
      have h1 : algebraMap R A r ∈ LinearMap.range (Algebra.linearMap R A) := ⟨r, rfl⟩
      have h2 : y - algebraMap R A r ∈ (maximalIdeal R) • (⊤ : Submodule R A) := by
        rwa [Ideal.smul_top_eq_map]
      simpa using Submodule.add_mem_sup h1 h2
    intro y
    obtain ⟨r, hr⟩ : y ∈ LinearMap.range (Algebra.linearMap R A) := key ▸ Submodule.mem_top
    exact ⟨r, hr⟩

/-- If `y` is a root of `f = (X - b) h + m` with all coefficients of `m` in `𝔪` and `h(y)`
invertible, then `y` is congruent to `b` modulo `𝔪 A`. -/
private lemma sub_mem_of_isUnit_aeval {A : Type*} [CommRing A] [Algebra R A] (f h : R[X]) (b : R)
    (y : A) (hm : ∀ n, (f - (X - C b) * h).coeff n ∈ maximalIdeal R) (hfy : aeval y f = 0)
    (hunit : IsUnit (aeval y h)) :
    y - algebraMap R A b ∈ Ideal.map (algebraMap R A) (maximalIdeal R) := by
  have hsplit : (y - algebraMap R A b) * aeval y h
      = aeval y f - aeval y (f - (X - C b) * h) := by
    rw [← map_sub, show f - (f - (X - C b) * h) = (X - C b) * h from by ring, map_mul, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C]
  have hmem : (y - algebraMap R A b) * aeval y h ∈
      Ideal.map (algebraMap R A) (maximalIdeal R) := by
    rw [hsplit, hfy, zero_sub]
    exact neg_mem (aeval_mem_map R y (maximalIdeal R) _ hm)
  have hrw : y - algebraMap R A b
      = ((y - algebraMap R A b) * aeval y h) * (↑hunit.unit⁻¹ : A) := by
    rw [mul_assoc, hunit.mul_val_inv, mul_one]
  rw [hrw]
  exact Ideal.mul_mem_right _ _ hmem

/-- **A finite algebra over a local ring has finitely many local factors.** If a module-finite
`R`-algebra `S` is a product of local rings `A i`, the index type is finite: the idempotents
`ε i = e⁻¹(δ i)` are not in `𝔪 S` — else `ε i S = 𝔪 (ε i S)` and Nakayama would make `ε i` vanish —
so their reductions are nonzero orthogonal idempotents of the finite `κ`-algebra `S/𝔪S`, hence
`κ`-linearly independent. -/
lemma finite_of_ringEquiv_pi_local (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R S] {ι : Type u} (A : ι → Type u) [∀ i, CommRing (A i)]
    [∀ i, IsLocalRing (A i)] (e : S ≃+* ∀ i, A i) : Finite ι := by
  classical
  let _ : DecidableEq ι := Classical.decEq ι
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  set J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R) with hJ
  set ε : ι → S := fun i => e.symm (Pi.single i 1) with hεdef
  have hεmul : ∀ i j, i ≠ j → ε i * ε j = 0 := by
    intro i j hij
    have h0 : (Pi.single i (1 : A i)) * (Pi.single j (1 : A j)) = 0 := by
      funext k
      rcases eq_or_ne k i with rfl | hk
      · simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne hk]
    rw [hεdef]
    simp only [← map_mul, h0, map_zero]
  have hεidem : ∀ i, ε i * ε i = ε i := by
    intro i
    have h0 : (Pi.single i (1 : A i)) * (Pi.single i (1 : A i)) = Pi.single i 1 := by
      funext k
      rcases eq_or_ne k i with rfl | hk
      · simp
      · simp [Pi.single_eq_of_ne hk]
    rw [hεdef]
    simp only [← map_mul, h0]
  have hεJ : ∀ i, ε i ∉ J := by
    intro i hmem
    set N : Submodule R S := (Ideal.span {ε i}).restrictScalars R with hN
    have hNmem : ∀ x : S, (∃ c, c * ε i = x) → x ∈ N := fun x hx =>
      Ideal.mem_span_singleton'.mpr hx
    have hNeq : N = Submodule.map (LinearMap.mulLeft R (ε i)) ⊤ := by
      ext x
      simp only [hN, Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
        Submodule.mem_map, Submodule.mem_top, LinearMap.mulLeft_apply, true_and]
      exact ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; ring⟩, fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; ring⟩⟩
    have hNfg : N.FG := by rw [hNeq]; exact Module.Finite.fg_top.map _
    have hmem' : ε i ∈ (maximalIdeal R) • (⊤ : Submodule R S) := by
      rw [Ideal.smul_top_eq_map]; exact hmem
    have hstep : N ≤ (maximalIdeal R) • N := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      have key : ∀ z ∈ (maximalIdeal R) • (⊤ : Submodule R S),
          (c * ε i) * z ∈ (maximalIdeal R) • N := by
        intro z hz
        refine Submodule.smul_induction_on hz (fun r hr t _ => ?_) (fun z w hz' hw' => ?_)
        · rw [mul_smul_comm]
          exact Submodule.smul_mem_smul hr (hNmem _ ⟨c * t, by ring⟩)
        · rw [mul_add]
          exact Submodule.add_mem _ hz' hw'
      have hxx : c * ε i = (c * ε i) * ε i := by rw [mul_assoc, hεidem]
      rw [hxx]
      exact key (ε i) hmem'
    have hNbot : N = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hNfg hstep
        ((IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
    have h0 : ε i = 0 := by
      have hmemN : ε i ∈ N := hNmem _ ⟨1, one_mul _⟩
      rw [hNbot] at hmemN
      simpa using hmemN
    have hpi : (Pi.single i (1 : A i)) = 0 := by
      have hc : e (e.symm (Pi.single i (1 : A i))) = e 0 := congrArg e h0
      rwa [e.apply_symm_apply, map_zero] at hc
    have h1 : (1 : A i) = 0 := by simpa using congrFun hpi i
    exact one_ne_zero h1
  have hfin : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := R) (B := S)
        (I := maximalIdeal R)).symm.toLinearEquiv
  have hli : LinearIndependent (R ⧸ maximalIdeal R) (fun i => Ideal.Quotient.mk J (ε i)) := by
    rw [linearIndependent_iff']
    intro t c hsum j hj
    have hterm : ∀ i ∈ t, i ≠ j →
        (c i • Ideal.Quotient.mk J (ε i)) * Ideal.Quotient.mk J (ε j) = 0 := by
      intro i _ hij
      rw [smul_mul_assoc, ← map_mul, hεmul i j hij, map_zero, smul_zero]
    have hmulsum := congrArg (fun z => z * Ideal.Quotient.mk J (ε j)) hsum
    simp only [Finset.sum_mul, zero_mul] at hmulsum
    rw [Finset.sum_eq_single_of_mem j hj hterm, smul_mul_assoc, ← map_mul, hεidem] at hmulsum
    have hne : Ideal.Quotient.mk J (ε j) ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hεJ j
    exact (smul_eq_zero.mp hmulsum).resolve_right hne
  exact hli.finite

/-- **The root produced by a factor of rank one.** Let `A` be a nontrivial finite free `R`-algebra
every element of which is a scalar modulo `𝔪 A`, and let `y ∈ A` be a root of `f` congruent to
`b ∈ R` modulo `𝔪 A`. Then `R → A` is an isomorphism and the preimage `a` of `y` satisfies
`f(a) = 0` and `ā = b̄`.

This is the common last step of the three implications 3 ⇒ 1, 9 ⇒ 1 and 13 ⇒ 1 of the source. -/
private lemma exists_isRoot_of_sub_mem (A : Type*) [CommRing A] [Nontrivial A] [Algebra R A]
    [Module.Finite R A] [Module.Free R A] (f : R[X]) (b : R) (y : A)
    (hmod : ∀ z : A, ∃ r : R, z - algebraMap R A r ∈ Ideal.map (algebraMap R A) (maximalIdeal R))
    (hfy : aeval y f = 0)
    (hyb : y - algebraMap R A b ∈ Ideal.map (algebraMap R A) (maximalIdeal R)) :
    ∃ a : R, f.IsRoot a ∧ residue R a = residue R b := by
  obtain ⟨hinj, hsurj⟩ := bijective_algebraMap_of_free R A hmod
  obtain ⟨a, ha⟩ := hsurj y
  have key : ∀ q : R[X], algebraMap R A (q.eval a) = aeval y q := by
    intro q
    rw [← ha, Polynomial.aeval_def, Polynomial.eval₂_at_apply]
  refine ⟨a, hinj ?_, ?_⟩
  · rw [map_zero, key f, hfy]
  · have hmem : algebraMap R A (a - b) ∈ Ideal.map (algebraMap R A) (maximalIdeal R) := by
      rw [map_sub, ha]; exact hyb
    have hcomap : a - b ∈ maximalIdeal R := by
      have hker : Ideal.comap (algebraMap R A) (⊥ : Ideal A) = ⊥ := by
        rw [← RingHom.ker_eq_comap_bot]
        exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
      have h0 : Ideal.comap (algebraMap R A) (Ideal.map (algebraMap R A) (maximalIdeal R))
          = maximalIdeal R := by
        rw [Ideal.comap_map_of_surjective _ hsurj, hker, sup_bot_eq]
      rw [← h0]
      exact hmem
    rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomap

/-- **The root produced by a lifted linear factor.** If a monic `f` factors as `f = g h` in `R[X]`
with `ḡ = X - a₀` and `ḡ`, `h̄` coprime, then `f` has a root `a ∈ R` with `ā = a₀`.

This is the module-theoretic heart of the equivalence, the source's proof of 3 ⇒ 1: the images
`γ`, `δ` of `g`, `h` in `S = R[X]/(f)` multiply to zero, and generate the unit ideal by Nakayama
because their reductions are coprime; so `e = u γ` is an idempotent and `S = S/(γ) × S/(δ)`. The
factor `A = S/(γ)` is therefore a direct summand of the finite free module `S`, hence finite free,
and every element of it is a scalar modulo `𝔪 A` because `ḡ` is linear; so `R → A` is an
isomorphism, and the preimage `a` of the image of `X` satisfies `f(a) = 0` and `g(a) = 0`, the
latter giving `ā = a₀`. -/
private lemma exists_isRoot_of_map_eq_X_sub_C (f g h : R[X]) (hf : f.Monic) (hfgh : f = g * h)
    (a₀ : ResidueField R) (hg : g.map (residue R) = X - C a₀)
    (hcop : IsCoprime (g.map (residue R)) (h.map (residue R))) :
    ∃ a : R, f.IsRoot a ∧ residue R a = a₀ := by
  classical
  have hSfin : Module.Finite R (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hf).basis
  have hSfree : Module.Free R (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  have hγδ : AdjoinRoot.mk f g * AdjoinRoot.mk f h = 0 := by
    rw [← map_mul, ← hfgh]; exact AdjoinRoot.mk_self
  -- Bézout modulo `𝔪` plus Nakayama: the images of `g` and `h` generate the unit ideal.
  obtain ⟨u, v, huv⟩ : ∃ u v : AdjoinRoot f,
      u * AdjoinRoot.mk f g + v * AdjoinRoot.mk f h = 1 := by
    obtain ⟨u₀, v₀, huv⟩ := hcop
    obtain ⟨u, hu⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective u₀
    obtain ⟨v, hv⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective v₀
    set w : R[X] := 1 - (u * g + v * h) with hw
    have hwm : w.map (residue R) = 0 := by
      simp only [hw, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_one, hu, hv, huv, sub_self]
    have hmk : AdjoinRoot.mk f w ∈
        Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) := by
      rw [← AdjoinRoot.aeval_eq]
      exact aeval_mem_map R _ _ _ (coeff_mem_maximalIdeal_of_map_eq_zero R hwm)
    have hspan : (Ideal.span {AdjoinRoot.mk f g, AdjoinRoot.mk f h} :
        Ideal (AdjoinRoot f)) = ⊤ := by
      rw [← Submodule.restrictScalars_eq_top_iff R]
      refine eq_top_of_sup_smul_top R _ (fun x => ?_)
      have h1 : x * (AdjoinRoot.mk f (u * g + v * h)) ∈
          (Ideal.span {AdjoinRoot.mk f g, AdjoinRoot.mk f h} : Ideal (AdjoinRoot f)) := by
        refine Ideal.mul_mem_left _ _ ?_
        rw [map_add, map_mul, map_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h2 : x * AdjoinRoot.mk f w ∈ (maximalIdeal R) • (⊤ : Submodule R (AdjoinRoot f)) := by
        rw [Ideal.smul_top_eq_map]
        exact Ideal.mul_mem_left _ _ hmk
      have hx : x = x * (AdjoinRoot.mk f (u * g + v * h)) + x * AdjoinRoot.mk f w := by
        rw [← mul_add, ← map_add, hw]
        simp
      rw [hx]
      exact Submodule.add_mem_sup h1 h2
    exact Ideal.mem_span_pair.mp (hspan ▸ Submodule.mem_top)
  -- the factor `A = R[X]/(f, g)`
  set I : Ideal (AdjoinRoot f) := Ideal.span {AdjoinRoot.mk f g} with hI
  have : Module.Finite R (AdjoinRoot f ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Projective R (AdjoinRoot f ⧸ I) :=
    projective_of_algEquiv_prod R
      (nonempty_algEquiv_quotient_prod R (AdjoinRoot.mk f g) (AdjoinRoot.mk f h) u v hγδ huv).some
  have : Module.Free R (AdjoinRoot f ⧸ I) := Module.free_of_flat_of_isLocalRing
  set x : AdjoinRoot f ⧸ I := Ideal.Quotient.mk I (AdjoinRoot.root f) with hxdef
  have haeval : ∀ p : R[X], aeval x p = Ideal.Quotient.mk I (AdjoinRoot.mk f p) := fun p => by
    have h1 : (Ideal.Quotient.mkₐ R I) (AdjoinRoot.root f) = x := rfl
    rw [← h1, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, Ideal.Quotient.mkₐ_eq_mk]
  have hgen : Function.Surjective (aeval x : R[X] →ₐ[R] (AdjoinRoot f ⧸ I)) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective s
    exact ⟨p, haeval p⟩
  have hgx : aeval x g = 0 := by
    rw [haeval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hfx : aeval x f = 0 := by rw [haeval, AdjoinRoot.mk_self, map_zero]
  -- the image of `X` is a scalar modulo `𝔪 A`, because `ḡ` is linear
  obtain ⟨b, hb⟩ : ∃ b : R, residue R b = a₀ := Ideal.Quotient.mk_surjective a₀
  have hwc : ∀ n, (g - (X - C b)).coeff n ∈ maximalIdeal R := by
    refine coeff_mem_maximalIdeal_of_map_eq_zero R ?_
    rw [Polynomial.map_sub, hg, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hb,
      sub_self]
  have hxb : x - algebraMap R (AdjoinRoot f ⧸ I) b ∈
      Ideal.map (algebraMap R (AdjoinRoot f ⧸ I)) (maximalIdeal R) := by
    have h2 := aeval_mem_map R x (maximalIdeal R) (g - (X - C b)) hwc
    have h3 : x - algebraMap R (AdjoinRoot f ⧸ I) b = -(aeval x (g - (X - C b))) := by
      rw [map_sub, hgx, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      ring
    rw [h3]
    exact neg_mem h2
  -- `A` is not the zero ring: it has a `κ`-point, namely `a₀`
  have hfa₀ : Polynomial.eval₂ (residue R) a₀ f = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, hfgh, Polynomial.map_mul, hg]
    simp
  have : Nontrivial (AdjoinRoot f ⧸ I) := by
    have hθγ : (AdjoinRoot.lift (residue R) a₀ hfa₀) (AdjoinRoot.mk f g) = 0 := by
      rw [AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map, hg]
      simp
    refine RingHom.domain_nontrivial (Ideal.Quotient.lift I (AdjoinRoot.lift (residue R) a₀ hfa₀)
      (fun a ha => ?_))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hθγ, mul_zero]
  -- so `R → A` is an isomorphism, and the preimage of the image of `X` is the root
  obtain ⟨a, haf, hares⟩ := exists_isRoot_of_sub_mem R (AdjoinRoot f ⧸ I) f b x
    (exists_sub_mem_map_maximalIdeal R x hgen b hxb) hfx hxb
  exact ⟨a, haf, by rw [hares, hb]⟩

/-! ### The remaining implications -/

/-- 1 ⇒ 8. By Proposition 00UE the étale algebra `S` becomes standard étale after inverting some
`g ∉ q`, so one may assume `S = R[t]_g/(f)` with `f` monic and `f'` invertible. The prime `q`,
having residue field `κ`, is a root `a₀` of `f̄` which is not a root of `ḡ`, and `f̄'(a₀) ≠ 0`.
Henselianness lifts `a₀` to a root `a ∈ R` of `f`; then `g(a)` is a unit and `t ↦ a` is a
retraction with `τ⁻¹(𝔪) = q`. Uniqueness is Lemma 06RR. This is exactly
`henselian_etale_retraction` together with `henselian_etale_retraction_unique`; the residue
hypothesis is the same one, since `Ideal.ResidueField.mapₐ` and `Ideal.ResidueField.map` have the
same underlying function. -/
private theorem item1_imp_item8 : Item1 R → Item8 R := by
  intro h1 S _ _ hE q _ _ hb
  have := h1
  have := hE
  have hlo : q.comap (algebraMap R S) = maximalIdeal R := (q.over_def (maximalIdeal R)).symm
  have hres : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R S) hlo.symm) := hb
  obtain ⟨τ, hτ⟩ := henselian_etale_retraction R S q hlo hres
  exact ⟨τ, hτ, fun τ' hτ' => henselian_etale_retraction_unique R S q hlo hres τ' τ hτ' hτ⟩

/-- 7 ⇒ 1. Let `f ∈ R[T]` be monic and `a₀ ∈ κ` a simple root of `f̄`. Dividing, `f̄ = (T - a₀)h₀`
with `h₀(a₀) = f̄'(a₀) ≠ 0`; let `h ∈ R[T]` lift `h₀`. Then `P = (f, f' h)` is a
`StandardEtalePair R`, its side condition `f' p₁ + f p₂ = (f' h)^n` holding with `n = 1`,
`p₁ = h` and `p₂ = 0`, so `S = P.Ring = R[T][Y]/(f, Y f' h - 1)` carries Mathlib's
`Algebra.Etale R P.Ring`. Inverting `h` as well as `f'` is what makes `a₀` the *only* point of the
closed fibre, and this is what lets the *unpinned* retraction of (7) be used in place of the pinned
one of (8): `θ = P.lift a₀ : S →ₐ[R] κ` exists because `f̄(a₀) = 0` and `(f̄' h₀)(a₀) ≠ 0`, and it
is surjective because `θ ∘ algebraMap R S = residue R` is, so `q = ker θ` is a maximal ideal lying
over `𝔪` with `κ = κ(q)` — bijectivity of `Ideal.ResidueField.map` here is surjectivity, its source
being a field, and surjectivity follows from `Ideal.algebraMap_residueField_surjective` for the
maximal `q` together with `θ`'s surjectivity. Applying (7) to `S` and `q` gives `τ : S →ₐ[R] R`.
Put `a := τ P.X`; then `P.HasMap a` by `StandardEtalePair.HasMap.map`, that is `f(a) = 0` and
`(f' h)(a)` is a unit, so `h₀(ā) ≠ 0`; since `0 = f̄(ā) = (ā - a₀)h₀(ā)` this forces `ā = a₀`.

(The source instead proves the "really unimportant" 7 ⇒ 8 by the same localisation trick and then
8 ⇒ 2; the argument above is that composite, with the non-monic polynomials of (2) traded for the
monic ones of (1), which is all the étale side of the equivalence needs — 1 ⇒ 2 below is
elementary.) -/
private theorem item7_imp_item1 : Item7 R → Item1 R := by
  intro H
  refine ((HenselianLocalRing.TFAE R).out 2 1).mp ?_
  intro f hfm a₀ h₁ h₂
  obtain ⟨h, hfac, -, hha₀⟩ := exists_lift_divByMonic R f a₀ h₁ h₂
  set P : StandardEtalePair R := ⟨f, hfm, derivative f * h, ⟨h, 0, 1, by ring⟩⟩
  have hPf : P.f = f := rfl
  have hPg : P.g = derivative f * h := rfl
  have hmapa₀ : P.HasMap a₀ := by
    refine ⟨h₁, ?_⟩
    rw [hPg, map_mul]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero h₂ ?_)
    rw [aeval_eq_eval_map, hha₀]
    exact h₂
  set S := P.Ring
  let θ : S →ₐ[R] ResidueField R := P.lift a₀ hmapa₀
  have hθalg : ∀ r : R, θ (algebraMap R S r) = residue R r := fun r => by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact θ.commutes r
  have hθsurj : Function.Surjective θ := fun y => by
    obtain ⟨r, hr⟩ : ∃ r : R, residue R r = y := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap R S r, by rwa [hθalg]⟩
  set q : Ideal S := RingHom.ker (θ : S →+* ResidueField R) with hqdef
  have hqmax : q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hθsurj
  have hqp : q.IsPrime := hqmax.isPrime
  have hlo : q.comap (algebraMap R S) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, hqdef, RingHom.mem_ker, RingHom.coe_coe, hθalg r]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hover : q.LiesOver (maximalIdeal R) := ⟨hlo.symm⟩
  have hbij : Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R S) hlo.symm) := by
    refine ⟨RingHom.injective _, fun x => ?_⟩
    obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective q x
    obtain ⟨r, hr⟩ : ∃ r : R, residue R r = θ s := Ideal.Quotient.mk_surjective (θ s)
    refine ⟨algebraMap R _ r, ?_⟩
    rw [Ideal.ResidueField.map_algebraMap, ← hs]
    have hmem : s - algebraMap R S r ∈ q := by
      change θ (s - algebraMap R S r) = 0
      rw [map_sub, hθalg r, hr, sub_self]
    have h0 := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨τ⟩ := H S inferInstance q hbij
  have hax : P.HasMap (τ P.X) := StandardEtalePair.hasMap_X.map τ
  set a := τ P.X
  have haf : f.eval a = 0 := by
    simpa [hPf, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hax.1
  refine ⟨a, haf, ?_⟩
  have hune : (h.map (residue R)).eval (residue R a) ≠ 0 := by
    have hu := hax.2
    rw [hPg] at hu
    have hu' : IsUnit ((derivative f * h).eval a) := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hu
    have hz := (hu'.map (residue R)).ne_zero
    rw [← eval_map_residue] at hz
    simp only [Polynomial.map_mul, Polynomial.eval_mul] at hz
    exact fun h0 => hz (by rw [h0, mul_zero])
  have hroot : ((X - C a₀) * h.map (residue R)).eval (residue R a) = 0 := by
    rw [← hfac, eval_map_residue, haf, map_zero]
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hroot
  exact sub_eq_zero.mp ((mul_eq_zero.mp hroot).resolve_right hune)

end Stacks.Henselian.Characterizations
