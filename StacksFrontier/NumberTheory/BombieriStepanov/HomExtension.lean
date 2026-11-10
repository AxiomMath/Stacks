module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Homomorphisms into a field, along an integral extension

Three facts about ring homomorphisms `S → Ω` into a field, used to count points of curves over
finite fields as homomorphisms of their coordinate rings.

* **Transitivity.** If a finite group `G` acts on `S` with invariants `R`, any two `R`-algebra
  homomorphisms `φ, φ' : S → Ω` with finite residue ring `S / ker φ` differ by an element of `G`:
  `φ' = φ ∘ g`. The kernels lie over the same prime of `R`, so `G` moves one to the other; the
  two embeddings of the finite field `S / ker φ` into `Ω` have the same image, hence differ by an
  automorphism, which the stabilizer of the kernel realizes
  (`Ideal.Quotient.stabilizerHom_surjective`).
* **Extension.** A homomorphism `R → Ω` with maximal kernel into an algebraically closed field
  extends along an injective integral extension `R → S`: lift the kernel to a maximal ideal of
  `S` and embed the algebraic residue field extension into `Ω`.
* **Frobenius-fixed points.** An algebraically closed field of characteristic `p` has exactly
  `p ^ n` elements with `a ^ (p ^ n) = a`.

## Main results

* `Stacks.BombieriStepanov.exists_smul_eq_of_algHom`
* `Stacks.BombieriStepanov.exists_comp_algebraMap_eq`
* `Stacks.BombieriStepanov.ncard_setOf_pow_eq_self`
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.BombieriStepanov

section Roots

/-- In a field, at most `n` elements satisfy `a ^ n = a`, for `n ≥ 2`. -/
theorem setOf_pow_eq_self_finite_ncard_le {Ω : Type*} [Field Ω] {n : ℕ} (hn : 1 < n) :
    {a : Ω | a ^ n = a}.Finite ∧ {a : Ω | a ^ n = a}.ncard ≤ n := by
  classical
  have h0 : (X ^ n - X : Ω[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hn
  have hset : {a : Ω | a ^ n = a} = ((X ^ n - X : Ω[X]).roots.toFinset : Set Ω) := by
    ext a
    simp [Multiset.mem_toFinset, mem_roots h0, sub_eq_zero]
  rw [hset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq Ω hn]

/-- **Frobenius-fixed points of an algebraically closed field.** In an algebraically closed
field of characteristic `p`, exactly `p ^ n` elements satisfy `a ^ (p ^ n) = a`, for `n ≠ 0`. -/
theorem ncard_setOf_pow_eq_self {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
    [CharP Ω p] {n : ℕ} (hn : n ≠ 0) : {a : Ω | a ^ (p ^ n) = a}.ncard = p ^ n := by
  classical
  have hp : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  have hsep : (X ^ (p ^ n) - X : Ω[X]).Separable :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have hsplit : Splits ((X ^ (p ^ n) - X : Ω[X]).map (algebraMap Ω Ω)) :=
    IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree hsep hsplit
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq Ω hp] at hcard
  have hset : {a : Ω | a ^ (p ^ n) = a} = (X ^ (p ^ n) - X : Ω[X]).rootSet Ω := by
    ext a
    rw [mem_rootSet_of_ne hsep.ne_zero]
    simp [sub_eq_zero]
  rw [hset, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  convert hcard

/-- A ring homomorphism from a finite field `K` into a field has image the set of solutions of
`a ^ #K = a`. -/
theorem range_eq_setOf_pow_card_eq_self {K Ω : Type*} [Field K] [Fintype K] [Field Ω]
    (e : K →+* Ω) : Set.range e = {a : Ω | a ^ Fintype.card K = a} := by
  obtain ⟨hfin, hle⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) (Fintype.one_lt_card (α := K))
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
  · rintro _ ⟨z, rfl⟩
    simp only [Set.mem_ofPred_eq, ← map_pow, FiniteField.pow_card]
  · rwa [Set.ncard_range_of_injective e.injective, Nat.card_eq_fintype_card]

/-- Two embeddings of a finite field into a field differ by an automorphism. -/
theorem exists_ringEquiv_comp_eq {K Ω : Type*} [Field K] [Finite K] [Field Ω]
    (f f' : K →+* Ω) : ∃ σ : K ≃+* K, ∀ z, f (σ z) = f' z := by
  have := Fintype.ofFinite K
  have hrange : Set.range f = Set.range f' := by
    rw [range_eq_setOf_pow_card_eq_self f, range_eq_setOf_pow_card_eq_self f']
  choose e he using fun z => (Set.ext_iff.1 hrange (f' z)).2 ⟨z, rfl⟩
  have he_inj : Function.Injective e := fun z₁ z₂ h => f'.injective (by rw [← he, ← he, h])
  have he_surj : Function.Surjective e := fun z => by
    obtain ⟨z', hz'⟩ : f z ∈ Set.range f' :=
      (Set.ext_iff.1 hrange _).1 ⟨z, rfl⟩
    exact ⟨z', f.injective (by rw [he, hz'])⟩
  let eH : K →+* K :=
    { toFun := e
      map_one' := f.injective (by rw [he, map_one, map_one])
      map_mul' := fun a b => f.injective (by rw [he, map_mul, map_mul, he, he])
      map_zero' := f.injective (by rw [he, map_zero, map_zero])
      map_add' := fun a b => f.injective (by rw [he, map_add, map_add, he, he]) }
  exact ⟨RingEquiv.ofBijective eH ⟨he_inj, he_surj⟩, he⟩

end Roots

section Transitivity

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S] [Algebra R Ω]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsInvariant R S G]

/-- **Homomorphisms into a field differ by the Galois group.** Let a finite group `G` act on `S`
with invariants `R`, and let `φ, φ' : S → Ω` be `R`-algebra homomorphisms into a field with
`S / ker φ` finite. Then `φ' = φ ∘ g` for some `g ∈ G`. -/
theorem exists_smul_eq_of_algHom (φ φ' : S →ₐ[R] Ω) [Finite (S ⧸ RingHom.ker φ)] :
    ∃ g : G, ∀ s, φ' s = φ (g • s) := by
  classical
  set Q := RingHom.ker φ
  set Q' := RingHom.ker φ' with hQ'
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q'.IsPrime := RingHom.ker_isPrime _
  have hunder : Q.under R = Q'.under R := by
    ext r
    simp [Q, Q', Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q Q' hunder
  -- `ψ = φ' ∘ g` has the same kernel as `φ`
  set ψ : S →+* Ω := (φ' : S →+* Ω).comp (MulSemiringAction.toRingHom G S g) with hψ
  have hkerψ : ∀ s, ψ s = 0 ↔ s ∈ Q := by
    intro s
    change φ' (g • s) = 0 ↔ s ∈ Q
    rw [← RingHom.mem_ker, ← hQ', hg, Ideal.smul_mem_pointwise_smul_iff]
  have : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField Q (Finite.isField_of_domain (S ⧸ Q))
  let : Field (S ⧸ Q) := Ideal.Quotient.field Q
  set f : S ⧸ Q →+* Ω := Ideal.Quotient.lift Q (φ : S →+* Ω) (fun s hs => hs)
  set f' : S ⧸ Q →+* Ω := Ideal.Quotient.lift Q ψ (fun s hs => (hkerψ s).2 hs)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_comp_eq f f'
  set P := Q.under R
  let eR : (S ⧸ Q) ≃ₐ[R ⧸ P] (S ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := σ) (fun r => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        refine f.injective ?_
        rw [hσ]
        change ψ (algebraMap R S r) = φ (algebraMap R S r)
        rw [hψ, RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]
        simp)
  obtain ⟨τ, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q eR
  refine ⟨τ * g⁻¹, fun s => ?_⟩
  have key : ∀ t, ψ t = φ ((τ : G) • t) := by
    intro t
    have h1 : f' (Ideal.Quotient.mk Q t) = f (σ (Ideal.Quotient.mk Q t)) := (hσ _).symm
    have h2 : σ (Ideal.Quotient.mk Q t) = Ideal.Quotient.mk Q ((τ : G) • t) := by
      have := congrArg (fun a : (S ⧸ Q) ≃ₐ[R ⧸ P] (S ⧸ Q) => a (Ideal.Quotient.mk Q t)) hτ
      exact this.symm
    rw [h2] at h1
    exact (Ideal.Quotient.lift_mk _ _ _).symm.trans (h1.trans (Ideal.Quotient.lift_mk _ _ _))
  have := key (g⁻¹ • s)
  rw [hψ, RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_inv_smul] at this
  rwa [mul_smul]

end Transitivity

section Extension

/-- **Extending a homomorphism along an integral extension.** Let `R → S` be injective and
integral and let `ψ : R → Ω` be a homomorphism with maximal kernel into an algebraically closed
field. Then `ψ = φ ∘ (R → S)` for some homomorphism `φ : S → Ω`. -/
theorem exists_comp_algebraMap_eq {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω]
    [IsAlgClosed Ω] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* Ω) [(RingHom.ker ψ).IsMaximal] :
    ∃ φ : S →+* Ω, φ.comp (algebraMap R S) = ψ := by
  set P := RingHom.ker ψ
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P
    (((RingHom.injective_iff_ker_eq_bot _).1 hinj).trans_le bot_le)
  have := hQmax
  have : Q.LiesOver P := ⟨hQ.symm⟩
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let : Field (S ⧸ Q) := Ideal.Quotient.field Q
  let : Algebra (R ⧸ P) Ω := (Ideal.Quotient.lift P ψ (fun r hr => hr)).toAlgebra
  have : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (S ⧸ Q) →ₐ[R ⧸ P] Ω := IsAlgClosed.lift
  refine ⟨(l : S ⧸ Q →+* Ω).comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (l.commutes (Ideal.Quotient.mk P r)).trans (Ideal.Quotient.lift_mk _ _ _)

end Extension

end Stacks.BombieriStepanov

end
