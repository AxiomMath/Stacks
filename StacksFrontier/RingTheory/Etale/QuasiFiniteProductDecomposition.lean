module

public import Mathlib.RingTheory.Etale.QuasiFinite
import StacksCore.Tactic.StacksAttribute

/-!
# Étale localization of a quasi-finite algebra: the product decomposition

Let `R → S` be of finite type and quasi-finite at the prime `q` of `S` lying over the prime `p`
of `R`. Then there are an étale ring map `R → R'`, a prime `p'` of `R'` over `p` and a product
decomposition `R' ⊗_R S = A × B` with
1. `κ(p) = κ(p')`,
2. `R' → A` finite,
3. `A` has exactly one prime `r` lying over `p'`,
4. `r` lies over `q`, and
5. `B` has no prime lying over both `q` and `p'`.

## Main results

* `Ideal.eq_of_liesOver_of_comap_includeRight_eq`: if `κ(p) → κ(p')` is bijective, there is at
  most one prime of `R' ⊗[R] S` lying over both `p'` and a given prime `q` of `S`.
* `Algebra.exists_etale_isIdempotentElem_quasiFiniteAt_five_properties`: Stacks 00UJ with all
  five properties.

## Implementation notes

As in Mathlib's `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, which provides
(1)–(4), the decomposition `R' ⊗_R S = A × B` is given by an idempotent `e` of `R' ⊗_R S`, with
`A = (R' ⊗_R S)[1/e]` and `B = (R' ⊗_R S)[1/(1 - e)]`. The primes of `A` are the primes of
`R' ⊗_R S` not containing `e`, which is how (3) and (4) are stated; (5) is stated for primes of
`B` itself. Property (5) follows from (1): since `κ(p) = κ(p')`, only one prime of `R' ⊗_R S`
lies over both `p'` and `q`, and that prime lies in `A`.

## References

* [Stacks Project, Tag 00UJ](https://stacks.math.columbia.edu/tag/00UJ)
-/

@[expose] public section

universe u v

open TensorProduct

/-- If `κ(p) → κ(P)` is surjective, every element of `R'` is, up to a factor from `R` outside `p`,
congruent modulo `P` to an element of `R`. -/
private lemma Ideal.exists_algebraMap_mul_sub_algebraMap_mem_of_surjective
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] (p : Ideal R) [p.IsPrime]
    (P : Ideal R') [P.IsPrime] [P.LiesOver p]
    (hP : Function.Surjective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)))
    (a : R') : ∃ t ∉ p, ∃ r : R, algebraMap R R' t * a - algebraMap R R' r ∈ P := by
  obtain ⟨w, hw⟩ := hP (algebraMap R' P.ResidueField a)
  obtain ⟨⟨r, ⟨t, ht⟩⟩, hrt⟩ := IsLocalization.surj (nonZeroDivisors (R ⧸ p)) w
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  have htp : t ∉ p := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem] at ht
    exact ht
  refine ⟨t, htp, r, ?_⟩
  simp only [Ideal.algebraMap_quotient_residueField_mk] at hrt
  have := congr(Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p) $hrt)
  rw [map_mul, hw, AlgHom.commutes, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R R' P.ResidueField,
    IsScalarTower.algebraMap_apply R R' P.ResidueField, ← map_mul, ← sub_eq_zero, ← map_sub,
    Ideal.algebraMap_residueField_eq_zero] at this
  rwa [mul_comm]

/-- If `κ(p) → κ(P)` is bijective (surjective suffices), at most one prime of `R' ⊗[R] S` lies
over both `P` and a given prime `q` of `S`. -/
lemma Ideal.eq_of_liesOver_of_comap_includeRight_eq
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal R') [P.IsPrime] [P.LiesOver p]
    (hP : Function.Surjective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)))
    (Q₁ Q₂ : Ideal (R' ⊗[R] S)) [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver P] [Q₂.LiesOver P]
    (h : Q₁.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom =
      Q₂.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) :
    Q₁ = Q₂ := by
  set I : Ideal (R' ⊗[R] S) := P.map (algebraMap R' (R' ⊗[R] S))
  -- every `x` is, up to a unit factor from `R \ p`, congruent modulo `P` to some `1 ⊗ y`
  have key : ∀ x : R' ⊗[R] S, ∃ t ∉ p, ∃ y : S,
      algebraMap R (R' ⊗[R] S) t * x - (1 ⊗ₜ y) ∈ I := by
    intro x
    induction x with
    | tmul a s =>
      obtain ⟨t, ht, r, hr⟩ := Ideal.exists_algebraMap_mul_sub_algebraMap_mem_of_surjective p P hP a
      refine ⟨t, ht, algebraMap R S r * s, ?_⟩
      have : algebraMap R (R' ⊗[R] S) t * (a ⊗ₜ s) - (1 ⊗ₜ (algebraMap R S r * s)) =
          algebraMap R' (R' ⊗[R] S) (algebraMap R R' t * a - algebraMap R R' r) * (1 ⊗ₜ s) := by
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, mul_one, map_sub, sub_mul]
        rw [Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, ← Algebra.smul_def r s,
          ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one r]
      rw [this]
      exact I.mul_mem_right _ (Ideal.mem_map_of_mem _ hr)
    | add x₁ x₂ h₁ h₂ =>
      obtain ⟨t₁, ht₁, y₁, hy₁⟩ := h₁
      obtain ⟨t₂, ht₂, y₂, hy₂⟩ := h₂
      refine ⟨t₁ * t₂, fun h ↦ (‹p.IsPrime›.mem_or_mem h).elim ht₁ ht₂,
        algebraMap R S t₂ * y₁ + algebraMap R S t₁ * y₂, ?_⟩
      have : algebraMap R (R' ⊗[R] S) (t₁ * t₂) * (x₁ + x₂) -
          (1 ⊗ₜ (algebraMap R S t₂ * y₁ + algebraMap R S t₁ * y₂)) =
          algebraMap R (R' ⊗[R] S) t₂ * (algebraMap R (R' ⊗[R] S) t₁ * x₁ - (1 ⊗ₜ y₁)) +
          algebraMap R (R' ⊗[R] S) t₁ * (algebraMap R (R' ⊗[R] S) t₂ * x₂ - (1 ⊗ₜ y₂)) := by
        have h1 : ∀ (c : R) (y : S), (1 ⊗ₜ (algebraMap R S c * y) : R' ⊗[R] S) =
            algebraMap R (R' ⊗[R] S) c * (1 ⊗ₜ y) := by
          intro c y
          rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.tmul_smul]
        rw [TensorProduct.tmul_add, h1, h1, map_mul]
        ring
      rw [this]
      exact I.add_mem (I.mul_mem_left _ hy₁) (I.mul_mem_left _ hy₂)
  -- membership in a prime over `P` is decided by the `S`-component
  have mem_iff : ∀ (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime] [Q.LiesOver P] (x : R' ⊗[R] S) (t : R)
      (_ : t ∉ p) (y : S) (_ : algebraMap R (R' ⊗[R] S) t * x - (1 ⊗ₜ y) ∈ I),
      x ∈ Q ↔ y ∈ Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom := by
    intro Q _ _ x t ht y hxy
    have hIQ : I ≤ Q := by
      rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Q.over_def P]
    have htQ : algebraMap R (R' ⊗[R] S) t ∉ Q := by
      rw [IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]
      intro h
      apply ht
      rw [P.over_def p, Q.over_def P]
      exact h
    have hd := hIQ hxy
    rw [Ideal.mem_comap]
    change x ∈ Q ↔ (1 ⊗ₜ y : R' ⊗[R] S) ∈ Q
    constructor
    · intro hx
      have := Q.sub_mem (Q.mul_mem_left (algebraMap R (R' ⊗[R] S) t) hx) hd
      simpa using this
    · intro hy
      have := Q.add_mem hd hy
      simp only [sub_add_cancel] at this
      exact (‹Q.IsPrime›.mem_or_mem this).resolve_left htQ
  ext x
  obtain ⟨t, ht, y, hxy⟩ := key x
  rw [mem_iff Q₁ x t ht y hxy, mem_iff Q₂ x t ht y hxy, h]

/-- **Stacks 00UJ.** Let `S` be a finite type `R`-algebra and `q` a prime of `S` lying over the
prime `p` of `R` such that `S` is quasi-finite at `q`. There are an étale `R`-algebra `R'`, a prime
`p'` of `R'` lying over `p` and an idempotent `e` of `R' ⊗[R] S` — the product decomposition
`R' ⊗[R] S = A × B` with `A = (R' ⊗[R] S)[1/e]` and `B = (R' ⊗[R] S)[1/(1 - e)]` — such that
1. `κ(p) → κ(p')` is bijective,
2. `A` is finite over `R'`,
3. there is exactly one prime `r` of `A` (a prime of `R' ⊗[R] S` not containing `e`) lying over
   `p'`,
4. `r` lies over `q`, and
5. no prime of `B` lies over both `p'` and `q`. -/
@[stacks 00UJ "The decomposition `R' ⊗_R S = A × B` is given by an idempotent `e`, with
`A = (R' ⊗[R] S)[1/e]` and `B = (R' ⊗[R] S)[1/(1 - e)]`; the primes of `A` in (3) and (4) are
the primes of `R' ⊗[R] S` not containing `e`. Properties (1)–(4) are Mathlib's
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`; (5) is the last conjunct."]
theorem Algebra.exists_etale_isIdempotentElem_quasiFiniteAt_five_properties
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      e ∉ P' ∧
      (∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') ∧
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
      ¬ ∃ Q : Ideal (Localization.Away (1 - e)), Q.IsPrime ∧ Q.LiesOver P ∧
        Q.comap ((algebraMap (R' ⊗[R] S) (Localization.Away (1 - e))).comp
          Algebra.TensorProduct.includeRight.toRingHom) = q := by
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hbij, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance, e, he,
    P', inferInstance, inferInstance, hbij, hfin, heP', huniq, hP'q, ?_⟩
  rintro ⟨Q, hQ, hQP, hQq⟩
  set Q₀ := Q.comap (algebraMap (R' ⊗[R] S) (Localization.Away (1 - e)))
  have : Q₀.IsPrime := Ideal.comap_isPrime _ Q
  have : Q₀.LiesOver P := ⟨by
    rw [Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, Q.over_def P]⟩
  have hQ₀ : Q₀ = P' := Ideal.eq_of_liesOver_of_comap_includeRight_eq p P hbij.2 Q₀ P' (by
    rw [Ideal.comap_comap, hQq, hP'q])
  -- `1 - e` is a unit in `B`, so `1 - e ∉ Q₀`; as `e (1 - e) = 0`, `e ∈ Q₀ = P'`
  have h1e : 1 - e ∉ Q₀ := fun h ↦ hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (IsLocalization.Away.algebraMap_isUnit (1 - e)))
  have hzero : e * (1 - e) ∈ Q₀ := by
    rw [mul_sub, mul_one, he.eq, sub_self]
    exact Q₀.zero_mem
  exact heP' (hQ₀ ▸ ((‹Q₀.IsPrime›).mem_or_mem hzero).resolve_right h1e)
