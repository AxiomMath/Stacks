module

public import StacksFrontier.RingTheory.Henselian.Pair.Criteria.Characterizations

@[expose] public section

/-!
# Gabber's criterion: lifting the decomposition of the integral closure

Let `(A, I)` satisfy Gabber's criterion: `I` lies in the Jacobson radical of `A` and every
polynomial `X ^ n (X - 1) + ∑ aᵢ X ^ i` with `aᵢ ∈ I` and `n ≥ 1` has a root in `1 + I`. If `B'` is
the integral closure of `A` in an `A`-algebra `A'`, then every decomposition
`B' ⧸ IB' ≅ A ⧸ I × C'` lifts to a decomposition `B' ≅ B'₁ × B'₂` of `A`-algebras, with
`B'₁ ⧸ IB'₁ ≅ A ⧸ I` and `B'₂ ⧸ IB'₂ ≅ C'` compatibly with the given one.

## Main results

* `gabber_root_eq_of_isRoot`: the root in `1 + I` of Gabber's polynomial is unique.
* `exists_integralClosure_algEquiv_prod_lift_of_gabber_root_condition`: the lifted decomposition
  of the integral closure.

## References

* [Stacks: Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
* [Stacks: Tag 0EM4](https://stacks.math.columbia.edu/tag/0EM4)
-/

open Polynomial

universe u v w x

section

/-- If `I` lies in the Jacobson radical of `A`, a polynomial
`X ^ n (X - 1) + ∑ aᵢ X ^ i` with `aᵢ ∈ I` has at most one root in `1 + I`. -/
theorem gabber_root_eq_of_isRoot
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : A[X]) (n : ℕ) (a : Fin (n + 1) → I)
    (hform : f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ))
    {α β : A} (hα : α - 1 ∈ I) (hfα : f.IsRoot α) (hβ : β - 1 ∈ I) (hfβ : f.IsRoot β) :
    β = α := by
  have hmap : f.map (Ideal.Quotient.mk I) = (X - 1) * X ^ n := by
    rw [mul_comm]
    simp [hform, Polynomial.map_sum, (Ideal.Quotient.eq_zero_iff_mem).mpr (a _).property]
  obtain ⟨g, hg⟩ := (dvd_iff_isRoot).mpr hfα
  have hαq : Ideal.Quotient.mk I α = 1 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem α 1).mpr hα
  have hβq : Ideal.Quotient.mk I β = 1 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem β 1).mpr hβ
  have hmapg : g.map (Ideal.Quotient.mk I) = X ^ n := by
    have hm := congrArg (Polynomial.map (Ideal.Quotient.mk I)) hg
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, hαq, hmap, C_1] at hm
    have hd := congrArg (fun p : (A ⧸ I)[X] ↦ p /ₘ (X - 1)) hm
    have hmonic : (X - 1 : (A ⧸ I)[X]).Monic := by
      simpa using monic_X_sub_C (1 : A ⧸ I)
    rw [mul_divByMonic_cancel_left _ hmonic, mul_divByMonic_cancel_left _ hmonic] at hd
    exact hd.symm
  have hgeval : Ideal.Quotient.mk I (g.eval β) = 1 := by
    rw [← eval₂_at_apply, ← eval_map, hmapg]
    simp [hβq]
  have hgunit : IsUnit (g.eval β) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (hI (by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [hgeval]))
  have hzero : (β - α) * g.eval β = 0 := by
    have h := hfβ
    rw [IsRoot, hg, eval_mul, eval_sub, eval_X, eval_C] at h
    exact h
  exact sub_eq_zero.mp (hgunit.mul_left_eq_zero.mp hzero)

/-- An idempotent `u` of an `A`-algebra `R` whose image under a surjection
`π : R → P × Q` with kernel `IR` is `(1, 0)` splits `R` as a product of `A`-algebras whose
reductions modulo `I` are `P` and `Q`, compatibly with `π`. -/
private lemma exists_algEquiv_prod_lift_of_isIdempotentElem
    {A : Type u} [CommRing A] (I : Ideal A) {R : Type v} [CommRing R] [Algebra A R]
    {P : Type w} {Q : Type x} [CommRing P] [CommRing Q] (π : R →+* P × Q)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = I.map (algebraMap A R))
    {u : R} (hu : IsIdempotentElem u) (hπu : π u = (1, 0)) :
    ∃ (R₁ R₂ : Type v) (_ : CommRing R₁) (_ : CommRing R₂) (_ : Algebra A R₁)
      (_ : Algebra A R₂) (E : R ≃ₐ[A] R₁ × R₂) (ρ₁ : R₁ →+* P) (ρ₂ : R₂ →+* Q),
      Function.Surjective ρ₁ ∧ RingHom.ker ρ₁ = I.map (algebraMap A R₁) ∧
      Function.Surjective ρ₂ ∧ RingHom.ker ρ₂ = I.map (algebraMap A R₂) ∧
      ∀ x : R, π x = (ρ₁ (E x).1, ρ₂ (E x).2) := by
  let J := I.map (algebraMap A R)
  let K₁ : Ideal R := Ideal.span {1 - u}
  let K₂ : Ideal R := Ideal.span {u}
  let E : R ≃ₐ[A] (R ⧸ K₁) × (R ⧸ K₂) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem A (e := 1 - u) (f := u) hu.one_sub hu (by simp)
      hu.one_sub_mul_self
  have hE (x : R) : E x = (Ideal.Quotient.mk K₁ x, Ideal.Quotient.mk K₂ x) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem_apply _ _ _ _ _ _
  have hπ1 : (π (1 - u)).1 = 0 := by simp [hπu]
  have hπ2 : (π u).2 = 0 := by simp [hπu]
  have hK₁ : ∀ x ∈ K₁, ((RingHom.fst P Q).comp π) x = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change (π (r * (1 - u))).1 = 0
    rw [map_mul, Prod.fst_mul, hπ1, mul_zero]
  have hK₂ : ∀ x ∈ K₂, ((RingHom.snd P Q).comp π) x = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change (π (r * u)).2 = 0
    rw [map_mul, Prod.snd_mul, hπ2, mul_zero]
  let ρ₁ : R ⧸ K₁ →+* P := Ideal.Quotient.lift K₁ ((RingHom.fst P Q).comp π) hK₁
  let ρ₂ : R ⧸ K₂ →+* Q := Ideal.Quotient.lift K₂ ((RingHom.snd P Q).comp π) hK₂
  have hρ₁ (x : R) : ρ₁ (Ideal.Quotient.mk K₁ x) = (π x).1 := rfl
  have hρ₂ (x : R) : ρ₂ (Ideal.Quotient.mk K₂ x) = (π x).2 := rfl
  have hJ (j : R) (hj : j ∈ J) : π j = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact hj
  have hmap₁ : I.map (algebraMap A (R ⧸ K₁)) = J.map (Ideal.Quotient.mk K₁) := by
    rw [Ideal.map_map]
    rfl
  have hmap₂ : I.map (algebraMap A (R ⧸ K₂)) = J.map (Ideal.Quotient.mk K₂) := by
    rw [Ideal.map_map]
    rfl
  refine ⟨R ⧸ K₁, R ⧸ K₂, inferInstance, inferInstance, inferInstance, inferInstance, E, ρ₁,
    ρ₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨x, hx⟩ := hπ (p, 0)
    exact ⟨Ideal.Quotient.mk K₁ x, by rw [hρ₁, hx]⟩
  · rw [hmap₁]
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : (π x).1 = 0 := hz
      have hux : u * x ∈ J := by
        change u * x ∈ I.map (algebraMap A R)
        rw [← hker, RingHom.mem_ker, map_mul, hπu]
        ext <;> simp [hx]
      have heq : Ideal.Quotient.mk K₁ x = Ideal.Quotient.mk K₁ (u * x) := by
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        exact Ideal.mem_span_singleton'.mpr ⟨x, by ring⟩
      rw [heq]
      exact Ideal.mem_map_of_mem _ hux
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      change ρ₁ (Ideal.Quotient.mk K₁ j) = 0
      rw [hρ₁, hJ j hj]
      rfl
  · intro q
    obtain ⟨x, hx⟩ := hπ (0, q)
    exact ⟨Ideal.Quotient.mk K₂ x, by rw [hρ₂, hx]⟩
  · rw [hmap₂]
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : (π x).2 = 0 := hz
      have hux : (1 - u) * x ∈ J := by
        change (1 - u) * x ∈ I.map (algebraMap A R)
        rw [← hker, RingHom.mem_ker, map_mul, map_sub, map_one, hπu]
        ext <;> simp [hx]
      have heq : Ideal.Quotient.mk K₂ x = Ideal.Quotient.mk K₂ ((1 - u) * x) := by
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        exact Ideal.mem_span_singleton'.mpr ⟨x, by ring⟩
      rw [heq]
      exact Ideal.mem_map_of_mem _ hux
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      change ρ₂ (Ideal.Quotient.mk K₂ j) = 0
      rw [hρ₂, hJ j hj]
      rfl
  · intro x
    rw [hE, hρ₁, hρ₂]

/-- If reduction modulo `IB'` induces a bijection on idempotents of the integral closure `B'`, the
idempotent of `B' ⧸ IB'` corresponding to `(1, 0)` in a decomposition `A ⧸ I × C'` lifts to `B'`. -/
private lemma exists_isIdempotentElem_lift_of_algEquiv_prod
    {A : Type u} [CommRing A] {I : Ideal A}
    {A' : Type v} [CommRing A'] [Algebra A A']
    {C' : Type w} [CommRing C'] [Algebra (A ⧸ I) C']
    (e' : (integralClosure A A' ⧸ I.map (algebraMap A (integralClosure A A'))) ≃ₐ[A ⧸ I]
      ((A ⧸ I) × C'))
    (hbij : InducesBijectionOnIdempotents (I.map (algebraMap A (integralClosure A A')))) :
    ∃ u : integralClosure A A', IsIdempotentElem u ∧
      e' (Ideal.Quotient.mk (I.map (algebraMap A (integralClosure A A'))) u) = (1, 0) := by
  have hidem : IsIdempotentElem (e'.symm (1, 0)) :=
    (show IsIdempotentElem ((1, 0) : (A ⧸ I) × C') by
      simp [IsIdempotentElem]).map e'.symm
  obtain ⟨⟨u, hu⟩, hlift⟩ := hbij.2 ⟨e'.symm (1, 0), hidem⟩
  have hmk : Ideal.Quotient.mk _ u = e'.symm (1, 0) := congrArg Subtype.val hlift
  exact ⟨u, hu, by rw [hmk, AlgEquiv.apply_symm_apply]⟩

/-- Assume Gabber's criterion for `(A, I)`: `I` lies in the Jacobson radical of `A` and every
monic `X ^ n (X - 1) + ∑ aᵢ X ^ i` with `aᵢ ∈ I` and `n ≥ 1` has a root in `1 + I`. Let `B'` be
the integral closure of `A` in an `A`-algebra `A'`. Then every decomposition
`B' ⧸ IB' ≅ A ⧸ I × C'` of `A ⧸ I`-algebras lifts to a decomposition `B' ≅ B'₁ × B'₂` of
`A`-algebras: there are surjections `B'₁ → A ⧸ I` and `B'₂ → C'` with kernels `IB'₁` and `IB'₂`
through which the reduction of `B'` is the given decomposition. In the source `A'` is étale over
`A` and the decomposition is the one of Tag 0EM3; the lift holds for any `A'` and any
decomposition. -/
@[stacks 0EM4 "the decomposition `B' ⧸ IB' ≅ A ⧸ I × C'` of the integral closure lifts to \
`B' ≅ B'₁ × B'₂` under Gabber's criterion; stated for any `A`-algebra `A'` and any \
decomposition"]
theorem exists_integralClosure_algEquiv_prod_lift_of_gabber_root_condition
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal A))
    (hroot : ∀ (f : A[X]), f.Monic →
      ∀ (n : ℕ), 1 ≤ n →
        ∀ a : Fin (n + 1) → I,
          f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
            ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (A' : Type (max u v)) [CommRing A'] [Algebra A A']
    (C' : Type w) [CommRing C'] [Algebra (A ⧸ I) C']
    (e' : (integralClosure A A' ⧸ I.map (algebraMap A (integralClosure A A'))) ≃ₐ[A ⧸ I]
      ((A ⧸ I) × C')) :
    ∃ (B₁ B₂ : Type (max u v)) (_ : CommRing B₁) (_ : CommRing B₂) (_ : Algebra A B₁)
      (_ : Algebra A B₂) (E : integralClosure A A' ≃ₐ[A] B₁ × B₂) (ρ₁ : B₁ →+* A ⧸ I)
      (ρ₂ : B₂ →+* C'),
      Function.Surjective ρ₁ ∧ RingHom.ker ρ₁ = I.map (algebraMap A B₁) ∧
      Function.Surjective ρ₂ ∧ RingHom.ker ρ₂ = I.map (algebraMap A B₂) ∧
      ∀ x : integralClosure A A',
        e' (Ideal.Quotient.mk (I.map (algebraMap A (integralClosure A A'))) x) =
          (ρ₁ (E x).1, ρ₂ (E x).2) := by
  have h5 : IsContainedInJacobson I ∧
      ∀ (f : A[X]), f.Monic → ∀ (n : ℕ), 1 ≤ n → ∀ a : Fin (n + 1) → I,
        f = X ^ n * (X - 1) + ∑ i : Fin (n + 1), C (a i : A) * X ^ (i : ℕ) →
          ∃! α : A, α - 1 ∈ I ∧ f.IsRoot α := by
    refine ⟨hI, fun f hf n hn a hform ↦ ?_⟩
    obtain ⟨α, hα, hfα⟩ := hroot f hf n hn a hform
    exact ⟨α, ⟨hα, hfα⟩, fun β hβ ↦ gabber_root_eq_of_isRoot I hI f n a hform hα hfα hβ.1 hβ.2⟩
  have h4 : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      InducesBijectionOnIdempotents (I.map (algebraMap A B)) :=
    ((henselianPair_tfae.{u, v} A I).out 5 4).mp h5
  obtain ⟨u, hu, hπu⟩ := exists_isIdempotentElem_lift_of_algEquiv_prod e' (h4 _)
  let J := I.map (algebraMap A (integralClosure A A'))
  let π : integralClosure A A' →+* (A ⧸ I) × C' := e'.toRingHom.comp (Ideal.Quotient.mk J)
  have hπx (x : integralClosure A A') : π x = e' (Ideal.Quotient.mk J x) := rfl
  obtain ⟨B₁, B₂, h₁, h₂, a₁, a₂, E, ρ₁, ρ₂, hs₁, hk₁, hs₂, hk₂, hcomp⟩ :=
    exists_algEquiv_prod_lift_of_isIdempotentElem I π
      (e'.surjective.comp Ideal.Quotient.mk_surjective)
      ((RingHom.ker_comp_of_injective (Ideal.Quotient.mk J) e'.injective).trans Ideal.mk_ker)
      hu (by rw [hπx]; exact hπu)
  refine ⟨B₁, B₂, h₁, h₂, a₁, a₂, E, ρ₁, ρ₂, hs₁, hk₁, hs₂, hk₂, fun x ↦ ?_⟩
  exact (hπx x).symm.trans (hcomp x)

end
