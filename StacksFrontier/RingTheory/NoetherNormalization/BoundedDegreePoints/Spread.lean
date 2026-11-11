module

public import StacksFrontier.RingTheory.NoetherNormalization.BoundedDegreePoints.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Spreading out a Noether normalization over the fraction field

Let `R` be a domain with fraction field `K`, let `B` be a finite type `R`-algebra and let `T`
be a `K`-algebra with an `R`-algebra map `j : B → T` such that every element of `T` becomes an
element of `j(B)` after multiplication by a nonzero element of `R` (e.g. `T = K ⊗_R B`).
Given a finite injective `K`-algebra map `ψ : K[X₁, …, Xₙ] → T` (a Noether normalization of
`T`), we find `0 ≠ f ∈ R`, elements `y₁, …, yₙ ∈ B` with `j(yᵢ) = sᵢ ψ(Xᵢ)` for nonzero
`sᵢ ∈ R`, and `u₁, …, u_d ∈ B` such that for every `b ∈ B` some `f ^ m j(b)` lies in the
`R[j(y)]`-span of `j(u₁), …, j(u_d)`: the normalization is defined and finite over `R[1/f]`.

We also show that, `k` being an algebraically closed field over `K`, every `K`-point
`a ∈ Kⁿ` of the polynomial ring lifts to a `K`-algebra map `T → k` (lying over).

## Main results

* `exists_algHom_apply_eq_of_injective_of_isIntegral`: lifting `K`-points to `T → k`.
* `exists_pow_smul_mem_span_of_finite`: spreading out the normalization.
-/

@[expose] public section

open MvPolynomial

/-- Let `ψ : K[X₁, …, Xₙ] → T` be an injective integral `K`-algebra map and `k` an algebraically
closed field over `K`. Then for every `a ∈ Kⁿ` there is a `K`-algebra map `φ : T → k` with
`φ(ψ(Xᵢ)) = aᵢ` for all `i`. -/
theorem exists_algHom_apply_eq_of_injective_of_isIntegral {K T k : Type*} [Field K]
    [CommRing T] [Algebra K T] [Field k] [IsAlgClosed k] [Algebra K k] {n : ℕ}
    (ψ : MvPolynomial (Fin n) K →ₐ[K] T) (hinj : Function.Injective ψ)
    (hint : ψ.toRingHom.IsIntegral) (a : Fin n → K) :
    ∃ φ : T →ₐ[K] k, ∀ i, φ (ψ (X i)) = algebraMap K k (a i) := by
  let : Algebra (MvPolynomial (Fin n) K) T := ψ.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin n) K) T := ⟨hint⟩
  let ev : MvPolynomial (Fin n) K →ₐ[K] K := aeval a
  have hev : Function.Surjective ev := fun x => ⟨C x, by simp [ev]⟩
  have : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := T) (RingHom.ker ev)
    (by
      have h : RingHom.ker (algebraMap (MvPolynomial (Fin n) K) T) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp hinj
      rw [h]
      exact bot_le)
  have hcomp : (algebraMap K (T ⧸ P)).comp ev.toRingHom =
      (Ideal.Quotient.mk P).comp (algebraMap (MvPolynomial (Fin n) K) T) := by
    refine RingHom.ext fun p => ?_
    change Ideal.Quotient.mk P (algebraMap K T (ev p)) = Ideal.Quotient.mk P (ψ p)
    rw [Ideal.Quotient.eq, ← ψ.commutes, MvPolynomial.algebraMap_eq, ← map_sub]
    change C (ev p) - p ∈ P.under (MvPolynomial (Fin n) K)
    rw [hPc, RingHom.mem_ker]
    simp [ev]
  have : Algebra.IsIntegral K (T ⧸ P) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact IsIntegral.map_of_comp_eq ev.toRingHom (Ideal.Quotient.mk P) hcomp
      (Algebra.IsIntegral.isIntegral t)
  let φ₀ : T ⧸ P →ₐ[K] k := IsAlgClosed.lift
  refine ⟨φ₀.comp (Ideal.Quotient.mkₐ K P), fun i => ?_⟩
  have h := RingHom.congr_fun hcomp (X i)
  change algebraMap K (T ⧸ P) (ev (X i)) = Ideal.Quotient.mk P (ψ (X i)) at h
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← h, AlgHom.commutes]
  simp [ev]

variable {R B T : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
  [CommRing T] [Algebra R T] [Algebra (FractionRing R) T] [IsScalarTower R (FractionRing R) T]

/-- Clearing denominators: if every `ψ(Xᵢ)` becomes an element of an `R`-subalgebra `S` after
multiplication by a nonzero element of `R`, then so does every `ψ(p)`. -/
theorem exists_smul_mem_of_forall_X {n : ℕ}
    (ψ : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R] T) (S : Subalgebra R T)
    (hX : ∀ i, ∃ s : R, s ≠ 0 ∧ s • ψ (X i) ∈ S) (p : MvPolynomial (Fin n) (FractionRing R)) :
    ∃ s : R, s ≠ 0 ∧ s • ψ p ∈ S := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors R) a
    refine ⟨t, nonZeroDivisors.ne_zero t.2, ?_⟩
    rw [← MvPolynomial.algebraMap_eq, ψ.commutes, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R (FractionRing R) T, ← map_mul, mul_comm, ht,
      ← IsScalarTower.algebraMap_apply]
    exact S.algebraMap_mem r
  | add p q hp hq =>
    obtain ⟨s₁, hs₁, h₁⟩ := hp
    obtain ⟨s₂, hs₂, h₂⟩ := hq
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_add, smul_add]
    refine S.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact S.smul_mem h₁ _
    · rw [mul_smul]
      exact S.smul_mem h₂ _
  | mul_X p i hp =>
    obtain ⟨s₁, hs₁, h₁⟩ := hp
    obtain ⟨s₂, hs₂, h₂⟩ := hX i
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_mul, ← smul_mul_smul_comm]
    exact S.mul_mem h₁ h₂

/-- If every element of `T` lies in an `R`-submodule `N` after multiplication by a nonzero
element of `R`, then for every finite set `F ⊆ T` there is a single nonzero `f ∈ R` with
`f • z ∈ N` for all `z ∈ F`. -/
theorem exists_smul_mem_of_finset {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : ∀ z : M, ∃ s : R, s ≠ 0 ∧ s • z ∈ N) (F : Finset M) :
    ∃ f : R, f ≠ 0 ∧ ∀ z ∈ F, f • z ∈ N := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a F _ ih =>
    obtain ⟨f, hf, hF⟩ := ih
    obtain ⟨s, hs, ha⟩ := hN a
    refine ⟨f * s, mul_ne_zero hf hs, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [mul_smul]
      exact N.smul_mem _ ha
    · rw [mul_comm, mul_smul]
      exact N.smul_mem _ (hF z hz)

/-- Spreading out a Noether normalization. Let `j : B → T` be an `R`-algebra map such that
every element of `T` lies in `j(B)` after multiplication by a nonzero element of `R`, and let
`ψ : K[X₁, …, Xₙ] → T` be a finite `K`-algebra map, `K = Frac(R)`. Then there are `0 ≠ f ∈ R`,
`yᵢ ∈ B` and nonzero `sᵢ ∈ R` with `j(yᵢ) = sᵢ • ψ(Xᵢ)`, and `u : Fin d → B`, such that
for every `b ∈ B` some `f ^ m • j(b)` lies in the `R[j(y)]`-span of the `j(uₗ)`. -/
theorem exists_pow_smul_mem_span_of_finite [Algebra.FiniteType R B] (j : B →ₐ[R] T)
    (hj : ∀ t : T, ∃ s : R, s ≠ 0 ∧ s • t ∈ j.range) {n : ℕ}
    (ψ : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R] T)
    (hψ : ψ.toRingHom.Finite) :
    ∃ (f : R) (_ : f ≠ 0) (d : ℕ) (y : Fin n → B) (s : Fin n → R) (u : Fin d → B),
      (∀ i, s i ≠ 0 ∧ j (y i) = s i • ψ (X i)) ∧
      ∀ b : B, ∃ m : ℕ, f ^ m • j b ∈
        Submodule.span (Algebra.adjoin R (Set.range (j ∘ y))) (Set.range (j ∘ u)) := by
  classical
  have hx : ∀ i, ∃ s : R, s ≠ 0 ∧ ∃ y, j y = s • ψ (X i) := fun i => by
    obtain ⟨s, hs, h⟩ := hj (ψ (X i))
    exact ⟨s, hs, j.mem_range.mp h⟩
  choose s hs y hy using hx
  set Ry := Algebra.adjoin R (Set.range (j ∘ y))
  have hRy : ∀ i, j (y i) ∈ Ry := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  have hclear := exists_smul_mem_of_forall_X ψ Ry (fun i => ⟨s i, hs i, hy i ▸ hRy i⟩)
  let : Algebra (MvPolynomial (Fin n) (FractionRing R)) T := ψ.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) (FractionRing R)) T := hψ
  obtain ⟨d, u', hu'⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin n) (FractionRing R))
    (M := T)
  have hu : ∀ l, ∃ t : R, t ≠ 0 ∧ ∃ u, j u = t • u' l := fun l => by
    obtain ⟨t, ht, h⟩ := hj (u' l)
    exact ⟨t, ht, j.mem_range.mp h⟩
  choose t ht u hu using hu
  set N := Submodule.span Ry (Set.range (j ∘ u))
  have hsmul : ∀ (r : R) {z : T}, z ∈ N → r • z ∈ N := fun r z hz =>
    Submodule.smul_of_tower_mem N r hz
  have hC : ∀ z : T, ∃ r : R, r ≠ 0 ∧ r • z ∈ N.restrictScalars R := by
    intro z
    have hz : z ∈ Submodule.span _ (Set.range u') := hu' ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hz
    refine Finset.sum_induction _ (fun z => ∃ r : R, r ≠ 0 ∧ r • z ∈ N.restrictScalars R) ?_
      ⟨1, one_ne_zero, by simp⟩ ?_
    · rintro a b ⟨r₁, h₁, ha⟩ ⟨r₂, h₂, hb⟩
      refine ⟨r₁ * r₂, mul_ne_zero h₁ h₂, ?_⟩
      rw [smul_add]
      refine (N.restrictScalars R).add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact (N.restrictScalars R).smul_mem _ ha
      · rw [mul_smul]
        exact (N.restrictScalars R).smul_mem _ hb
    · intro l _
      obtain ⟨r, hr, hcl⟩ := hclear (c l)
      refine ⟨r * t l, mul_ne_zero hr (ht l), ?_⟩
      change (r * t l) • (ψ (c l) * u' l) ∈ N
      rw [← smul_mul_smul_comm, ← hu l]
      have h := N.smul_mem (⟨_, hcl⟩ : Ry) (Submodule.subset_span ⟨l, rfl⟩)
      rwa [Subalgebra.smul_def, smul_eq_mul] at h
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := R) (A := B)
  obtain ⟨f, hf, hfF⟩ := exists_smul_mem_of_finset (N.restrictScalars R) hC
    (insert 1 ((Finset.univ.image fun p : Fin d × Fin d => j (u p.1) * j (u p.2)) ∪ G.image j))
  have hf1 : f • (1 : T) ∈ N := hfF 1 (Finset.mem_insert_self _ _)
  have hfu : ∀ i l, f • (j (u i) * j (u l)) ∈ N := fun i l => hfF _
    (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ (i, l)))))
  have hfG : ∀ b ∈ G, f • j b ∈ N := fun b hb => hfF _
    (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)))
  have hmul : ∀ z₁ ∈ N, ∀ z₂ ∈ N, f • (z₁ * z₂) ∈ N := by
    intro z₁ h₁ z₂ h₂
    obtain ⟨q₁, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h₁
    obtain ⟨q₂, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h₂
    rw [Finset.sum_mul_sum, Finset.smul_sum]
    refine N.sum_mem fun i _ => ?_
    rw [Finset.smul_sum]
    refine N.sum_mem fun l _ => ?_
    rw [smul_mul_smul_comm, smul_comm]
    exact N.smul_mem _ (hfu i l)
  refine ⟨f, hf, d, y, s, u, fun i => ⟨hs i, hy i⟩, fun b => ?_⟩
  have hb : b ∈ Algebra.adjoin R (G : Set B) := hG ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by rw [pow_one]; exact hfG x hx⟩
  | algebraMap r =>
    refine ⟨1, ?_⟩
    rw [pow_one, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_comm]
    exact hsmul r hf1
  | add x₁ x₂ _ _ h₁ h₂ =>
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    refine ⟨a + b, ?_⟩
    rw [map_add]
    exact Submodule.pow_add_smul_add_mem (N.restrictScalars R) f ha hb
  | mul x₁ x₂ _ _ h₁ h₂ =>
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₂
    refine ⟨a + b + 1, ?_⟩
    have h : f ^ (a + b + 1) • (j x₁ * j x₂) = f • ((f ^ a • j x₁) * (f ^ b • j x₂)) := by
      rw [smul_mul_smul_comm, smul_smul, ← pow_add, ← pow_succ']
    rw [map_mul, h]
    exact hmul _ ha _ hb
