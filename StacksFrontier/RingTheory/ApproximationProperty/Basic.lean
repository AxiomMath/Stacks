module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe
public import StacksFrontier.RingTheory.ApproximationProperty.Defs

/-!
# First consequences of the approximation property

Let `(A, 𝔪)` be a Noetherian local ring with the approximation property: every finite system of
polynomial equations over `A` which has a solution in the completion `Â = lim A/𝔪ⁿ` has a
solution in `A` (Stacks, Section 16.1). This file collects the elementary consequences of the
property used in the proof that such a ring is a G-ring (C. Rotthaus, §1).

* A solution in `A` can be chosen congruent to a given solution `x` in `Â` modulo any power
  `𝔪 ^ N`. This is the congruence trick of the proof of Stacks, Lemma 07QY: choose `c` in `A`
  with `xᵢ ≡ cᵢ` modulo `𝔪 ^ N Â` and generators `g₁, …, gᵣ` of `𝔪 ^ N`. The system enlarged by
  the equations `Xᵢ - cᵢ = ∑ₗ gₗ Zᵢₗ` still has a solution in `Â`, and every solution of the
  enlarged system in `A` is congruent to `x` modulo `𝔪 ^ N Â`.
* In algebra form: every `A`-algebra map from a finite type `A`-algebra `E` to `Â` is
  approximated, modulo `𝔪 ^ N` on finitely many given elements, by an `A`-algebra map `E → A`.
* `A` is henselian. A simple root modulo `𝔪` lifts to a root in the complete local ring `Â`, and
  approximating that root modulo `𝔪` gives a root in `A` with the prescribed residue.
* If `A` is a domain, then so is `Â` (Rotthaus, Proposition (1.4)). If `a b = 0` in `Â` with
  `a`, `b` nonzero, Krull's intersection theorem gives `N` with `a, b ∉ 𝔪 ^ N Â`, and
  approximating the solution `(a, b)` of `X Y = 0` modulo `𝔪 ^ N` gives a pair of zero divisors
  in `A`.
* The approximation property is invariant under isomorphisms of local rings.

## Main results

* `IsLocalRing.HasApproximationProperty.exists_aeval_eq_zero`: the approximation property for
  systems indexed by arbitrary finite types.
* `IsLocalRing.HasApproximationProperty.exists_aeval_eq_zero_sub_mem`: approximation of a
  solution in `Â` modulo `𝔪 ^ N`.
* `IsLocalRing.HasApproximationProperty.exists_algHom_sub_mem`,
  `IsLocalRing.HasApproximationProperty.exists_algHom`: the algebra form of the property.
* `IsLocalRing.HasApproximationProperty.henselianLocalRing`: `A` is henselian.
* `IsLocalRing.HasApproximationProperty.isDomain_adicCompletion`: if `A` is a domain, so is `Â`.
* `IsLocalRing.HasApproximationProperty.of_ringEquiv`: invariance under ring isomorphisms.

## Implementation notes

The completion is `AdicCompletion (maximalIdeal A) A`, and `𝔪 ^ N Â` is the extended ideal
`(maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A))`. The map of
completions along which the property is transported by a ring isomorphism is assembled from
Mathlib's universal property `AdicCompletion.liftRingHom`.

## References

* [C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466]
* [Stacks Project, Tag 07BX](https://stacks.math.columbia.edu/tag/07BX)
* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
-/

@[expose] public section

universe u v

open IsLocalRing

namespace IsLocalRing.HasApproximationProperty

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Polynomial evaluations at two families which agree modulo an ideal agree modulo it. -/
private theorem aeval_sub_mem_of_sub_mem {R S σ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (J : Ideal S) {u v : σ → S} (h : ∀ i, u i - v i ∈ J) (q : MvPolynomial σ R) :
    MvPolynomial.aeval u q - MvPolynomial.aeval v q ∈ J := by
  rw [← Ideal.Quotient.eq]
  have : (Ideal.Quotient.mkₐ R J).comp (MvPolynomial.aeval u) =
      (Ideal.Quotient.mkₐ R J).comp (MvPolynomial.aeval v) := by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    congr 1
    funext i
    exact Ideal.Quotient.eq.mpr (h i)
  exact DFunLike.congr_fun this q

/-- **The approximation property for systems indexed by finite types.** A system of polynomial
equations over `A`, with finitely many equations in finitely many variables indexed by arbitrary
finite types, which has a solution in the completion of `A` has a solution in `A`. -/
theorem exists_aeval_eq_zero (hA : HasApproximationProperty A) {σ ι : Type*} [Finite σ]
    [Finite ι] (f : ι → MvPolynomial σ A) (x : σ → AdicCompletion (maximalIdeal A) A)
    (hx : ∀ j, MvPolynomial.aeval x (f j) = 0) :
    ∃ y : σ → A, ∀ j, MvPolynomial.aeval y (f j) = 0 := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, ⟨eι⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨y, hy⟩ := hA n m (fun j => MvPolynomial.rename eσ (f (eι.symm j))) (x ∘ eσ.symm)
    (fun j => by
      rw [MvPolynomial.aeval_rename]
      simpa [Function.comp_def] using hx (eι.symm j))
  refine ⟨y ∘ eσ, fun j => ?_⟩
  have := hy (eι j)
  rw [MvPolynomial.aeval_rename] at this
  simpa using this

/-- **Approximation modulo `𝔪 ^ N`.** Let `A` be a Noetherian local ring with the approximation
property. If a finite system of polynomial equations over `A` has a solution `x` in the completion
`Â`, then for every `N` it has a solution `y` in `A` with `yᵢ ≡ xᵢ` modulo `𝔪 ^ N Â`. -/
theorem exists_aeval_eq_zero_sub_mem [IsNoetherianRing A] (hA : HasApproximationProperty A)
    {σ ι : Type*} [Finite σ] [Finite ι] (f : ι → MvPolynomial σ A)
    (x : σ → AdicCompletion (maximalIdeal A) A) (hx : ∀ j, MvPolynomial.aeval x (f j) = 0)
    (N : ℕ) :
    ∃ y : σ → A, (∀ j, MvPolynomial.aeval y (f j) = 0) ∧
      ∀ i, algebraMap A (AdicCompletion (maximalIdeal A) A) (y i) - x i ∈
        (maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  classical
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal A ^ N))
  have hgmem : ∀ l, g l ∈ maximalIdeal A ^ N := fun l => hg ▸ Submodule.subset_span ⟨l, rfl⟩
  -- approximate each coordinate of `x` modulo `𝔪 ^ N` and write the error in the generators
  have hc : ∀ i, ∃ c : A, x i - algebraMap A (AdicCompletion (maximalIdeal A) A) c ∈
      (maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    fun i => AdicCompletion.exists_sub_mem_map_pow _ (IsNoetherian.noetherian _) N (x i)
  choose c hc using hc
  have hmap : (maximalIdeal A ^ N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      Ideal.span (Set.range fun l => algebraMap A (AdicCompletion (maximalIdeal A) A) (g l)) := by
    rw [← hg, Ideal.map_span, ← Set.range_comp]
    rfl
  have hz : ∀ i, ∃ z : Fin r → AdicCompletion (maximalIdeal A) A,
      ∑ l, z l * algebraMap A (AdicCompletion (maximalIdeal A) A) (g l) =
        x i - algebraMap A (AdicCompletion (maximalIdeal A) A) (c i) := by
    intro i
    have := hc i
    rw [hmap] at this
    exact Ideal.mem_span_range_iff_exists_fun.mp this
  choose z hz using hz
  -- the enlarged system `f = 0`, `Xᵢ - cᵢ - ∑ₗ gₗ Zᵢₗ = 0` and its solution in `Â`
  let F : ι ⊕ σ → MvPolynomial (σ ⊕ σ × Fin r) A := fun
    | Sum.inl j => MvPolynomial.rename Sum.inl (f j)
    | Sum.inr i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (c i) -
        ∑ l, MvPolynomial.C (g l) * MvPolynomial.X (Sum.inr (i, l))
  let ξ : σ ⊕ σ × Fin r → AdicCompletion (maximalIdeal A) A := fun
    | Sum.inl i => x i
    | Sum.inr il => z il.1 il.2
  obtain ⟨y, hy⟩ := hA.exists_aeval_eq_zero F ξ (by
    rintro (j | i)
    · simp only [F, MvPolynomial.aeval_rename]
      exact hx j
    · simp only [F, ξ, map_sub, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      rw [← hz i]
      simp [mul_comm])
  refine ⟨y ∘ Sum.inl, fun j => ?_, fun i => ?_⟩
  · have := hy (Sum.inl j)
    simpa only [F, MvPolynomial.aeval_rename] using this
  · have h1 := hy (Sum.inr i)
    simp only [F, map_sub, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply] at h1
    have hmem : y (Sum.inl i) - c i ∈ maximalIdeal A ^ N := by
      rw [sub_eq_zero] at h1
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hgmem l)
    have : algebraMap A (AdicCompletion (maximalIdeal A) A) ((y ∘ Sum.inl) i) - x i =
        algebraMap A (AdicCompletion (maximalIdeal A) A) (y (Sum.inl i) - c i) -
          (x i - algebraMap A (AdicCompletion (maximalIdeal A) A) (c i)) := by
      rw [Function.comp_apply, map_sub]
      ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ hmem) (hc i)

/-- **The approximation property in algebra form, with congruences.** Let `A` be a Noetherian
local ring with the approximation property and `E` a finite type `A`-algebra. For every
`A`-algebra map `f : E → Â`, every finite family `x` of elements of `E` and every `N`, there is
an `A`-algebra map `g : E → A` with `g (xᵢ) ≡ f (xᵢ)` modulo `𝔪 ^ N Â`. -/
theorem exists_algHom_sub_mem [IsNoetherianRing A] (hA : HasApproximationProperty A)
    {E : Type v} [CommRing E] [Algebra A E] [Algebra.FiniteType A E]
    (f : E →ₐ[A] AdicCompletion (maximalIdeal A) A) {k : ℕ} (x : Fin k → E) (N : ℕ) :
    ∃ g : E →ₐ[A] A, ∀ i, algebraMap A (AdicCompletion (maximalIdeal A) A) (g (x i)) - f (x i) ∈
      Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) (maximalIdeal A ^ N) := by
  classical
  -- a presentation `E = A[X₁, …, Xₙ] / (p₁, …, pₘ)`
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  obtain ⟨m, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (RingHom.ker π.toRingHom))
  have hpker : ∀ j, π (p j) = 0 := fun j => by
    have : p j ∈ RingHom.ker π.toRingHom := hp ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  let xh : Fin n → AdicCompletion (maximalIdeal A) A := fun l => f (π (MvPolynomial.X l))
  have hcomp : ∀ q, MvPolynomial.aeval xh q = f (π q) := by
    intro q
    have : f.comp π = MvPolynomial.aeval xh := MvPolynomial.algHom_ext fun l => by simp [xh]
    rw [← this, AlgHom.comp_apply]
  -- approximate the solution `xh` of the relations modulo `𝔪 ^ N`
  obtain ⟨y, hy, hyx⟩ := hA.exists_aeval_eq_zero_sub_mem p xh
    (fun j => by rw [hcomp, hpker, map_zero]) N
  have hker : RingHom.ker π.toRingHom ≤
      RingHom.ker (MvPolynomial.aeval y : MvPolynomial (Fin n) A →ₐ[A] A).toRingHom := by
    rw [← hp]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hy j
  refine ⟨AlgHom.liftOfSurjective π hπ (MvPolynomial.aeval y) hker, fun i => ?_⟩
  obtain ⟨q, hq⟩ := hπ (x i)
  have hyq : algebraMap A (AdicCompletion (maximalIdeal A) A) (MvPolynomial.aeval y q) =
      MvPolynomial.aeval (fun l => algebraMap A (AdicCompletion (maximalIdeal A) A) (y l)) q :=
    MvPolynomial.comp_aeval_apply y (Algebra.ofId A (AdicCompletion (maximalIdeal A) A)) q
  rw [← hq, AlgHom.liftOfSurjective_apply, ← hcomp, hyq]
  exact aeval_sub_mem_of_sub_mem _ hyx q

/-- **The approximation property in algebra form.** Let `A` be a Noetherian local ring with the
approximation property and `E` a finite type `A`-algebra. If there is an `A`-algebra map from `E`
to the completion of `A`, then there is an `A`-algebra map from `E` to `A`. -/
theorem exists_algHom [IsNoetherianRing A] (hA : HasApproximationProperty A)
    {E : Type v} [CommRing E] [Algebra A E] [Algebra.FiniteType A E]
    (f : E →ₐ[A] AdicCompletion (maximalIdeal A) A) : Nonempty (E →ₐ[A] A) :=
  let ⟨g, _⟩ := hA.exists_algHom_sub_mem f (k := 0) Fin.elim0 0
  ⟨g⟩

/-- **A Noetherian local ring with the approximation property is henselian.** A root modulo `𝔪`
of a monic polynomial at which the derivative is a unit lifts to a root in the complete local ring
`Â`, and approximating that root modulo `𝔪` gives a root in `A` with the same residue. -/
theorem henselianLocalRing [IsNoetherianRing A] (hA : HasApproximationProperty A) :
    HenselianLocalRing A := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  have hloc : ∀ a ∈ maximalIdeal A, algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) := fun a ha => by
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap A (AdicCompletion (maximalIdeal A) A))]
      at ha
    exact ha
  -- the root in the completion, which is `𝔪`-adically complete, hence henselian
  obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian
    (I := maximalIdeal (AdicCompletion (maximalIdeal A) A))
    (f.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) (hf.map _)
    (algebraMap A (AdicCompletion (maximalIdeal A) A) a₀)
    (by rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]; exact hloc _ h₁)
    (by
      rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      exact (h₂.map _).map _)
  -- its approximation modulo `𝔪`
  obtain ⟨y, hy, hyb⟩ := hA.exists_aeval_eq_zero_sub_mem (σ := Unit) (ι := Unit)
    (fun _ => Polynomial.aeval (MvPolynomial.X ()) f) (fun _ => b) (fun _ => by
      rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map]
      exact hb) 1
  refine ⟨y (), ?_, ?_⟩
  · have := hy ()
    rwa [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X,
      Polynomial.coe_aeval_eq_eval] at this
  · rw [← IsLocalRing.maximalIdeal_comap (algebraMap A (AdicCompletion (maximalIdeal A) A)),
      Ideal.mem_comap, map_sub]
    have h1 := hyb ()
    rw [pow_one, ← AdicCompletion.maximalIdeal_eq_map] at h1
    have := Ideal.add_mem _ h1 hba
    rwa [sub_add_sub_cancel] at this

/-- An element of the completion of a Noetherian local ring lying in `𝔪 ^ n Â` for every `n` is
zero (Krull's intersection theorem in the complete ring `Â`). -/
private theorem eq_zero_of_forall_mem_map_pow [IsNoetherianRing A]
    (x : AdicCompletion (maximalIdeal A) A)
    (h : ∀ n, x ∈ (maximalIdeal A ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    x = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (AdicCompletion (maximalIdeal A) A))
    x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, AdicCompletion.maximalIdeal_eq_map,
    ← Ideal.map_pow]
  exact h n

/-- **The completion of a Noetherian local domain with the approximation property is a domain**
(Rotthaus, Proposition (1.4)). If `a b = 0` in `Â` with `a` and `b` nonzero, choose `N` with
`a, b ∉ 𝔪 ^ N Â`; a solution of `X Y = 0` in `A` congruent to `(a, b)` modulo `𝔪 ^ N` then
consists of two nonzero elements of `A` with product zero. -/
theorem isDomain_adicCompletion [IsNoetherianRing A] [IsDomain A]
    (hA : HasApproximationProperty A) : IsDomain (AdicCompletion (maximalIdeal A) A) := by
  have hex : ∀ c : AdicCompletion (maximalIdeal A) A, c ≠ 0 →
      ∃ n, c ∉ (maximalIdeal A ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
    intro c hc
    by_contra h
    exact hc (eq_zero_of_forall_mem_map_pow c fun n => not_not.mp fun hn => h ⟨n, hn⟩)
  have : NoZeroDivisors (AdicCompletion (maximalIdeal A) A) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    rw [not_or] at hne
    obtain ⟨na, hna⟩ := hex a hne.1
    obtain ⟨nb, hnb⟩ := hex b hne.2
    obtain ⟨y, hy, hyx⟩ := hA.exists_aeval_eq_zero_sub_mem (σ := Fin 2) (ι := Unit)
      (fun _ => MvPolynomial.X 0 * MvPolynomial.X 1) ![a, b] (fun _ => by simpa using hab)
      (max na nb)
    have h0 : y 0 * y 1 = 0 := by simpa using hy ()
    have key : ∀ (i : Fin 2) (n : ℕ), n ≤ max na nb → ![a, b] i ∉
        (maximalIdeal A ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) → y i ≠ 0 :=
      fun i n hn hni hi => hni (Ideal.map_mono (Ideal.pow_le_pow_right hn)
        (by simpa [hi] using hyx i))
    rcases mul_eq_zero.mp h0 with h | h
    · exact key 0 na (le_max_left na nb) hna h
    · exact key 1 nb (le_max_right na nb) hnb h
  exact NoZeroDivisors.to_isDomain _

/-- A ring map carrying `J` into `I` carries `J ^ n` into `I ^ n`. -/
private theorem pow_le_comap_pow {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {J : Ideal R} {I : Ideal S} (hf : J.map f ≤ I) (n : ℕ) : J ^ n ≤ (I ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hf n)

/-- The reductions modulo powers which define the map of completions along `f` are compatible. -/
private theorem completionMap_compat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {J : Ideal R} {I : Ideal S} (hf : J.map f ≤ I) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        ((Ideal.quotientMap _ f (pow_le_comap_pow f hf n)).comp
          (AdicCompletion.evalₐ J n).toRingHom) =
      (Ideal.quotientMap _ f (pow_le_comap_pow f hf m)).comp
        (AdicCompletion.evalₐ J m).toRingHom := by
  ext x
  induction x using AdicCompletion.induction_on with
  | h a =>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
    apply pow_le_comap_pow f hf m
    simpa only [neg_sub, smul_eq_mul, Ideal.mul_top] using
      (Submodule.neg_mem (J ^ m • (⊤ : Submodule R R)) (SModEq.sub_mem.mp (a.property hmn)))

/-- The map of adic completions induced by a ring homomorphism carrying `J` into `I`. -/
private noncomputable def completionMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Ideal R) (I : Ideal S) (hf : J.map f ≤ I) : AdicCompletion J R →+* AdicCompletion I S :=
  AdicCompletion.liftRingHom I
    (fun n ↦ (Ideal.quotientMap _ f (pow_le_comap_pow f hf n)).comp
      (AdicCompletion.evalₐ J n).toRingHom)
    (completionMap_compat f hf)

/-- The map of completions along `f` is compatible with `f` on the uncompleted rings. -/
private theorem completionMap_algebraMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Ideal R) (I : Ideal S) (hf : J.map f ≤ I) (r : R) :
    completionMap f J I hf (algebraMap R (AdicCompletion J R) r) =
      algebraMap S (AdicCompletion I S) (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionMap, AdicCompletion.evalₐ_liftRingHom]
  simp

/-- **The approximation property is invariant under ring isomorphisms.** If `A ≃+* B` is an
isomorphism of local rings and `A` has the approximation property, then so does `B`: a system over
`B` with a solution in `B̂` is carried to a system over `A` with a solution in `Â`, and a solution
of the latter in `A` is carried back to a solution of the former in `B`. -/
theorem of_ringEquiv (hA : HasApproximationProperty A) {B : Type v} [CommRing B]
    [IsLocalRing B] (e : A ≃+* B) : HasApproximationProperty B := by
  intro n m f x hx
  let Ψ := completionMap e.symm.toRingHom (maximalIdeal B) (maximalIdeal A)
    (map_ringEquiv_maximalIdeal e.symm).le
  have hΨ : Ψ.comp (algebraMap B (AdicCompletion (maximalIdeal B) B)) =
      (algebraMap A (AdicCompletion (maximalIdeal A) A)).comp e.symm.toRingHom :=
    RingHom.ext fun b => completionMap_algebraMap e.symm.toRingHom (maximalIdeal B)
      (maximalIdeal A) (map_ringEquiv_maximalIdeal e.symm).le b
  obtain ⟨y, hy⟩ := hA n m (fun j => MvPolynomial.map e.symm.toRingHom (f j)) (Ψ ∘ x)
    (fun j => by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hΨ, ← MvPolynomial.eval₂_comp_left,
        ← MvPolynomial.aeval_def, hx j, map_zero])
  refine ⟨e ∘ y, fun j => ?_⟩
  have h := hy j
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at h
  have h' := congrArg e.toRingHom h
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h'
  rw [MvPolynomial.aeval_def]
  convert h' using 2
  · ext b
    simp
  · rfl

end IsLocalRing.HasApproximationProperty

end
