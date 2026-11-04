module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.MvPolynomialCriterion
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# Lowering the number of nonintegral generators of an étale presentation

Let `k` be a field, let `A = k[x₁, …, xₙ] / I` and let `B` be a finite étale `A`-algebra. An
*étale presentation* of `B` is an étale `k`-algebra map `φ : k[x₁, …, xₙ] → C` together with a
surjection `τ : C / φ(I)C → B` compatible with `A → B`. Attached to such a presentation is the
invariant `NF(C, φ, τ)`: over all finite families `y₁, …, y_r` generating `C` over the image of
`φ`, the minimum of `r - s`, where `y₁, …, y_s` is the longest initial segment consisting of
elements integral over the image of `φ`. It vanishes exactly when `φ` is finite.

In positive characteristic this invariant can always be lowered while the presentation is kept.
The mechanism is that `d(φ(xᵢ) + z^(p·eᵢ)) = d(φ(xᵢ))` in `Ω_{C⁄k}`, so replacing `φ(xᵢ)` by
`φ(xᵢ) + z^(p·eᵢ)` for a suitable element `z` of the kernel `C → B` leaves `φ` étale (by the
differential criterion `MvPolynomial.etale_aeval_iff_height_eq_and_span_range_D_eq_top`) while
making one further generator integral.

## Main definitions

* `Stacks.Etale.nonfiniteGeneratorNumber` — the invariant `NF(C, φ, τ)`.

## Main results

* `Stacks.Etale.finite_of_nonfiniteGeneratorNumber_eq_zero` — a finite-type ring map whose
  invariant vanishes is finite.
* `Stacks.Etale.exists_etalePresentation_nonfiniteGeneratorNumber_lt` — in positive
  characteristic the invariant of an étale presentation can be strictly lowered.
* `Stacks.Etale.exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero` — iterating, an étale
  presentation with vanishing invariant exists.

## Implementation notes

The invariant does not in fact depend on `τ`, so the definition takes only the ring map `φ`.
Generation of `C` over the image of `φ` is expressed as `Subring.closure (Set.range φ ∪
Set.range y) = ⊤`, and the algebra `A` of the source is represented canonically as the quotient
of the polynomial ring by `I`. If no finite generating family exists, the infimum of the empty
set of naturals is `0`; the theorems below are applied only to maps of finite type, where
families exist, and `nonfiniteGeneratorNumber_set_nonempty` records that.

The element `z` is produced from a monic relation satisfied by `y_{s+1}` over `A`, and the
exponents `eᵢ` from the Noether-normalization substitution `subst` of
`StacksFrontier.RingTheory.NoetherNormalization.Basic`, whose leading-coefficient analysis supplies
exponents divisible by `p`.

## References

* [Stacks Project, Tag 0G1F](https://stacks.math.columbia.edu/tag/0G1F)
-/

@[expose] public section

universe u v w

namespace Stacks.Etale

/-- The minimum, over finite ordered generating families of `S` over the image of `φ`, of the
number of terms left after an initial segment consisting of elements integral over `φ`.

This is the invariant denoted `NF(C, φ, τ)` in Stacks, Tag 0G1F. If there is no finite
generating family, the infimum of the empty set in `ℕ` is `0`. -/
noncomputable def nonfiniteGeneratorNumber {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : ℕ :=
  sInf {m : ℕ | ∃ (r s : ℕ) (y : Fin r → S),
    s ≤ r ∧
      Subring.closure (Set.range f ∪ Set.range y) = ⊤ ∧
      (∀ i : Fin r, i.val < s → f.IsIntegralElem (y i)) ∧
      m = r - s}

/-- The set over which `nonfiniteGeneratorNumber` takes its infimum is nonempty for a ring map
of finite type: any finite generating family is a witness, with empty integral initial
segment. -/
private theorem nonfiniteGeneratorNumber_set_nonempty {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FiniteType) :
    {m : ℕ | ∃ (r s : ℕ) (y : Fin r → S), s ≤ r ∧
      Subring.closure (Set.range f ∪ Set.range y) = ⊤ ∧
      (∀ i : Fin r, i.val < s → f.IsIntegralElem (y i)) ∧ m = r - s}.Nonempty := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.FiniteType R S := RingHom.finiteType_algebraMap.mpr hf
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
  let y : Fin s.card → S := fun i => (s.equivFin.symm i).val
  have hy : Set.range y = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).property
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [y]⟩
  have hgen : Subring.closure (Set.range f ∪ Set.range y) = ⊤ := by
    rw [← RingHom.algebraMap_toAlgebra f, ← Algebra.adjoin_eq_ring_closure, hy]
    exact congrArg Subalgebra.toSubring hs
  exact ⟨s.card, s.card, 0, y, by omega, hgen, fun _ _ => by omega, by simp⟩

/-- A ring map of finite type whose nonfinite-generator invariant vanishes is finite. -/
theorem finite_of_nonfiniteGeneratorNumber_eq_zero {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hft : f.FiniteType)
    (hzero : nonfiniteGeneratorNumber f = 0) : f.Finite := by
  have hmem := Nat.sInf_mem (nonfiniteGeneratorNumber_set_nonempty f hft)
  change nonfiniteGeneratorNumber f ∈ _ at hmem
  rw [hzero] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  obtain ⟨r, s, y, hsr, hgen, hint, hval⟩ := hmem
  have hIntegral : f.IsIntegral := by
    intro x
    apply IsIntegral.of_mem_closure'' (f := f) (Set.range f ∪ Set.range y)
      _ x (by rw [hgen]; exact Set.mem_univ x)
    rintro z (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · exact RingHom.isIntegralElem_map f
    · exact hint i (by omega)
  exact RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨hIntegral, hft⟩

private theorem exists_minimal_generator_witness {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (hpos : 0 < nonfiniteGeneratorNumber f) :
    ∃ (r s : ℕ) (y : Fin r → S),
      s ≤ r ∧ Subring.closure (Set.range f ∪ Set.range y) = ⊤ ∧
      (∀ i : Fin r, i.val < s → f.IsIntegralElem (y i)) ∧
      r - s = nonfiniteGeneratorNumber f := by
  classical
  let W : Set ℕ := {m | ∃ (r s : ℕ) (y : Fin r → S),
    s ≤ r ∧ Subring.closure (Set.range f ∪ Set.range y) = ⊤ ∧
    (∀ i : Fin r, i.val < s → f.IsIntegralElem (y i)) ∧ m = r - s}
  have hne : W.Nonempty := by
    by_contra h
    have he : W = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have : nonfiniteGeneratorNumber f = 0 := by
      unfold nonfiniteGeneratorNumber
      rw [Nat.sInf_eq_zero]
      exact Or.inr (by simpa [W] using he)
    omega
  obtain ⟨r, s, y, hsr, hgen, hint, hm⟩ := Nat.sInf_mem hne
  exact ⟨r, s, y, hsr, hgen, hint, hm.symm⟩

private theorem nonfiniteGeneratorNumber_le_of_witness {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S)
    (r s : ℕ) (y : Fin r → S)
    (hsr : s ≤ r)
    (hgen : Subring.closure (Set.range f ∪ Set.range y) = ⊤)
    (hint : ∀ i : Fin r, i.val < s → f.IsIntegralElem (y i)) :
    nonfiniteGeneratorNumber f ≤ r - s :=
  Nat.sInf_le ⟨r, s, y, hsr, hgen, hint, rfl⟩

private theorem exists_monic_relation_in_kernel
    {R A C B : Type*} [CommRing R] [Nontrivial R] [CommRing A] [CommRing C] [CommRing B]
    [Algebra A B] [Module.Finite A B]
    (fA : R →+* A) (hfA : Function.Surjective fA)
    (f : R →+* C) (q : C →+* B)
    (hcomm : ∀ x, q (f x) = algebraMap A B (fA x)) (y : C) :
    ∃ P : Polynomial R, P.Monic ∧ 0 < P.natDegree ∧
      q (Polynomial.eval₂ f y P) = 0 := by
  classical
  have hyint : (algebraMap A B).IsIntegralElem (q y) := by
    let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    exact Algebra.IsIntegral.isIntegral (R := A) (A := B) (q y)
  obtain ⟨Q, hQmonic, hQeval⟩ := hyint
  by_cases hQpos : 0 < Q.natDegree
  · have hQlifts : Q ∈ Polynomial.lifts fA :=
      (Polynomial.lifts_iff_coeff_lifts Q).2 fun i => hfA (Q.coeff i)
    obtain ⟨P, hPmap, hdeg, hPmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hQlifts hQmonic
    refine ⟨P, hPmonic, hdeg ▸ hQpos, ?_⟩
    have hmaps : q.comp f = (algebraMap A B).comp fA := RingHom.ext hcomm
    rw [Polynomial.hom_eval₂, hmaps, ← Polynomial.eval₂_map fA (algebraMap A B) (q y) (p := P),
      hPmap]
    exact hQeval
  · have hQdeg : Q.natDegree = 0 := Nat.eq_zero_of_not_pos hQpos
    have hQconst : Q = Polynomial.C 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hQdeg]
      have hc : Q.coeff 0 = 1 := by
        simpa [hQdeg] using hQmonic.coeff_natDegree
      rw [hc]
    have h01 : (1 : B) = 0 := by
      simpa [hQconst] using hQeval
    let : Subsingleton B := subsingleton_of_zero_eq_one h01.symm
    refine ⟨Polynomial.X, Polynomial.monic_X, by rw [Polynomial.natDegree_X]; omega, ?_⟩
    simpa using (Subsingleton.elim (q y) (0 : B))

private theorem module_finite_of_etale_field
    {K D : Type*} [Field K] [CommRing D] [Algebra K D] [Algebra.Etale K D] :
    Module.Finite K D := by
  classical
  obtain ⟨ι, hι, L, hfield, hKL, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K D).mp inferInstance
  let : Finite ι := hι
  have (i : ι) : Module.Finite K (L i) := (hfinite i).1
  have : Module.Finite K (∀ i, L i) := Module.Finite.pi
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

private theorem exists_nonzero_relation_of_etale
    {R C K : Type*} [CommRing R] [IsDomain R] [CommRing C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : R →+* C) (hf : f.Etale) (z : C) :
    ∃ P : Polynomial R, P ≠ 0 ∧ Polynomial.eval₂ f z P = 0 := by
  let : Algebra R C := f.toAlgebra
  let : Algebra.Etale R C := hf
  let D := TensorProduct R K C
  let : Algebra R D := Algebra.TensorProduct.leftAlgebra
  let : Algebra K D := Algebra.TensorProduct.leftAlgebra
  let : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R K D := inferInstance
  let : IsScalarTower R C D := inferInstance
  let : Algebra.Etale K D := Algebra.Etale.baseChange R C K
  let : Module.Finite K D := module_finite_of_etale_field
  let : Algebra.IsAlgebraic K D := Algebra.IsAlgebraic.of_finite K D
  have hzalg : IsAlgebraic K (Algebra.TensorProduct.includeRight (R := R) (A := K) z) :=
    Algebra.IsAlgebraic.isAlgebraic (R := K) (A := D) _
  have hzalgR : IsAlgebraic R (Algebra.TensorProduct.includeRight (R := R) (A := K) z) :=
    (IsFractionRing.isAlgebraic_iff R K D).mpr hzalg
  obtain ⟨P, hP, hPz⟩ := hzalgR
  refine ⟨P, hP, ?_⟩
  have hinj : Function.Injective (algebraMap C D) := by
    show Function.Injective (Algebra.TensorProduct.includeRight (R := R) (A := K))
    exact Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  apply hinj
  have heval : algebraMap C D (Polynomial.eval₂ f z P) =
      Polynomial.eval₂ (algebraMap R D) (algebraMap C D z) P := by
    rw [Polynomial.hom_eval₂]
    congr 1
    ext x
    show algebraMap C D (algebraMap R C x) = algebraMap R D x
    exact (IsScalarTower.algebraMap_apply R C D x).symm
  rw [heval]
  have hroot : Polynomial.eval₂ (algebraMap R D)
      (Algebra.TensorProduct.includeRight (R := R) (A := K) z) P = 0 := by
    simpa [Polynomial.aeval_def] using hPz
  have hinc : algebraMap C D z = Algebra.TensorProduct.includeRight (R := R) (A := K) z := by
    rfl
  rw [← hinc] at hroot
  simpa using hroot

/-- An algebra map out of a polynomial ring lands in a subring containing the image of the
base ring and of the variables. -/
private theorem map_mem_of_X_mem {k C σ : Type*} [CommRing k] [CommRing C] [Algebra k C]
    (φ : MvPolynomial σ k →ₐ[k] C) (S : Subring C) (hk : ∀ a : k, algebraMap k C a ∈ S)
    (hX : ∀ i, φ (MvPolynomial.X i) ∈ S) (f : MvPolynomial σ k) : φ f ∈ S := by
  have hφeq : φ = MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) := by ext i; simp
  rw [hφeq]
  exact MvPolynomial.eval₂_mem (fun ν _ => hk _) hX

private theorem eval₂_finSuccEquiv
    {k C : Type*} [CommRing k] [CommRing C] [Algebra k C] {n : ℕ}
    (ψ : MvPolynomial (Fin n) k →ₐ[k] C) (z : C)
    (f : MvPolynomial (Fin (n + 1)) k) :
    Polynomial.eval₂ ψ.toRingHom z (MvPolynomial.finSuccEquiv k n f) =
      MvPolynomial.aeval (Fin.cases z (fun i => ψ (MvPolynomial.X i))) f := by
  let F : MvPolynomial (Fin (n + 1)) k →ₐ[k] C :=
    (Polynomial.eval₂AlgHom ψ z (fun _ => Commute.all _ _)).comp
      (MvPolynomial.finSuccEquiv k n).toAlgHom
  let G : MvPolynomial (Fin (n + 1)) k →ₐ[k] C :=
    MvPolynomial.aeval (Fin.cases z (fun i => ψ (MvPolynomial.X i)) )
  have hFG : F = G := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [F, G, MvPolynomial.finSuccEquiv_X_zero]
    · intro j
      simp [F, G, MvPolynomial.finSuccEquiv_X_succ]
  simpa [F, G] using congrArg (fun h : _ →ₐ[k] C => h f) hFG

private theorem aeval_finSuccEquiv_symm
    {k C : Type*} [CommRing k] [CommRing C] [Algebra k C] {n : ℕ}
    (φ : MvPolynomial (Fin n) k →ₐ[k] C) (z : C)
    (P : Polynomial (MvPolynomial (Fin n) k)) :
    MvPolynomial.aeval (Fin.cases z (fun i => φ (MvPolynomial.X i)))
        ((MvPolynomial.finSuccEquiv k n).symm P) =
      Polynomial.eval₂ φ.toRingHom z P := by
  simpa using (eval₂_finSuccEquiv φ z ((MvPolynomial.finSuccEquiv k n).symm P)).symm

private theorem exists_p_divisible_tilt_leadingCoeff
    {k : Type*} [Field k] (p n : ℕ) (hp : 0 < p)
    (g : MvPolynomial (Fin (n + 1)) k)
    (hg : g ≠ 0) :
    ∃ (E : Fin (n + 1) → ℕ) (a : k),
      E 0 = 1 ∧ (∀ i : Fin n, p ∣ E i.succ) ∧ (∀ i, 1 ≤ E i) ∧
      (∃ ν ∈ g.support, a = g.coeff ν) ∧
      (MvPolynomial.finSuccEquiv k n (subst n E g)).leadingCoeff =
        MvPolynomial.C a := by
  classical
  have hsupp : g.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hg (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨e, he0, he1, hinj⟩ := supporting_lemma_normalized n g.support
  let L : ℕ := (g.support.sup fun ν => ν 0) + 1
  let M : ℕ := p * L
  have hLpos : 0 < L := by simp [L]
  have hMpos : 0 < M := Nat.mul_pos hp hLpos
  have hbound : ∀ ν ∈ g.support, ν 0 < M := by
    intro ν hν
    have hle : ν 0 ≤ g.support.sup (fun ν => ν 0) :=
      Finset.le_sup (f := fun ν => ν 0) hν
    have hlt : ν 0 < L := by simp [L]; omega
    exact lt_of_lt_of_le hlt (Nat.le_mul_of_pos_left L hp)
  let E : Fin (n + 1) → ℕ := Fin.cases 1 (fun i => M * e i.succ)
  have hE0 : E 0 = 1 := by simp [E]
  have hEdiv : ∀ i : Fin n, p ∣ E i.succ := by
    intro i
    refine ⟨L * e i.succ, ?_⟩
    simp [E, M, Nat.mul_comm, Nat.mul_left_comm]
  have hEpos : ∀ i, 1 ≤ E i := Fin.cases (by simp [E]) fun j => by
    simp only [E, Fin.cases_succ]
    exact Nat.mul_pos hMpos (he1 j.succ)
  let D : (Fin (n + 1) →₀ ℕ) → ℕ := fun ν => ∑ i, e i * ν i
  let D' : (Fin (n + 1) →₀ ℕ) → ℕ := fun ν => ∑ i : Fin n, e i.succ * ν i.succ
  let W : (Fin (n + 1) →₀ ℕ) → ℕ := fun ν => ∑ i, E i * ν i
  have hDsplit (ν : Fin (n + 1) →₀ ℕ) : D ν = ν 0 + D' ν := by
    simp [D, D', Fin.sum_univ_succ, he0]
  have hWsplit (ν : Fin (n + 1) →₀ ℕ) : W ν = ν 0 + M * D' ν := by
    show (∑ i, E i * ν i) = ν 0 + M * (∑ i : Fin n, e i.succ * ν i.succ)
    simp only [Fin.sum_univ_succ, E, Fin.cases_zero, one_mul, Fin.cases_succ, Finset.mul_sum,
      mul_assoc]
  have hWlt : ∀ ν ∈ g.support, ∀ ν' ∈ g.support, D' ν < D' ν' → W ν < W ν' := by
    intro ν hν ν' hν' hlt
    rw [hWsplit, hWsplit]
    calc
      ν 0 + M * D' ν < M + M * D' ν := Nat.add_lt_add_right (hbound ν hν) _
      _ = M * (D' ν + 1) := by ring
      _ ≤ M * D' ν' := Nat.mul_le_mul_left M (Nat.succ_le_of_lt hlt)
      _ ≤ ν' 0 + M * D' ν' := Nat.le_add_left _ _
  have hWinj : ∀ ν ∈ g.support, ∀ ν' ∈ g.support, W ν = W ν' → ν = ν' := by
    intro ν hν ν' hν' hW
    have hWcalc : ν 0 + M * D' ν = ν' 0 + M * D' ν' := by
      simpa [hWsplit] using hW
    by_cases hA : D' ν = D' ν'
    · have h0 : ν 0 = ν' 0 := by
        rw [hA] at hWcalc
        omega
      have hD : D ν = D ν' := by rw [hDsplit, hDsplit, hA, h0]
      exact (hinj ν hν ν' hν').mp hD
    · rcases lt_or_gt_of_ne hA with hlt | hgt
      · have := hWlt ν hν ν' hν' hlt
        omega
      · have := hWlt ν' hν' ν hν hgt
        omega
  set Ψ : MvPolynomial (Fin (n + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin n) k) :=
    (MvPolynomial.finSuccEquiv k n).toAlgHom.comp (subst n E)
  have hΨX0 : Ψ (MvPolynomial.X 0) = Polynomial.X := by
    show MvPolynomial.finSuccEquiv k n
      (subst n E (MvPolynomial.X 0)) = Polynomial.X
    rw [subst_X_zero, MvPolynomial.finSuccEquiv_X_zero]
  have hΨXsucc : ∀ j : Fin n,
      Ψ (MvPolynomial.X j.succ) = Polynomial.C (MvPolynomial.X j) +
        Polynomial.X ^ (E j.succ) := by
    intro j
    have hne : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
    show MvPolynomial.finSuccEquiv k n
      (subst n E (MvPolynomial.X j.succ)) = _
    rw [subst_X_ne_zero n E j.succ hne, map_add, map_pow,
      MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero]
  have hΨX_monic_deg : ∀ i : Fin (n + 1),
      (Ψ (MvPolynomial.X i)).Monic ∧ (Ψ (MvPolynomial.X i)).natDegree = E i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [hΨX0, hE0]
      exact ⟨Polynomial.monic_X, Polynomial.natDegree_X⟩
    · intro j
      rw [hΨXsucc j]
      have hEj : 0 < E j.succ := hEpos j.succ
      have hdeg : (Polynomial.C (MvPolynomial.X j) :
          Polynomial (MvPolynomial (Fin n) k)).degree <
          (Polynomial.X ^ E j.succ : Polynomial (MvPolynomial (Fin n) k)).degree := by
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        rw [Polynomial.degree_X_pow]
        exact_mod_cast hEj
      refine ⟨?_, ?_⟩
      · rw [add_comm]
        exact (Polynomial.monic_X_pow _).add_of_left hdeg
      · rw [add_comm, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg,
          Polynomial.natDegree_X_pow]
  have hΨX_monic : ∀ i, (Ψ (MvPolynomial.X i)).Monic := fun i => (hΨX_monic_deg i).1
  have hΨX_deg : ∀ i, (Ψ (MvPolynomial.X i)).natDegree = E i :=
    fun i => (hΨX_monic_deg i).2
  let Pν : (Fin (n + 1) →₀ ℕ) → Polynomial (MvPolynomial (Fin n) k) :=
    fun ν => ∏ i, (Ψ (MvPolynomial.X i)) ^ (ν i)
  have hPνmonic : ∀ ν, (Pν ν).Monic := fun ν =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => (hΨX_monic i).pow _
  have hPνdeg : ∀ ν, (Pν ν).natDegree = W ν := by
    intro ν
    show (∏ i, (Ψ (MvPolynomial.X i)) ^ (ν i)).natDegree = W ν
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => (hΨX_monic i).pow _]
    simp only [W]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hΨX_monic i).natDegree_pow, hΨX_deg i]
    ring
  have hΨg : Ψ g = ∑ ν ∈ g.support,
      Polynomial.C (MvPolynomial.C (g.coeff ν)) * Pν ν := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [psi_monomial Ψ ν (g.coeff ν)]
  obtain ⟨νₛ, hνₛ, hmax⟩ := g.support.exists_max_image W hsupp
  have hdom : ∀ ν ∈ g.support, ν ≠ νₛ → W ν < W νₛ := by
    intro ν hν hne
    exact (hmax ν hν).lt_of_ne fun heq => hne (hWinj ν hν νₛ hνₛ heq)
  let a : k := g.coeff νₛ
  have ha0 : a ≠ 0 := MvPolynomial.mem_support_iff.mp hνₛ
  have hmain : (Ψ g).leadingCoeff = MvPolynomial.C a := by
    rw [hΨg]
    have hCne : (MvPolynomial.C a : MvPolynomial (Fin n) k) ≠ 0 := by
      simpa [MvPolynomial.C_eq_zero] using ha0
    have hsum := natDegree_leadingCoeff_dominant_sum
      g.support (fun ν => MvPolynomial.C (g.coeff ν)) Pν W νₛ hνₛ
      hPνmonic hPνdeg hCne hdom
    simpa [a] using hsum.2
  exact ⟨E, a, hE0, hEdiv, hEpos, ⟨νₛ, hνₛ, rfl⟩, hmain⟩

/-- In positive characteristic, an étale presentation of a finite étale algebra whose
nonfinite-generator invariant is positive can be replaced by a compatible étale presentation
with strictly smaller invariant. -/
@[stacks 0G1F]
theorem exists_etalePresentation_nonfiniteGeneratorNumber_lt
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (B : Type w) [CommRing B]
    [Algebra ((MvPolynomial (Fin n) k) ⧸ I) B]
    [Algebra k B] [IsScalarTower k ((MvPolynomial (Fin n) k) ⧸ I) B]
    [Module.Finite ((MvPolynomial (Fin n) k) ⧸ I) B]
    [Algebra.Etale ((MvPolynomial (Fin n) k) ⧸ I) B]
    (C : Type v) [CommRing C] [Algebra k C]
    (φ : MvPolynomial (Fin n) k →ₐ[k] C) (hφ : φ.toRingHom.Etale)
    (τ : (C ⧸ Ideal.map φ.toRingHom I) →ₐ[k] B) (hτ : Function.Surjective τ)
    (hcomm : ∀ f : MvPolynomial (Fin n) k,
      τ (Ideal.Quotient.mk (Ideal.map φ.toRingHom I) (φ f)) =
        algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f))
    (hpos : 0 < nonfiniteGeneratorNumber φ.toRingHom) :
    ∃ (φ' : MvPolynomial (Fin n) k →ₐ[k] C),
      φ'.toRingHom.Etale ∧
      ∃ τ' : (C ⧸ Ideal.map φ'.toRingHom I) →ₐ[k] B,
        Function.Surjective τ' ∧
        (∀ f : MvPolynomial (Fin n) k,
          τ' (Ideal.Quotient.mk (Ideal.map φ'.toRingHom I) (φ' f)) =
            algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f)) ∧
        nonfiniteGeneratorNumber φ'.toRingHom < nonfiniteGeneratorNumber φ.toRingHom := by
  classical
  let R := MvPolynomial (Fin n) k
  let A := R ⧸ I
  obtain ⟨r, s, y, hsr, hgen, hint, hmin⟩ :=
    exists_minimal_generator_witness φ.toRingHom hpos
  have hslt : s < r := by omega
  let x : C := y ⟨s, hslt⟩
  let qAlg : C →ₐ[k] B := τ.comp (Ideal.Quotient.mkₐ k (Ideal.map φ.toRingHom I))
  have hqcomm : ∀ a : R, qAlg (φ a) = algebraMap A B (Ideal.Quotient.mk I a) := hcomm
  obtain ⟨P, hPmonic, hPpos, hqP⟩ := exists_monic_relation_in_kernel
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective φ.toRingHom qAlg.toRingHom hqcomm x
  let z : C := Polynomial.eval₂ φ.toRingHom x P
  have hzker : qAlg z = 0 := hqP
  have hCnontr : Nontrivial C := by
    by_contra hC
    have : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    have hle := nonfiniteGeneratorNumber_le_of_witness φ.toRingHom 0 0
      Fin.elim0 (by omega)
      (eq_top_iff.2 fun c _ => Subsingleton.elim (φ 0) c ▸ Subring.subset_closure (Or.inl ⟨0, rfl⟩))
      (fun i => i.elim0)
    omega
  let : Nontrivial C := hCnontr
  obtain ⟨Q, hQ, hQroot⟩ := exists_nonzero_relation_of_etale
    (R := MvPolynomial (Fin n) k) (C := C)
    (K := Localization (nonZeroDivisors (MvPolynomial (Fin n) k))) φ.toRingHom hφ z
  let g : MvPolynomial (Fin (n + 1)) k := (MvPolynomial.finSuccEquiv k n).symm Q
  have hgrel : MvPolynomial.aeval (Fin.cases z (fun i => φ (MvPolynomial.X i))) g = 0 :=
    (aeval_finSuccEquiv_symm φ z Q).trans hQroot
  let negVars : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k :=
    Fin.cases (MvPolynomial.X 0) (fun i => -MvPolynomial.X i.succ)
  let N : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    MvPolynomial.aeval negVars
  have hN2g : N (N g) = g := by
    have hNN : N.comp N = AlgHom.id k _ := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [N, negVars]
    exact congrArg (fun F : _ →ₐ[k] _ => F g) hNN
  let gneg : MvPolynomial (Fin (n + 1)) k := N g
  have hgneg : gneg ≠ 0 := by
    intro h
    apply hQ
    have : g = 0 := by simpa [gneg, h] using hN2g.symm
    simpa [g] using congrArg (MvPolynomial.finSuccEquiv k n) this
  obtain ⟨E, a, _, hEdiv, hEpos, haCoeff, hdlc⟩ :=
    exists_p_divisible_tilt_leadingCoeff p n hp gneg hgneg
  let t : Fin n → C := fun i => φ (MvPolynomial.X i) + z ^ (E i.succ)
  let ψ : MvPolynomial (Fin n) k →ₐ[k] C := MvPolynomial.aeval (fun i => -t i)
  let φ' : MvPolynomial (Fin n) k →ₐ[k] C := MvPolynomial.aeval t
  let H : Polynomial (MvPolynomial (Fin n) k) :=
    MvPolynomial.finSuccEquiv k n (subst n E gneg)
  have hHroot : Polynomial.eval₂ ψ.toRingHom z H = 0 := by
    let w : Fin (n + 1) → C := Fin.cases z (fun i => -t i)
    let v : Fin (n + 1) → C := Fin.cases z (fun i => φ (MvPolynomial.X i))
    have hcomp :
        ((MvPolynomial.aeval w).comp (subst n E)).comp N = MvPolynomial.aeval v := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ ?_ i
      · simp [N, negVars, w, v, subst_X_zero]
      · intro j
        have hne : (j.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
        simp [N, negVars, w, v, t, subst_X_ne_zero, hne]
    rw [show H = MvPolynomial.finSuccEquiv k n (subst n E gneg) from rfl,
      eval₂_finSuccEquiv]
    have hw : (Fin.cases z (fun i => ψ (MvPolynomial.X i)) : Fin (n + 1) → C) = w := by
      funext i
      refine Fin.cases ?_ ?_ i <;> simp [w, ψ]
    rw [hw]
    show (((MvPolynomial.aeval w).comp (subst n E)).comp N) g = 0
    rw [hcomp]
    exact hgrel
  obtain ⟨νa, hνa, ha⟩ := haCoeff
  have ha0 : a ≠ 0 := by
    intro h
    apply MvPolynomial.mem_support_iff.mp hνa
    simpa [ha] using h
  have hHunit : IsUnit H.leadingCoeff := by
    rw [hdlc]
    exact IsUnit.map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)
      (isUnit_iff_ne_zero.mpr ha0)
  let Hm : Polynomial (MvPolynomial (Fin n) k) := hHunit.unit⁻¹ • H
  have hHmonic : Hm.Monic := by
    simpa [Hm] using Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hHunit
  have hHmroot : Polynomial.eval₂ ψ.toRingHom z Hm = 0 := by
    show Polynomial.eval₂ ψ.toRingHom z
      ((hHunit.unit⁻¹ : Units (MvPolynomial (Fin n) k)) • H) = 0
    rw [Units.smul_def, Polynomial.eval₂_smul, hHroot]
    simp
  have hψint : ψ.toRingHom.IsIntegralElem z := ⟨Hm, hHmonic, hHmroot⟩
  let neg : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
    MvPolynomial.aeval (fun i => -MvPolynomial.X i)
  have hψcomp : ψ.toRingHom = φ'.toRingHom.comp neg.toRingHom := by
    have heq : ψ = φ'.comp neg := by
      apply MvPolynomial.algHom_ext
      intro i
      show ψ (MvPolynomial.X i) = φ' (neg (MvPolynomial.X i))
      simp [ψ, φ', neg]
    exact congrArg AlgHom.toRingHom heq
  have hφ'int : φ'.toRingHom.IsIntegralElem z := by
    rw [hψcomp] at hψint
    exact RingHom.IsIntegralElem.of_comp hψint
  let : Algebra R C := φ'.toRingHom.toAlgebra
  let : IsScalarTower k R C := .of_algebraMap_eq' (by
    ext a
    simp [RingHom.algebraMap_toAlgebra])
  have hφeq : φ = MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) := by
    ext i; simp
  have hOldEtale :
      (MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) : R →ₐ[k] C).toRingHom.Etale := by
    simpa only [← hφeq] using hφ
  have hfiniteKC : Algebra.FiniteType k C := by
    have hftφ : φ.toRingHom.FiniteType := by
      let : Algebra R C := φ.toRingHom.toAlgebra
      let : Algebra.Etale R C := hφ
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    have hftkR : (algebraMap k R).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    have heq : φ.toRingHom.comp (algebraMap k R) = algebraMap k C := RingHom.ext φ.commutes
    exact RingHom.finiteType_algebraMap.mp (heq ▸ hftφ.comp hftkR)
  let : Algebra.FiniteType k C := hfiniteKC
  let : CharP C p := CharP.of_ringHom_of_ne_zero (algebraMap k C) p (by omega)
  have hOldCrit :=
    (MvPolynomial.etale_aeval_iff_height_eq_and_span_range_D_eq_top k C
      (fun i => φ (MvPolynomial.X i))).mp hOldEtale
  have hDpow : ∀ i : Fin n, KaehlerDifferential.D k C (z ^ E i.succ) = 0 := by
    intro i
    obtain ⟨d, hd⟩ := hEdiv i
    rw [hd, Nat.mul_comm, pow_mul]
    exact Stacks.Derivations.derivation_pow_char p (KaehlerDifferential.D k C) (z ^ d)
  have hDsame : ∀ i : Fin n,
      KaehlerDifferential.D k C (t i) =
        KaehlerDifferential.D k C (φ (MvPolynomial.X i)) := by
    intro i
    rw [show t i = φ (MvPolynomial.X i) + z ^ E i.succ by rfl,
      map_add, hDpow, add_zero]
  have hφ'etale : φ'.toRingHom.Etale :=
    (MvPolynomial.etale_aeval_iff_height_eq_and_span_range_D_eq_top k C t).mpr
      ⟨hOldCrit.1, by simpa only [hDsame] using hOldCrit.2⟩
  let D : Subalgebra R C :=
    Algebra.adjoin R (Set.range (fun i : Fin n => φ (MvPolynomial.X i)) ∪ {z})
  have hDxi (i : Fin n) : φ (MvPolynomial.X i) ∈ D :=
    Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)
  have hDz : z ∈ D := Algebra.subset_adjoin (Or.inr (Set.mem_singleton z))
  have hφmem : ∀ f : R, φ f ∈ D := map_mem_of_X_mem φ D.toSubring
    (fun a => by rw [← φ'.commutes]; exact D.algebraMap_mem (MvPolynomial.C a)) hDxi
  let φD : R →+* D := φ.toRingHom.codRestrict D hφmem
  have hφDcomp : (algebraMap D C).comp φD = φ.toRingHom := rfl
  have hφxiInt : ∀ i : Fin n, φ'.toRingHom.IsIntegralElem (φ (MvPolynomial.X i)) := by
    intro i
    have ht : φ'.toRingHom.IsIntegralElem (t i) := by
      rw [show t i = φ' (MvPolynomial.X i) by simp [φ']]
      exact RingHom.isIntegralElem_map φ'.toRingHom
    have hzint : IsIntegral R z := hφ'int
    have hpw : φ'.toRingHom.IsIntegralElem (z ^ E i.succ) := by
      rcases hzint.pow (E i.succ) with ⟨Q, hQm, hQroot⟩
      exact ⟨Q, hQm, by simpa [RingHom.algebraMap_toAlgebra] using hQroot⟩
    simpa [t] using RingHom.IsIntegralElem.sub φ'.toRingHom ht hpw
  have hDint : Algebra.IsIntegral R D := by
    apply Algebra.IsIntegral.adjoin
    rintro u (⟨i, rfl⟩ | rfl)
    · exact hφxiInt i
    · exact hφ'int
  have hyD : ∀ i : Fin r, i.val < s → IsIntegral D (y i) := by
    intro i hi
    show (algebraMap D C).IsIntegralElem (y i)
    rw [← hφDcomp] at hint
    exact RingHom.IsIntegralElem.of_comp (hint i hi)
  let zD : D := ⟨z, hDz⟩
  have hxD : IsIntegral D x := by
    refine ⟨P.map φD - Polynomial.C zD,
      (hPmonic.map φD).sub_of_left ?_, ?_⟩
    · calc
        Polynomial.degree (Polynomial.C zD) < 1 := Polynomial.degree_C_lt
        _ ≤ Polynomial.degree (P.map φD) := by
          rw [Polynomial.degree_eq_natDegree (hPmonic.map φD).ne_zero,
            (hPmonic.natDegree_map φD)]
          exact_mod_cast (Nat.succ_le_iff.mpr hPpos)
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_map, Polynomial.eval₂_C]
      rw [hφDcomp]
      show Polynomial.eval₂ φ.toRingHom x P - z = 0
      simp [z]
  let : Algebra.IsIntegral R D := hDint
  have hyInt : ∀ i : Fin r, i.val < s → φ'.toRingHom.IsIntegralElem (y i) := by
    intro i hi
    show IsIntegral R (y i)
    exact isIntegral_trans (R := R) (A := D) (B := C) (y i) (hyD i hi)
  have hxInt : φ'.toRingHom.IsIntegralElem x := by
    show IsIntegral R x
    exact isIntegral_trans (R := R) (A := D) (B := C) x hxD
  let Y : Fin (n + r) → C :=
    Fin.addCases (fun i => φ (MvPolynomial.X i)) y
  have hYleft (i : Fin n) : Y (Fin.castAdd r i) = φ (MvPolynomial.X i) := by simp [Y]
  have hYright (i : Fin r) : Y (Fin.natAdd n i) = y i := by simp [Y]
  let G : Subring C := Subring.closure (Set.range φ'.toRingHom ∪ Set.range Y)
  have hφmemG : ∀ f : R, φ f ∈ G := map_mem_of_X_mem φ G
    (fun a => by
      rw [← φ'.commutes]
      exact Subring.subset_closure (Or.inl ⟨MvPolynomial.C a, rfl⟩))
    (fun i => by
      rw [← hYleft i]
      exact Subring.subset_closure (Or.inr ⟨Fin.castAdd r i, rfl⟩))
  have hsubsetOld : Set.range φ.toRingHom ∪ Set.range y ⊆ G := by
    rintro c (⟨f, rfl⟩ | ⟨i, rfl⟩)
    · exact hφmemG f
    · exact Subring.subset_closure (Or.inr ⟨Fin.natAdd n i, hYright i⟩)
  have hgen' : Subring.closure (Set.range φ'.toRingHom ∪ Set.range Y) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Subring.closure_le.2 hsubsetOld
  have hYint : ∀ j : Fin (n + r), j.val < n + s + 1 →
      φ'.toRingHom.IsIntegralElem (Y j) := by
    intro j hj
    induction j using Fin.addCases with
    | left i =>
        rw [hYleft]
        exact hφxiInt i
    | right i =>
        have hi : i.val ≤ s := by
          have hval : n + i.val < n + s + 1 := by simpa [Fin.natAdd] using hj
          omega
        by_cases his : i.val < s
        · rw [hYright]
          exact hyInt i his
        · rw [hYright, show i = ⟨s, hslt⟩ from Fin.ext (show i.val = s by omega)]
          exact hxInt
  have hleNew := nonfiniteGeneratorNumber_le_of_witness φ'.toRingHom
    (n + r) (n + s + 1) Y (by omega) hgen' hYint
  have hNFlt : nonfiniteGeneratorNumber φ'.toRingHom <
      nonfiniteGeneratorNumber φ.toRingHom := by omega
  have hcompNew : qAlg.comp φ' = qAlg.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    show qAlg (φ' (MvPolynomial.X i)) = qAlg (φ (MvPolynomial.X i))
    rw [show φ' (MvPolynomial.X i) = t i by simp [φ']]
    show qAlg (φ (MvPolynomial.X i) + z ^ E i.succ) = qAlg (φ (MvPolynomial.X i))
    rw [map_add, map_pow, hzker, zero_pow (Nat.one_le_iff_ne_zero.mp (hEpos i.succ)), add_zero]
  let J' : Ideal C := Ideal.map φ'.toRingHom I
  have hJker : J' ≤ RingHom.ker qAlg.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show qAlg (φ' f) = 0
    calc
      qAlg (φ' f) = qAlg (φ f) :=
        congrArg (fun F : R →ₐ[k] B => F f) hcompNew
      _ = algebraMap A B (Ideal.Quotient.mk I f) := hcomm f
      _ = 0 := by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  let τ' : (C ⧸ J') →ₐ[k] B := Ideal.Quotient.liftₐ J' qAlg hJker
  have hqAlgSurj : Function.Surjective qAlg :=
    hτ.comp (Ideal.Quotient.mkₐ_surjective (R₁ := k) (Ideal.map φ.toRingHom I))
  have hτ'Surj : Function.Surjective τ' := fun b => by
    obtain ⟨c, hc⟩ := hqAlgSurj b
    exact ⟨Ideal.Quotient.mk J' c, hc⟩
  have hcomm' : ∀ f : R,
      τ' (Ideal.Quotient.mk J' (φ' f)) = algebraMap A B (Ideal.Quotient.mk I f) :=
    fun f => (congrArg (fun F : R →ₐ[k] B => F f) hcompNew).trans (hcomm f)
  exact ⟨φ', hφ'etale, τ', hτ'Surj, hcomm', hNFlt⟩

/-- In positive characteristic every étale presentation of a finite étale algebra can be
replaced by a compatible one whose nonfinite-generator invariant is zero, so whose étale map is
finite. -/
theorem exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (B : Type w) [CommRing B]
    [Algebra ((MvPolynomial (Fin n) k) ⧸ I) B] [Algebra k B]
    [IsScalarTower k ((MvPolynomial (Fin n) k) ⧸ I) B]
    [Module.Finite ((MvPolynomial (Fin n) k) ⧸ I) B]
    [Algebra.Etale ((MvPolynomial (Fin n) k) ⧸ I) B]
    (C : Type v) [CommRing C] [Algebra k C] (φ : MvPolynomial (Fin n) k →ₐ[k] C)
    (hφ : φ.toRingHom.Etale) (τ : (C ⧸ Ideal.map φ.toRingHom I) →ₐ[k] B)
    (hτ : Function.Surjective τ)
    (hcomm : ∀ f, τ (Ideal.Quotient.mk (Ideal.map φ.toRingHom I) (φ f)) =
      algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f)) :
    ∃ ψ : MvPolynomial (Fin n) k →ₐ[k] C, ψ.toRingHom.Etale ∧
      nonfiniteGeneratorNumber ψ.toRingHom = 0 ∧
      ∃ τ' : (C ⧸ Ideal.map ψ.toRingHom I) →ₐ[k] B, Function.Surjective τ' ∧
        ∀ f, τ' (Ideal.Quotient.mk (Ideal.map ψ.toRingHom I) (ψ f)) =
          algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f) := by
  let recStep : ∀ m : ℕ, ∀ ψ : MvPolynomial (Fin n) k →ₐ[k] C,
      ψ.toRingHom.Etale → ∀ τ : (C ⧸ Ideal.map ψ.toRingHom I) →ₐ[k] B,
      Function.Surjective τ →
      (∀ f, τ (Ideal.Quotient.mk (Ideal.map ψ.toRingHom I) (ψ f)) =
        algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f)) →
      nonfiniteGeneratorNumber ψ.toRingHom = m →
      ∃ θ : MvPolynomial (Fin n) k →ₐ[k] C, θ.toRingHom.Etale ∧
        nonfiniteGeneratorNumber θ.toRingHom = 0 ∧
        ∃ τ' : (C ⧸ Ideal.map θ.toRingHom I) →ₐ[k] B, Function.Surjective τ' ∧
          ∀ f, τ' (Ideal.Quotient.mk (Ideal.map θ.toRingHom I) (θ f)) =
            algebraMap ((MvPolynomial (Fin n) k) ⧸ I) B (Ideal.Quotient.mk I f) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro ψ hψ τ hτ hcomm hmeasure
      by_cases hm : m = 0
      · exact ⟨ψ, hψ, hmeasure.trans hm, τ, hτ, hcomm⟩
      · obtain ⟨ψ', hψ', τ', hτ', hcomm', hlt⟩ :=
          exists_etalePresentation_nonfiniteGeneratorNumber_lt
            k p hp n I B C ψ hψ τ hτ hcomm (by omega)
        exact ih _ (hlt.trans_eq hmeasure) ψ' hψ' τ' hτ' hcomm' rfl
  exact recStep _ φ hφ τ hτ hcomm rfl

end Stacks.Etale

end
