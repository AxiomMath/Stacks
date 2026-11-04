module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksCore.LinearAlgebra.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Idempotents.Lifting
public import StacksFrontier.RingTheory.Jacobson.Criteria
public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens

@[expose] public section

/-!
# Zariski pairs

A *Zariski pair* is a pair `(A, I)` consisting of a commutative ring `A` and an ideal `I ⊆ A`
contained in the Jacobson radical of `A`. The predicate is the project's
`IsContainedInJacobson`, so this file only registers the Stacks tag for it and develops the
consequences of the condition.

Three such consequences are proved here. A flat, integral, finitely presented algebra over a
Zariski pair is trivial as soon as it is trivial modulo the distinguished ideal. An element of a
finite algebra whose reduction is the idempotent `(1, 0)` of a product decomposition is
annihilated by a monic polynomial reducing to `(X - 1) * X ^ d`. Finally, localizing a Noetherian
Zariski pair away from an element of the ideal produces a Jacobson ring.

## Main results

* `bijective_algebraMap_of_bijective_quotientMap`: a flat, integral, finitely presented algebra
  over a Zariski pair `(A, I)` is isomorphic to `A` when it is so modulo `I`.
* `exists_monic_isRoot_map_eq_X_sub_one_mul_X_pow`: the monic polynomial adapted to a product
  decomposition of the reduction of a finite algebra.
* `isJacobsonRing_of_isContainedInJacobson_of_isLocalization_away`: a Noetherian Zariski pair
  localizes away from an element of its ideal to a Jacobson ring.

## Implementation notes

Assertions that a canonical map is an isomorphism are phrased as bijectivity of the corresponding
ring homomorphism, and the extension `IB` of `I` to an algebra `B` is the ideal
`I.map (algebraMap A B)`. Localizations are represented by an arbitrary algebra satisfying
`IsLocalization.Away`, rather than by a chosen concrete model.

In `exists_monic_isRoot_map_eq_X_sub_one_mul_X_pow` each factor of the decomposition is an
algebra over `A ⧸ I`, so the extension of `I` to either factor vanishes; the source's hypothesis
that `A / I → B₁ / IB₁` is surjective is therefore stated as surjectivity of the structure map
`A ⧸ I → B₁`.

## References

* [Stacks: Tag 0ELX](https://stacks.math.columbia.edu/tag/0ELX)
-/

add_to_stacks 0ELY "A Zariski pair is a pair `(A, I)` with `I` contained in the Jacobson radical
of `A`; the ambient ring is determined by the type of the ideal." IsContainedInJacobson

universe u v w x

open Polynomial

/-- **Stacks 0ELZ.** Let `(A, I)` be a Zariski pair and let `B` be a flat, integral,
finitely presented `A`-algebra. If the canonical map `A ⧸ I → B ⧸ IB` is an isomorphism,
then `A → B` is an isomorphism. -/
@[stacks 0ELZ]
theorem bijective_algebraMap_of_bijective_quotientMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.IsIntegral A B] [Algebra.FinitePresentation A B]
    (I : Ideal A) (hI : IsContainedInJacobson I)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap A B) := by
  let _ : Module.Finite A B := Algebra.IsIntegral.finite
  let f : A →ₗ[A] B := Algebra.linearMap A B
  have htop : (⊤ : Submodule A B) ≤ LinearMap.range f ⊔ I • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨q, hq⟩ := hquot.2 (Ideal.Quotient.mk (I.map (algebraMap A B)) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hd : b - algebraMap A B a ∈ I.map (algebraMap A B) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hq, Ideal.quotientMap_mk]
      simp
    refine (show b = algebraMap A B a + (b - algebraMap A B a) by abel) ▸ add_mem ?_ ?_
    · exact Submodule.mem_sup_left ⟨a, rfl⟩
    · exact Submodule.mem_sup_right (by rw [Ideal.smul_top_eq_map]; exact hd)
  have hrange : LinearMap.range f = ⊤ := by
    have heq := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson
      (I := I) (J := ⊥) (N := LinearMap.range f) (N' := ⊤)
      Module.Finite.fg_top hI htop
    simpa using heq.symm
  have hsurj : Function.Surjective (algebraMap A B) := LinearMap.range_eq_top.mp hrange
  let K : Ideal A := RingHom.ker (algebraMap A B)
  have hKfg : K.FG := Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId A B) hsurj
  let e := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId A B) hsurj
  let _ : K.Pure := by
    rw [Ideal.Pure]
    unfold K
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hKid : IsIdempotentElem K := Ideal.isIdempotentElem_of_pure K
  have hKI : K ≤ I := by
    intro a ha
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hquot.1
    rw [Ideal.quotientMap_mk]
    change algebraMap A B a = 0 at ha
    simp [ha]
  have hKbot : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I K hKfg
    (by
      intro x hx
      have hx' : x ∈ K * K := by rwa [hKid.eq]
      show x ∈ I * K
      exact Ideal.mul_mono hKI le_rfl hx')
    hI
  exact ⟨(RingHom.injective_iff_ker_eq_bot (algebraMap A B)).2 hKbot, hsurj⟩

set_option maxHeartbeats 800000 in
-- The quotient comparison and the characteristic polynomial calculation need more elaboration
-- than the default budget allows.
/-- **Stacks 0EM0.** Let `(A, I)` be a Zariski pair and `B` a finite `A`-algebra. If
`B / IB` decomposes as a product of `A / I`-algebras, the first factor is generated by the
image of `A / I`, and `b` maps to `(1, 0)`, then `b` is annihilated by a monic polynomial
whose reduction is `(X - 1) X ^ d` for some `d ≥ 1`. -/
@[stacks 0EM0]
theorem exists_monic_isRoot_map_eq_X_sub_one_mul_X_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    (I : Ideal A) (hI : IsContainedInJacobson I)
    (B₁ : Type w) (B₂ : Type x) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] (B₁ × B₂))
    (hsurj : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B)
    (hb : e (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = (1, 0)) :
    ∃ (d : ℕ) (f : A[X]), 1 ≤ d ∧ f.Monic ∧
      (f.map (algebraMap A B)).IsRoot b ∧
      f.map (Ideal.Quotient.mk I) =
        ((Polynomial.X : (A ⧸ I)[X]) - 1) * Polynomial.X ^ d := by
  classical
  let J : Ideal B := I.map (algebraMap A B)
  let Q := B ⧸ J
  let q : B →+* Q := Ideal.Quotient.mk J
  have : Module.Finite A Q := Module.Finite.quotient A J
  have : Module.Finite (A ⧸ I) Q :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I) Q
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A ⧸ I) (M := Q)
  let t : Fin (n + 1) → Q := fun j ↦
    Fin.cases (e.symm (1, 0)) (fun i ↦ e.symm (0, (e (s i)).2)) j
  have ht : Submodule.span (A ⧸ I) (Set.range t) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := hsurj (e (s i)).1
    have heq : s i = a • t 0 + t i.succ := by
      apply e.injective
      simp only [map_add, map_smul]
      show e (s i) = a • e (e.symm (1, 0)) + e (e.symm (0, (e (s i)).2))
      ext <;> simp [Algebra.smul_def, ha]
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self 0)))
      (Submodule.subset_span (Set.mem_range_self i.succ))
  choose v hv using fun j : Fin (n + 1) ↦ Ideal.Quotient.mk_surjective (t j)
  have htA : Submodule.span A (Set.range t) = ⊤ := by
    rw [← Submodule.restrictScalars_span A (A ⧸ I) Ideal.Quotient.mk_surjective,
      ht, Submodule.restrictScalars_top]
  have hvspan : Submodule.span A (Set.range v) = ⊤ := by
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
    let E : (B ⧸ (I • (⊤ : Submodule A B))) ≃ₗ[A] Q :=
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
        (Submodule.Quotient.restrictScalarsEquiv A J).symm
    have hE (y : B) : E ((I • (⊤ : Submodule A B)).mkQ y) = q y := rfl
    have hspan : Submodule.span A
        ((I • (⊤ : Submodule A B)).mkQ '' Set.range v) = ⊤ := by
      have hEv (j : Fin (n + 1)) :
          E.symm (t j) = (I • (⊤ : Submodule A B)).mkQ (v j) := by
        apply E.injective
        rw [E.apply_symm_apply, hE, hv]
      calc
        Submodule.span A ((I • (⊤ : Submodule A B)).mkQ '' Set.range v)
            = Submodule.span A (E.symm '' Set.range t) := by
                rw [← Set.range_comp, ← Set.range_comp]
                exact congrArg (Submodule.span A ∘ Set.range) (funext fun j => (hEv j).symm)
        _ = Submodule.map E.symm.toLinearMap (Submodule.span A (Set.range t)) := by
              rw [Submodule.map_span]
              rfl
        _ = ⊤ := by simp [htA]
    have H : I • (⊤ : Submodule A B) ⊔ Submodule.span A (Set.range v) = ⊤ :=
      (Submodule.span_image_mkQ_eq_top_iff (I • (⊤ : Submodule A B))
        (Set.range v)).mp hspan
    exact H.ge.trans (sup_comm _ _).le
  let δ : Fin (n + 1) → Fin (n + 1) → A := fun i j ↦
    if i = 0 ∧ j = 0 then 1 else 0
  have hr (j : Fin (n + 1)) :
      b * v j - (if j = 0 then v 0 else 0) ∈ I • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map]
    show b * v j - (if j = 0 then v 0 else 0) ∈ I.map (algebraMap A B)
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply e.injective
    have hbq : e (q b) = (1, 0) := hb
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · have he0 : e (q (v 0)) = (1, 0) := by
        simpa [t] using congrArg e (hv 0)
      show e (q (b * v 0 - v 0)) = e 0
      simp only [map_sub, map_mul, he0, map_zero]
      rw [hbq]
      simp
    · have hei : e (q (v i.succ)) = (0, (e (s i)).2) := by
        simpa [t] using congrArg e (hv i.succ)
      simp only [Fin.succ_ne_zero, ite_false, sub_zero]
      show e (q (b * v i.succ)) = e 0
      simp only [map_mul, hei, map_zero]
      rw [hbq]
      simp
  have hrange (j : Fin (n + 1)) :
      b * v j - (if j = 0 then v 0 else 0) ∈
        LinearMap.range (Ideal.finsuppTotal (Fin (n + 1)) B I v) := by
    rw [Ideal.range_finsuppTotal, hvspan]
    exact hr j
  choose c hc using hrange
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) A := fun i j ↦ δ i j + (c j i : A)
  have hrep : M.Represents v (Algebra.lmul A B b) := by
    rw [Matrix.represents_iff']
    intro j
    simp only [M, add_smul]
    rw [Finset.sum_add_distrib]
    have hδ : ∑ i, δ i j • v i = if j = 0 then v 0 else 0 := by
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;> simp [δ]
    rw [hδ, ← Ideal.finsuppTotal_apply_eq_of_fintype I (c j), hc j]
    show (if j = 0 then v 0 else 0) + (b * v j - if j = 0 then v 0 else 0) = b * v j
    abel
  let MR : Matrix.isRepresentation A v := ⟨M, Algebra.lmul A B b, hrep⟩
  let f : A[X] := M.charpoly
  refine ⟨n + 1, f * X, by omega, (Matrix.charpoly_monic M).mul monic_X, ?_, ?_⟩
  · simp only [Polynomial.IsRoot, Polynomial.map_mul, map_X, eval_mul, eval_X]
    have hz : Polynomial.aeval (Algebra.lmul A B b) f = 0 := by
      rw [← Matrix.isRepresentation.eq_toEnd_of_represents A v hvspan MR hrep]
      rw [Polynomial.aeval_algHom_apply]
      have hh : Polynomial.aeval MR f = 0 := by
        apply Subtype.ext
        simpa [f, Polynomial.aeval_subalgebra_coe] using Matrix.aeval_self_charpoly M
      simp [hh]
    have hz' : eval b (f.map (algebraMap A B)) = 0 := by
      have hz'' : Polynomial.aeval b f = 0 :=
        Algebra.lmul_injective (R := A) (by simpa [← Polynomial.aeval_algHom_apply] using hz)
      simpa [Polynomial.aeval_def] using hz''
    rw [hz', zero_mul]
  · rw [Polynomial.map_mul, map_X, ← Matrix.charpoly_map]
    have hmap : M.map (Ideal.Quotient.mk I) = Matrix.diagonal
        (fun j : Fin (n + 1) ↦ if j = 0 then 1 else 0) := by
      ext i j
      show (Ideal.Quotient.mk I) (M i j) = _
      have hc0 : (Ideal.Quotient.mk I) (c j i : A) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (c j i).property
      simp only [M, map_add, hc0, add_zero, δ, Matrix.diagonal_apply]
      split_ifs <;> simp_all
    rw [hmap, Matrix.charpoly_diagonal, Fin.prod_univ_succ]
    simpa [pow_succ] using (mul_assoc (X - 1 : (A ⧸ I)[X]) (X ^ n) X)

/-- A non-maximal prime of a localization of a Noetherian Zariski pair away from an element of
the distinguished ideal is contained in infinitely many primes. -/
private lemma infinite_primes_over_of_not_isMaximal
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : IsContainedInJacobson I) (f : A) (hf : f ∈ I)
    (Af : Type v) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]
    (p : Ideal Af) (hp : p.IsPrime) (hnp : ¬p.IsMaximal) :
    {q : Ideal Af | p ≤ q ∧ q.IsPrime}.Infinite := by
  let P : Ideal A := p.under A
  have hP : P.IsPrime := (IsLocalization.isPrime_iff_isPrime_disjoint (.powers f) Af p).mp hp |>.1
  let B := A ⧸ P
  let fB : B := Ideal.Quotient.mk P f
  obtain ⟨q, hqmax, hpq⟩ := p.exists_le_maximal hp.ne_top
  have hpq' : p < q := hpq.lt_of_ne fun h => hnp (h ▸ hqmax)
  let Q : Ideal A := q.under A
  have hQ : Q.IsPrime :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (.powers f) Af q).mp hqmax.isPrime |>.1
  have hPQ : P < Q := by
    let e := IsLocalization.orderIsoOfPrime (.powers f) Af
    show (e ⟨p, hp⟩).1 < (e ⟨q, hqmax.isPrime⟩).1
    exact e.lt_iff_lt.mpr hpq'
  obtain ⟨m, hm, hQm⟩ := Q.exists_le_maximal hQ.ne_top
  let hmI : m.IsMaximal := hm
  have hfm : f ∈ m := Ring.jacobson_le_of_isMaximal m (by
    rw [← Ideal.jacobson_bot]
    exact hI hf)
  have hQm' : Q < m := hQm.lt_of_ne fun e => by
    change q.under A = m at e
    exact Set.disjoint_left.mp
      ((IsLocalization.isPrime_iff_isPrime_disjoint (.powers f) Af q).mp hqmax.isPrime |>.2)
      (Submonoid.mem_powers f) (e ▸ hfm)
  let Qb : Ideal B := Q.map (Ideal.Quotient.mk P)
  let mb : Ideal B := m.map (Ideal.Quotient.mk P)
  let _ : IsDomain B := Ideal.Quotient.isDomain P
  have hQb : Qb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hPQ.le)
  have hmb : mb.IsMaximal := hm.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by simpa [Ideal.mk_ker] using hPQ.le.trans hQm)
  have hQbmb : Qb < mb := (Ideal.map_mono hQm).lt_of_ne fun e => hQm'.ne <| by
    rw [← Ideal.comap_map_mk hPQ.le, ← Ideal.comap_map_mk (hPQ.le.trans hQm), e]
  let C := Localization.AtPrime mb
  let x : C := algebraMap B C fB
  have hdim : 2 ≤ ringKrullDim C := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height mb C]
    have hbotQ : (⊥ : Ideal B) < Qb := by
      rw [bot_lt_iff_ne_bot]
      intro e
      have : Q = P := by
        change Ideal.map (Ideal.Quotient.mk P) Q = ⊥ at e
        rw [← Ideal.comap_map_mk hPQ.le, e]
        ext a
        simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
      exact hPQ.ne' this
    have h1 : 1 ≤ Qb.height := by
      have := Ideal.height_strict_mono_of_isPrime_of_isPrime hbotQ
      exact Order.one_le_iff_pos.mpr (by simpa using this)
    have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQbmb
    have h2' : Qb.height + 1 ≤ mb.height :=
      (ENat.add_one_le_iff (Qb.height_ne_top hQb.ne_top)).2 h2
    have hnat : (2 : ℕ∞) ≤ mb.height := calc
      (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ 1 + Qb.height := add_le_add_right h1 1
      _ = Qb.height + 1 := add_comm _ _
      _ ≤ mb.height := h2'
    exact WithBot.coe_le_coe.mpr hnat
  have hx0 : x ≠ 0 := by
    intro hx
    have hinj : Function.Injective (algebraMap B C) :=
      IsLocalization.injective _ mb.primeCompl_le_nonZeroDivisors
    have hfb0 : fB = 0 := hinj (by simpa [x] using hx)
    have hfP : f ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hfb0
    exact Set.disjoint_left.mp
      ((IsLocalization.isPrime_iff_isPrime_disjoint (.powers f) Af p).mp hp |>.2)
      (Submonoid.mem_powers f) hfP
  have hinf : ((PrimeSpectrum.basicOpen x : TopologicalSpace.Opens _) : Set _).Infinite :=
    PrimeSpectrum.infinite_of_two_le_ringKrullDim C hdim _ (PrimeSpectrum.basicOpen x).isOpen
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hx0⟩
  let rA (t : PrimeSpectrum.basicOpen x) : Ideal A :=
    (t.1.asIdeal.under B).comap (Ideal.Quotient.mk P)
  have hrA (t : PrimeSpectrum.basicOpen x) :
      (rA t).IsPrime ∧ Disjoint (Submonoid.powers f : Set A) (rA t) := by
    refine ⟨((IsLocalization.isPrime_iff_isPrime_disjoint mb.primeCompl C t.1.asIdeal).mp
      t.1.isPrime |>.1).comap _, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hmem
    apply (PrimeSpectrum.mem_basicOpen x t.1).mp t.2
    apply t.1.isPrime.mem_of_pow_mem n
    simpa [x, map_pow, rA, fB, Ideal.mem_comap] using hmem
  let F : (PrimeSpectrum.basicOpen x) → {q : Ideal Af | p ≤ q ∧ q.IsPrime} := fun r =>
    ⟨(rA r).map (algebraMap A Af), by
      constructor
      · rw [show p = P.map (algebraMap A Af) from (IsLocalization.map_under (.powers f) Af p).symm]
        exact Ideal.map_mono fun a ha => by
          show Ideal.Quotient.mk P a ∈ r.1.asIdeal.under B
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show a ∈ P from ha)]
          exact Ideal.zero_mem _
      · exact IsLocalization.isPrime_of_isPrime_disjoint (.powers f) Af _ (hrA r).1 (hrA r).2⟩
  have hFinj : Function.Injective F := by
    intro r s hrs
    have hrs' := congrArg Subtype.val hrs
    dsimp only [F] at hrs'
    have hrs'' : rA r = rA s := by
      rw [← IsLocalization.under_map_of_isPrime_disjoint (.powers f) Af (hrA r).1 (hrA r).2,
        ← IsLocalization.under_map_of_isPrime_disjoint (.powers f) Af (hrA s).1 (hrA s).2]
      exact congrArg (fun J : Ideal Af => J.under A) hrs'
    have hrB := (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective) hrs''
    apply Subtype.ext
    apply PrimeSpectrum.ext
    rw [← IsLocalization.map_under mb.primeCompl C r.1.asIdeal,
      ← IsLocalization.map_under mb.primeCompl C s.1.asIdeal]
    exact congrArg (Ideal.map (algebraMap B C)) hrB
  let _ : Infinite (PrimeSpectrum.basicOpen x) := Set.infinite_coe_iff.mpr hinf
  apply (Set.infinite_range_of_injective (Subtype.val_injective.comp hFinj)).mono
  rintro _ ⟨r, rfl⟩
  exact (F r).2

/-- **Stacks 0GED.** The localization of a Noetherian ring away from an element of an ideal in
its Jacobson radical is a Jacobson ring. -/
@[stacks 0GED, ega "IV 10.5.8"]
theorem isJacobsonRing_of_isContainedInJacobson_of_isLocalization_away
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hI : IsContainedInJacobson I) (f : A) (hf : f ∈ I)
    (Af : Type v) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af] :
    IsJacobsonRing Af := by
  let _ : IsNoetherianRing Af := IsLocalization.isNoetherianRing (.powers f) Af inferInstance
  apply isJacobsonRing_of_forall_isMaximal_or_infinite_setOf_isPrime Af
  intro p hp
  exact or_iff_not_imp_left.mpr (infinite_primes_over_of_not_isMaximal I hI f hf Af p hp)

end
