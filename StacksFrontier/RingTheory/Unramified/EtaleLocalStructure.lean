module

public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.Unramified.LocusBaseChangeAtPrime
import StacksCore.Tactic.StacksAttribute

/-!
# Étale local structure of a ring map unramified at a prime

Let `R → S` be a ring map of finite type and let `q` be a prime of `S` lying over the prime `p`
of `R`, at which `R → S` is unramified. Then there are an étale ring map `R → R'`, a prime `p'`
of `R'` lying over `p`, and a product decomposition `R' ⊗_R S = A × B` such that `R' → A` is
surjective and `p'A` is a prime of `A` lying over `p'` and over `q`. Geometrically: étale locally
around `p`, the germ of `Spec S → Spec R` at `q` is a closed immersion.

## Main results

* `Algebra.exists_etale_isIdempotentElem_surjective_of_isUnramifiedAt`: for `R → S` of finite
  type and unramified at `q`, there are an étale `R → R'`, a prime `p'` of `R'` over `p` and a
  factor `A` of `R' ⊗_R S` such that `R' → A` is surjective and `p'A` is a prime over `p'` and `q`.

## Implementation notes

The product decomposition `R' ⊗_R S = A × B` is given, as in Mathlib's
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, by an idempotent `e` of `R' ⊗_R S`:
the factor `A` is the localization `(R' ⊗_R S)[1/e]`, and `B` is `(R' ⊗_R S)[1/(1 - e)]`; for an
idempotent these are the quotients by `1 - e` and by `e`, and `R' ⊗_R S ≅ A × B`. The map
`R' → A` is the canonical `algebraMap R' (Localization.Away e)`, the ideal `p'A` is
`p'.map (algebraMap R' (Localization.Away e))`, and "lying over `q`" is read along the composite
`S → R' ⊗_R S → A`, whose `S`-algebra structure is not a global instance.

"Unramified at `q`" is `Algebra.IsUnramifiedAt R q`, the formal unramifiedness of `S_q` over `R`;
for `R → S` of finite type it holds if and only if some `R → S_g` with `g ∉ q` is unramified.

## References

* [Stacks Project, Tag 00UX](https://stacks.math.columbia.edu/tag/00UX)
-/


@[expose] public section

universe u v

open TensorProduct

/-- Given primes `P` of `A` and `Q` of `B` lying over the same prime `p` of `R`, there is a prime
of `A ⊗[R] B` lying over both `P` and `Q`. -/
private lemma exists_isPrime_comap_includeLeft_eq_and_comap_includeRight_eq
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (P : Ideal A) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    ∃ M : Ideal (A ⊗[R] B), M.IsPrime ∧
      M.comap (algebraMap A (A ⊗[R] B)) = P ∧
      M.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = Q := by
  let : Algebra p.ResidueField P.ResidueField :=
    (Ideal.ResidueField.map p P (algebraMap R A) (P.over_def p)).toAlgebra
  let : Algebra p.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map p Q (algebraMap R B) (Q.over_def p)).toAlgebra
  have : IsScalarTower R p.ResidueField P.ResidueField := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R A P.ResidueField]
    exact (Ideal.ResidueField.map_algebraMap p P (algebraMap R A) (P.over_def p) x).symm
  have : IsScalarTower R p.ResidueField Q.ResidueField := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R B Q.ResidueField]
    exact (Ideal.ResidueField.map_algebraMap p Q (algebraMap R B) (Q.over_def p) x).symm
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (P.ResidueField ⊗[p.ResidueField] Q.ResidueField)
  let f : A →ₐ[R] P.ResidueField ⊗[p.ResidueField] Q.ResidueField :=
    (Algebra.TensorProduct.includeLeft (R := p.ResidueField) (S := R)).comp
      (IsScalarTower.toAlgHom R A P.ResidueField)
  let g : B →ₐ[R] P.ResidueField ⊗[p.ResidueField] Q.ResidueField :=
    ((Algebra.TensorProduct.includeRight (R := p.ResidueField) (A := P.ResidueField)
      (B := Q.ResidueField)).restrictScalars R).comp (IsScalarTower.toAlgHom R B Q.ResidueField)
  let φ := Algebra.TensorProduct.lift f g fun _ _ ↦ .all _ _
  refine ⟨m.comap φ.toRingHom, Ideal.IsPrime.comap _, ?_, ?_⟩
  · have : (m.comap φ.toRingHom).comap (algebraMap A (A ⊗[R] B)) =
        (m.comap Algebra.TensorProduct.includeLeftRingHom).comap (algebraMap A P.ResidueField) := by
      ext x
      simp [φ, f, Algebra.TensorProduct.algebraMap_apply]
    rw [this, Ideal.eq_bot_of_prime (m.comap _), ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]
  · have : (m.comap φ.toRingHom).comap
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom =
        (m.comap (Algebra.TensorProduct.includeRight (R := p.ResidueField)
          (A := P.ResidueField) (B := Q.ResidueField)).toRingHom).comap
          (algebraMap B Q.ResidueField) := by
      ext x
      simp [φ, g]
    rw [this, Ideal.eq_bot_of_prime (m.comap _), ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]

/-- For `B` the localization of `A` away from `x` and a prime `P` of `A` not containing `x`, the
ideal `P B` is prime and lies over `P`. -/
private lemma isPrime_map_and_under_map_of_isLocalization_away
    {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (x : A)
    [IsLocalization.Away x B] (P : Ideal A) [P.IsPrime] (hx : x ∉ P) :
    (P.map (algebraMap A B)).IsPrime ∧ Ideal.under A (P.map (algebraMap A B)) = P := by
  have hd := (Ideal.disjoint_powers_iff_notMem_of_isPrime x).mpr hx
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) B P ‹_› hd,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) B ‹_› hd⟩

/-- Let `T` be essentially of finite type over `R'`, unramified at a prime `r` over `p'`, and let
`a` be an idempotent of `T` such that `T[1/a]` is finite over `R'` and `r` is the unique prime of
`T` over `p'` avoiding `a`, with `κ(r)/κ(p')` purely inseparable. Then some `b ∉ p'` multiplies
`a * T` into the image of `R'`. -/
private lemma exists_notMem_forall_exists_mul_eq_of_isUnramifiedAt
    {R' T : Type*} [CommRing R'] [CommRing T] [Algebra R' T] [Algebra.EssFiniteType R' T]
    (p' : Ideal R') [p'.IsPrime] {a : T} (ha : IsIdempotentElem a)
    (r : Ideal T) [r.IsPrime] [r.LiesOver p'] [Algebra.IsUnramifiedAt R' r] (har : a ∉ r)
    [Module.Finite R' (Localization.Away a)]
    (huniq : ∀ Q : Ideal T, Q.IsPrime → Q.LiesOver p' → a ∉ Q → Q = r)
    (hpi : letI := Localization.AtPrime.algebraOfLiesOver p' r
      IsPurelyInseparable p'.ResidueField r.ResidueField) :
    ∃ b ∉ p', ∀ y : T, ∃ c : R',
      a * (algebraMap R' T b * y) = a * algebraMap R' T c := by
  let _ := Localization.AtPrime.algebraOfLiesOver p' r
  set A := Localization.Away a
  set q : Ideal A := r.map (algebraMap T A) with hqdef
  have hdisj : ∀ Q : Ideal T, Q.IsPrime →
      (Disjoint (Submonoid.powers a : Set T) (Q : Set T) ↔ a ∉ Q) :=
    fun _ _ ↦ Ideal.disjoint_powers_iff_notMem_of_isPrime a
  have hq : p'.primesOver A = {q} :=
    primesOver_eq_singleton_of_isLocalization (Submonoid.powers a) p' r
      ((hdisj r ‹_›).mpr har) (fun Q hQ hQ' hQ'' ↦ huniq Q hQ hQ' ((hdisj Q hQ).mp hQ''))
  have hqmem : q ∈ p'.primesOver A := hq ▸ rfl
  have : q.IsPrime := hqmem.1
  have : q.LiesOver p' := hqmem.2
  let _ := Localization.AtPrime.algebraOfLiesOver p' q
  have hunder : r = Ideal.under T q :=
    (isPrime_map_and_under_map_of_isLocalization_away A a r har).2.symm
  have : q.LiesOver r := ⟨hunder⟩
  have : Algebra.IsUnramifiedAt T q := Algebra.FormallyUnramified.comp T A _
  have : Algebra.IsUnramifiedAt R' q := Algebra.IsUnramifiedAt.comp r q
  have hsurjr : Function.Surjective (algebraMap p'.ResidueField r.ResidueField) :=
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable p'.ResidueField r.ResidueField
  have hsurjq : Function.Surjective (algebraMap p'.ResidueField q.ResidueField) :=
    surjective_algebraMap_residueField_of_isLocalization (Submonoid.powers a) p' r q hunder hsurjr
  obtain ⟨b, hbp, hb⟩ := exists_notMem_forall_exists_mul_eq_of_localRingHom_surjective p' q hq
    (Localization.localRingHom_surjective_of_primesOver_eq_singleton hq hsurjq)
  refine ⟨b, hbp, fun y ↦ ?_⟩
  obtain ⟨c, hc⟩ := hb (algebraMap T A y)
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply R' T A, ← map_mul,
    IsScalarTower.algebraMap_apply R' T A] at hc
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a) A).mp hc
  have : a ^ (k + 1) * (algebraMap R' T b * y) = a ^ (k + 1) * algebraMap R' T c := by
    rw [pow_succ, mul_comm (a ^ k) a, mul_assoc, mul_assoc, hk]
  simpa [ha.pow_succ_eq] using this

/-- Let `R''` be the localization of `R'` away from an `f ∉ p'`, let `a` be an idempotent of
`R' ⊗[R] S` such that `f` multiplies `a(R' ⊗[R] S)` into the image of `R'`, and let `r` be a prime
of `R' ⊗[R] S` over `p'` and `q` avoiding `a`. Then `R''`, the prime `p'R''` and the image of `a`
satisfy the conclusion of `Algebra.exists_etale_isIdempotentElem_surjective_of_isUnramifiedAt`. -/
private lemma exists_etale_isIdempotentElem_of_exists_mul_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)
    {R' : Type u} [CommRing R'] [Algebra R R'] (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p]
    (R'' : Type u) [CommRing R''] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
    [Algebra.Etale R R''] (f : R') [IsLocalization.Away f R''] (hf : f ∉ p')
    {a : R' ⊗[R] S} (ha : IsIdempotentElem a)
    (hmul : ∀ y : R' ⊗[R] S, ∃ c : R',
      a * (algebraMap R' (R' ⊗[R] S) f * y) = a * algebraMap R' (R' ⊗[R] S) c)
    (r : Ideal (R' ⊗[R] S)) [r.IsPrime] [r.LiesOver p'] (har : a ∉ r)
    (hrq : r.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom = q) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Algebra.Etale R R₀)
      (p₀ : Ideal R₀) (_ : p₀.IsPrime) (_ : p₀.LiesOver p) (e : R₀ ⊗[R] S)
      (_ : IsIdempotentElem e),
      Function.Surjective (algebraMap R₀ (Localization.Away e)) ∧
      (p₀.map (algebraMap R₀ (Localization.Away e))).IsPrime ∧
      (p₀.map (algebraMap R₀ (Localization.Away e))).LiesOver p₀ ∧
      (p₀.map (algebraMap R₀ (Localization.Away e))).comap
        ((algebraMap (R₀ ⊗[R] S) (Localization.Away e)).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] R₀ ⊗[R] S).toRingHom) = q := by
  classical
  let _ : Algebra (R' ⊗[R] S) (R'' ⊗[R] S) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'')
      (AlgHom.id R S)).toRingHom.toAlgebra
  have halg : ∀ x : R' ⊗[R] S, algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) x =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' R'') (AlgHom.id R S) x := fun _ ↦ rfl
  have hbase : ∀ x : R', algebraMap R' (R'' ⊗[R] S) x =
      algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' x) :=
    IsScalarTower.algebraMap_apply R' R'' (R'' ⊗[R] S)
  have htower : ∀ x : R', algebraMap R' (R'' ⊗[R] S) x =
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (algebraMap R' (R' ⊗[R] S) x) := by
    intro x
    rw [halg, hbase]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have : IsScalarTower R' (R' ⊗[R] S) (R'' ⊗[R] S) := IsScalarTower.of_algebraMap_eq htower
  have : IsLocalization.Away (algebraMap R' (R' ⊗[R] S) f) (R'' ⊗[R] S) :=
    isLocalizationAway_map_of_isLocalizationAway f halg
  have hmapAlg : ∀ x : R',
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (algebraMap R' (R' ⊗[R] S) x) =
        algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' x) := fun x ↦ by rw [← htower, hbase]
  have hmapTmul : ∀ s : S,
      algebraMap (R' ⊗[R] S) (R'' ⊗[R] S) (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s := by
    intro s
    rw [halg]
    simp
  set ψ := algebraMap (R' ⊗[R] S) (R'' ⊗[R] S)
  set a'' := ψ a
  set A := Localization.Away a''
  obtain ⟨hp₀, hp₀under⟩ := isPrime_map_and_under_map_of_isLocalization_away R'' f p' hf
  have hp₀lies : (p'.map (algebraMap R' R'')).LiesOver p :=
    ⟨by rw [← Ideal.under_under (A := R) (B := R'), hp₀under]; exact p'.over_def p⟩
  have hgr : algebraMap R' (R' ⊗[R] S) f ∉ r := by
    intro hmem
    exact hf (by rw [r.over_def p']; exact Ideal.mem_comap.mpr hmem)
  set Q := r.map ψ
  obtain ⟨hQp, hQr⟩ := isPrime_map_and_under_map_of_isLocalization_away (R'' ⊗[R] S)
    (algebraMap R' (R' ⊗[R] S) f) r hgr
  have hQu : Ideal.under R'' Q = p'.map (algebraMap R' R'') := by
    calc Ideal.under R'' Q
        = (Ideal.under R' (Ideal.under R'' Q)).map (algebraMap R' R'') :=
          (IsLocalization.map_under (Submonoid.powers f) R'' _).symm
      _ = p'.map (algebraMap R' R'') := by
          rw [Ideal.under_under, ← Ideal.under_under (B := R' ⊗[R] S), hQr, ← r.over_def p']
  have hQa : a'' ∉ Q := fun hmem ↦ har (hQr ▸ Ideal.mem_comap.mpr hmem)
  have hsurj : Function.Surjective (algebraMap R'' A) := by
    refine surjective_algebraMap_localizationAway_of_isIdempotentElem (ha.map ψ) ?_
    refine forall_exists_mul_eq_of_tmul _ ?_
    intro s
    obtain ⟨c, hc⟩ := hmul (1 ⊗ₜ[R] s)
    have hu : IsUnit (algebraMap R' R'' f) := IsLocalization.Away.algebraMap_isUnit f
    have hc' := congrArg ψ hc
    simp only [map_mul, ψ, hmapAlg, hmapTmul] at hc'
    refine ⟨(↑hu.unit⁻¹ : R'') * algebraMap R' R'' c, ?_⟩
    calc a'' * (1 ⊗ₜ[R] s)
        = algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' f * (↑hu.unit⁻¹ : R'')) *
            (a'' * (1 ⊗ₜ[R] s)) := by
          rw [hu.mul_val_inv, map_one, one_mul]
      _ = algebraMap R'' (R'' ⊗[R] S) (↑hu.unit⁻¹ : R'') *
            (a'' * (algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' f) * (1 ⊗ₜ[R] s))) := by
          rw [map_mul]
          ring
      _ = algebraMap R'' (R'' ⊗[R] S) (↑hu.unit⁻¹ : R'') *
            (a'' * algebraMap R'' (R'' ⊗[R] S) (algebraMap R' R'' c)) := by rw [hc']
      _ = a'' * algebraMap R'' (R'' ⊗[R] S) ((↑hu.unit⁻¹ : R'') * algebraMap R' R'' c) := by
          rw [map_mul]
          ring
  set QA := Q.map (algebraMap (R'' ⊗[R] S) A)
  obtain ⟨hQAp, hQAu⟩ := isPrime_map_and_under_map_of_isLocalization_away A a'' Q hQa
  have hQAR : Ideal.under R'' QA = p'.map (algebraMap R' R'') := by
    rw [← Ideal.under_under (B := R'' ⊗[R] S), hQAu, hQu]
  have hmap : (p'.map (algebraMap R' R'')).map (algebraMap R'' A) = QA := by
    rw [← hQAR, Ideal.under_def, Ideal.map_comap_of_surjective _ hsurj]
  refine ⟨R'', inferInstance, inferInstance, inferInstance, p'.map (algebraMap R' R''),
    hp₀, hp₀lies, a'', ha.map ψ, hsurj, hmap ▸ hQAp, ⟨by rw [hmap, hQAR]⟩, ?_⟩
  rw [hmap, ← Ideal.comap_comap]
  change Ideal.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R'' ⊗[R] S).toRingHom
    (Ideal.under (R'' ⊗[R] S) QA) = q
  rw [hQAu, ← hrq, ← hQr, Ideal.under_def, Ideal.comap_comap]
  congr 1
  ext s
  exact (hmapTmul s).symm

/-- **Étale local structure of a ring map unramified at a prime.** Let `S` be a finite type
`R`-algebra and let `q` be a prime of `S` lying over the prime `p` of `R` at which `S` is
unramified over `R`. There are an étale `R`-algebra `R'`, a prime `p'` of `R'` lying over `p` and
an idempotent `e` of `R' ⊗[R] S` — the product decomposition `R' ⊗[R] S = A × B` with
`A = (R' ⊗[R] S)[1/e]` and `B = (R' ⊗[R] S)[1/(1 - e)]` — such that `R' → A` is surjective and
`p'A` is a prime of `A` lying over `p'` and, along `S → R' ⊗[R] S → A`, over `q`. -/
@[stacks 00UX "The product decomposition `R' ⊗_R S = A × B` is given by an idempotent `e`, with
`A = (R' ⊗[R] S)[1/e]`, as in Mathlib's `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`
(Tag 00UJ); `p'A` lying over `q` is read along `S → R' ⊗[R] S → A`. See the module docstring."]
public theorem Algebra.exists_etale_isIdempotentElem_surjective_of_isUnramifiedAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (e : R' ⊗[R] S)
      (_ : IsIdempotentElem e),
      Function.Surjective (algebraMap R' (Localization.Away e)) ∧
      (p'.map (algebraMap R' (Localization.Away e))).IsPrime ∧
      (p'.map (algebraMap R' (Localization.Away e))).LiesOver p' ∧
      (p'.map (algebraMap R' (Localization.Away e))).comap
        ((algebraMap (R' ⊗[R] S) (Localization.Away e)).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom) = q := by
  classical
  obtain ⟨R', _, _, _, p', _, _, n, e, he, r, hrp, hrl, hfin, hnm, huniq, hres, hBnq⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
      (R := R) (S := S) p
  obtain ⟨Q, hQ, hQl, hQr⟩ :=
    exists_isPrime_comap_includeLeft_eq_and_comap_includeRight_eq (A := R') (B := S) p p' q
  have : Q.LiesOver p' := ⟨hQl.symm⟩
  have hQu : Algebra.IsUnramifiedAt R' Q := by
    let := Algebra.TensorProduct.rightAlgebra (R := R) (A := R') (B := S)
    have : Q.LiesOver q := ⟨hQr.symm⟩
    exact (Algebra.isUnramifiedAt_iff_isUnramifiedAt_of_isPushout R S R' (R' ⊗[R] S) q Q).mp
      inferInstance
  have hQqf : Algebra.QuasiFiniteAt R' Q := inferInstance
  have hlast : e (Fin.last n) ∈ Q := by
    by_contra h
    exact hBnq Q inferInstance h hQqf
  obtain ⟨i, hi⟩ : ∃ i : Fin n, e i.castSucc ∉ Q := by
    by_contra! h
    have hsum : ∑ j, e j ∈ Q := Q.sum_mem fun j _ ↦ Fin.lastCases hlast h j
    rw [he.complete] at hsum
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr hsum)
  have hQi : Q = r i := huniq i Q hQ inferInstance hi
  subst hQi
  have := hrl i
  have := hfin i
  obtain ⟨b, hbp, hb⟩ := exists_notMem_forall_exists_mul_eq_of_isUnramifiedAt p' (he.idem _)
    (r i) (hnm i) (fun Q hQ hQ' hQ'' ↦ huniq i Q hQ hQ' hQ'') (hres i).2
  have : Algebra.Etale R (Localization.Away b) :=
    Algebra.Etale.comp R R' (Localization.Away b)
  exact exists_etale_isIdempotentElem_of_exists_mul_eq p q p' (Localization.Away b) b hbp
    (he.idem _) hb (r i) (hnm i) hQr

end
