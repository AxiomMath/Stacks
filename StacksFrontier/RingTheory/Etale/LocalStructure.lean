module

import StacksCore.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import StacksFrontier.RingTheory.QuasiFinite.BaseChange
import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Étale local structure of a finite type algebra along a fibre

Let `R → S` be of finite type and let `p` be a prime of `R`. After an étale base change
`R → R'` at a prime `p'` over `p` with `κ(p) = κ(p')`, the base change `R' ⊗[R] S` splits as
`A₁ × ⋯ × Aₙ × B` with each `Aᵢ` finite over `R'` carrying a single prime over `p'`, and with
`R' → B` quasi-finite at no prime over `p'`. This is Stacks 00UK.

The proof is the source's: one splits off the quasi-finite primes of the fibre one at a time by
Stacks 00UJ (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`) and induct. The
induction is on the number of *minimal* primes lying over `p`, which is finite because the fibre
`κ(p) ⊗[R] S` is Noetherian: splitting off a factor replaces `S` by the quotient of `R' ⊗[R] S` by
an idempotent `e`, whose primes over `p'` are, by contraction, the primes over `p'` containing `e`
— a downward closed set of primes, because a prime below a prime containing an idempotent contains
it, so contraction preserves minimality and the minimal prime below the prime that was split off
is lost. Since `κ(p) = κ(p')` the primes over `p` and over `p'` are in order preserving bijection
(`Ideal.fiberIsoOfBijectiveResidueField`), so the count is unchanged by the base change.

## Main results

* `Stacks.Etale.FibreSplitting.solution`: the statement of
  `Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`.

## Implementation notes

The measure the induction runs on is `Stacks.Etale.FibreSplitting.minPrimesOver`, the minimal
elements of `Ideal.primesOver`. Mathlib's `Module.Finite` analogue
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq` inducts on the number of
*all* primes over `p` — which is what `Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem`
counts — but that number is infinite for a merely finite type algebra; the minimal ones are the
right replacement, and no quasi-finiteness enters the measure.

## References

* [StacksProject 00UK](https://stacks.math.columbia.edu/tag/00UK)
-/

namespace Stacks.Etale.FibreSplitting

open TensorProduct



/-- A prime containing the kernel of a surjection `ψ` is the contraction of a prime of the target,
over the same base prime. -/
private lemma exists_isPrime_liesOver_comap_eq_of_ker_le {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (Q : Ideal R) {ψ : A →ₐ[R] B}
    (hψ : Function.Surjective ψ) (q : Ideal A) [hq : q.IsPrime] [q.LiesOver Q]
    (hkq : RingHom.ker ψ.toRingHom ≤ q) :
    ∃ (q' : Ideal B) (_ : q'.IsPrime) (_ : q'.LiesOver Q), q = q'.comap ψ := by
  have hround : (q.map ψ).comap ψ = q := by
    rw [Ideal.comap_map_of_surjective _ hψ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hkq
  have hunder : (q.map ψ).comap (algebraMap R B) = q.comap (algebraMap R A) := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_comap, ← ψ.commutes y, ← Ideal.mem_comap, hround]
  refine ⟨q.map ψ, Ideal.map_isPrime_of_surjective hψ hkq, ⟨?_⟩, hround.symm⟩
  rw [Ideal.under, hunder]
  exact q.over_def Q

section MinPrimesOver

/-- The minimal primes among those lying over `P`, as a subset of `P.primesOver A`. -/
private def minPrimesOver {R : Type*} [CommRing R] (P : Ideal R) (A : Type*) [CommRing A]
    [Algebra R A] : Set ↥(P.primesOver A) := {q | IsMin q}

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private lemma finite_minPrimesOver [Algebra.FiniteType R A] (P : Ideal R) [P.IsPrime] :
    (minPrimesOver P A).Finite := by
  have : Algebra.FiniteType P.ResidueField (P.Fiber A) := inferInstance
  have : IsNoetherianRing (P.Fiber A) := Algebra.FiniteType.isNoetherianRing P.ResidueField _
  have h : minPrimesOver P A =
      (PrimeSpectrum.primesOverOrderIsoFiber R A P) ⁻¹' {x | IsMin x} := by
    ext q
    simp [minPrimesOver, OrderIso.isMin_apply]
  rw [h]
  exact (PrimeSpectrum.finite_setOfPred_isMin (P.Fiber A)).preimage
    (PrimeSpectrum.primesOverOrderIsoFiber R A P).injective.injOn

private lemma exists_mem_minPrimesOver_le (P : Ideal R) [P.IsPrime] (q : ↥(P.primesOver A)) :
    ∃ q' ∈ minPrimesOver P A, q' ≤ q := by
  set e := PrimeSpectrum.primesOverOrderIsoFiber R A P
  obtain ⟨I, hI, hIle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (P.Fiber A)))
    (J := (e q).asIdeal) bot_le
  have hIp : I.IsPrime := hI.1.1
  refine ⟨e.symm ⟨I, hIp⟩, ?_, e.symm_apply_le.mpr hIle⟩
  have : IsMin (⟨I, hIp⟩ : PrimeSpectrum (P.Fiber A)) := by
    rw [PrimeSpectrum.isMin_iff]
    simpa using hI
  simpa [minPrimesOver] using e.symm.isMin_apply.mpr this

private lemma ncard_minPrimesOver_congr {R₂ A₂ : Type*} [CommRing R₂] [CommRing A₂]
    [Algebra R₂ A₂] (P : Ideal R) (P₂ : Ideal R₂)
    (f : ↥(P.primesOver A) ≃o ↥(P₂.primesOver A₂)) :
    (minPrimesOver P A).ncard = (minPrimesOver P₂ A₂).ncard := by
  rw [show minPrimesOver P A = f ⁻¹' minPrimesOver P₂ A₂ by
    ext q; simp [minPrimesOver, f.isMin_apply]]
  rw [← Set.ncard_image_of_injective _ f.injective, Set.image_preimage_eq _ f.surjective]

/-- Contraction along `A → A ⧸ I` is an order embedding of the primes over `P` of `A ⧸ I` into the
primes over `P` of `A`, with image the primes containing `I`. -/
private def primesOverQuotient (P : Ideal R) (I : Ideal A) :
    ↥(P.primesOver (A ⧸ I)) ↪o ↥(P.primesOver A) where
  toFun Q := ⟨Q.1.comap (Ideal.Quotient.mkₐ R I), inferInstance, inferInstance⟩
  inj' _ _ h := Subtype.ext (Ideal.comap_injective_of_surjective _
    (Ideal.Quotient.mkₐ_surjective R I) congr(($h).1))
  map_rel_iff' :=
    Ideal.comap_le_comap_iff_of_surjective _ (Ideal.Quotient.mkₐ_surjective R I) _ _

private lemma mem_range_primesOverQuotient (P : Ideal R) (I : Ideal A)
    {q : ↥(P.primesOver A)} : q ∈ Set.range (primesOverQuotient P I) ↔ I ≤ q.1 := by
  refine ⟨fun ⟨Q, hQ⟩ ↦ hQ ▸ Ideal.mk_ker.symm.trans_le (Ideal.ker_le_comap (K := Q.1) _),
    fun hI ↦ ?_⟩
  have := q.2.1
  have := q.2.2
  obtain ⟨Q, hQ, hQo, hq⟩ := exists_isPrime_liesOver_comap_eq_of_ker_le P
    (Ideal.Quotient.mkₐ_surjective R I) q.1 (Ideal.mk_ker.trans_le hI)
  exact ⟨⟨Q, hQ, hQo⟩, Subtype.ext hq.symm⟩

/-- A prime contained in a prime containing an idempotent contains that idempotent. -/
private lemma mem_of_isIdempotentElem_of_le {e : A} (he : IsIdempotentElem e) {Q Q' : Ideal A}
    [Q.IsPrime] [hQ' : Q'.IsPrime] (hQ : e ∈ Q) (h : Q' ≤ Q) : e ∈ Q' := by
  have h0 : e * (1 - e) = 0 := by rw [mul_one_sub, he.eq, sub_self]
  refine (hQ'.mem_or_mem (h0 ▸ Q'.zero_mem)).resolve_right fun h1 ↦ ?_
  exact ‹Q.IsPrime›.one_notMem (by simpa using Q.add_mem hQ (h h1))

/-- An order embedding whose range is a lower set preserves minimality. -/
private lemma IsMin.of_orderEmbedding {α β : Type*} [Preorder α] [Preorder β] {f : α ↪o β}
    (hf : IsLowerSet (Set.range f)) {a : α} (ha : IsMin a) : IsMin (f a) := by
  intro b hb
  obtain ⟨a', rfl⟩ := hf hb ⟨a, rfl⟩
  exact f.map_rel_iff.mpr (ha (f.map_rel_iff.mp hb))

/-- Splitting off the factor cut out by an idempotent `e` loses at least one minimal prime over
`P`: the primes over `P` of `A ⧸ (e)` are the primes over `P` containing `e`, a downward closed
family of primes, and it misses a minimal prime below any prime over `P` avoiding `e`. -/
private lemma ncard_minPrimesOver_quotient_lt (P : Ideal R) [P.IsPrime] {e : A}
    (he : IsIdempotentElem e) (P' : Ideal A) [P'.IsPrime] [P'.LiesOver P] (heP' : e ∉ P')
    (hfin : (minPrimesOver P A).Finite) :
    (minPrimesOver P (A ⧸ Ideal.span {e})).ncard < (minPrimesOver P A).ncard := by
  set F := primesOverQuotient P (Ideal.span {e} : Ideal A) with hF
  have hlower : IsLowerSet (Set.range F) := by
    intro q q' hq' hq
    rw [hF, mem_range_primesOverQuotient, Ideal.span_le, Set.singleton_subset_iff] at hq ⊢
    exact mem_of_isIdempotentElem_of_le he hq hq'
  obtain ⟨M, hM, hMle⟩ := exists_mem_minPrimesOver_le P (Ideal.primesOver.mk P P')
  rw [← Set.ncard_image_of_injective _ F.injective]
  refine Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr ⟨?_, M, hM, ?_⟩) hfin
  · rintro _ ⟨Q, hQ, rfl⟩
    exact IsMin.of_orderEmbedding hlower hQ
  · rintro ⟨Q, -, rfl⟩
    have hmem : Ideal.span {e} ≤ (F Q).1 := (mem_range_primesOverQuotient P _).mp ⟨Q, rfl⟩
    exact heP' (hMle (hmem (Ideal.mem_span_singleton_self e)))

end MinPrimesOver

section Away

/-- For an idempotent `a`, the localization away from `a` is the quotient by `1 - a`. -/
private noncomputable def awayAlgEquivQuotient {A : Type*} [CommRing A] {a : A}
    (ha : IsIdempotentElem a) : Localization.Away a ≃ₐ[A] A ⧸ Ideal.span {1 - a} :=
  have : IsLocalization.Away a (A ⧸ Ideal.span {1 - a}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem ha
  IsLocalization.algEquiv (.powers a) _ _

/-- For an idempotent `a`, finiteness of the localization away from `a` over a base ring is
finiteness of the quotient by `1 - a`. -/
private lemma finite_away_iff_finite_quotient {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {a : A} (ha : IsIdempotentElem a) :
    Module.Finite R (Localization.Away a) ↔ Module.Finite R (A ⧸ Ideal.span {1 - a}) :=
  ⟨fun _ ↦ Module.Finite.equiv ((awayAlgEquivQuotient ha).restrictScalars R).toLinearEquiv,
    fun _ ↦ Module.Finite.equiv ((awayAlgEquivQuotient ha).restrictScalars R).symm.toLinearEquiv⟩

/-- Finiteness of the factor cut out by an idempotent transfers along any identification of the
complementary quotients. -/
private lemma finite_away_of_quotientEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {a : A} {b : B} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b)
    (f : (A ⧸ Ideal.span {1 - a}) ≃ₗ[R] B ⧸ Ideal.span {1 - b})
    (H : Module.Finite R (Localization.Away a)) : Module.Finite R (Localization.Away b) :=
  have := (finite_away_iff_finite_quotient ha).mp H
  (finite_away_iff_finite_quotient hb).mpr (Module.Finite.equiv f)

/-- An algebra equivalence carries the factor cut out by an idempotent to the factor cut out by
its image. -/
private lemma finite_away_of_algEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {a : A} (ha : IsIdempotentElem a)
    [Module.Finite R (Localization.Away a)] : Module.Finite R (Localization.Away (f a)) :=
  finite_away_of_quotientEquiv ha (ha.map f)
    (Ideal.quotientEquivAlg _ _ f (by rw [Ideal.map_span]; simp)).toLinearEquiv ‹_›

/-- Splitting off an orthogonal idempotent `ε` does not change the factor cut out by `a`: if the
image of `a` in `A ⧸ (ε)` cuts out a finite factor, so does `a`. -/
private lemma finite_away_of_finite_away_quotient {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {ε a : A} (ha : IsIdempotentElem a) (h : ε * a = 0)
    (H : Module.Finite R (Localization.Away (Ideal.Quotient.mk (Ideal.span {ε}) a))) :
    Module.Finite R (Localization.Away a) :=
  have hle : Ideal.span {ε} ≤ Ideal.span {1 - a} := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton']
    exact ⟨ε, by linear_combination -h⟩
  have hmap : Ideal.span {1 - Ideal.Quotient.mk (Ideal.span {ε}) a} =
      (Ideal.span {1 - a}).map (Ideal.Quotient.mkₐ R (Ideal.span {ε})) := by
    rw [Ideal.map_span]; simp
  finite_away_of_quotientEquiv (ha.map _) ha
    ((Ideal.quotientEquivAlgOfEq R hmap).trans
      (DoubleQuot.quotQuotEquivQuotOfLEₐ R hle)).toLinearEquiv H

/-- The factor cut out by an idempotent stays finite after a base change of the base ring. -/
private lemma finite_away_rTensor {R R' R'' S : Type*} [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing S] [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
    [Algebra R S] {a : R' ⊗[R] S} (ha : IsIdempotentElem a)
    [Module.Finite R' (Localization.Away a)] :
    Module.Finite R''
      (Localization.Away (Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'') a)) := by
  have h₁ : Module.Finite R' ((R' ⊗[R] S) ⧸ Ideal.span {1 - a}) :=
    (finite_away_iff_finite_quotient ha).mp ‹_›
  have h₂ : Module.Finite R'' ((R'' ⊗[R] S) ⧸ Ideal.span
      {(Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'') : R' ⊗[R] S →ₐ[R'] _) (1 - a)}) :=
    Module.Finite.equiv (Algebra.tensorQuotientTensorEquiv R'' (1 - a)).toLinearEquiv
  rw [map_sub, map_one] at h₂
  rw [finite_away_iff_finite_quotient (ha.map _)]
  exact h₂

end Away

/-- Bijectivity of the residue field extension is transitive in a tower: this is Stacks 00UK's
`κ(p) = κ(p')` propagating along a composite of étale base changes. -/
private lemma bijective_residueFieldMapₐ_trans {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (p : Ideal R)
    (P : Ideal A) (Q : Ideal B) [p.IsPrime] [P.IsPrime] [Q.IsPrime] [P.LiesOver p] [Q.LiesOver P]
    [Q.LiesOver p]
    (h₁ : Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R A) (P.over_def p)))
    (h₂ : Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId A B) (Q.over_def P))) :
    Function.Bijective (Ideal.ResidueField.mapₐ p Q (Algebra.ofId R B) (Q.over_def p)) := by
  convert h₂.comp h₁
  rw [← @AlgHom.coe_restrictScalars' R A, ← AlgHom.coe_comp]; congr 1; ext

/-- A prime avoiding an element `x` that the kernel generator `ε` annihilates descends along a
surjection `ψ` with kernel `(ε)`: it is the contraction of a prime over the same base prime, still
avoiding the image of `x`. -/
private lemma exists_isPrime_liesOver_comap_eq_of_notMem {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (Q : Ideal R) {ψ : A →ₐ[R] B}
    (hψ : Function.Surjective ψ) {ε : A} (hker : RingHom.ker ψ.toRingHom = Ideal.span {ε})
    (q : Ideal A) [hq : q.IsPrime] [q.LiesOver Q] {x : A} (hx : ε * x = 0) (hxq : x ∉ q) :
    ∃ (q' : Ideal B) (_ : q'.IsPrime) (_ : q'.LiesOver Q), q = q'.comap ψ ∧ ψ x ∉ q' := by
  obtain ⟨q', _, _, hq'⟩ := exists_isPrime_liesOver_comap_eq_of_ker_le Q hψ q (by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff]
    exact (hq.mem_or_mem (hx ▸ q.zero_mem)).resolve_right hxq)
  exact ⟨q', inferInstance, inferInstance, hq', fun h ↦ hxq (hq' ▸ h)⟩

/-- Re-index a family of complete orthogonal idempotents over `Option (Fin (n + 1))` as one over
`Fin (n + 2)`, the distinguished idempotent first. -/
private lemma completeOrthogonalIdempotents_fin_cons {A : Type*} [CommRing A] {n : ℕ} {x : A}
    {f : Fin (n + 1) → A}
    (h : CompleteOrthogonalIdempotents fun t ↦ Option.rec (motive := fun _ ↦ A) x f t) :
    CompleteOrthogonalIdempotents (Fin.cons x f : Fin (n + 1 + 1) → A) :=
  have hE : (fun t ↦ Option.rec (motive := fun _ ↦ A) x f t) ∘ finSuccEquiv (n + 1) =
      Fin.cons x f := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  hE ▸ (CompleteOrthogonalIdempotents.equiv (finSuccEquiv (n + 1))).mpr h

/-- The conclusion of Stacks 00UK, as a predicate on `R`, `S` and `p`. -/
private def Conclusion (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      Function.Bijective (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)) ∧
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      ∀ (q : Ideal (R' ⊗[R] S)) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q

/-- If `R → S` is quasi-finite at no prime over `p`, then `R' = R` and the trivial decomposition
already solve the problem. -/
private lemma base {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (h : ∀ (q : Ideal S) (_ : q.IsPrime), q.LiesOver p → ¬ Algebra.QuasiFiniteAt R q) :
    Conclusion R S p := by
  refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, ⟨rfl⟩, 0, 1,
    ⟨⟨by simp [IsIdempotentElem], by
      simp only [Nat.reduceAdd, Pi.one_apply, mul_one, Subsingleton.pairwise]⟩, by simp⟩,
    nofun, nofun, nofun, ?_, nofun, nofun, nofun, ?_⟩
  · rw! [Algebra.ofId_self, Ideal.ResidueField.mapₐ_id]; exact Function.bijective_id
  · intro q _ hover _ hqf
    have := hover
    have := hqf
    exact h (q.comap (Algebra.TensorProduct.lid R S).symm.toAlgHom) inferInstance inferInstance
      (Algebra.QuasiFiniteAt.comap_algEquiv (R := R) q (Algebra.TensorProduct.lid R S).symm)

/-- The inductive step: having split off one quasi-finite prime by Stacks 00UJ, a solution for the
complementary factor gives a solution for `S`. -/
private lemma step {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R')
    [P.IsPrime] [P.LiesOver p] (e : R' ⊗[R] S) (he : IsIdempotentElem e)
    (P' : Ideal (R' ⊗[R] S)) [P'.IsPrime] [P'.LiesOver P] (heP' : e ∉ P')
    (hpP : Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
    (hfinE : Module.Finite R' (Localization.Away e))
    (H : ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
    (IH : Conclusion R' (R' ⊗[R] S ⧸ Ideal.span {e}) P) :
    Conclusion R S p := by
  obtain ⟨R'', _, _, _, Q, _, _, n, e', he', r, hrp, hrQ, hPQ, hfin', hr', Huniq, Hlast⟩ := IH
  let _ : Algebra R R'' := .compHom _ (algebraMap R R')
  have : IsScalarTower R R' R'' := .of_algebraMap_eq' rfl
  have : Q.LiesOver p := .trans _ P _
  have hpQ := bijective_residueFieldMapₐ_trans p P Q hpP hPQ
  let φ : R' ⊗[R] S →ₐ[R'] R'' ⊗[R] S := Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'')
  let e₁ : R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[R''] R'' ⊗[R] S ⧸ Ideal.span {φ e} :=
    Algebra.tensorQuotientTensorEquiv R'' e
  obtain ⟨e'', he'', he''e'⟩ := CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
    (Ideal.Quotient.mk (Ideal.span {φ e})) (φ e) (he.map φ) (by simp) (e₁ ∘ e')
    (he'.map e₁.toRingHom) fun _ ↦ Ideal.Quotient.mk_surjective _
  let ψ : R'' ⊗[R] S →ₐ[R''] R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) :=
    e₁.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R'' (Ideal.span {φ e}))
  have hψs : Function.Surjective ψ := e₁.symm.surjective.comp Ideal.Quotient.mk_surjective
  have hmk : ∀ i, Ideal.Quotient.mk (Ideal.span {φ e}) (e'' i) = e₁ (e' i) :=
    fun i ↦ (congr_fun he''e' i).symm
  have hψe : ∀ i, ψ (e'' i) = e' i := fun i ↦ by
    show e₁.symm (Ideal.Quotient.mk (Ideal.span {φ e}) (e'' i)) = e' i
    rw [hmk, e₁.symm_apply_apply]
  have hker : RingHom.ker ψ.toRingHom = Ideal.span {φ e} := by
    ext x
    have hx : ψ x = e₁.symm (Ideal.Quotient.mk (Ideal.span {φ e}) x) := rfl
    rw [RingHom.mem_ker]
    simp [hx, map_eq_zero_iff _ e₁.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have he''idem : ∀ i, IsIdempotentElem (e'' i) := fun i ↦ he''.idem (some i)
  have hortho : ∀ i, φ e * e'' i = 0 := fun k ↦ he''.ortho (i := none) (j := some k) (by simp)
  let P'φ := (Ideal.fiberIsoOfBijectiveResidueField hpQ).symm
    (Ideal.fiberIsoOfBijectiveResidueField hpP ⟨P', ‹_›, ‹_›⟩)
  have : P'φ.1.IsPrime := P'φ.2.1
  have : P'φ.1.LiesOver Q := P'φ.2.2
  have : P'φ.1.LiesOver P := .trans _ Q _
  have : (P'φ.1.comap φ.toRingHom).LiesOver P := inferInstanceAs ((P'φ.1.comap φ).LiesOver P)
  have hP'φ : P'φ.1.comap φ.toRingHom = P' := by
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpP
    rw [Ideal.comap_comap]
    convert Ideal.comap_fiberIsoOfBijectiveResidueField_symm hpQ _
    · ext; simp [φ]
    · simp; rfl
  have hcomap : ∀ J : Ideal (R'' ⊗[R] S),
      (J.comap φ.toRingHom).comap
        (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom =
      J.comap (Algebra.TensorProduct.includeRight (R := R) (A := R'') (B := S)).toRingHom := by
    intro J
    rw [Ideal.comap_comap]
    congr 1
    ext x
    simp [φ]
  refine ⟨R'', inferInstance, inferInstance, .comp R R' R'', Q, inferInstance, inferInstance,
    n + 1, Fin.cons (φ e) e'', completeOrthogonalIdempotents_fin_cons he'',
    Fin.cons P'φ.1 fun j ↦ (r j).comap ψ, ?_, ?_, hpQ, ?_, ?_, ?_, ?_⟩
  · refine Fin.cases ?_ fun j ↦ ?_
    · simpa only [Fin.cons_zero] using P'φ.2.1
    · simp only [Fin.cons_succ]; infer_instance
  · refine Fin.cases ?_ fun j ↦ ?_
    · simpa only [Fin.cons_zero] using P'φ.2.2
    · simp only [Fin.cons_succ]; infer_instance
  · refine Fin.cases ?_ fun j ↦ ?_
    · rw [Fin.castSucc_zero, Fin.cons_zero]
      exact finite_away_rTensor (R'' := R'') he
    · rw [← Fin.succ_castSucc, Fin.cons_succ]
      have := hfin' j
      have h₁ : Module.Finite R'' (Localization.Away (e₁ (e' j.castSucc))) :=
        finite_away_of_algEquiv e₁ (he'.idem _)
      rw [← hmk] at h₁
      exact finite_away_of_finite_away_quotient (he''idem _) (hortho _) h₁
  · refine Fin.cases ?_ fun j ↦ ?_
    · simp only [Fin.castSucc_zero, Fin.cons_zero]
      exact fun hmem ↦ heP' (hP'φ ▸ (show e ∈ P'φ.1.comap φ.toRingHom from hmem))
    · simpa only [← Fin.succ_castSucc, Fin.cons_succ, Ideal.mem_comap, hψe] using hr' j
  · refine Fin.cases ?_ fun j ↦ ?_
    · intro q hq hqQ hmem
      simp only [Fin.castSucc_zero, Fin.cons_zero] at hmem ⊢
      have : q.LiesOver P := .trans _ Q _
      have : (q.comap φ.toRingHom).LiesOver P := inferInstanceAs ((q.comap φ).LiesOver P)
      have hqφ : q.comap φ.toRingHom = P' := H _ inferInstance inferInstance hmem
      refine Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpQ _ _ ?_
      rw [← hcomap q, ← hcomap P'φ.1, hqφ, hP'φ]
    · intro q hq hqQ hmem
      simp only [← Fin.succ_castSucc, Fin.cons_succ] at hmem ⊢
      obtain ⟨q', hq'p, hq'Q, hqq', hnot⟩ :=
        exists_isPrime_liesOver_comap_eq_of_notMem Q hψs hker q (hortho _) hmem
      rw [hqq', Huniq j q' hq'p hq'Q (by rw [← hψe]; exact hnot)]
  · intro q hq hqQ hmem hqf
    rw [← Fin.succ_last, Fin.cons_succ] at hmem
    obtain ⟨q', hq'p, hq'Q, hqq', hnot⟩ :=
      exists_isPrime_liesOver_comap_eq_of_notMem Q hψs hker q (hortho _) hmem
    exact Hlast q' hq'Q (by rw [← hψe]; exact hnot)
      (Algebra.QuasiFiniteAt.of_surjectiveOnStalks q ψ
        (RingHom.surjectiveOnStalks_of_surjective hψs) q' hqq')

private lemma key : ∀ (n : ℕ) {R : Type u} {S : Type max u v} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime],
    (minPrimesOver p S).ncard ≤ n → Conclusion R S p := by
  intro n
  induction n with
  | zero =>
    intro R S _ _ _ _ p _ hn
    refine base p fun q hq hover hqf => ?_
    obtain ⟨M, hM, -⟩ := exists_mem_minPrimesOver_le p ⟨q, hq, hover⟩
    rw [(Set.ncard_eq_zero (finite_minPrimesOver p)).mp (Nat.le_zero.mp hn)] at hM
    simp at hM
  | succ n IH =>
    intro R S _ _ _ _ p _ hn
    by_cases hex : ∃ (q : Ideal S) (_ : q.IsPrime), q.LiesOver p ∧ Algebra.QuasiFiniteAt R q
    · obtain ⟨q, hq, hover, hqf⟩ := hex
      obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hpP, hfinE, H⟩ :=
        Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
      refine step p R' P e he P' heP' hpP hfinE H (IH P ?_)
      have h1 : (minPrimesOver P (R' ⊗[R] S ⧸ Ideal.span {e})).ncard
          < (minPrimesOver P (R' ⊗[R] S)).ncard :=
        ncard_minPrimesOver_quotient_lt P he P' heP' (finite_minPrimesOver P)
      have h2 : (minPrimesOver P (R' ⊗[R] S)).ncard = (minPrimesOver p S).ncard :=
        ncard_minPrimesOver_congr P p (Ideal.fiberIsoOfBijectiveResidueField hpP)
      omega
    · exact base p fun q hq hover hqf => hex ⟨q, hq, hover, hqf⟩

/-- The statement of Stacks 00UK,
`Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`, proved by splitting
off the quasi-finite primes of the fibre one at a time, by induction on the number of minimal
primes over `p`. -/
public theorem solution {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      Function.Bijective (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)) ∧
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      ∀ (q : Ideal (R' ⊗[R] S)) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q := by
  have : Algebra.FiniteType R (ULift.{u} S) :=
    .of_surjective (ULift.algEquiv (R := R) (A := S)).symm.toAlgHom
      (ULift.algEquiv (R := R) (A := S)).symm.surjective
  obtain ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hP, hfin, hP', H, Hlast⟩ :=
    key (minPrimesOver p (ULift.{u} S)).ncard (R := R) (S := ULift.{u} S) p le_rfl
  let e₁ : R' ⊗[R] S ≃ₐ[R'] R' ⊗[R] ULift.{u} S :=
    Algebra.TensorProduct.congr .refl ULift.algEquiv.symm
  refine ⟨R', _, _, ‹_›, P, ‹_›, ‹_›, n, e₁.symm ∘ e, he.map _,
    fun i => (P' i).comap e₁.toAlgHom, inferInstance, inferInstance, hP, ?_, by simpa,
    fun i q _ _ hq => ?_, fun q _ _ hq => ?_⟩
  · intro i
    have := hfin i
    exact finite_away_of_algEquiv (e₁.symm.restrictScalars R') (he.idem _)
  · have := H i (q.comap e₁.symm.toAlgHom) inferInstance inferInstance (by simpa using hq)
    simp [← this, Ideal.comap_comapₐ]
  · intro hqf
    exact Hlast (q.comap e₁.symm.toAlgHom) inferInstance (by simpa using hq)
      (Algebra.QuasiFiniteAt.comap_algEquiv (R := R') q e₁.symm)

end Stacks.Etale.FibreSplitting

/-!
# Étale local structure of a finite type algebra along a fibre

Let `R → S` be a ring map of finite type and let `p` be a prime of `R`. The fibre ring
`κ(p) ⊗[R] S` is of finite type over the field `κ(p)`, hence Noetherian, so its spectrum has
only finitely many isolated closed points; these are exactly the primes `q` of `S` over `p` at
which `R → S` is quasi-finite. After an étale base change `R → R'` at a prime `p'` of `R'` over
`p` with `κ(p) = κ(p')`, each of them splits off as a factor which is *finite* over `R'` and
contains a single prime over `p'`:
`R' ⊗[R] S = A₁ × ⋯ × Aₙ × B`, with `R' → B` quasi-finite at no prime over `p'`.

## Main results

* `Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`: the
  decomposition above, for a finite type algebra.

## Implementation notes

The product decomposition is recorded by a family of complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factor cut out by an idempotent being the localization away
from it: `Aᵢ = (R' ⊗[R] S)[1/e i]` for `i < n` and `B = (R' ⊗[R] S)[1/e n]`. This is the spelling
of the neighbouring `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` and
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`, and it keeps every ring
in the statement in a fixed universe; an equivalence
`R' ⊗[R] S ≃ₐ[R'] (∀ i, A i) × B` onto a product of newly quantified types says the same thing.

Primes of a factor are named by the primes of `R' ⊗[R] S` they come from: the primes of
`(R' ⊗[R] S)[1/e i]` are the primes `q` of `R' ⊗[R] S` with `e i ∉ q`, compatibly with lying
over `p'`, and `Algebra.QuasiFiniteAt R' q` depends only on the local ring of `R' ⊗[R] S` at `q`,
which is the local ring of the factor at the corresponding prime. So "exactly one prime of `Aᵢ`
lies over `p'`" is the pair of assertions that `r i` is a prime over `p'` with `e i ∉ r i` and
that any such prime equals `r i`; and "`R' → B` is quasi-finite at no prime over `p'`" is
non-quasi-finiteness at every prime `q` over `p'` with `e n ∉ q`.

Under the stronger hypothesis `Module.Finite R S` the last factor has no prime over `p'`
whatsoever, which is the form
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq` takes in Mathlib. For a
merely finite type algebra `B` does have primes over `p'` — for `S = R[X]` there is nothing to
split off and `B = R' ⊗[R] S` — and non-quasi-finiteness is what remains true.

Faithfulness. (1) No hypothesis is dead: `Algebra.FiniteType R S` is what makes the fibre
Noetherian, so that only finitely many factors are needed, and `p.IsPrime` is what `κ(p)` and
"lying over `p`" refer to; every remaining hypothesis is the data `R`, `S`, `p` of the source.
(2) The scalars and base are the source's: the étale algebra and the decomposition are over `R'`,
the finiteness of `Aᵢ` is over `R'` and not over a localization of it, and the base change is
`R' ⊗[R] S` along `R → R'`. (3) The maps the source names are pinned: the residue field
extension is the canonical `Ideal.ResidueField.mapₐ p p' (Algebra.ofId R R')`, whose bijectivity
is `κ(p) = κ(p')`, and the primes of the factors are pinned as primes of `R' ⊗[R] S` avoiding the
corresponding idempotent, not merely postulated to exist. (4) The instantiation is not
degenerate: for `S = R × R[X]` and any prime `p` one may take `R' = R`, `p' = p`, `n = 1`,
`e = ![(1, 0), (0, 1)]`, `A₁ = R` finite over `R` with the single prime `p × R[X]` over `p`, and
`B = R[X]`, quasi-finite over `R` at no prime at all by `Polynomial.not_quasiFiniteAt`; taking
`R` a field and `S = R[X]` gives a witness with `n = 0`.

## References

* [StacksProject 00UK](https://stacks.math.columbia.edu/tag/00UK)

## Tags

étale, quasi-finite, finite type, complete orthogonal idempotents, fibre, residue field
-/

@[expose] public section



open TensorProduct

/-- **Étale local structure of a finite type algebra along a fibre** (Stacks 00UK). Let `S` be a
finite type `R`-algebra and `p` a prime of `R`. There are an étale `R`-algebra `R'`, a prime `p'`
of `R'` lying over `p` with `κ(p) = κ(p')`, and a decomposition
`R' ⊗[R] S = A₁ × ⋯ × Aₙ × B` — given by complete orthogonal idempotents `e 0, …, e n`, with
`Aᵢ = (R' ⊗[R] S)[1/e i]` and `B = (R' ⊗[R] S)[1/e n]` — such that each `Aᵢ` is finite over `R'`
and has exactly one prime `r i` lying over `p'`, while `R' → B` is quasi-finite at no prime lying
over `p'`. -/
@[stacks 00UK "The product decomposition is given by complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factors being `(R' ⊗[R] S)[1/e i]`, and the primes of a factor
are named by the primes of `R' ⊗[R] S` avoiding the corresponding idempotent. See the module
docstring."]
public theorem Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      Function.Bijective (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)) ∧
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      ∀ (q : Ideal (R' ⊗[R] S)) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q := by apply Stacks.Etale.FibreSplitting.solution

end

/-!
# Étale local structure of a finite type algebra along a fibre, with inseparable residue fields

Let `R → S` be of finite type and let `p` be a prime of `R`. After an étale base change `R → R'`
at a prime `p'` over `p`, the base change `R' ⊗[R] S` splits as `A₁ × ⋯ × Aₙ × B` with each `Aᵢ`
finite over `R'` carrying a single prime `rᵢ` over `p'` whose residue field is purely inseparable
over `κ(p')`, and with `R' → B` quasi-finite at no prime over `p'`. This is Stacks 00UL.

The proof is the source's: two étale extensions. The first one, produced by Stacks 00UD from a
finite Galois extension `L/κ(p)` into which the separable part of each of the finitely many
quasi-finite `κ(q)/κ(p)` embeds, makes all those residue field extensions purely inseparable; the
second one is Stacks 00UK, which does not change them.

## Main results

* `Stacks.Etale.InseparableFibreSplitting.solution`: the statement of
  `Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable`.

## Implementation notes

The decomposition asserted by the source is `Stacks.Etale.InseparableFibreSplitting.IsSplitFibre R'
T p'`, stated for an arbitrary `R'`-algebra `T` rather than only for a base change; the conclusion
of Stacks 00UL is then `Stacks.Etale.InseparableFibreSplitting.Conclusion`, the existence of an
étale `R'` and a prime `p'` over `p` with `IsSplitFibre R' (R' ⊗[R] S) p'`. Stating it for an
arbitrary `T` is what makes `Stacks.Etale.InseparableFibreSplitting.IsSplitFibre.of_algEquiv` — the
decomposition depends only on the `R'`-algebra `T` up to isomorphism — available, and that lemma is
the whole of the composition of the two étale extensions:
`Stacks.Etale.InseparableFibreSplitting.conclusion_of_baseChange` transports the conclusion for `R₁
⊗[R] S` over `R₁` along `R'' ⊗[R₁] (R₁ ⊗[R] S) ≃ R'' ⊗[R] S`.

The two halves of the source's proof are
`Stacks.Etale.InseparableFibreSplitting.exists_etale_purelyInseparableFibre` (the first étale
extension) and `Stacks.Etale.InseparableFibreSplitting.conclusion_of_purelyInseparableFibre`
(Stacks 00UK together with the residue field bookkeeping).

Three lemmas carry the mathematics of the halves.

* `Stacks.Etale.InseparableFibreSplitting.exists_pow_mem_range_of_splits` is the field theory of
  the first half: if the minimal polynomial over `F` of every separable element of `E` splits in
  `L`, then under any pair of `F`-compatible maps `E → M` and `L → M` every element of `E` acquires
  a `p`-power in the image of `L`. Applied to `κ(p) ⊆ κ(q)` and `L ≅ κ(p₁)` inside `κ(𝔮)`, this is
  exactly the assertion that the first étale extension makes the fibre purely inseparable.
* `Stacks.Etale.InseparableFibreSplitting.isPurelyInseparable_residueField_baseChange` is the
  second half: pure inseparability of `κ(q)/κ(p)` passes to `κ(𝔮)/κ(p')` for a prime `𝔮` of
  `R' ⊗[R] S` over `p'` and over `q`. Its proof is the residue field square
  `Stacks.Etale.InseparableFibreSplitting.residueFieldMap_comp_algebraMap` fed into the criterion
  `Stacks.Etale.InseparableFibreSplitting.isPurelyInseparable_residueField_of_forall_pow_mem`,
  which is used by both halves: `κ(𝔮)/κ(p')` is purely inseparable as soon as every element of
  `κ(q)` becomes purely inseparable in `κ(𝔮)`, because `κ(𝔮)` is generated as a field by the
  images of `R'` and of `S` (`Stacks.Etale.InseparableFibreSplitting.eq_top_of_forall_mem`).
* `Stacks.Etale.InseparableFibreSplitting.exists_finite_isSeparable_splits` produces the field `L`
  of the source's proof: for finitely many finite extensions `E i` of `K` there is a finite
  separable `L/K` in which the minimal polynomial of every separable element of every `E i` splits,
  namely the normal closure inside `SeparableClosure K` of the compositum of the separable closures
  of `K` in the `E i`. The extensions in question are the residue fields of the finitely many
  primes over `p` at which `R → S` is quasi-finite; they are finitely many because such a prime is
  minimal over `p`, which is `Stacks.Etale.InseparableFibreSplitting.finite_quasiFinitePrimesOver`.

## References

* [StacksProject 00UL](https://stacks.math.columbia.edu/tag/00UL)
-/

namespace Stacks.Etale.InseparableFibreSplitting

open TensorProduct



attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-! ### Field theory -/

/-! ### Finiteness of the quasi-finite primes of a fibre -/

/-- A prime over `p` at which `R → S` is quasi-finite is minimal over `p`
(`Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`), so a finite type algebra has only finitely many
of them. These are the primes `q₁, …, qₙ` of the source's proof of Stacks 00UL. -/
private lemma finite_quasiFinitePrimesOver {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    {q : ↥(p.primesOver S) | haveI := q.2.1; Algebra.QuasiFiniteAt R q.1}.Finite := by
  refine (Stacks.Etale.FibreSplitting.finite_minPrimesOver (A := S) p).subset fun q hq => ?_
  have := q.2.1
  have := q.2.2
  have : Algebra.QuasiFiniteAt R q.1 := hq
  intro b hb
  have := b.2.1
  have := b.2.2
  have h : b.1 = q.1 := Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) hb
    ((b.1.over_def p).symm.trans (q.1.over_def p))
  exact le_of_eq (Subtype.ext h).symm

/-! ### Residue fields of a base change -/

section BaseChange

variable {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']

/-- The residue field map induced by an algebra map `A → B` at a prime `J` of `B` and the prime
`I` of `A` it lies over is the structure map of the canonical `κ(I)`-algebra structure on
`κ(J)`. -/
private lemma algebraMap_residueField_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] [J.LiesOver I]
    [Algebra (Localization.AtPrime I) (Localization.AtPrime J)]
    [Localization.AtPrime.IsLiesOverAlgebra I J] :
    (algebraMap I.ResidueField J.ResidueField) =
      Ideal.ResidueField.map I J (algebraMap A B) (J.over_def I) :=
  Ideal.ResidueField.ringHom_ext <| by
    ext x
    simp [← IsScalarTower.algebraMap_apply]

/-- The exponential characteristic of `κ(p')` is that of `κ(p)`, for a prime `p'` lying over
`p`. -/
@[ega "0 21.1.3" "more general"]
private lemma expChar_residueField (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime]
    [p'.LiesOver p] (e : ℕ) [ExpChar p.ResidueField e] : ExpChar p'.ResidueField e :=
  expChar_of_injective_ringHom
    (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)).injective e

/-- A prime `𝔮` of `R' ⊗[R] S` at which `R' → R' ⊗[R] S` is quasi-finite and which lies over `p`
comes from a prime `q` of `S` lying over `p` at which `R → S` is quasi-finite. -/
private lemma exists_comap_includeRight_quasiFiniteAt [Algebra.FiniteType R S] (p : Ideal R)
    (𝔮 : Ideal (R' ⊗[R] S)) [𝔮.IsPrime] [𝔮.LiesOver p] (hqf : Algebra.QuasiFiniteAt R' 𝔮) :
    ∃ (q : Ideal S) (_ : q.IsPrime) (_ : q.LiesOver p),
      q = 𝔮.comap (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom ∧
        Algebra.QuasiFiniteAt R q := by
  refine ⟨_, Ideal.comap_isPrime _ _, ⟨?_⟩, rfl,
    (Algebra.quasiFiniteAt_baseChange_iff R' _ 𝔮 rfl).mp hqf⟩
  rw [Ideal.under, Ideal.comap_comap,
    show (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom.comp
      (algebraMap R S) = algebraMap R (R' ⊗[R] S) from by ext t; simp]
  exact 𝔮.over_def p

/-- The residue field at a prime `𝔮` of `B` is generated as a field by the image of `B`: it is the
fraction field of `B ⧸ 𝔮`. -/
private lemma mem_of_forall_algebraMap_mem {B : Type*} [CommRing B] (𝔮 : Ideal B) [𝔮.IsPrime]
    (E : Subfield 𝔮.ResidueField) (h : ∀ b : B, algebraMap B 𝔮.ResidueField b ∈ E)
    (x : 𝔮.ResidueField) : x ∈ E := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ 𝔮) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  simpa using E.div_mem (h a) (h b)

/-- **The residue field at a prime of `R' ⊗[R] S` is generated by the images of `R'` and `S`.** A
subfield of `κ(𝔮)` containing both images is everything. -/
private lemma eq_top_of_forall_mem (𝔮 : Ideal (R' ⊗[R] S)) [𝔮.IsPrime]
    (E : Subfield 𝔮.ResidueField)
    (hleft : ∀ r : R', algebraMap (R' ⊗[R] S) 𝔮.ResidueField (algebraMap R' _ r) ∈ E)
    (hright : ∀ s : S, algebraMap (R' ⊗[R] S) 𝔮.ResidueField
      (Algebra.TensorProduct.includeRight s) ∈ E) : E = ⊤ := by
  refine top_unique fun x _ => mem_of_forall_algebraMap_mem 𝔮 E (fun b => ?_) x
  induction b with
  | zero => simp
  | tmul r s =>
    rw [show (r ⊗ₜ[R] s : R' ⊗[R] S) =
      algebraMap R' (R' ⊗[R] S) r * Algebra.TensorProduct.includeRight s from by
        simp [Algebra.TensorProduct.tmul_mul_tmul], map_mul]
    exact mul_mem (hleft r) (hright s)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- **Criterion for the residue field of a prime of a base change to be purely inseparable.** Let
`𝔮` be a prime of `R' ⊗[R] S` lying over a prime `p'` of `R'` and over a prime `q` of `S`. If every
element of `κ(q)` has an `e`-th power root in the image of `κ(p')` in `κ(𝔮)`, where `e` is the
exponential characteristic, then `κ(𝔮)/κ(p')` is purely inseparable. -/
private lemma isPurelyInseparable_residueField_of_forall_pow_mem (p' : Ideal R') [p'.IsPrime]
    (𝔮 : Ideal (R' ⊗[R] S)) [𝔮.IsPrime] [𝔮.LiesOver p'] (e : ℕ) [ExpChar p'.ResidueField e]
    {q : Ideal S} [q.IsPrime]
    (hq : q = 𝔮.comap (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom)
    (H : ∀ x : q.ResidueField, ∃ n : ℕ,
      Ideal.ResidueField.map q 𝔮 _ hq x ^ e ^ n ∈
        (algebraMap p'.ResidueField 𝔮.ResidueField).range) :
    IsPurelyInseparable p'.ResidueField 𝔮.ResidueField := by
  rw [isPurelyInseparable_iff_pow_mem p'.ResidueField e]
  intro x
  rw [← mem_perfectClosure_iff_pow_mem e]
  have h : (perfectClosure p'.ResidueField 𝔮.ResidueField).toSubfield = ⊤ := by
    refine eq_top_of_forall_mem 𝔮 _ (fun r => ?_) (fun s => ?_)
    · rw [IntermediateField.mem_toSubfield, mem_perfectClosure_iff_pow_mem e]
      refine ⟨0, algebraMap R' p'.ResidueField r, ?_⟩
      rw [pow_zero, pow_one, algebraMap_residueField_eq p' 𝔮]
      simp
    · rw [IntermediateField.mem_toSubfield, mem_perfectClosure_iff_pow_mem e]
      obtain ⟨n, hn⟩ := H (algebraMap S q.ResidueField s)
      rw [Ideal.ResidueField.map_algebraMap q 𝔮 _ hq s] at hn
      exact ⟨n, hn⟩
  rw [← IntermediateField.mem_toSubfield, h]
  trivial

/-- **The residue field square of a base change**: the square of residue fields at `p`, `p'`, `q`
and a prime `𝔮` of `R' ⊗[R] S` over `p'` and over `q` commutes. -/
private lemma residueFieldMap_comp_algebraMap (p : Ideal R) [p.IsPrime] (p' : Ideal R')
    [p'.IsPrime] [p'.LiesOver p] (𝔮 : Ideal (R' ⊗[R] S)) [𝔮.IsPrime] [𝔮.LiesOver p']
    {q : Ideal S} [q.IsPrime] [q.LiesOver p]
    (hq : q = 𝔮.comap (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom) :
    (Ideal.ResidueField.map q 𝔮 _ hq).comp (algebraMap p.ResidueField q.ResidueField) =
      (algebraMap p'.ResidueField 𝔮.ResidueField).comp
        (Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p)) := by
  refine Ideal.ResidueField.ringHom_ext ?_
  ext t
  rw [algebraMap_residueField_eq p q, algebraMap_residueField_eq p' 𝔮]
  simp [IsScalarTower.algebraMap_apply R R' (R' ⊗[R] S)]

/-- **Pure inseparability of a residue field extension in a fibre passes to a base change.** If `𝔮`
is a prime of `R' ⊗[R] S` lying over `p'` in `R'` and over `q` in `S`, and if `κ(q)/κ(p)` is purely
inseparable, then so is `κ(𝔮)/κ(p')`. This is the residue field content of the second étale
extension in the source's proof of Stacks 00UL. -/
private lemma isPurelyInseparable_residueField_baseChange (p : Ideal R) [p.IsPrime]
    (p' : Ideal R') [p'.IsPrime] [p'.LiesOver p] (𝔮 : Ideal (R' ⊗[R] S)) [𝔮.IsPrime]
    [𝔮.LiesOver p'] {q : Ideal S} [q.IsPrime] [q.LiesOver p]
    (hq : q = 𝔮.comap (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom)
    [IsPurelyInseparable p.ResidueField q.ResidueField] :
    IsPurelyInseparable p'.ResidueField 𝔮.ResidueField := by
  have : ExpChar p.ResidueField (ringExpChar p.ResidueField) := ringExpChar.expChar _
  have := expChar_residueField p p' (ringExpChar p.ResidueField)
  refine isPurelyInseparable_residueField_of_forall_pow_mem p' 𝔮
    (ringExpChar p.ResidueField) hq fun x => ?_
  obtain ⟨m, y, hy⟩ :=
    (isPurelyInseparable_iff_pow_mem p.ResidueField (ringExpChar p.ResidueField)).mp
      inferInstance x
  refine ⟨m, Ideal.ResidueField.map p p' (algebraMap R R') (p'.over_def p) y, ?_⟩
  rw [← map_pow, ← hy]
  exact (RingHom.congr_fun (residueFieldMap_comp_algebraMap p p' 𝔮 hq) y).symm

end BaseChange

/-! ### Quasi-finiteness at a prime of a finite factor -/

/-- If the factor of `T` cut out by `a` is finite over `R'`, then `R' → T` is quasi-finite at every
prime of `T` not containing `a`. -/
private lemma quasiFiniteAt_of_finite_away {R' T : Type*} [CommRing R'] [CommRing T]
    [Algebra R' T] {a : T} (𝔮 : Ideal T) [𝔮.IsPrime] (ha : a ∉ 𝔮)
    [Module.Finite R' (Localization.Away a)] : Algebra.QuasiFiniteAt R' 𝔮 := by
  have hd : Disjoint ((Submonoid.powers a : Submonoid T) : Set T) (𝔮 : Set T) := by
    simp only [Set.disjoint_left, SetLike.mem_coe]
    rintro x ⟨n, rfl⟩ hx
    exact ha (Ideal.IsPrime.mem_of_pow_mem ‹𝔮.IsPrime› n hx)
  have hPp : (Ideal.map (algebraMap T (Localization.Away a)) 𝔮).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) _ 𝔮 ‹_› hd
  have hcomap : Ideal.comap (algebraMap T (Localization.Away a))
      (Ideal.map (algebraMap T (Localization.Away a)) 𝔮) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) _ ‹𝔮.IsPrime› hd
  have h : IsLocalization (Ideal.comap (algebraMap T (Localization.Away a))
      (Ideal.map (algebraMap T (Localization.Away a)) 𝔮)).primeCompl
      (Localization.AtPrime (Ideal.map (algebraMap T (Localization.Away a)) 𝔮)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers a) (S := Localization.Away a)
      (T := Localization.AtPrime (Ideal.map (algebraMap T (Localization.Away a)) 𝔮))
      (Ideal.map (algebraMap T (Localization.Away a)) 𝔮)
  have hsub : (Ideal.comap (algebraMap T (Localization.Away a))
      (Ideal.map (algebraMap T (Localization.Away a)) 𝔮)).primeCompl = 𝔮.primeCompl := by
    ext x; simp [Ideal.mem_primeCompl_iff, hcomap]
  rw [hsub] at h
  have : IsLocalization 𝔮.primeCompl
      (Localization.AtPrime (Ideal.map (algebraMap T (Localization.Away a)) 𝔮)) := h
  let e : Localization.AtPrime 𝔮 ≃ₐ[T]
      Localization.AtPrime (Ideal.map (algebraMap T (Localization.Away a)) 𝔮) :=
    IsLocalization.algEquiv 𝔮.primeCompl _ _
  exact (Algebra.QuasiFinite.iff_of_algEquiv (R := R') (e.restrictScalars R')).mpr inferInstance

/-! ### The decomposition, and the two halves of the source's proof -/

/-- **The decomposition of Stacks 00UL for an `R'`-algebra `T` along a prime `p'` of `R'`:** `T`
splits as `A₁ × ⋯ × Aₙ × B`, recorded by complete orthogonal idempotents `e` with
`Aᵢ = T[1/e i]`, with each `Aᵢ` finite over `R'` carrying a single prime `r i` over `p'` whose
residue field is finite purely inseparable over `κ(p')`, and with `R' → B` quasi-finite at no prime
over `p'`. -/
private def IsSplitFibre (R' : Type*) (T : Type*) [CommRing R'] [CommRing T] [Algebra R' T]
    (p' : Ideal R') [p'.IsPrime] : Prop :=
  ∃ (n : ℕ) (e : Fin (n + 1) → T) (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal T)
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal T), q.IsPrime → q.LiesOver p' → e i.castSucc ∉ q → q = r i) ∧
      (∀ i : Fin n, letI := Localization.AtPrime.algebraOfLiesOver p' (r i)
        Module.Finite p'.ResidueField (r i).ResidueField ∧
          IsPurelyInseparable p'.ResidueField (r i).ResidueField) ∧
      ∀ (q : Ideal T) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q

/-- **The decomposition depends only on the `R'`-algebra `T` up to isomorphism.** -/
private lemma IsSplitFibre.of_algEquiv {R' T T' : Type*} [CommRing R'] [CommRing T] [CommRing T']
    [Algebra R' T] [Algebra R' T'] {p' : Ideal R'} [p'.IsPrime] (f : T ≃ₐ[R'] T')
    (h : IsSplitFibre R' T p') : IsSplitFibre R' T' p' := by
  obtain ⟨n, e, he, r, hrp, hro, hfin, hnot, huniq, hres, hlast⟩ := h
  refine ⟨n, ⇑f ∘ e, he.map (f : T →+* T'), fun i => (r i).comap f.symm.toAlgHom,
    fun i => inferInstance, fun i => inferInstance, fun i => ?_, fun i => ?_, ?_, fun i => ?_, ?_⟩
  · -- each factor stays finite over `R'`
    have := hfin i
    exact Stacks.Etale.FibreSplitting.finite_away_of_algEquiv f (he.idem _)
  · -- the idempotent avoids the transported prime
    simpa using hnot i
  · -- the transported prime is the only one
    intro i q hq hqo hne
    show q = (r i).comap f.symm.toAlgHom
    rw [← huniq i (q.comap f.toAlgHom) inferInstance inferInstance (by simpa using hne)]
    ext z
    simp
  · -- the residue field extension is unchanged
    have := hrp i
    have := hro i
    obtain ⟨h1, h2⟩ := hres i
    have := h1
    have := h2
    let E : ((r i).comap f.symm.toAlgHom).ResidueField ≃ₐ[p'.ResidueField]
        (r i).ResidueField :=
      Ideal.residueFieldAlgEquiv' p' ((r i).comap f.symm.toAlgHom) (r i) f.symm rfl
    exact ⟨Module.Finite.equiv E.symm.toLinearEquiv, E.symm.isPurelyInseparable⟩
  · -- the remaining factor is still nowhere quasi-finite
    intro q hq hqo hne hcontra
    have := hcontra
    exact hlast (q.comap f.toAlgHom) inferInstance (by simpa using hne)
      (Algebra.QuasiFiniteAt.comap_algEquiv q f)

/-- The conclusion of Stacks 00UL for the data `R`, `S`, `p`: an étale `R`-algebra `R'` and a prime
`p'` of `R'` over `p` for which the fibre of `R' ⊗[R] S` over `p'` splits. -/
private def Conclusion (R : Type u) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p), IsSplitFibre R' (R' ⊗[R] S) p'

/-- `PurelyInseparableFibre R S p` says that the residue field extension `κ(q)/κ(p)` is purely
inseparable at every prime `q` of `S` over `p` at which `R → S` is quasi-finite. -/
private def PurelyInseparableFibre (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Prop :=
  ∀ (q : Ideal S) (_ : q.IsPrime) (_ : q.LiesOver p), Algebra.QuasiFiniteAt R q →
    letI := Localization.AtPrime.algebraOfLiesOver p q
    IsPurelyInseparable p.ResidueField q.ResidueField

/-- **The first étale extension.** After an étale base change the residue field extensions at the
quasi-finite primes of the fibre are purely inseparable. This is the first half of the source's
proof of Stacks 00UL: one applies Stacks 00UD to a finite Galois extension of `κ(p)` containing
the separable part of each of the finitely many quasi-finite `κ(q)`. -/
private lemma exists_etale_purelyInseparableFibre {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Algebra.Etale R R₁) (p₁ : Ideal R₁)
      (_ : p₁.IsPrime) (_ : p₁.LiesOver p), PurelyInseparableFibre R₁ (R₁ ⊗[R] S) p₁ := by
  classical
  have : Finite {q : ↥(p.primesOver S) // Algebra.QuasiFiniteAt R q.1} :=
    (finite_quasiFinitePrimesOver p).to_subtype
  have : ∀ i : {q : ↥(p.primesOver S) // Algebra.QuasiFiniteAt R q.1},
      Algebra.QuasiFiniteAt R (i.1.1) := fun i => i.2
  -- the field `L` of the source's proof
  obtain ⟨L, _, _, _, _, hL⟩ :=
    Stacks.Etale.ResidueFieldRealization.exists_finite_isSeparable_splits (K := p.ResidueField)
      (fun i : {q : ↥(p.primesOver S) // Algebra.QuasiFiniteAt R q.1} => (i.1.1).ResidueField)
  obtain ⟨R₁, _, _, _, p₁, _, _, ε, hε⟩ :=
    Algebra.exists_etale_liesOver_residueFieldRingEquiv p L
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, p₁, inferInstance, inferInstance, ?_⟩
  intro 𝔮 h𝔮 h𝔮o hqf
  have h𝔮p : 𝔮.LiesOver p := Ideal.LiesOver.trans (P := p₁) 𝔮 p
  -- the prime `q` of `S` under `𝔮`
  obtain ⟨q, hqp, hqo, hqdef, hqqf⟩ := exists_comap_includeRight_quasiFiniteAt p 𝔮 hqf
  have : ExpChar p.ResidueField (ringExpChar p.ResidueField) := ringExpChar.expChar _
  have := expChar_residueField p p₁ (ringExpChar p.ResidueField)
  -- the map `L → κ(𝔮)` given by `ε⁻¹` and `κ(p₁) → κ(𝔮)`, which agrees with `κ(p) → κ(q) → κ(𝔮)`
  set χ : L →+* 𝔮.ResidueField :=
    (algebraMap p₁.ResidueField 𝔮.ResidueField).comp (ε.symm : L →+* p₁.ResidueField) with hχdef
  have hχ : χ.comp (algebraMap p.ResidueField L) =
      (Ideal.ResidueField.map q 𝔮 _ hqdef).comp (algebraMap p.ResidueField q.ResidueField) := by
    rw [residueFieldMap_comp_algebraMap p p₁ 𝔮 hqdef, hχdef, RingHom.comp_assoc]
    congr 1
    refine RingHom.ext fun z => ?_
    have hz := RingHom.congr_fun hε z
    simp only [RingHom.coe_comp, Function.comp_apply] at hz
    rw [RingHom.comp_apply, ← hz]
    simp
  refine isPurelyInseparable_residueField_of_forall_pow_mem p₁ 𝔮
    (ringExpChar p.ResidueField) hqdef fun x => ?_
  obtain ⟨n, y, hy⟩ :=
    Stacks.Etale.ResidueFieldRealization.exists_pow_mem_range_of_splits
      (ringExpChar p.ResidueField) _ χ hχ (hL ⟨⟨q, hqp, hqo⟩, hqqf⟩) x
  exact ⟨n, ε.symm y, by simpa [hχdef] using hy⟩

/-- **The second étale extension.** Stacks 00UK, together with the observation that it does not
change the residue field extensions in the fibre. -/
private lemma conclusion_of_purelyInseparableFibre {R : Type u} {S : Type w} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (H : PurelyInseparableFibre R S p) : Conclusion R S p := by
  obtain ⟨R', hcr, halg, het, p', hpp, hpo, n, e, he, r, hrp, hro, -, hfin, hnot,
    huniq, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt
      (R := R) (S := S) p
  refine ⟨R', hcr, halg, het, p', hpp, hpo, n, e, he, r, hrp, hro, hfin, hnot, huniq,
    fun i => ?_, hlast⟩
  have hrpi : (r i).IsPrime := hrp i
  have hroi : (r i).LiesOver p' := hro i
  have hrop : (r i).LiesOver p := Ideal.LiesOver.trans (P := p') (r i) p
  have hqf : Algebra.QuasiFiniteAt R' (r i) := quasiFiniteAt_of_finite_away (r i) (hnot i)
  -- the prime `q` of `S` under `r i`
  obtain ⟨q, hqp, hqo, hqdef, hqqf⟩ := exists_comap_includeRight_quasiFiniteAt p (r i) hqf
  have : IsPurelyInseparable p.ResidueField q.ResidueField := H q hqp hqo hqqf
  exact ⟨inferInstance, isPurelyInseparable_residueField_baseChange p p' (r i) hqdef⟩

/-- Reading the conclusion for `R₁ ⊗[R] S` over `R₁` as the conclusion for `S` over `R`: the
composition of two étale extensions is étale, and the decomposition transports along
`R₂ ⊗[R₁] (R₁ ⊗[R] S) ≃ R₂ ⊗[R] S`. -/
private lemma conclusion_of_baseChange {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) (R₁ : Type u) [CommRing R₁] [Algebra R R₁]
    [Algebra.Etale R R₁] (p₁ : Ideal R₁) [p₁.LiesOver p]
    (h : Conclusion R₁ (R₁ ⊗[R] S) p₁) : Conclusion R S p := by
  obtain ⟨R₂, _, _, _, p₂, _, _, h⟩ := h
  let : Algebra R R₂ := Algebra.compHom _ (algebraMap R R₁)
  have : IsScalarTower R R₁ R₂ := .of_algebraMap_eq' rfl
  have : Algebra.Etale R R₂ := .comp R R₁ R₂
  have : p₂.LiesOver p := .trans _ p₁ _
  exact ⟨R₂, inferInstance, inferInstance, inferInstance, p₂, inferInstance, inferInstance,
    h.of_algEquiv (Algebra.TensorProduct.cancelBaseChange R R₁ R₂ R₂ S)⟩

/-- The statement of Stacks 00UL,
`Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable`: a first étale
extension makes the residue field extensions at the quasi-finite primes of the fibre purely
inseparable, and Stacks 00UK applied over it gives the decomposition. -/
public theorem solution {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      (∀ i : Fin n, letI := Localization.AtPrime.algebraOfLiesOver p' (r i)
        Module.Finite p'.ResidueField (r i).ResidueField ∧
          IsPurelyInseparable p'.ResidueField (r i).ResidueField) ∧
      ∀ (q : Ideal (R' ⊗[R] S)) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q := by
  show Conclusion R S p
  obtain ⟨R₁, _, _, _, p₁, _, _, H⟩ := exists_etale_purelyInseparableFibre (S := S) p
  exact conclusion_of_baseChange p R₁ p₁ (conclusion_of_purelyInseparableFibre p₁ H)

end Stacks.Etale.InseparableFibreSplitting

/-!
# Étale local structure of a finite type algebra along a fibre, with inseparable residue fields

Let `R → S` be a ring map of finite type and let `p` be a prime of `R`. The fibre ring
`κ(p) ⊗[R] S` is of finite type over the field `κ(p)`, hence Noetherian, so its spectrum has only
finitely many isolated closed points; these are exactly the primes `q` of `S` over `p` at which
`R → S` is quasi-finite. After an étale base change `R → R'` at a prime `p'` of `R'` over `p`,
each of them splits off as a factor which is *finite* over `R'`, contains a single prime `rᵢ` over
`p'`, and has `κ(rᵢ)/κ(p')` purely inseparable:
`R' ⊗[R] S = A₁ × ⋯ × Aₙ × B`, with `R' → B` quasi-finite at no prime over `p'`.

This sharpens Tag 00UK, which produces the same decomposition with `κ(p) = κ(p')` but says nothing
about the residue fields `κ(rᵢ)`: to make them purely inseparable over `κ(p')` one first enlarges
`κ(p)` to a finite Galois extension containing the separable part of each `κ(qᵢ)` (Tag 00UD), and
that enlargement is incompatible with `κ(p) = κ(p')`. Geometrically, the fibre of
`Spec (R' ⊗[R] S) → Spec R'` over `p'` has `n` isolated closed points, each of them a
*purely inseparable* point of the fibre, and its remaining part is nowhere quasi-finite.

## Main results

* `Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable`: the
  decomposition above, for a finite type algebra.

## Implementation notes

The product decomposition is recorded by a family of complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factor cut out by an idempotent being the localization away
from it: `Aᵢ = (R' ⊗[R] S)[1/e i]` for `i < n` and `B = (R' ⊗[R] S)[1/e n]`. This is the spelling
of the neighbouring `Algebra.exists_etale_completeOrthogonalIdempotents_finite_not_quasiFiniteAt`
(Tag 00UK) and of Mathlib's
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`, and it keeps every ring in
the statement in a fixed universe; an equivalence
`R' ⊗[R] S ≃ₐ[R'] (∀ i, A i) × B` onto a product of newly quantified types says the same thing.

Primes of a factor are named by the primes of `R' ⊗[R] S` they come from: the primes of
`(R' ⊗[R] S)[1/e i]` are the primes `q` of `R' ⊗[R] S` with `e i ∉ q`, compatibly with lying over
`p'`, and both `Algebra.QuasiFiniteAt R' q` and the residue field `κ(q)` depend only on the local
ring of `R' ⊗[R] S` at `q`, which is the local ring of the factor at the corresponding prime. So
"exactly one prime of `Aᵢ` lies over `p'`" is the pair of assertions that `r i` is a prime over
`p'` with `e i ∉ r i` and that any such prime equals `r i`; "`κ(rᵢ)/κ(p')` is a finite purely
inseparable field extension" is the same statement for `r i` read in `R' ⊗[R] S`; and
"`R' → B` is quasi-finite at no prime over `p'`" is non-quasi-finiteness at every prime `q` over
`p'` with `e n ∉ q`.

The extension `κ(p') → κ(r i)` is the canonical one, `Localization.localRingHom` along
`algebraMap R' (R' ⊗[R] S)`, introduced as an algebra structure by
`Localization.AtPrime.algebraOfLiesOver` — the same device `Ideal.inertiaDeg` uses, and pinned by
`Localization.AtPrime.IsLiesOverAlgebra`. The residue field taken is that of the prime `r i` of
`R' ⊗[R] S` rather than of the corresponding prime of the factor `Aᵢ`; the two agree, by the
previous paragraph.

Finiteness of `κ(rᵢ)/κ(p')` is stated alongside pure inseparability, as in the source, although it
already follows from the first two items: `Aᵢ` finite over `R'` with a unique prime over `p'` is
quasi-finite at `rᵢ`, whence `Algebra.WeaklyQuasiFiniteAt.finite_residueField`.

Mathlib's lemma carrying the tag 00UL,
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`, is the weakening of
Tag 00UK to `Module.Finite R S`; it asserts `κ(p) = κ(p')` and no separability property, so it is
neither weaker nor stronger than this statement.

Faithfulness. (1) No hypothesis is dead: `Algebra.FiniteType R S` is what makes the fibre
Noetherian, so that finitely many factors suffice, and `p.IsPrime` is what `κ(p)` and "lying over
`p`" refer to; every remaining hypothesis is the data `R`, `S`, `p` of the source. (2) The scalars
and base are the source's: the étale algebra is over `R` and not over a localization of it, the
decomposition and the finiteness of `Aᵢ` are over `R'`, the residue field extensions are over
`κ(p')`, and the base change is `R' ⊗[R] S` along `R → R'`. (3) The maps the source names are
pinned: `κ(rᵢ)/κ(p')` is the canonical residue field extension described above, and the primes of
the factors are pinned as primes of `R' ⊗[R] S` avoiding the corresponding idempotent, not merely
postulated to exist. (4) The instantiation is not degenerate: for `R = 𝔽ₚ(t)`,
`S = R[X]/(X ^ p - t) × R[Y]` and `p = 0` one may take `R' = R`, `p' = p`, `n = 1`,
`e = ![(1, 0), (0, 1)]`, so that `A₁ = R[X]/(X ^ p - t)` is a field, finite over `R`, with unique
prime `r₁ = 0` over `p'` and `κ(r₁)/κ(p')` purely inseparable of degree `p`, while `B = R[Y]` is
quasi-finite over `R` at no prime at all by `Polynomial.not_quasiFiniteAt`. A witness where the
étale extension is unavoidable: `R = ℚ`, `S = ℚ[X]/(X ^ 2 + 1)`, `p = 0`; here `κ(q)/κ(p)` is
separable of degree `2`, so `R' = ℚ` cannot work, while `R' = S` gives `S ⊗[ℚ] S ≅ S × S`, `n = 2`
and `B = 0`. Taking `R` a field and `S = R[X]` gives a witness with `n = 0`.

## References

* [Stacks Project, Tag 00UL](https://stacks.math.columbia.edu/tag/00UL)

## Tags

étale, quasi-finite, finite type, purely inseparable, complete orthogonal idempotents, fibre,
residue field
-/

@[expose] public section



open TensorProduct

/-- **Étale local structure of a finite type algebra along a fibre** (Stacks 00UL). Let `S` be a
finite type `R`-algebra and `p` a prime of `R`. There are an étale `R`-algebra `R'`, a prime `p'`
of `R'` lying over `p`, and a decomposition `R' ⊗[R] S = A₁ × ⋯ × Aₙ × B` — given by complete
orthogonal idempotents `e 0, …, e n`, with `Aᵢ = (R' ⊗[R] S)[1/e i]` and `B = (R' ⊗[R] S)[1/e n]`
— such that each `Aᵢ` is finite over `R'` and has exactly one prime `r i` lying over `p'`, each
residue field extension `κ(r i)/κ(p')` is finite purely inseparable, and `R' → B` is quasi-finite
at no prime lying over `p'`. -/
@[stacks 00UL "The product decomposition is given by complete orthogonal idempotents
`e : Fin (n + 1) → R' ⊗[R] S`, the factors being `(R' ⊗[R] S)[1/e i]`, and the primes of a factor
are named by the primes of `R' ⊗[R] S` avoiding the corresponding idempotent. Unlike Tag 00UK
this does not assert `κ(p) = κ(p')`, which the source's proof gives up in order to control the
residue fields. See the module docstring."]
public theorem Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (p' : Ideal R')
      (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (r : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      (∀ i : Fin n, Module.Finite R' (Localization.Away (e i.castSucc))) ∧
      (∀ i : Fin n, e i.castSucc ∉ r i) ∧
      (∀ (i : Fin n) (q : Ideal (R' ⊗[R] S)), q.IsPrime → q.LiesOver p' →
        e i.castSucc ∉ q → q = r i) ∧
      (∀ i : Fin n, letI := Localization.AtPrime.algebraOfLiesOver p' (r i)
        Module.Finite p'.ResidueField (r i).ResidueField ∧
          IsPurelyInseparable p'.ResidueField (r i).ResidueField) ∧
      ∀ (q : Ideal (R' ⊗[R] S)) [q.IsPrime], q.LiesOver p' → e (Fin.last n) ∉ q →
        ¬ Algebra.QuasiFiniteAt R' q := by apply Stacks.Etale.InseparableFibreSplitting.solution

end
