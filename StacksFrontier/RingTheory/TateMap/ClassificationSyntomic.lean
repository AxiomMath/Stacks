module

public import StacksFrontier.RingTheory.Syntomic.SquarePresentation
public import StacksFrontier.RingTheory.TateMap.Classification
public import StacksFrontier.RingTheory.Syntomic.Morphisms

/-!
# Quasi-finite syntomic algebras are locally chart base changes of universal basic charts

Let `A → B` be quasi-finite and syntomic. Around every prime `q` of `B`, and inside any given
principal open `D(b₀) ∋ q`, there is a principal open `D(b) ∋ q` such that every localization of
`B` away from `b` is a chart base change of a quasi-finite basic chart `univChart n d k` of the
universal family. This is the form of Lemma 0FKA used to construct the Tate map of
Proposition 0FKD.

All names are in the namespace `Stacks.TateMap`.

## Main definitions

* `lciOneEquivOfPresentation`: a presentation `S = A[x_1, …, x_n]/(f)` identifies `S` with
  `A[x_1, …, x_n, 1/1]/(f)`.

## Main results

* `exists_classification_of_syntomic`: the classification near a prime.

## References

* [Stacks Project, Tag 0FKA](https://stacks.math.columbia.edu/tag/0FKA)
* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.TateMap

open Stacks.Discriminant

/-- A presentation `S = A[x_1, …, x_n]/(f_1, …, f_n)` identifies `A[x_1, …, x_n, 1/1]/(f)` with
`S`. -/
def lciOneEquivOfPresentation {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {n : ℕ}
    (P : Algebra.Presentation A S (Fin n) (Fin n)) :
    localizedCompleteIntersection A n 1 P.relation ≃ₐ[A] S :=
  letI := (lciOfQuot 1 P.relation).toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P.relation))
      (localizedCompleteIntersection A n 1 P.relation) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((lciOfQuot 1 P.relation).commutes a).symm
  haveI : IsLocalization.Away (1 : MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P.relation))
      (localizedCompleteIntersection A n 1 P.relation) := by
    have := isLocalization_lciOfQuot (1 : MvPolynomial (Fin n) A) P.relation
    rwa [map_one] at this
  ((IsLocalization.atOne (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range P.relation))
      (localizedCompleteIntersection A n 1 P.relation)).restrictScalars A).symm.trans
    ((Ideal.quotientEquivAlgOfEq A P.span_range_relation_eq_ker).trans
      (P.quotientEquiv.restrictScalars A))

/-- **The classification of a quasi-finite syntomic algebra near a prime.** Let `A → B` be
quasi-finite and syntomic, let `q` be a prime of `B` and `b₀ ∉ q`. There are `b ∉ q` divisible by
`b₀`, a positive degree bound `d`, a specialization `φ : univBase n d → A` of the universal
coefficients and a polynomial `k` with `univChart n d k` quasi-finite over `univBase n d`, such
that every localization `B'` of `B` away from `b` is a chart base change of
`univBase n d → univChart n d k` along `φ`. -/
theorem exists_classification_of_syntomic {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] (q : Ideal B) [q.IsPrime] (b₀ : B)
    (hb₀ : b₀ ∉ q) :
    ∃ b : B, b ∉ q ∧ b₀ ∣ b ∧ ∃ (n d : ℕ) (_ : NeZero d)
      (k : MvPolynomial (Fin n) (univBase.{u} n d))
      (φ : univBase.{u} n d →+* A), Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k) ∧
      ∀ (B' : Type u) [CommRing B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
        [IsLocalization.Away b B'],
        letI := φ.toAlgebra
        ∃ (_ : Algebra (univChart n d k) B'),
          Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) A B') := by
  obtain ⟨g, hg, hrg⟩ := Algebra.Syntomic.exists_notMem_isRelativeGlobalCompleteIntersection
    (R := A) q
  let S := Localization.Away (algebraMap B (Localization.Away g) b₀)
  have hS : IsLocalization.Away (b₀ * g) S := inferInstance
  have : Algebra.IsRelativeGlobalCompleteIntersection A S :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_isLocalizationAway
      (algebraMap B (Localization.Away g) b₀)
  have ht : b₀ * g ∉ q := fun h ↦ (Ideal.IsPrime.mem_or_mem ‹_› h).elim hb₀ hg
  have : Algebra.QuasiFinite A S := Algebra.QuasiFinite.of_isLocalization
    (Submonoid.powers (b₀ * g))
  have hdisj : Disjoint (Submonoid.powers (b₀ * g) : Set B) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ hm
    exact ht (‹q.IsPrime›.mem_of_pow_mem m hm)
  have hqS : (q.map (algebraMap B S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (b₀ * g)) S q ‹_› hdisj
  obtain ⟨n, P, -⟩ := Algebra.exists_square_presentation (R := A) (S := S)
    (q.map (algebraMap B S))
  let e := lciOneEquivOfPresentation P
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A n 1 P.relation) :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mpr inferInstance
  let q₁ := (q.map (algebraMap B S)).comap e.toRingHom
  have : q₁.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨d, hd, k, φ, hf, hqf, hk⟩ := exists_classification 1 P.relation q₁
  set s := e (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k))
  have hs : s ∉ q.map (algebraMap B S) := hk
  obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers (b₀ * g)) s
  simp only at hc
  have hu : IsUnit (algebraMap B S ((b₀ * g) ^ m)) :=
    IsLocalization.map_units S (⟨(b₀ * g) ^ m, m, rfl⟩ : Submonoid.powers (b₀ * g))
  have hcq : c ∉ q := by
    intro hcq
    apply hs
    have hmem : s * algebraMap B S ((b₀ * g) ^ m) ∈ q.map (algebraMap B S) := by
      rw [hc]; exact Ideal.mem_map_of_mem _ hcq
    exact (Ideal.IsPrime.mem_or_mem hqS hmem).resolve_right fun h ↦ hqS.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  refine ⟨b₀ * g * c, fun h ↦ (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht hcq,
    ⟨g * c, by ring⟩, n, d, hd, k, φ, hqf, fun B' _ _ _ _ _ ↦ ?_⟩
  let := φ.toAlgebra
  have htu : IsUnit (algebraMap B B' (b₀ * g)) :=
    IsLocalization.Away.isUnit_of_dvd (b₀ * g * c) ⟨c, rfl⟩
  let iSB : Algebra S B' := (IsLocalization.Away.lift (b₀ * g) htu).toAlgebra
  have : IsScalarTower B S B' := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq (b₀ * g) htu x).symm
  have h1 : IsLocalization.Away (algebraMap B S c) B' := isLocalization_away_of_mul (b₀ * g) c
  have hassoc : Associated (algebraMap B S c) s := by
    refine ⟨hu.unit⁻¹, ?_⟩
    rw [← hc, mul_assoc, IsUnit.mul_val_inv, mul_one]
  have h2 : IsLocalization.Away s B' := (IsLocalization.Away.iff_of_associated hassoc).mp h1
  let iLB : Algebra (localizedCompleteIntersection A n 1 P.relation) B' :=
    ((algebraMap S B').comp e.toRingHom).toAlgebra
  have h3 := IsLocalization.isLocalization_of_base_ringEquiv (S := B') (Submonoid.powers s)
    e.symm.toRingEquiv
  rw [Submonoid.map_powers] at h3
  have hes : e.symm.toRingEquiv s =
      algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k) := e.symm_apply_apply _
  rw [hes] at h3
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin n) A)
      (localizedCompleteIntersection A n 1 P.relation) (MvPolynomial.map φ k)) B' := h3
  have : IsScalarTower A (localizedCompleteIntersection A n 1 P.relation) B' :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A B' a = algebraMap S B' (e (algebraMap A _ a))
      rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply A B S,
        ← IsScalarTower.algebraMap_apply B S B', ← IsScalarTower.algebraMap_apply]
  have hk' : IsUnit (algebraMap (localizedCompleteIntersection A n 1 P.relation) B'
      (algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.map φ k))) :=
    IsLocalization.Away.algebraMap_isUnit _
  exact ⟨classificationAlgebra k φ 1 P.relation hf B' hk',
    ⟨classificationOf k φ 1 P.relation hf (MvPolynomial.map φ k) B' hk'⟩⟩

end Stacks.TateMap
