module

public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.Smoothing.ReductionToBaseField
public import StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution
public import StacksFrontier.RingTheory.Smoothing.TwistedQuotientClosure

/-!
# Popescu's theorem

A regular ring map `R → Λ` of Noetherian rings makes `Λ` a filtered colimit of smooth
`R`-algebras.

## Main results

* `Stacks.Smoothing.indSmooth_of_isRegularRingMap`: Popescu's theorem.

## Implementation notes

The proof is the source's. Lemma `07F5` (`indSmooth_of_indSmooth_of_field_base`) reduces the
statement to a field base, and over a field the factorizations are produced by Noetherian
induction on the ideal `𝔥_A = √(H_{A/k} Λ)`: either `𝔥_A = Λ`, and Lemma `07EU` already gives a
smooth factorization, or a prime `q` minimal over `𝔥_A` is resolved — in characteristic zero by
Lemma `07FE`, in characteristic `p > 0` by Lemma `07FJ` — and the resolution strictly enlarges
`𝔥_A`, so the induction hypothesis applies to it.

Lemma `07FJ` is `Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`, proved in
`StacksFrontier/RingTheory/Smoothing/TwistedQuotientClosure.lean` out of the twenty-six items of
the source's argument; its statement is the predicate
`Stacks.Smoothing.CanBeResolvedInPositiveCharacteristic` of
`StacksFrontier/RingTheory/Smoothing/LocalSmoothingSituation.lean`, where it sits upstream of both
its proof and this file. Everything else in the argument is proved here.

One step of the source's proof of 07FJ is not justified by the source's text — the λ-choice in
the proof of Stacks 07FH — and **the repair is due to Brian Nugent**; see
`StacksFrontier/RingTheory/Smoothing/InseparableResidueField.lean`. Popescu's theorem therefore
rests on that repair.

## References

* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.Smoothing

universe u

section Field

/-- Over a field of characteristic zero every field extension is separable: the base is perfect,
so each finitely generated subextension is separably generated. -/
private theorem isSeparableExtension_of_ringChar_eq_zero (k K : Type u) [Field k] [Field K]
    [Algebra k K] (h : ringChar k = 0) : Algebra.IsSeparableExtension k K := by
  let : CharP k 0 := h ▸ inferInstanceAs (CharP k (ringChar k))
  let : CharZero k := CharP.charP_to_charZero k
  refine ⟨fun F _ ↦ ⟨?_⟩⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  exact ⟨s, hs, hsep⟩

/-- A regular ring map out of a field is the same thing as geometric regularity of its target:
the only prime of the base is `⊥`, whose residue field is the base itself, so the finite
extensions tested by `IsRegularRingMap` are those of the criterion `0381`. -/
private theorem isGeometricallyRegular_of_isRegularRingMap {k Λ : Type u} [Field k] [CommRing Λ]
    [Algebra k Λ] (hregular : IsRegularRingMap k Λ) : Algebra.IsGeometricallyRegular k Λ := by
  refine ⟨fun K _ _ _ ↦ ?_⟩
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k Λ).2
  intro K _ instAlg _ _
  let p : Ideal k := ⊥
  let : p.IsPrime := inferInstance
  let κ := p.ResidueField
  let e : k ≃ₐ[k] κ := p.algEquivResidueFieldOfField
  have heval (x : k) : e x = algebraMap k κ x := by simpa using e.commutes x
  let : Algebra κ K := ((algebraMap k K).comp e.symm.toAlgHom).toAlgebra
  let : IsScalarTower k κ K := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap k K x = algebraMap k K (e.symm (e x))
    rw [e.symm_apply_apply]
  have hmaps : RingHom.comp (algebraMap κ K) (algebraMap k κ) = @algebraMap k K _ _ instAlg := by
    ext x
    exact (IsScalarTower.algebraMap_apply k κ K x).symm
  let : Module.Finite κ K :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl K) (by
      ext x
      change algebraMap κ K (e x) = @algebraMap k K _ _ instAlg x
      rw [heval]
      exact RingHom.congr_fun hmaps x)
  let : Algebra k K := ((algebraMap κ K).comp (algebraMap k κ)).toAlgebra
  have halgebra : (inferInstance : Algebra k K) = instAlg :=
    Algebra.algebra_ext _ _ fun x ↦ RingHom.congr_fun hmaps x
  exact halgebra ▸ (hregular.2 p K).2

/-- **Noetherian induction on `𝔥_A`.** Every map `A → Λ` from a finitely presented `k`-algebra
to a Noetherian geometrically regular `k`-algebra factors through a smooth `k`-algebra.

The characteristic-`p` step is Lemma `07FJ`,
`Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`. -/
private theorem exists_smooth_factorization_of_isGeometricallyRegular
    (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] :
    ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra A Λ] [IsScalarTower k A Λ]
      [Algebra.FinitePresentation k A],
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Algebra A B) (_ : Algebra B Λ),
        IsScalarTower k A B ∧ IsScalarTower A B Λ ∧ IsScalarTower k B Λ ∧ Algebra.Smooth k B := by
  classical
  -- `Λ` is regular, being the base change of itself along `k → k`.
  have hregΛ : IsRegularRing Λ := by
    let : IsRegularRing (k ⊗[k] Λ) :=
      Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct k
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k Λ).toRingEquiv
  -- The statement to be proved by induction, indexed by the value of `𝔥_A`.
  let P : Ideal Λ → Prop := fun J ↦
    ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra A Λ] [IsScalarTower k A Λ]
      [Algebra.FinitePresentation k A],
      (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical = J →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B) (_ : Algebra A B) (_ : Algebra B Λ),
        IsScalarTower k A B ∧ IsScalarTower A B Λ ∧ IsScalarTower k B Λ ∧ Algebra.Smooth k B
  have hP : ∀ J : Ideal Λ, P J := by
    intro J
    induction J using WellFoundedGT.induction with
    | ind J ih =>
      intro A _ _ _ _ _ hJ
      by_cases htop : J = ⊤
      · -- `𝔥_A = Λ`: Lemma `07EU` gives a smooth factorization outright.
        exact exists_smooth_factorization_of_singularIdeal_map_eq_top k A Λ
          (Ideal.radical_eq_top.mp (hJ.trans htop))
      -- Otherwise pick a prime `q` minimal over `𝔥_A` and resolve the chain there.
      obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes (I := J) htop
      let : q.IsPrime := hq.1.1
      have hJq : J ≤ q := hq.1.2
      have hqRad :
          q ∈ (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical.minimalPrimes := by
        rw [hJ]; exact hq
      have hresolve : CanBeResolved k A Λ q := by
        by_cases hchar : ringChar k = 0
        · -- Characteristic zero: `Λ_q` is a regular local ring and `κ(q)/k` is separable, so
          -- Lemma `07FE` applies.
          let : IsRegularLocalRing (Localization.AtPrime q) :=
            IsRegularRing.isRegularLocalRing_of_isLocalization q (Localization.AtPrime q)
          let : Algebra.IsSeparableExtension k q.ResidueField :=
            isSeparableExtension_of_ringChar_eq_zero k q.ResidueField hchar
          exact canBeResolved_of_isRegularLocalRing_of_isSeparableExtension k A Λ q hqRad
        · -- Characteristic `p > 0`: this is Lemma `07FJ`.
          exact canBeResolvedInPositiveCharacteristic k A Λ (ringChar k)
            (Nat.pos_of_ne_zero hchar) q hqRad
      obtain ⟨B, _, _, _, _, _, _, _, _, hIncl, hNotBelow⟩ := hresolve
      -- `𝔥_B` contains `𝔥_A` and is not contained in `q`, while `𝔥_A ⊆ q`; so `𝔥_A < 𝔥_B`.
      have hstrict : J < (Ideal.map (algebraMap B Λ) (singularIdeal k B)).radical := by
        refine lt_of_le_of_ne (hJ ▸ hIncl) fun heq ↦ hNotBelow ?_
        rw [← heq]
        exact hJq
      obtain ⟨C, _, _, _, _, _, _, _, hSmooth⟩ := ih _ hstrict B rfl
      let : Algebra A C := (RingHom.comp (algebraMap B C) (algebraMap A B)).toAlgebra
      let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
      have hTowerkAC : IsScalarTower k A C :=
        IsScalarTower.of_algebraMap_eq' (by
          rw [IsScalarTower.algebraMap_eq k B C, IsScalarTower.algebraMap_eq k A B]
          simp [IsScalarTower.algebraMap_eq A B C, RingHom.comp_assoc])
      have hTowerACΛ : IsScalarTower A C Λ :=
        IsScalarTower.of_algebraMap_eq' (by
          rw [IsScalarTower.algebraMap_eq A B Λ, IsScalarTower.algebraMap_eq B C Λ,
            IsScalarTower.algebraMap_eq A B C]
          simp [RingHom.comp_assoc])
      exact ⟨C, _, _, _, _, hTowerkAC, hTowerACΛ, inferInstance, hSmooth⟩
  intro A _ _ _ _ _
  exact hP _ A rfl

/-- A regular ring map from a field to a Noetherian ring makes the target a filtered colimit of
smooth algebras. This is the case of Popescu's theorem that the reduction of Lemma `07F5` needs,
and the Noetherian induction above is its proof. -/
private theorem indSmooth_of_isRegularRingMap_of_field
    (k : Type u) [Field k] (Λ : Type u) [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (hregular : IsRegularRingMap k Λ) : IndSmooth k Λ := by
  let : Algebra.IsGeometricallyRegular k Λ := isGeometricallyRegular_of_isRegularRingMap hregular
  rw [indSmooth_iff_exists_factorization]
  intro A _ algA hFP φ
  let := algA
  let : Algebra.FinitePresentation k A := hFP
  let : Algebra A Λ := φ.toRingHom.toAlgebra
  let : IsScalarTower k A Λ := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  obtain ⟨B, _, _, _, _, _, _, _, hSmooth⟩ :=
    exists_smooth_factorization_of_isGeometricallyRegular k Λ A
  refine ⟨B, inferInstance, inferInstance, hSmooth, (Algebra.ofId A B).restrictScalars k,
    (Algebra.ofId B Λ).restrictScalars k, AlgHom.ext fun a ↦ ?_⟩
  change algebraMap B Λ (algebraMap A B a) = φ a
  exact (IsScalarTower.algebraMap_apply A B Λ a).symm

end Field

/-- **Popescu's theorem.** A regular ring map of Noetherian rings makes its target a filtered
colimit of smooth algebras. -/
@[stacks 07GC "Popescu's theorem with NO carried hypotheses: every regular ring map of \
Noetherian rings is a filtered colimit of smooth ring maps. Regularity is `IsRegularRingMap` \
(Situation 07F2) and the conclusion is `IndSmooth`, the `ObjectProperty.ind` spelling of Lemma \
07C3. Every step of the source's argument is proved: the reduction to a field base (07F5), the \
Noetherian induction on `𝔥_A`, the case `𝔥_A = Λ` (07EU), the characteristic-zero resolution \
(07FE), and the characteristic-`p` resolution (07FJ, `canBeResolvedInPositiveCharacteristic`), \
whose own λ-choice repair is due to Brian Nugent. Nothing is assumed."]
theorem indSmooth_of_isRegularRingMap
    (R : Type u) [CommRing R] (Λ : Type u) [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] (hregular : IsRegularRingMap R Λ) :
    IndSmooth R Λ :=
  indSmooth_of_indSmooth_of_field_base
    (fun k _ S _ _ _ hreg ↦ indSmooth_of_isRegularRingMap_of_field k S hreg) R Λ hregular

end Stacks.Smoothing

end
