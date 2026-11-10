module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.TameRamificationKummer

/-!
# Unramified extensions under scalar extension

Auxiliary results for the permanence of unramified and tamely ramified extensions along an
extension of discrete valuation rings: étale algebras over a field are finite products of
fields, unramifiedness is étaleness of the integral closure, and unramifiedness of the factors of
a product after base change.

## References

* [The Stacks Project, Tag 0EXY](https://stacks.math.columbia.edu/tag/0EXY)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y

open scoped TensorProduct

theorem exists_algEquiv_pi_field_of_etale
    (K : Type u) (R : Type v) [Field K] [CommRing R] [Nontrivial R]
    [Algebra K R] [Algebra.Etale K R] :
    ∃ (n : ℕ) (E : Fin n → Type v) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, Module.Finite K (E i))
      (_ : ∀ i, Algebra.IsSeparable K (E i)),
      0 < n ∧ Nonempty (R ≃ₐ[K] ∀ i, E i) := by
  classical
  obtain ⟨I, hI, E, hfield, halg, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K R).mp inferInstance
  let _ := Fintype.ofFinite I
  have : Nonempty I := by
    by_contra hn
    have : IsEmpty I := not_nonempty_iff.mp hn
    exact zero_ne_one (e.injective (Subsingleton.elim _ _))
  let f := Fintype.equivFin I
  have (i : I) : Module.Finite K (E i) := (h i).1
  have (i : I) : Algebra.IsSeparable K (E i) := (h i).2
  refine ⟨Fintype.card I, fun i => E (f.symm i), inferInstance, inferInstance,
    inferInstance, inferInstance, Fintype.card_pos, ?_⟩
  exact ⟨e.trans (AlgEquiv.piCongrLeft' K E f)⟩

/-- The integral closure of `A` in `L` is torsion free over `A`. -/
private theorem isTorsionFree_integralClosure
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L] :
    Module.IsTorsionFree A (integralClosure A L) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  intro x y h
  apply IsFractionRing.injective A K
  apply (algebraMap K L).injective
  simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val h

/-- Formal unramifiedness of the integral closure gives `IsUnramifiedWithRespectTo`. -/
private theorem isUnramifiedWithRespectTo_of_formallyUnramified
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra.FormallyUnramified A (integralClosure A L)] :
    IsUnramifiedWithRespectTo A K L := by
  let S := integralClosure A L
  have : Module.Finite A S := IsIntegralClosure.finite A K L S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain A K L
  have : Module.IsTorsionFree A S := isTorsionFree_integralClosure A K L
  intro m hm hlo
  have := hm
  have := hlo
  exact (isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable A S m).mp inferInstance

theorem isUnramifiedWithRespectTo_iff_etale
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L] :
    IsUnramifiedWithRespectTo A K L ↔
      Algebra.Etale A (integralClosure A L) := by
  let S := integralClosure A L
  have : Module.Finite A S := IsIntegralClosure.finite A K L S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain A K L
  have : Algebra.FinitePresentation A S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.IsTorsionFree A S := isTorsionFree_integralClosure A K L
  constructor
  · intro h
    have : Algebra.FormallyUnramified A S := by
      apply Algebra.formallyUnramified_iff_forall.mpr
      intro q
      obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
      have : m.IsMaximal := hm
      have : m.LiesOver (IsLocalRing.maximalIdeal A) :=
        (Ideal.liesOver_iff _ _).mpr
          (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A m)).symm
      have hmU : Algebra.IsUnramifiedAt A m :=
        (isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable A S m).mpr
          (h m hm inferInstance)
      exact Algebra.isOpen_unramifiedLocus.stableUnderGeneralization
        ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm) hmU
    exact Algebra.Etale.of_formallyUnramified_of_flat
  · intro h
    have := h
    exact isUnramifiedWithRespectTo_of_formallyUnramified A K L

theorem isTamelyRamifiedWithRespectTo_of_isUnramifiedWithRespectTo
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (h : IsUnramifiedWithRespectTo A K L) :
    IsTamelyRamifiedWithRespectTo A K L := by
  intro m hm hlo
  obtain ⟨he, hs⟩ := h m hm hlo
  refine ⟨hs, Or.inr ?_⟩
  simpa only [he] using Nat.coprime_one_right (ringChar (A ⧸ IsLocalRing.maximalIdeal A))

private theorem isIntegralClosure_tensorProduct_of_smooth
    (R : Type u) (K : Type v) (S : Type w)
    [CommRing R] [CommRing K] [CommRing S] [Algebra R K] [IsFractionRing R K]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra.Smooth R S]
    [Algebra.IsIntegral R S] : IsIntegralClosure S R (S ⊗[R] K) := by
  constructor
  · exact Algebra.TensorProduct.includeLeft_injective (S := S) (IsFractionRing.injective R K)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ :=
        (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2
          ⟨x, hx.tower_top⟩
      have hy' : ∃ s : S,
          algebraMap S (S ⊗[R] K) s = (TensorProduct.toIntegralClosure R S K y).val := by
        clear hy
        induction y with
        | add a b ha hb =>
          obtain ⟨s, hs⟩ := ha
          obtain ⟨t, ht⟩ := hb
          exact ⟨s + t, by simp only [map_add, Subalgebra.coe_add, hs, ht]⟩
        | tmul s k =>
          obtain ⟨r, hr⟩ :=
            (show ∃ r : R, algebraMap R K r = k.val from by
              have hk := k.property
              exact Algebra.mem_bot.mp (by
                rw [← IsIntegrallyClosed.integralClosure_eq_bot R K]
                exact hk))
          refine ⟨r • s, ?_⟩
          change (r • s) ⊗ₜ[R] (1 : K) = s ⊗ₜ[R] k.val
          rw [← hr, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      obtain ⟨s, hs⟩ := hy'
      exact ⟨s, hs.trans (congrArg Subtype.val hy)⟩
    · rintro ⟨s, rfl⟩
      exact (Algebra.IsIntegral.isIntegral s).map
        (IsScalarTower.toAlgHom R S (S ⊗[R] K))

private theorem isIntegral_pi_single
    (R : Type u) [CommRing R] {I : Type v} (E : I → Type w)
    [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] [DecidableEq I]
    (i : I) (x : E i) (hx : IsIntegral R x) : IsIntegral R (Pi.single i x) := by
  obtain ⟨p, hp, hx⟩ := hx
  refine ⟨p * Polynomial.X, hp.mul Polynomial.monic_X, ?_⟩
  ext j
  change Pi.evalAlgHom R E j (Polynomial.aeval (Pi.single i x) (p * Polynomial.X)) = 0
  rw [← Polynomial.aeval_algHom_apply, map_mul, Polynomial.aeval_X]
  by_cases hji : j = i
  · subst j
    simp only [Pi.evalAlgHom_apply, Pi.single_eq_same, Polynomial.aeval_def, hx, zero_mul]
  · simp [Pi.evalAlgHom_apply, Pi.single_eq_of_ne hji]

private theorem exists_surjective_integralClosure_pi_eval
    (R : Type u) [CommRing R] {I : Type v} (E : I → Type w)
    [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)] (i : I) :
    ∃ f : integralClosure R (∀ j, E j) →ₐ[R] integralClosure R (E i),
      Function.Surjective f := by
  classical
  let f := ((Pi.evalAlgHom R E i).comp (integralClosure R (∀ j, E j)).val).codRestrict
    (integralClosure R (E i)) (fun x => x.property.map (Pi.evalAlgHom R E i))
  refine ⟨f, ?_⟩
  intro x
  refine ⟨⟨Pi.single i x.val, isIntegral_pi_single R E i x.val x.property⟩, ?_⟩
  exact Subtype.ext (Pi.single_eq_same i x.val)

theorem formallyUnramified_integralClosure_pi_of_etale
    (R : Type u) (K : Type v) (S : Type w)
    [CommRing R] [CommRing K] [CommRing S] [Algebra R K] [IsFractionRing R K]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra.Etale R S]
    [Algebra.IsIntegral R S] {I : Type x} (E : I → Type y)
    [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)]
    (e : (S ⊗[R] K) ≃ₐ[R] ∀ i, E i) (i : I) :
    Algebra.FormallyUnramified R (integralClosure R (E i)) := by
  have : IsIntegralClosure S R (S ⊗[R] K) :=
    isIntegralClosure_tensorProduct_of_smooth R K S
  let e₀ := IsIntegralClosure.equiv R S (S ⊗[R] K) (integralClosure R (S ⊗[R] K))
  have : Algebra.Etale R (integralClosure R (∀ j, E j)) :=
    Algebra.Etale.of_equiv (e₀.trans e.mapIntegralClosure)
  obtain ⟨f, hf⟩ := exists_surjective_integralClosure_pi_eval R E i
  exact Algebra.FormallyUnramified.of_surjective f hf

theorem isUnramifiedWithRespectTo_of_formallyUnramified_integralClosure
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra.FormallyUnramified A (integralClosure A L)] :
    IsUnramifiedWithRespectTo A K L := by
  exact isUnramifiedWithRespectTo_of_formallyUnramified A K L

theorem isUnramifiedWithRespectTo_pi_of_baseChange
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K' : Type y)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K']
    [Algebra A B] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K']
    [Module.Finite K K'] [Algebra.IsSeparable K K']
    {I : Type*} (E : I → Type*) [∀ i, Field (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    [∀ i, Algebra.IsSeparable L (E i)]
    (e : (L ⊗[K] K') ≃ₐ[L] ∀ i, E i)
    (h : IsUnramifiedWithRespectTo A K K') (i : I) :
    IsUnramifiedWithRespectTo B L (E i) := by
  let A' := integralClosure A K'
  let C := B ⊗[A] A'
  have : Algebra.Etale A A' := (isUnramifiedWithRespectTo_iff_etale A K K').mp h
  have : Module.Finite A A' := IsIntegralClosure.finite A K K' A'
  have : IsLocalization (Algebra.algebraMapSubmonoid A' (nonZeroDivisors A)) K' :=
    IsIntegralClosure.isLocalization A K K' A'
  have : Algebra.IsPushout A A' K K' :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K A' K'
  have : Algebra.IsPushout A K A' K' := (Algebra.IsPushout.comm A A' K K').mp this
  let eK : (K ⊗[A] A') ≃ₐ[K] K' := Algebra.IsPushout.equiv A K A' K'
  let eL : (L ⊗[A] A') ≃ₐ[L] L ⊗[K] K' :=
    (Algebra.TensorProduct.cancelBaseChange A K L L A').symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L) (A₁ := L)) eK)
  let eC : (C ⊗[B] L) ≃ₐ[B] ∀ j, E j :=
    (Algebra.TensorProduct.comm B C L).trans
      (((Algebra.TensorProduct.cancelBaseChange A B L L A').trans (eL.trans e)).restrictScalars B)
  have : Algebra.FormallyUnramified B (integralClosure B (E i)) :=
    formallyUnramified_integralClosure_pi_of_etale B L C E eC i
  exact isUnramifiedWithRespectTo_of_formallyUnramified_integralClosure B L (E i)

end

end IsDiscreteValuationRing
