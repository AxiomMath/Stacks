module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar

/-!
# Unramified extensions of a discrete valuation ring are those with étale integral closure

Let `A` be a discrete valuation ring with fraction field `K` and `L/K` a finite separable
extension. Then `L` is unramified with respect to `A` in the sense of [Stacks, Tag 09E9] exactly
when the integral closure of `A` in `L` is étale over `A`. The integral closure is a finite
torsion-free Dedekind `A`-algebra, and at each of its maximal ideals unramifiedness is equivalent
to ramification index one with separable residue field extension; the unramified locus is open,
so unramifiedness at the maximal ideals is unramifiedness everywhere, and a finite flat
unramified algebra of finite presentation is étale.

## Main results

* `IsDiscreteValuationRing.isUnramifiedWithRespectTo_iff_etale_integralClosure`.

## References

* [Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9)
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

universe u v w

/-- At a maximal ideal over the closed point, a finite torsion-free Dedekind algebra over a
discrete valuation ring is unramified iff the ramification index is one and the residue field
extension is separable. -/
private theorem isUnramifiedAt_iff_ramificationIdx'_eq_one_and_isSeparable
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Type v} [CommRing C] [IsDedekindDomain C] [Algebra A C]
    [Module.Finite A C] [Module.IsTorsionFree A C] (n : Ideal C) [n.IsMaximal]
    [n.LiesOver (IsLocalRing.maximalIdeal A)] :
    Algebra.IsUnramifiedAt A n ↔
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) n = 1 ∧
      @Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ n) _ _
        (Ideal.Quotient.algebraOfLiesOver n (IsLocalRing.maximalIdeal A)) := by
  let p := IsLocalRing.maximalIdeal A
  let _ := Localization.AtPrime.algebraOfLiesOver p n
  rw [Algebra.isUnramifiedAt_iff_map_eq A p n,
    Algebra.isSeparable_residueField_iff,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
      (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) n)
      (Ideal.map_le_of_le_comap (Ideal.over_def n p).le)]
  exact and_comm

/-- **A finite separable extension is unramified with respect to a discrete valuation ring exactly
when an integral closure of the ring in it is étale.** Here `S` is any integral closure of `A` in
`L` in the sense of `IsIntegralClosure`, for example `integralClosure A L` itself. -/
theorem isUnramifiedWithRespectTo_iff_etale_integralClosure
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (S : Type w) [CommRing S] [Algebra A S] [Algebra S L] [IsScalarTower A S L]
    [IsIntegralClosure S A L] :
    IsUnramifiedWithRespectTo A K L ↔ Algebra.Etale A S := by
  suffices key : IsUnramifiedWithRespectTo A K L ↔ Algebra.Etale A (integralClosure A L) by
    rw [key]
    let e : integralClosure A L ≃ₐ[A] S := IsIntegralClosure.equiv A (integralClosure A L) L S
    exact ⟨fun _ => .of_equiv e, fun _ => .of_equiv e.symm⟩
  let B := integralClosure A L
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.IsTorsionFree A B := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => ?_
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val h
  refine ⟨fun h => ?_, fun _ m _ _ =>
    (isUnramifiedAt_iff_ramificationIdx'_eq_one_and_isSeparable A m).mp inferInstance⟩
  have : Algebra.FormallyUnramified A B := by
    refine Algebra.formallyUnramified_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    have : m.IsMaximal := hm
    have : m.LiesOver (IsLocalRing.maximalIdeal A) :=
      (Ideal.liesOver_iff _ _).mpr
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A m)).symm
    exact Algebra.isOpen_unramifiedLocus.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm)
      ((isUnramifiedAt_iff_ramificationIdx'_eq_one_and_isSeparable A m).mpr
        (h m hm inferInstance))
  exact Algebra.Etale.of_formallyUnramified_of_flat

end IsDiscreteValuationRing

end
