module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.FormallySmoothCompletion
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent

@[expose] public section

/-!
# Excellence of a regular local G-ring

A Noetherian local G-ring is J-2, hence quasi-excellent, and a regular local G-ring is
excellent. The J-2 property is obtained by base change to the completion, which is excellent:
for a finite-type domain over the base, the singular locus upstairs is cut out by an ideal
meeting the base in a nonzero element, and that element carves out a regular open locus.
-/

open IsLocalRing
open scoped TensorProduct

universe u

section

variable (D E : Type u) [CommRing D] [CommRing E] [IsDomain D] [IsNoetherianRing D]
  [IsNoetherianRing E] [Algebra D E]

omit [IsDomain D] [IsNoetherianRing E] in
/-- Along a regular faithfully flat ring map, regularity of a local ring of the target descends
to the local ring of the contracted prime. -/
private theorem isRegularLocalRing_comap_of_isRegularRingHom
    (hreg : IsRegularRingHom (algebraMap D E)) (p : Ideal D) [p.IsPrime] (q : Ideal E)
    [q.IsPrime] (hpq : p = q.comap (algebraMap D E))
    (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap D E) hpq).toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.Flat.localRingHom hreg.1 q p hpq
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom p q (algebraMap D E) hpq
  exact IsRegularLocalRing.of_flat_of_isLocalHom (Localization.AtPrime q)

omit [IsNoetherianRing D] in
/-- A prime of the target of a regular ring map which contracts to the zero ideal of a domain
source has regular local ring: it lies in the fibre over the fraction field. -/
private theorem isRegularLocalRing_of_comap_eq_bot
    (hreg : IsRegularRingHom (algebraMap D E)) (q : Ideal E) [q.IsPrime]
    (hq : q.comap (algebraMap D E) = ⊥) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hfrac : IsFractionRing D (Localization.AtPrime (⊥ : Ideal D)) := by
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (⊥ : Ideal D).primeCompl
        (Localization.AtPrime (⊥ : Ideal D)))
  let : Field (Localization.AtPrime (⊥ : Ideal D)) := IsFractionRing.toField D
  have hall : ∀ (p : Ideal D) [p.IsPrime] (r : Ideal E) [r.IsPrime]
      (h : p = r.comap (algebraMap D E)),
      IsRegularRingHom (Localization.localRingHom p r (algebraMap D E) h) :=
    ((isRegularRingHom_tfae_localizations (algebraMap D E)).out 1 2).mp hreg
  have : IsRegularRing (Localization.AtPrime q) :=
    isRegularRing_of_isRegularRingHom _ (hall (⊥ : Ideal D) q hq.symm)
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- The J-0 property of a Noetherian domain follows from the J-1 property of a regular
faithfully flat algebra over it. The singular locus upstairs is the zero locus of an ideal `J`;
no prime containing `J` can contract to the zero ideal, so `J` contains the image of a nonzero
element of the domain, and the basic open of that element is regular. -/
private theorem isJ0_of_isJ1_of_isRegularRingHom_of_faithfullyFlat
    (hreg : IsRegularRingHom (algebraMap D E)) [Module.FaithfullyFlat D E]
    (hJ1 : IsJ1 E) : IsJ0 D := by
  classical
  have hopen : IsOpen {x : PrimeSpectrum E |
    IsRegularLocalRing (Localization.AtPrime x.asIdeal)} := hJ1
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hopen.isClosed_compl
  obtain ⟨d, hd0, hdJ⟩ : ∃ d : D, d ≠ 0 ∧ algebraMap D E d ∈ J := by
    by_cases hdisj : Disjoint (J : Set E) ((nonZeroDivisors D).map (algebraMap D E) : Set E)
    · obtain ⟨P, hP, hJP, hPM⟩ :=
        Ideal.exists_le_prime_disjoint J ((nonZeroDivisors D).map (algebraMap D E)) hdisj
      refine absurd (isRegularLocalRing_of_comap_eq_bot D E hreg P ?_) ?_
      · refine le_antisymm (fun d hd => ?_) bot_le
        by_contra hd0
        exact Set.disjoint_left.mp hPM hd ⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd0, rfl⟩
      · exact (Set.ext_iff.mp hJ ⟨P, hP⟩).mpr hJP
    · obtain ⟨x, hxJ, d, hd, rfl⟩ := Set.not_disjoint_iff.mp hdisj
      exact ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp hd, hxJ⟩
  refine ⟨(PrimeSpectrum.basicOpen d).1, (PrimeSpectrum.basicOpen d).2,
    ⟨⟨⊥, inferInstance⟩, by simpa [PrimeSpectrum.mem_basicOpen] using hd0⟩, fun x hx => ?_⟩
  by_contra hns
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := D) (B := E) x.asIdeal
  have hcomap : x.asIdeal = q.comap (algebraMap D E) := hqp.over
  have hqmem : (⟨q, hq⟩ : PrimeSpectrum E) ∈ {y : PrimeSpectrum E |
      IsRegularLocalRing (Localization.AtPrime y.asIdeal)}ᶜ := fun h =>
    hns (isRegularLocalRing_comap_of_isRegularRingHom D E hreg x.asIdeal q hcomap h)
  rw [hJ] at hqmem
  refine (PrimeSpectrum.mem_basicOpen _ _).mp hx ?_
  rw [hcomap]
  exact (PrimeSpectrum.mem_zeroLocus _ _).mp hqmem hdJ

end

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The completion of a Noetherian local ring is faithfully flat over it. -/
@[ega "IV 7.8.3" "(v)", sga "3 VIIB 5.5.2" "partial"]
private theorem faithfullyFlat_adicCompletion_maximalIdeal :
    Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A Noetherian local G-ring is J-2: the base change of a finite-type domain over it to the
completion is J-1, since the completion is excellent, and J-0 descends from that base change. -/
public theorem isJ2_of_isGRing_of_isLocalRing (hA : IsGRing A) : IsJ2 A := by
  have hcompl : IsExcellent (AdicCompletion (maximalIdeal A) A) :=
    isExcellent_of_standard_classes_and_finiteType.{u, u}.2.1
      (AdicCompletion (maximalIdeal A) A)
  refine ((isJ2_tfae A).out 2 1).mp ?_
  intro D _ _ _ _
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  have : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    faithfullyFlat_adicCompletion_maximalIdeal A
  let E := AdicCompletion (maximalIdeal A) A ⊗[A] D
  let : Algebra D E := Algebra.TensorProduct.rightAlgebra
  have hreg : IsRegularRingHom (algebraMap D E) :=
    isRegularRingHom_baseChange (R := A) (Λ := AdicCompletion (maximalIdeal A) A) (R' := D)
      (isRegularRingHom_algebraMap_adicCompletion hA (maximalIdeal A))
  have : IsNoetherianRing E :=
    Algebra.FiniteType.isNoetherianRing (AdicCompletion (maximalIdeal A) A) E
  have : Module.FaithfullyFlat D E :=
    Module.FaithfullyFlat.of_linearEquiv D (D ⊗[A] AdicCompletion (maximalIdeal A) A)
      (Algebra.TensorProduct.commRight A D
        (AdicCompletion (maximalIdeal A) A)).symm.toLinearEquiv
  exact isJ0_of_isJ1_of_isRegularRingHom_of_faithfullyFlat D E hreg (hcompl.1.2.2 E)

/-- A Noetherian local G-ring is quasi-excellent. -/
@[ega "IV 7.8.3" "(i)"]
public theorem isQuasiExcellent_of_isGRing_of_isLocalRing (hA : IsGRing A) :
    IsQuasiExcellent A :=
  ⟨inferInstance, hA, isJ2_of_isGRing_of_isLocalRing A hA⟩

/-- A regular local G-ring is excellent: it is quasi-excellent, and a regular local ring is
universally catenary. -/
@[ega "IV 7.8.4" "special case"]
public theorem isExcellent_of_isGRing_of_isRegularLocalRing [IsRegularLocalRing A]
    (hA : IsGRing A) : IsExcellent A :=
  ⟨isQuasiExcellent_of_isGRing_of_isLocalRing A hA, isUniversallyCatenary_of_isRegularLocalRing A⟩

end

end
