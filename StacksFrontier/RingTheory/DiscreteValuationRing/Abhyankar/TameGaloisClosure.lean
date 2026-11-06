module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.RamificationGoesUp

/-!
# Tamely ramified Galois closures and composita

Every tamely ramified extension is contained in a tamely ramified finite Galois extension, and any
two are contained in a common tamely ramified one.

## Main results

* `IsDiscreteValuationRing.exists_isGalois_and_common_extension_isTamelyRamifiedWithRespectTo`:
  the two permanence properties of tame ramification under finite overextensions.

## Implementation notes

Containment of field extensions is represented by compatible algebra structures and scalar
towers; the common overextension is not required to be a specified compositum, in accordance with
the source.

## References

* [The Stacks Project, Tag 0EXX](https://stacks.math.columbia.edu/tag/0EXX)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y

/-- Over the algebra structure induced by a `K`-algebra map `L → M`, `M` is an `A`-`L`-tower. -/
private theorem isScalarTower_of_algHom_tower
    (A : Type u) (K : Type v) (L : Type w) (M : Type x)
    [CommRing A] [CommRing K] [CommRing L] [CommRing M]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K M] [Algebra A M] [IsScalarTower A K M] (f : L →ₐ[K] M) :
    letI := f.toAlgebra
    IsScalarTower A L M :=
  letI := f.toAlgebra
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L]
    exact (f.commutes (algebraMap A K a)).symm

theorem isTamelyRamified_of_algHom
    (A : Type u) (K : Type v) (L : Type w) (M : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field M]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (f : L →ₐ[K] M) (hM : Stacks.KummerExtension.IsTamelyRamified A K M) :
    Stacks.KummerExtension.IsTamelyRamified A K L := by
  let : Algebra L M := f.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun k => (f.commutes k).symm
  let : IsScalarTower A L M := isScalarTower_of_algHom_tower A K L M f
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  exact isTamelyRamified_of_isTamelyRamified_tower A K L M hM

private theorem exists_algEquiv_of_pi_surjective
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    {E : ι → Type w} [∀ i, Field (E i)] [∀ i, Algebra R (E i)]
    {F : Type x} [Field F] [Algebra R F]
    (f : (∀ i, E i) →ₐ[R] F) (hf : Function.Surjective f) :
    ∃ i, Nonempty (E i ≃ₐ[R] F) := by
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩ :
      PrimeSpectrum (∀ i, E i))
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  have hker : RingHom.ker (Pi.evalAlgHom R E i).toRingHom ≤ RingHom.ker f.toRingHom :=
    le_of_eq (congrArg PrimeSpectrum.asIdeal hq)
  let g := AlgHom.liftOfSurjective (Pi.evalAlgHom R E i)
    (Function.surjective_eval i) f hker
  exact ⟨i, ⟨AlgEquiv.ofBijective g
    ⟨g.injective, AlgHom.liftOfSurjective_surjective _ _ _ _ hf⟩⟩⟩

open scoped TensorProduct

private theorem isTamelyRamified_of_tensorProduct_surjective
    (A : Type u) (K : Type v) (L : Type w) (M : Type x) (F : Type y)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field M] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Algebra L F] [IsScalarTower K L F] [IsScalarTower A L F]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : (L ⊗[K] M) →ₐ[L] F) (hf : Function.Surjective f)
    (hL : Stacks.KummerExtension.IsTamelyRamified A K L)
    (hM : Stacks.KummerExtension.IsTamelyRamified A K M) :
    Stacks.KummerExtension.IsTamelyRamified A K F := by
  let : FiniteDimensional L F := FiniteDimensional.right K L F
  let : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  apply isTamelyRamified_tower A K L F hL
  intro m hm
  let : m.IsPrime := hm.isPrime
  let C := integralClosure A L
  let B := Localization.AtPrime m
  let : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  let : Algebra B L := IsLocalization.localizationAlgebraOfSubmonoidLe _ _
    m.primeCompl (nonZeroDivisors C) m.primeCompl_le_nonZeroDivisors
  let : IsScalarTower C B L := IsLocalization.localization_isScalarTower_of_submonoid_le
    _ _ m.primeCompl (nonZeroDivisors C) m.primeCompl_le_nonZeroDivisors
  let : Algebra B F := ((algebraMap L F).comp (algebraMap B L)).toAlgebra
  let : IsScalarTower B L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  show Stacks.KummerExtension.IsTamelyRamified B L F
  obtain ⟨hfin, _, _, _, n, ms, hmax, hms, hlies, hdvr, _⟩ :=
    integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia A K L
  obtain ⟨i, hi, _⟩ := (hms m).mp hm
  have : IsDiscreteValuationRing B := by
    dsimp [B]
    subst m
    exact hdvr i
  have : m.LiesOver (IsLocalRing.maximalIdeal A) := by
    rw [← hi]
    exact hlies i
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl B L
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C L, IsScalarTower.algebraMap_apply C B L,
      ← IsScalarTower.algebraMap_apply A C B]
  have : IsExtension A B := by
    have hinj : Function.Injective (algebraMap A B) := by
      apply Function.Injective.of_comp (f := algebraMap B L)
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq A B L,
        IsScalarTower.algebraMap_eq A K L, RingHom.coe_comp]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    have hlocal : IsLocalHom (algebraMap A B) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 1 5).mpr
      show (IsLocalRing.maximalIdeal B).under A = IsLocalRing.maximalIdeal A
      rw [← Ideal.under_under (B := C), IsLocalization.AtPrime.under_maximalIdeal B m]
      exact (Ideal.LiesOver.over (P := m) (p := IsLocalRing.maximalIdeal A)).symm
    exact
      { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
        toIsLocalHom := hlocal }
  obtain ⟨n, E, hfield, hLE, hBE, htower, hfinite, hsep, _, ⟨e⟩, _, htame⟩ :=
    exists_algEquiv_pi_field_and_ramification_goes_up A B K L M
  let := hfield
  let := hLE
  let := hBE
  let := htower
  let := hfinite
  let := hsep
  obtain ⟨j, ⟨g⟩⟩ := exists_algEquiv_of_pi_surjective (f.comp e.symm.toAlgHom)
    (hf.comp e.symm.surjective)
  exact isTamelyRamified_of_algHom B L F (E j) g.symm.toAlgHom (htame hM j)

theorem isTamelyRamified_sup
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    (L M : IntermediateField K Ω)
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (hL : Stacks.KummerExtension.IsTamelyRamified A K L)
    (hM : Stacks.KummerExtension.IsTamelyRamified A K M) :
    Stacks.KummerExtension.IsTamelyRamified A K (L ⊔ M : IntermediateField K Ω) := by
  let S := L ⊔ M
  let l : L →ₐ[K] S := IntermediateField.inclusion le_sup_left
  let : Algebra L S := l.toAlgebra
  have : IsScalarTower K L S := IsScalarTower.of_algHom l
  have : IsScalarTower A L S := isScalarTower_of_algHom_tower A K L S l
  let g := Algebra.TensorProduct.productMap L.val M.val
  have hg : g.range = S.toSubalgebra := by
    rw [Algebra.TensorProduct.productMap_range, L.range_val, M.range_val,
      ← IntermediateField.sup_toSubalgebra_of_left]
  let g' : (L ⊗[K] M) →ₐ[K] S := g.codRestrict S.toSubalgebra fun z => by
    rw [← hg]
    exact ⟨z, rfl⟩
  let f : (L ⊗[K] M) →ₐ[L] S :=
    { g'.toRingHom with
      commutes' := fun z => by
        apply Subtype.ext
        show g (algebraMap L (L ⊗[K] M) z) = (z : Ω)
        simp [g] }
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ g.range := hg.symm ▸ hz
    obtain ⟨t, ht⟩ := hz'
    exact ⟨t, Subtype.ext ht⟩
  exact isTamelyRamified_of_tensorProduct_surjective A K L M S f hf hL hM

/-- The image of a tamely ramified extension under a `K`-algebra map into `Ω` is tamely ramified. -/
private theorem isTamelyRamified_fieldRange
    (A : Type u) (K : Type v) (L : Type w) (Ω : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K Ω] (g : L →ₐ[K] Ω) [FiniteDimensional K g.fieldRange]
    (hL : Stacks.KummerExtension.IsTamelyRamified A K L) :
    Stacks.KummerExtension.IsTamelyRamified A K g.fieldRange :=
  isTamelyRamified_of_algHom A K _ L g.equivFieldRange.symm.toAlgHom hL

set_option maxHeartbeats 1000000 in
-- Transporting the field and algebra structures in the finite-join induction requires
-- more elaboration steps than the default heartbeat limit.
private theorem isTamelyRamified_iSup
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    {ι : Type x} [Finite ι] [Nonempty ι] (E : ι → IntermediateField K Ω)
    [∀ i, FiniteDimensional K (E i)] [∀ i, Algebra.IsSeparable K (E i)]
    (hE : ∀ i, Stacks.KummerExtension.IsTamelyRamified A K (E i)) :
    Stacks.KummerExtension.IsTamelyRamified A K (⨆ i, E i : IntermediateField K Ω) := by
  classical
  let := Fintype.ofFinite ι
  let i : ι := Classical.arbitrary ι
  have hbot : Stacks.KummerExtension.IsTamelyRamified A K (⊥ : IntermediateField K Ω) :=
    isTamelyRamified_of_algHom A K _ (E i)
      ((Algebra.ofId K (E i)).comp (IntermediateField.botEquiv K Ω).toAlgHom) (hE i)
  have hsep (s : Finset ι) :
      Algebra.IsSeparable K (⨆ i ∈ s, E i : IntermediateField K Ω) := by
    let T : IntermediateField K Ω := ⨆ i : (s : Set ι), E i
    have : Algebra.IsSeparable K T := inferInstance
    have heq : T = (⨆ i ∈ s, E i : IntermediateField K Ω) :=
      iSup_subtype'' (α := IntermediateField K Ω) (s : Set ι) E
    exact heq ▸ (inferInstance : Algebra.IsSeparable K T)
  have hs (s : Finset ι) :
      Stacks.KummerExtension.IsTamelyRamified A K (⨆ i ∈ s, E i : IntermediateField K Ω) := by
    induction s using Finset.induction_on with
    | empty =>
      exact isTamelyRamified_of_algHom A K _ _
        (IntermediateField.equivOfEq (by simp)).toAlgHom hbot
    | @insert j s hj ih =>
      exact isTamelyRamified_of_algHom A K _ _
        (IntermediateField.equivOfEq (Finset.iSup_insert j s E)).toAlgHom
        (isTamelyRamified_sup A K Ω (E j) (⨆ k ∈ s, E k) (hE j) ih)
  exact isTamelyRamified_of_algHom A K _ _
    (IntermediateField.equivOfEq (by simp)).toAlgHom (hs Finset.univ)

/-- **Stacks 0EXX.** Every finite separable extension of the fraction field of a discrete
valuation ring which is tamely ramified with respect to the ring is contained in a finite
Galois extension with the same property. Any two such extensions are contained in a common
finite separable extension which is again tamely ramified. -/
@[stacks 0EXX]
theorem exists_isGalois_and_common_extension_isTamelyRamifiedWithRespectTo
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] :
    (∀ (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
        [Algebra.IsSeparable K L] [Algebra A L] [IsScalarTower A K L],
      IsTamelyRamifiedWithRespectTo A K L →
        ∃ (M : Type (max u v w)) (_ : Field M) (_ : Algebra K M)
          (_ : FiniteDimensional K M) (_ : Algebra.IsSeparable K M)
          (_ : Algebra A M) (_ : IsScalarTower A K M)
          (_ : Algebra L M) (_ : IsScalarTower K L M),
          IsGalois K M ∧ IsTamelyRamifiedWithRespectTo A K M) ∧
    (∀ (L₁ : Type w) [Field L₁] [Algebra K L₁] [FiniteDimensional K L₁]
        [Algebra.IsSeparable K L₁] [Algebra A L₁] [IsScalarTower A K L₁]
        (L₂ : Type x) [Field L₂] [Algebra K L₂] [FiniteDimensional K L₂]
        [Algebra.IsSeparable K L₂] [Algebra A L₂] [IsScalarTower A K L₂],
      IsTamelyRamifiedWithRespectTo A K L₁ →
        IsTamelyRamifiedWithRespectTo A K L₂ →
        ∃ (L : Type (max u v w x)) (_ : Field L) (_ : Algebra K L)
          (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
          (_ : Algebra A L) (_ : IsScalarTower A K L)
          (_ : Algebra L₁ L) (_ : IsScalarTower K L₁ L)
          (_ : Algebra L₂ L) (_ : IsScalarTower K L₂ L),
          IsTamelyRamifiedWithRespectTo A K L) := by
  classical
  let Ω := SeparableClosure K
  let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  constructor
  · intro L _ _ _ _ _ _ hL
    let f : L →ₐ[K] Ω := IsSepClosed.lift
    have : Nonempty (L →ₐ[K] Ω) := ⟨f⟩
    let M₀ := IntermediateField.normalClosure K L Ω
    have hfinite (g : L →ₐ[K] Ω) : FiniteDimensional K g.fieldRange :=
      g.toLinearMap.finiteDimensional_range
    have hM₀ : Stacks.KummerExtension.IsTamelyRamified A K M₀ := by
      show Stacks.KummerExtension.IsTamelyRamified A K
        (⨆ g : L →ₐ[K] Ω, g.fieldRange : IntermediateField K Ω)
      apply isTamelyRamified_iSup A K Ω
      exact fun g => isTamelyRamified_fieldRange A K L Ω g hL
    let j : L →ₐ[K] M₀ := f.codRestrict M₀.toSubalgebra fun z =>
      f.fieldRange_le_normalClosure ⟨z, rfl⟩
    let M := ULift.{max u w} M₀
    let e : M ≃ₐ[K] M₀ := ULift.algEquiv
    have : IsGalois K M := IsGalois.of_algEquiv e.symm
    let k : L →ₐ[K] M := e.symm.toAlgHom.comp j
    let : Algebra L M := k.toAlgebra
    have : IsScalarTower K L M := IsScalarTower.of_algHom k
    refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    exact isTamelyRamified_of_algHom A K M M₀ e.toAlgHom hM₀
  · intro L₁ _ _ _ _ _ _ L₂ _ _ _ _ _ _ h₁ h₂
    let f₁ : L₁ →ₐ[K] Ω := IsSepClosed.lift
    let f₂ : L₂ →ₐ[K] Ω := IsSepClosed.lift
    have : FiniteDimensional K f₁.fieldRange := f₁.toLinearMap.finiteDimensional_range
    have : FiniteDimensional K f₂.fieldRange := f₂.toLinearMap.finiteDimensional_range
    let S := f₁.fieldRange ⊔ f₂.fieldRange
    have hS : Stacks.KummerExtension.IsTamelyRamified A K S :=
      isTamelyRamified_sup A K Ω f₁.fieldRange f₂.fieldRange
        (isTamelyRamified_fieldRange A K L₁ Ω f₁ h₁) (isTamelyRamified_fieldRange A K L₂ Ω f₂ h₂)
    let L := ULift.{max u w x} S
    let e : L ≃ₐ[K] S := ULift.algEquiv
    have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K S e.toAlgHom
    let j₁ : L₁ →ₐ[K] S := f₁.codRestrict S.toSubalgebra fun z =>
      (le_sup_left : f₁.fieldRange ≤ S) ⟨z, rfl⟩
    let j₂ : L₂ →ₐ[K] S := f₂.codRestrict S.toSubalgebra fun z =>
      (le_sup_right : f₂.fieldRange ≤ S) ⟨z, rfl⟩
    let k₁ : L₁ →ₐ[K] L := e.symm.toAlgHom.comp j₁
    let k₂ : L₂ →ₐ[K] L := e.symm.toAlgHom.comp j₂
    let : Algebra L₁ L := k₁.toAlgebra
    let : Algebra L₂ L := k₂.toAlgebra
    have : IsScalarTower K L₁ L := IsScalarTower.of_algHom k₁
    have : IsScalarTower K L₂ L := IsScalarTower.of_algHom k₂
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    exact isTamelyRamified_of_algHom A K L S e.toAlgHom hS

end

end IsDiscreteValuationRing
