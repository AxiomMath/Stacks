module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Ramification transport for the level of a degree-`p` extension

Auxiliary results on prime-degree Kummer tensor products, localizations of finite products,
transport of ramification indices along algebra equivalences of localizations, and weakly
unramified transfer, used to make a degree-`p` extension have finite level and to lower its level.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL


open Polynomial
open scoped TensorProduct

namespace Stacks.Kummer.PrimeDegreeExtension

universe uBase uExtension uTarget

variable (Base : Type uBase) (Target : Type uTarget)
variable [Field Base] [Field Target] [Algebra Base Target]

private noncomputable def adjoinRootBaseChangeEquiv (polynomial : Base[X]) :
    Target ⊗[Base] AdjoinRoot polynomial ≃ₐ[Target]
      AdjoinRoot (polynomial.map (algebraMap Base Target)) := by
  let comparison := Algebra.TensorProduct.rid Base Target Target
  refine (AdjoinRoot.tensorAlgEquiv polynomial
    (polynomial.map Algebra.TensorProduct.includeRight.toRingHom) rfl).trans
      (AdjoinRoot.mapAlgEquiv comparison _ _ ?_)
  have coefficientMap : comparison.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Base →ₐ[Base] Target ⊗[Base] Base).toRingHom =
      algebraMap Base Target := by
    ext coefficient
    simp [comparison, Algebra.smul_def]
  rw [Polynomial.map_map]
  change Associated (polynomial.map (comparison.toRingHom.comp
    (Algebra.TensorProduct.includeRight : Base →ₐ[Base] Target ⊗[Base] Base).toRingHom)) _
  rw [coefficientMap]

variable (Extension : Type uExtension) [Field Extension] [Algebra Base Extension]

private noncomputable def presentationOfGenerator [FiniteDimensional Base Extension]
    (degree : ℕ) (positive : 0 < degree) (parameter : Base) (generator : Extension)
    (generatorEquation : generator ^ degree = algebraMap Base Extension parameter)
    (generates : Algebra.adjoin Base {generator} = ⊤)
    (dimension : Module.finrank Base Extension = degree) :
    AdjoinRoot (X ^ degree - C parameter) ≃ₐ[Base] Extension := by
  have integral : IsIntegral Base generator := Algebra.IsIntegral.isIntegral generator
  let basis := PowerBasis.ofAdjoinEqTop integral generates
  have evaluates : aeval generator (X ^ degree - C parameter) = 0 := by
    simpa using sub_eq_zero.mpr generatorEquation
  have polynomialDegree : (minpoly Base generator).natDegree = degree :=
    basis.finrank.symm.trans dimension
  have minimalPolynomial : minpoly Base generator = X ^ degree - C parameter := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic integral)
      (monic_X_pow_sub_C parameter (Nat.ne_of_gt positive)) (minpoly.dvd Base generator evaluates)
    simp [polynomialDegree]
  refine AdjoinRoot.equiv' (X ^ degree - C parameter) basis ?_ ?_
  · change aeval _ (minpoly Base generator) = 0
    rw [minimalPolynomial, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · exact evaluates

private theorem exists_root_of_tensor_not_isField
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base)
    (presentation : AdjoinRoot (X ^ prime - C parameter) ≃ₐ[Base] Extension)
    (notField : ¬ IsField (Extension ⊗[Base] Target)) :
    ∃ root : Target, root ^ prime = algebraMap Base Target parameter := by
  classical
  by_contra noRoot
  push Not at noRoot
  have irreducible : Irreducible (X ^ prime - C (algebraMap Base Target parameter)) :=
    X_pow_sub_C_irreducible_of_prime primeCondition noRoot
  have fieldModel : IsField
      (AdjoinRoot ((X ^ prime - C parameter).map (algebraMap Base Target))) := by
    apply AdjoinRoot.isField_iff_irreducible.mpr
    simpa using irreducible
  let comparison :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Target ≃ₐ[Target] Target)
      presentation.symm).trans
        (adjoinRootBaseChangeEquiv Base Target (X ^ prime - C parameter))).toRingEquiv
  exact notField (MulEquiv.isField (MulEquiv.isField fieldModel comparison.toMulEquiv)
    (Algebra.TensorProduct.comm Base Extension Target).toRingEquiv.toMulEquiv)

private theorem nonempty_algHom_of_tensor_not_isField
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base)
    (presentation : AdjoinRoot (X ^ prime - C parameter) ≃ₐ[Base] Extension)
    (notField : ¬ IsField (Extension ⊗[Base] Target)) :
    Nonempty (Extension →ₐ[Base] Target) := by
  obtain ⟨root, rootEquation⟩ := exists_root_of_tensor_not_isField
    Base Target Extension prime primeCondition parameter presentation notField
  let rootMap := AdjoinRoot.liftAlgHom (X ^ prime - C parameter)
    (Algebra.ofId Base Target) root (by simpa using sub_eq_zero.mpr rootEquation)
  exact ⟨rootMap.comp presentation.symm.toAlgHom⟩

private theorem nonempty_algEquiv_of_tensor_not_isField
    [FiniteDimensional Base Extension] [FiniteDimensional Base Target]
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base)
    (presentation : AdjoinRoot (X ^ prime - C parameter) ≃ₐ[Base] Extension)
    (dimension : Module.finrank Base Extension = Module.finrank Base Target)
    (notField : ¬ IsField (Extension ⊗[Base] Target)) :
    Nonempty (Extension ≃ₐ[Base] Target) := by
  obtain ⟨embedding⟩ := nonempty_algHom_of_tensor_not_isField
    Base Target Extension prime primeCondition parameter presentation notField
  exact ⟨AlgEquiv.ofBijective embedding ⟨embedding.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimension
      (f := embedding.toLinearMap)).mp
      embedding.injective⟩⟩

private theorem nonempty_algEquiv_of_generator_of_tensor_not_isField
    [FiniteDimensional Base Extension] [FiniteDimensional Base Target]
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base) (generator : Extension)
    (generatorEquation : generator ^ prime = algebraMap Base Extension parameter)
    (generates : Algebra.adjoin Base {generator} = ⊤)
    (extensionDegree : Module.finrank Base Extension = prime)
    (targetDegree : Module.finrank Base Target = prime)
    (notField : ¬ IsField (Extension ⊗[Base] Target)) :
    Nonempty (Extension ≃ₐ[Base] Target) :=
  nonempty_algEquiv_of_tensor_not_isField Base Target Extension prime primeCondition parameter
    (presentationOfGenerator Base Extension prime primeCondition.pos parameter generator
      generatorEquation generates extensionDegree)
    (extensionDegree.trans targetDegree.symm) notField

section BaseChange

universe uGround uAuxiliary

variable (Ground : Type uGround) (Auxiliary : Type uAuxiliary)
variable [Field Ground] [Field Auxiliary]
variable [Algebra Ground Base] [Algebra Ground Extension] [Algebra Ground Auxiliary]
variable [IsScalarTower Ground Base Extension]
variable [FiniteDimensional Base Extension] [FiniteDimensional Ground Auxiliary]

theorem nonempty_baseChange_algEquiv_of_generator_of_tensor_not_isField
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base) (generator : Extension)
    (generatorEquation : generator ^ prime = algebraMap Base Extension parameter)
    (generates : Algebra.adjoin Base {generator} = ⊤)
    (extensionDegree : Module.finrank Base Extension = prime)
    (auxiliaryDegree : Module.finrank Ground Auxiliary = prime)
    (baseChangeField : IsField (Base ⊗[Ground] Auxiliary))
    (notField : ¬ IsField (Extension ⊗[Ground] Auxiliary)) :
    letI := baseChangeField.toField
    Nonempty (Base ⊗[Ground] Auxiliary ≃ₐ[Base] Extension) := by
  let := baseChangeField.toField
  have smallerTensorNotField : ¬ IsField (Extension ⊗[Base] (Base ⊗[Ground] Auxiliary)) :=
    fun fieldTensor ↦ notField (MulEquiv.isField fieldTensor
      (Algebra.TensorProduct.cancelBaseChange Ground Base Extension Extension
        Auxiliary).symm.toMulEquiv)
  have targetDegree : Module.finrank Base (Base ⊗[Ground] Auxiliary) = prime := by
    rw [Module.finrank_baseChange]
    exact auxiliaryDegree
  obtain ⟨comparison⟩ := nonempty_algEquiv_of_generator_of_tensor_not_isField Base
    (Base ⊗[Ground] Auxiliary) Extension prime primeCondition parameter generator
    generatorEquation generates extensionDegree targetDegree smallerTensorNotField
  exact ⟨comparison.symm⟩

end BaseChange

end Stacks.Kummer.PrimeDegreeExtension


namespace Stacks.ProductLocalizations

universe uSource uComponent uIndex

private theorem exists_component_localizationEquiv
    (Source : Type uSource) [CommRing Source]
    {Index : Type uIndex} [Finite Index]
    (Component : Index → Type uComponent) [∀ index, CommRing (Component index)]
    [∀ index, IsDomain (Component index)]
    (comparison : Source ≃+* ∀ index, Component index)
    (prime : Ideal Source) [prime.IsPrime] :
    ∃ index, ∃ componentPrime : PrimeSpectrum (Component index),
      ∃ equivalence : Localization.AtPrime prime ≃+* Localization.AtPrime componentPrime.asIdeal,
        prime = componentPrime.asIdeal.comap
          ((Pi.evalRingHom Component index).comp comparison.toRingHom) ∧
        ∀ element : Source,
          equivalence (algebraMap Source (Localization.AtPrime prime) element) =
            algebraMap (Component index) (Localization.AtPrime componentPrime.asIdeal)
              (comparison element index) := by
  classical
  obtain ⟨⟨index, componentPrime⟩, primeEquation⟩ :=
    (PrimeSpectrum.sigmaToPi_bijective Component).surjective
      (PrimeSpectrum.comap comparison.symm.toRingHom ⟨prime, inferInstance⟩)
  let projection : Source →+* Component index :=
    (Pi.evalRingHom Component index).comp comparison.toRingHom
  have projectionSurjective : Function.Surjective projection := fun element ↦
    ⟨comparison.symm (Pi.single index element), by simp [projection]⟩
  have pullback : prime = componentPrime.asIdeal.comap projection := by
    have equation := congrArg (fun point : PrimeSpectrum (∀ index, Component index) ↦
      (PrimeSpectrum.comap comparison.toRingHom point).asIdeal) primeEquation
    simpa [projection, PrimeSpectrum.sigmaToPi_apply, Ideal.comap_comap] using equation.symm
  let localMap := Localization.localRingHom prime componentPrime.asIdeal projection pullback
  have bijective : Function.Bijective localMap := by
    constructor
    · refine IsLocalization.injective_of_map_algebraMap_zero (M := prime.primeCompl)
        (Localization.AtPrime prime) localMap ?_
      intro element zeroImage
      rw [Localization.localRingHom_to_map] at zeroImage
      have zeroCoordinate : projection element = 0 :=
        (IsLocalization.injective (Localization.AtPrime componentPrime.asIdeal)
          componentPrime.asIdeal.primeCompl_le_nonZeroDivisors) (by simpa using zeroImage)
      apply (IsLocalization.map_eq_zero_iff prime.primeCompl
        (Localization.AtPrime prime) element).mpr
      refine ⟨⟨comparison.symm (Pi.single index 1), ?_⟩, ?_⟩
      · change comparison.symm (Pi.single index 1) ∉ prime
        rw [pullback]
        change projection (comparison.symm (Pi.single index 1)) ∉ componentPrime.asIdeal
        simpa [projection] using componentPrime.isPrime.one_notMem
      · apply comparison.injective
        ext coordinate
        by_cases equality : coordinate = index
        · subst coordinate
          simpa [projection] using zeroCoordinate
        · simp [Pi.single_eq_of_ne equality]
    · subst prime
      exact IsDiscreteValuationRing.localRingHom_surjective_of_surjective projection
        projectionSurjective componentPrime.asIdeal
  exact ⟨index, componentPrime, RingEquiv.ofBijective localMap bijective, pullback,
    fun element ↦ Localization.localRingHom_to_map prime componentPrime.asIdeal projection pullback
      element⟩

private theorem exists_component_equiv_atMaximal
    (Source : Type uSource) [CommRing Source]
    {Index : Type uIndex} [Finite Index]
    (Component : Index → Type uComponent) [∀ index, CommRing (Component index)]
    [∀ index, IsDomain (Component index)] [∀ index, IsLocalRing (Component index)]
    (comparison : Source ≃+* ∀ index, Component index)
    (maximal : Ideal Source) [maximal.IsMaximal] :
    ∃ index, ∃ equivalence : Localization.AtPrime maximal ≃+* Component index,
      ∀ element : Source,
        equivalence (algebraMap Source (Localization.AtPrime maximal) element) =
          comparison element index := by
  classical
  obtain ⟨index, componentPrime, localComparison, pullback, comparisonEquation⟩ :=
    exists_component_localizationEquiv Source Component comparison maximal
  let projection : Source →+* Component index :=
    (Pi.evalRingHom Component index).comp comparison.toRingHom
  have projectionSurjective : Function.Surjective projection := fun element ↦
    ⟨comparison.symm (Pi.single index element), by simp [projection]⟩
  have mapEquation : maximal.map projection = componentPrime.asIdeal := by
    rw [pullback]
    exact Ideal.map_comap_of_surjective projection projectionSurjective componentPrime.asIdeal
  have componentMaximal : componentPrime.asIdeal.IsMaximal := by
    have alternatives := maximal.map_eq_top_or_isMaximal_of_surjective projection
      projectionSurjective (inferInstance : maximal.IsMaximal)
    rw [mapEquation] at alternatives
    exact alternatives.resolve_left componentPrime.isPrime.ne_top
  have units : componentPrime.asIdeal.primeCompl ≤ IsUnit.submonoid (Component index) := by
    intro element outside
    apply IsLocalRing.notMem_maximalIdeal.mp
    rwa [← IsLocalRing.eq_maximalIdeal componentMaximal]
  let unitComparison := IsLocalization.atUnits (Component index)
    componentPrime.asIdeal.primeCompl (S := Localization.AtPrime componentPrime.asIdeal) units
  refine ⟨index, localComparison.trans unitComparison.symm.toRingEquiv, ?_⟩
  intro element
  change unitComparison.symm (localComparison (algebraMap Source _ element)) = _
  rw [comparisonEquation]
  exact unitComparison.symm.commutes (comparison element index)

universe uBase

theorem exists_component_algEquiv_atMaximal
    (Base : Type uBase) [CommRing Base]
    (Source : Type uSource) [CommRing Source] [Algebra Base Source]
    {Index : Type uIndex} [Finite Index]
    (Component : Index → Type uComponent) [∀ index, CommRing (Component index)]
    [∀ index, IsDomain (Component index)] [∀ index, IsLocalRing (Component index)]
    [∀ index, Algebra Base (Component index)]
    (comparison : Source ≃ₐ[Base] ∀ index, Component index)
    (maximal : Ideal Source) [maximal.IsMaximal] :
    ∃ index, ∃ equivalence : Localization.AtPrime maximal ≃ₐ[Base] Component index,
      ∀ element : Source,
        equivalence (algebraMap Source (Localization.AtPrime maximal) element) =
          comparison element index := by
  obtain ⟨index, ringComparison, comparisonEquation⟩ :=
    exists_component_equiv_atMaximal Source Component comparison.toRingEquiv maximal
  refine ⟨index, { ringComparison with commutes' := ?_ }, comparisonEquation⟩
  intro scalar
  change ringComparison (algebraMap Base (Localization.AtPrime maximal) scalar) = _
  rw [IsScalarTower.algebraMap_apply Base Source (Localization.AtPrime maximal),
    comparisonEquation]
  exact congrFun (comparison.commutes scalar) index

end Stacks.ProductLocalizations


namespace Stacks.RamificationTransport

universe uBase uSource uTarget

/-- **A ring isomorphism matching two ideals equates the lengths of the two quotients.**

Each length is taken over its own ring: this compares `Module.length Source (Source ⧸ I)` with
`Module.length Target (Target ⧸ I.map c)`. -/
theorem quotient_length_eq_of_ringEquiv
    (Source : Type uSource) (Target : Type uTarget) [CommRing Source] [CommRing Target]
    (comparison : Source ≃+* Target) (sourceIdeal : Ideal Source) (targetIdeal : Ideal Target)
    (idealEquation : targetIdeal = sourceIdeal.map comparison.toRingHom) :
    Module.length Source (Source ⧸ sourceIdeal) = Module.length Target (Target ⧸ targetIdeal) := by
  let quotientComparison := Ideal.quotientEquiv sourceIdeal targetIdeal comparison idealEquation
  let : RingHomSurjective comparison.toRingHom := ⟨comparison.surjective⟩
  let linearComparison : (Source ⧸ sourceIdeal) →ₛₗ[comparison.toRingHom] (Target ⧸ targetIdeal) :=
    { toFun := quotientComparison
      map_add' := quotientComparison.map_add
      map_smul' := by
        intro scalar element
        change quotientComparison (Ideal.Quotient.mk sourceIdeal scalar * element) =
          Ideal.Quotient.mk targetIdeal (comparison scalar) * quotientComparison element
        rw [map_mul]
        rfl }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective linearComparison quotientComparison.bijective)]

variable (Base : Type uBase) (Source : Type uSource) (Target : Type uTarget)
variable [CommRing Base] [CommRing Source] [CommRing Target]
variable [Algebra Base Source] [Algebra Base Target]

private theorem under_eq_of_localizationAlgEquiv
    (sourcePrime : Ideal Source) [sourcePrime.IsPrime]
    (targetPrime : Ideal Target) [targetPrime.IsPrime]
    (comparison : Localization.AtPrime sourcePrime ≃ₐ[Base] Localization.AtPrime targetPrime) :
    sourcePrime.under Base = targetPrime.under Base := by
  let : IsLocalHom comparison.toRingHom :=
    IsLocalHom.of_surjective comparison.toRingHom comparison.surjective
  have maximalEquation := IsLocalRing.maximalIdeal_comap comparison.toRingHom
  calc
    sourcePrime.under Base =
        (IsLocalRing.maximalIdeal (Localization.AtPrime sourcePrime)).under Base := by
      simpa only [Ideal.under_under] using
        (congrArg (fun ideal : Ideal Source ↦ ideal.under Base)
          (IsLocalization.AtPrime.under_maximalIdeal
            (Localization.AtPrime sourcePrime) sourcePrime)).symm
    _ = (IsLocalRing.maximalIdeal (Localization.AtPrime targetPrime)).under Base := by
      rw [Ideal.under_def, Ideal.under_def, ← maximalEquation, Ideal.comap_comap]
      exact congrArg (fun homomorphism ↦
        Ideal.comap homomorphism (IsLocalRing.maximalIdeal (Localization.AtPrime targetPrime)))
          comparison.toAlgHom.comp_algebraMap
    _ = targetPrime.under Base := by
      simpa only [Ideal.under_under] using
        congrArg (fun ideal : Ideal Target ↦ ideal.under Base)
          (IsLocalization.AtPrime.under_maximalIdeal
            (Localization.AtPrime targetPrime) targetPrime)

private theorem ramificationIdx_eq_of_localizationAlgEquiv
    (sourcePrime : Ideal Source) [sourcePrime.IsPrime]
    (targetPrime : Ideal Target) [targetPrime.IsPrime]
    (comparison : Localization.AtPrime sourcePrime ≃ₐ[Base] Localization.AtPrime targetPrime) :
    sourcePrime.ramificationIdx Base = targetPrime.ramificationIdx Base := by
  have contractions := under_eq_of_localizationAlgEquiv Base Source Target
    sourcePrime targetPrime comparison
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  congr 1
  apply Stacks.RamificationTransport.quotient_length_eq_of_ringEquiv _ _ comparison.toRingEquiv
  rw [contractions, Ideal.map_map]
  exact congrArg (fun homomorphism ↦ Ideal.map homomorphism (targetPrime.under Base))
    comparison.toAlgHom.comp_algebraMap.symm

/-- A local ring is its own localization at its maximal ideal. -/
private noncomputable def localizationAtMaximalIdealEquiv [IsLocalRing Target] :
    Target ≃ₐ[Target] Localization.AtPrime (IsLocalRing.maximalIdeal Target) :=
  IsLocalization.atUnits Target (IsLocalRing.maximalIdeal Target).primeCompl
    fun _ outside ↦ IsLocalRing.notMem_maximalIdeal.mp outside

private theorem ramificationIdx_eq_of_localComponentEquiv [IsLocalRing Target]
    (sourcePrime : Ideal Source) [sourcePrime.IsPrime]
    (comparison : Localization.AtPrime sourcePrime ≃ₐ[Base] Target) :
    sourcePrime.ramificationIdx Base = (IsLocalRing.maximalIdeal Target).ramificationIdx Base := by
  exact ramificationIdx_eq_of_localizationAlgEquiv Base Source Target sourcePrime
    (IsLocalRing.maximalIdeal Target)
    (comparison.trans ((localizationAtMaximalIdealEquiv Target).restrictScalars Base))

private theorem under_eq_of_localComponentEquiv [IsLocalRing Target]
    (sourcePrime : Ideal Source) [sourcePrime.IsPrime]
    (comparison : Localization.AtPrime sourcePrime ≃ₐ[Base] Target) :
    sourcePrime.under Base = (IsLocalRing.maximalIdeal Target).under Base := by
  exact under_eq_of_localizationAlgEquiv Base Source Target sourcePrime
    (IsLocalRing.maximalIdeal Target)
    (comparison.trans ((localizationAtMaximalIdealEquiv Target).restrictScalars Base))

universe uIntermediate uComponent

theorem ramificationIdx_eq_one_of_integral_tower [IsLocalRing Base]
    (Intermediate : Type uIntermediate) [CommRing Intermediate] [IsLocalRing Intermediate]
    [Algebra Base Intermediate] [Algebra.IsIntegral Base Intermediate]
    [Algebra Intermediate Source] [IsScalarTower Base Intermediate Source]
    [Module.Flat Intermediate Source]
    (Component : Type uComponent) [CommRing Component] [IsLocalRing Component]
    [Algebra Base Component] [IsLocalHom (algebraMap Base Component)]
    [Algebra Component Source] [IsScalarTower Base Component Source]
    (sourcePrime : Ideal Source) [sourcePrime.IsMaximal]
    (comparison : Localization.AtPrime sourcePrime ≃ₐ[Component] Component)
    (degree : ℕ) (positive : 0 < degree)
    (intermediateIndex : (IsLocalRing.maximalIdeal Intermediate).ramificationIdx Base = degree)
    (componentIndex : (IsLocalRing.maximalIdeal Component).ramificationIdx Base = degree) :
    sourcePrime.ramificationIdx Intermediate = 1 := by
  have bottomContraction : sourcePrime.under Base = IsLocalRing.maximalIdeal Base := by
    rw [under_eq_of_localComponentEquiv Base Source Component sourcePrime
      (comparison.restrictScalars Base)]
    exact IsLocalRing.maximalIdeal_comap (algebraMap Base Component)
  have intermediateMaximal : (sourcePrime.under Intermediate).IsMaximal := by
    apply Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := Base)
    show ((sourcePrime.under Intermediate).under Base).IsMaximal
    rw [Ideal.under_under, bottomContraction]
    infer_instance
  let : sourcePrime.LiesOver (IsLocalRing.maximalIdeal Intermediate) :=
    ⟨(IsLocalRing.eq_maximalIdeal intermediateMaximal).symm⟩
  have tower := Ideal.ramificationIdx_tower (R := Base)
    (IsLocalRing.maximalIdeal Intermediate) sourcePrime
  rw [ramificationIdx_eq_of_localComponentEquiv Base Source Component sourcePrime
    (comparison.restrictScalars Base), componentIndex, intermediateIndex] at tower
  apply Nat.eq_of_mul_eq_mul_left positive
  simpa only [Nat.mul_one] using tower.symm

universe uField uAmbient

theorem flat_of_injective_into_field_algebra
    (Domain : Type uIntermediate) [CommRing Domain] [IsDedekindDomain Domain]
    (Fraction : Type uField) [Field Fraction] [Algebra Domain Fraction]
    [Module.IsTorsionFree Domain Fraction]
    (Input : Type uSource) [CommRing Input] [Algebra Domain Input]
    (Ambient : Type uAmbient) [CommRing Ambient]
    [Algebra Fraction Ambient] [Algebra Domain Ambient] [IsScalarTower Domain Fraction Ambient]
    (embedding : Input →ₐ[Domain] Ambient) (injective : Function.Injective embedding) :
    Module.Flat Domain Input := by
  have : Module.IsTorsionFree Domain Ambient := Module.IsTorsionFree.trans Fraction
  have : Module.IsTorsionFree Domain Input :=
    injective.moduleIsTorsionFree embedding
      (fun scalar element ↦ embedding.toLinearMap.map_smul scalar element)
  infer_instance

private theorem isLocalHom_of_map_maximalIdeal
    (Base : Type uBase) (Target : Type uTarget)
    [CommRing Base] [CommRing Target] [IsLocalRing Base] [IsLocalRing Target]
    (homomorphism : Base →+* Target)
    (idealEquation : (IsLocalRing.maximalIdeal Base).map homomorphism = IsLocalRing.maximalIdeal
      Target) :
    IsLocalHom homomorphism := by
  constructor
  intro element unitImage
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro membership
  have imageMembership : homomorphism element ∈ IsLocalRing.maximalIdeal Target := by
    rw [← idealEquation]
    exact Ideal.mem_map_of_mem homomorphism membership
  exact (IsLocalRing.notMem_maximalIdeal.mpr unitImage) imageMembership

private theorem ramificationIdx_eq_one_of_map_maximalIdeal
    (Base : Type uBase) (Target : Type uTarget)
    [CommRing Base] [CommRing Target] [IsLocalRing Base] [IsLocalRing Target]
    [Algebra Base Target]
    (idealEquation : (IsLocalRing.maximalIdeal Base).map (algebraMap Base Target) =
      IsLocalRing.maximalIdeal Target) :
    (IsLocalRing.maximalIdeal Target).ramificationIdx Base = 1 := by
  let : IsLocalHom (algebraMap Base Target) :=
    isLocalHom_of_map_maximalIdeal Base Target (algebraMap Base Target) idealEquation
  let comparison := localizationAtMaximalIdealEquiv Target
  have quotientLength := quotient_length_eq_of_ringEquiv Target
    (Localization.AtPrime (IsLocalRing.maximalIdeal Target)) comparison.toRingEquiv
    (IsLocalRing.maximalIdeal Target)
    ((IsLocalRing.maximalIdeal Base).map
      (algebraMap Base (Localization.AtPrime (IsLocalRing.maximalIdeal Target)))) (by
        calc
          (IsLocalRing.maximalIdeal Base).map (algebraMap Base _) =
              ((IsLocalRing.maximalIdeal Base).map (algebraMap Base Target)).map
                (algebraMap Target (Localization.AtPrime (IsLocalRing.maximalIdeal Target))) := by
            rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq Base Target]
          _ = (IsLocalRing.maximalIdeal Target).map (algebraMap Target _) :=
            congrArg (Ideal.map (algebraMap Target
              (Localization.AtPrime (IsLocalRing.maximalIdeal Target)))) idealEquation
          _ = _ := rfl)
  let : (IsLocalRing.maximalIdeal Target).LiesOver (IsLocalRing.maximalIdeal Base) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap Base Target)).symm⟩
  have : IsSimpleModule Target (Target ⧸ IsLocalRing.maximalIdeal Target) := by
    rw [isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
    infer_instance
  rw [Ideal.ramificationIdx_eq (IsLocalRing.maximalIdeal Base),
    ← quotientLength, Module.length_eq_one, ENat.toNat_one]

end Stacks.RamificationTransport


namespace Stacks.DiscreteValuationRing.WeakUnramifiedTransfer

universe uFirst uMiddle uSource uTarget uBase uFraction uAmbient

theorem weak_indices_through_equivalence
    (First : Type uFirst) (Middle : Type uMiddle)
    (Source : Type uSource) (Target : Type uTarget)
    [CommRing First] [CommRing Middle] [CommRing Source] [CommRing Target]
    [IsLocalRing First] [IsLocalRing Middle] [IsLocalRing Source]
    (firstMap : First →+* Middle) (secondMap : Middle →+* Source)
    (comparison : Source ≃+* Target)
    (firstWeak : (IsLocalRing.maximalIdeal First).map firstMap = IsLocalRing.maximalIdeal Middle)
    (secondWeak : (IsLocalRing.maximalIdeal Middle).map secondMap = IsLocalRing.maximalIdeal
      Source) :
    letI : Algebra First Target := (comparison.toRingHom.comp (secondMap.comp firstMap)).toAlgebra
    ∀ prime : Ideal Target, prime.IsMaximal → prime.ramificationIdx First = 1 := by
  let : IsLocalRing Target := comparison.isLocalRing
  let : Algebra First Target := (comparison.toRingHom.comp (secondMap.comp firstMap)).toAlgebra
  have weak : (IsLocalRing.maximalIdeal First).map (algebraMap First Target) =
      IsLocalRing.maximalIdeal Target := by
    change (IsLocalRing.maximalIdeal First).map
      (comparison.toRingHom.comp (secondMap.comp firstMap)) = _
    rw [← Ideal.map_map, ← Ideal.map_map, firstWeak, secondWeak]
    exact IsLocalRing.map_maximalIdeal_of_surjective comparison.toRingHom comparison.surjective
  intro prime maximal
  rw [IsLocalRing.eq_maximalIdeal maximal]
  exact Stacks.RamificationTransport.ramificationIdx_eq_one_of_map_maximalIdeal First Target
    weak

theorem scalarTower_of_injective_square
    (Base : Type uBase) (First : Type uFirst) (Target : Type uTarget)
    (Fraction : Type uFraction) (Ambient : Type uAmbient)
    [CommRing Base] [CommRing First] [CommRing Target] [CommRing Fraction] [CommRing Ambient]
    [Algebra Base First] [Algebra Base Target] [Algebra Base Fraction]
    [Algebra First Fraction] [IsScalarTower Base First Fraction]
    [Algebra Base Ambient] [Algebra Target Ambient] [IsScalarTower Base Target Ambient]
    (homomorphism : Fraction →ₐ[Base] Ambient) (scalarMap : First →+* Target)
    (injective : Function.Injective (algebraMap Target Ambient))
    (square : ∀ element : First,
      algebraMap Target Ambient (scalarMap element) =
        homomorphism (algebraMap First Fraction element)) :
    letI : Algebra First Target := scalarMap.toAlgebra
    IsScalarTower Base First Target := by
  let : Algebra First Target := scalarMap.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro element
  apply injective
  change algebraMap Target Ambient (algebraMap Base Target element) =
    algebraMap Target Ambient (scalarMap (algebraMap Base First element))
  rw [← IsScalarTower.algebraMap_apply Base Target Ambient, square,
    ← IsScalarTower.algebraMap_apply Base First Fraction, homomorphism.commutes]

end Stacks.DiscreteValuationRing.WeakUnramifiedTransfer

namespace Stacks.DiscreteValuationRing.EppLevelInduction

namespace SplitFactors

universe uBase uSource uTarget

variable (Base : Type uBase) (Source : Type uSource) (Target : Type uTarget)
variable [CommRing Base] [CommRing Source] [CommRing Target]
variable [Algebra Base Source] [Algebra Base Target]

private alias under_eq_of_localizationAlgEquiv :=
    Stacks.RamificationTransport.under_eq_of_localizationAlgEquiv

private alias ramificationIdx_eq_of_localizationAlgEquiv :=
    Stacks.RamificationTransport.ramificationIdx_eq_of_localizationAlgEquiv

alias ramificationIdx_eq_of_localComponentEquiv :=
    Stacks.RamificationTransport.ramificationIdx_eq_of_localComponentEquiv


end SplitFactors
namespace PrimeKummer

open Polynomial

universe uBase uExtension uTarget

variable (Base : Type uBase) (Target : Type uTarget)
variable [Field Base] [Field Target] [Algebra Base Target]

variable (Extension : Type uExtension) [Field Extension] [Algebra Base Extension]

noncomputable def presentationOfGenerator [FiniteDimensional Base Extension]
    (degree : ℕ) (positive : 0 < degree) (parameter : Base) (generator : Extension)
    (generatorEquation : generator ^ degree = algebraMap Base Extension parameter)
    (generates : Algebra.adjoin Base {generator} = ⊤)
    (dimension : Module.finrank Base Extension = degree) :
    AdjoinRoot (X ^ degree - C parameter) ≃ₐ[Base] Extension := by
  have integral : IsIntegral Base generator := Algebra.IsIntegral.isIntegral generator
  let basis := PowerBasis.ofAdjoinEqTop integral generates
  have evaluates : aeval generator (X ^ degree - C parameter) = 0 := by
    simpa using sub_eq_zero.mpr generatorEquation
  have polynomialDegree : (minpoly Base generator).natDegree = degree :=
    basis.finrank.symm.trans dimension
  have minimalPolynomial : minpoly Base generator = X ^ degree - C parameter := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic integral)
      (monic_X_pow_sub_C parameter (Nat.ne_of_gt positive)) (minpoly.dvd Base generator evaluates)
    simp [polynomialDegree]
  refine AdjoinRoot.equiv' (X ^ degree - C parameter) basis ?_ ?_
  · change aeval _ (minpoly Base generator) = 0
    rw [minimalPolynomial, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · exact evaluates

private alias exists_root_of_tensor_not_isField :=
    Stacks.Kummer.PrimeDegreeExtension.exists_root_of_tensor_not_isField

theorem nonempty_algHom_of_tensor_not_isField
    (prime : ℕ) (primeCondition : prime.Prime) (parameter : Base)
    (presentation : AdjoinRoot (X ^ prime - C parameter) ≃ₐ[Base] Extension)
    (notField : ¬ IsField (Extension ⊗[Base] Target)) :
    Nonempty (Extension →ₐ[Base] Target) :=
  Stacks.Kummer.PrimeDegreeExtension.nonempty_algHom_of_tensor_not_isField
    Base Target Extension prime primeCondition parameter presentation notField

end PrimeKummer

end Stacks.DiscreteValuationRing.EppLevelInduction
