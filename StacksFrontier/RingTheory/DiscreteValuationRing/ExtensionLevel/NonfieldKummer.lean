module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.RamificationTransport

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Weak solutions from a non-field Kummer tensor product

Splitting of tensor products of Galois extensions, scalar towers on integral closures, ramification
indices of Kummer extensions, and the weak solution obtained when the Kummer tensor product is not
a field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

/-! ### Making a degree-`p` extension have finite level -/

open scoped TensorProduct

namespace Stacks.GaloisTensorSplitting

universe uBase uExtension

variable (Base : Type uBase) (Extension : Type uExtension)
variable [Field Base] [Field Extension] [Algebra Base Extension]

private noncomputable def evaluationHom :
    Extension ⊗[Base] Extension →ₐ[Extension] ((Extension ≃ₐ[Base] Extension) → Extension) :=
  AlgHom.liftEquiv Base Extension Extension _
    (AlgHom.pi fun automorphism : Extension ≃ₐ[Base] Extension ↦ automorphism.toAlgHom)

private theorem evaluationHom_tmul (left right : Extension)
    (automorphism : Extension ≃ₐ[Base] Extension) :
    evaluationHom Base Extension (left ⊗ₜ[Base] right) automorphism =
      left * automorphism right := by
  rfl

private theorem evaluationHom_surjective [FiniteDimensional Base Extension] :
    Function.Surjective (evaluationHom Base Extension) := by
  classical
  have independent : LinearIndependent Extension
      (fun automorphism : Extension ≃ₐ[Base] Extension ↦ (automorphism : Extension → Extension)) :=
    (linearIndependent_monoidHom Extension Extension).comp
      (fun automorphism : Extension ≃ₐ[Base] Extension ↦ automorphism.toMonoidHom)
      (fun left right equality ↦ AlgEquiv.ext fun element ↦ congrArg
        (fun homomorphism : Extension →* Extension ↦ homomorphism element) equality)
  have spanning := span_flip_eq_top_iff_linearIndependent.mpr independent
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← spanning]
  apply Submodule.span_le.mpr
  rintro values ⟨element, rfl⟩
  refine ⟨1 ⊗ₜ[Base] element, ?_⟩
  ext automorphism
  simp [Function.flip_def]

private theorem evaluationHom_bijective [FiniteDimensional Base Extension] [IsGalois Base
  Extension] :
    Function.Bijective (evaluationHom Base Extension) := by
  classical
  let := Fintype.ofFinite (Extension ≃ₐ[Base] Extension)
  have dimension : Module.finrank Extension (Extension ⊗[Base] Extension) =
      Module.finrank Extension ((Extension ≃ₐ[Base] Extension) → Extension) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]
    exact (IsGalois.card_aut_eq_finrank Base Extension).symm.trans Nat.card_eq_fintype_card
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimension).mpr
    (evaluationHom_surjective Base Extension), evaluationHom_surjective Base Extension⟩

private noncomputable def splittingEquiv [FiniteDimensional Base Extension] [IsGalois Base
  Extension] :
    Extension ⊗[Base] Extension ≃ₐ[Extension] ((Extension ≃ₐ[Base] Extension) → Extension) :=
  AlgEquiv.ofBijective (evaluationHom Base Extension) (evaluationHom_bijective Base Extension)

private theorem splittingEquiv_tmul [FiniteDimensional Base Extension] [IsGalois Base Extension]
    (left right : Extension) (automorphism : Extension ≃ₐ[Base] Extension) :
    splittingEquiv Base Extension (left ⊗ₜ[Base] right) automorphism =
      left * automorphism right :=
  evaluationHom_tmul Base Extension left right automorphism

section BaseChange

universe uGround uAuxiliary

variable (Ground : Type uGround) (Auxiliary : Type uAuxiliary)
variable [Field Ground] [Field Auxiliary]
variable [Algebra Ground Base] [Algebra Ground Extension] [Algebra Ground Auxiliary]
variable [IsScalarTower Ground Base Extension]
variable [FiniteDimensional Base Extension] [IsGalois Base Extension]

private noncomputable def baseChangeSplittingEquiv
    (identification : Base ⊗[Ground] Auxiliary ≃ₐ[Base] Extension) :
    Extension ⊗[Ground] Auxiliary ≃ₐ[Extension]
      ((Extension ≃ₐ[Base] Extension) → Extension) :=
  (Algebra.TensorProduct.cancelBaseChange Ground Base Extension Extension Auxiliary).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Extension ≃ₐ[Extension] Extension)
      identification).trans (splittingEquiv Base Extension))

private theorem baseChangeSplittingEquiv_tmul
    (identification : Base ⊗[Ground] Auxiliary ≃ₐ[Base] Extension)
    (left : Extension) (right : Auxiliary) (automorphism : Extension ≃ₐ[Base] Extension) :
    baseChangeSplittingEquiv Base Extension Ground Auxiliary identification
        (left ⊗ₜ[Ground] right) automorphism =
      left * automorphism (identification (1 ⊗ₜ[Ground] right)) := by
  simp [baseChangeSplittingEquiv, splittingEquiv_tmul]

private theorem baseChangeSplittingEquiv_left
    (identification : Base ⊗[Ground] Auxiliary ≃ₐ[Base] Extension)
    (left : Extension) (automorphism : Extension ≃ₐ[Base] Extension) :
    baseChangeSplittingEquiv Base Extension Ground Auxiliary identification
        (left ⊗ₜ[Ground] (1 : Auxiliary)) automorphism = left := by
  rw [baseChangeSplittingEquiv_tmul]
  simp only [Algebra.TensorProduct.one_def.symm, map_one, mul_one]

private theorem baseChangeSplittingEquiv_right
    (identification : Base ⊗[Ground] Auxiliary ≃ₐ[Base] Extension)
    (right : Auxiliary) (automorphism : Extension ≃ₐ[Base] Extension) :
    baseChangeSplittingEquiv Base Extension Ground Auxiliary identification
        ((1 : Extension) ⊗ₜ[Ground] right) automorphism =
      automorphism (identification (1 ⊗ₜ[Ground] right)) := by
  rw [baseChangeSplittingEquiv_tmul, one_mul]

end BaseChange

section IntegralClosure

universe uRing uFraction uIndex

variable (Ring : Type uRing) (Fraction : Type uFraction) (Index : Type uIndex)
variable [CommRing Ring] [IsIntegrallyClosed Ring]
variable [Field Fraction] [Algebra Ring Fraction] [IsFractionRing Ring Fraction] [Finite Index]

private noncomputable def productClosureHom :
    (Index → Ring) →ₐ[Ring] integralClosure Ring (Index → Fraction) :=
  let coordinateMap : (Index → Ring) →ₐ[Ring] (Index → Fraction) :=
    AlgHom.pi fun index ↦ (Algebra.ofId Ring Fraction).comp
      (Pi.evalAlgHom Ring (fun _ : Index ↦ Ring) index)
  coordinateMap.codRestrict (integralClosure Ring (Index → Fraction))
    fun values ↦ (IsIntegral.of_finite Ring values).map coordinateMap

private theorem productClosureHom_bijective :
    Function.Bijective (productClosureHom Ring Fraction Index) := by
  constructor
  · intro left right equality
    funext index
    apply IsFractionRing.injective Ring Fraction
    exact congrArg (fun values : integralClosure Ring (Index → Fraction) ↦ values.val index)
      equality
  · intro values
    have coordinates : ∀ index : Index, ∃ value : Ring,
        algebraMap Ring Fraction value = values.val index := by
      intro index
      exact IsIntegrallyClosed.isIntegral_iff.mp
        (values.property.map (Pi.evalAlgHom Ring (fun _ : Index ↦ Fraction) index))
    choose representatives agreement using coordinates
    refine ⟨representatives, ?_⟩
    exact Subtype.ext (funext agreement)

private noncomputable def productClosureEquiv :
    (Index → Ring) ≃ₐ[Ring] integralClosure Ring (Index → Fraction) :=
  AlgEquiv.ofBijective (productClosureHom Ring Fraction Index)
    (productClosureHom_bijective Ring Fraction Index)

private theorem productClosureEquiv_apply (values : Index → Ring) (index : Index) :
    (productClosureEquiv Ring Fraction Index values).val index =
      algebraMap Ring Fraction (values index) := rfl

private noncomputable def closureEquivOfSplitting {Source : Type*} [CommRing Source] [Algebra Ring
  Source]
    (comparison : Source ≃ₐ[Ring] (Index → Fraction)) :
    integralClosure Ring Source ≃ₐ[Ring] (Index → Ring) :=
  comparison.mapIntegralClosure.trans (productClosureEquiv Ring Fraction Index).symm

private theorem closureEquivOfSplitting_apply {Source : Type*} [CommRing Source] [Algebra Ring
  Source]
    (comparison : Source ≃ₐ[Ring] (Index → Fraction))
    (values : integralClosure Ring Source) (index : Index) :
    algebraMap Ring Fraction
        (closureEquivOfSplitting Ring Fraction Index comparison values index) =
      comparison values.val index :=
  congrArg (fun coordinates : integralClosure Ring (Index → Fraction) ↦ coordinates.val index)
    ((productClosureEquiv Ring Fraction Index).apply_symm_apply
      (comparison.mapIntegralClosure values))

end IntegralClosure

end Stacks.GaloisTensorSplitting

open Polynomial


namespace Stacks.DiscreteValuationRing.IntegralClosureAction

universe uBase uCoefficients uIntegralSource uFraction uAmbient

variable (Base : Type uBase) (Coefficients : Type uCoefficients)
variable (IntegralSource : Type uIntegralSource) (Fraction : Type uFraction)
variable (Ambient : Type uAmbient)
variable [CommRing Base] [CommRing Coefficients] [CommRing IntegralSource]
variable [CommRing Fraction] [CommRing Ambient]
variable [Algebra Base Coefficients] [Algebra Base IntegralSource]
variable [Algebra Base Fraction] [Algebra IntegralSource Fraction]
variable [IsScalarTower Base IntegralSource Fraction]
variable [IsIntegralClosure IntegralSource Base Fraction]
variable [Algebra Base Ambient] [Algebra Coefficients Ambient]
variable [IsScalarTower Base Coefficients Ambient]

private noncomputable def scalarHom (homomorphism : Fraction →ₐ[Base] Ambient) :
    IntegralSource →ₐ[Base] integralClosure Coefficients Ambient :=
  (homomorphism.comp (IsScalarTower.toAlgHom Base IntegralSource Fraction)).codRestrict
    ((integralClosure Coefficients Ambient).restrictScalars Base) fun element ↦
      ((IsIntegralClosure.isIntegral Base Fraction element).map
        (homomorphism.comp (IsScalarTower.toAlgHom Base IntegralSource Fraction))).tower_top

private theorem scalarHom_square (homomorphism : Fraction →ₐ[Base] Ambient)
    (element : IntegralSource) :
    (scalarHom Base Coefficients IntegralSource Fraction Ambient homomorphism element).val =
      homomorphism (algebraMap IntegralSource Fraction element) := rfl

@[instance_reducible]
private noncomputable def scalarAlgebra (homomorphism : Fraction →ₐ[Base] Ambient) :
    Algebra IntegralSource (integralClosure Coefficients Ambient) :=
  (scalarHom Base Coefficients IntegralSource Fraction Ambient homomorphism).toRingHom.toAlgebra

private theorem scalarAlgebra_tower (homomorphism : Fraction →ₐ[Base] Ambient) :
    letI := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
    IsScalarTower Base IntegralSource (integralClosure Coefficients Ambient) :=
  IsScalarTower.of_algHom (scalarHom Base Coefficients IntegralSource Fraction Ambient homomorphism)

variable [Algebra IntegralSource Ambient]

private noncomputable def closureEmbedding (homomorphism : Fraction →ₐ[Base] Ambient)
    (square : ∀ element : IntegralSource,
      homomorphism (algebraMap IntegralSource Fraction element) =
        algebraMap IntegralSource Ambient element) :
    letI := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
    integralClosure Coefficients Ambient →ₐ[IntegralSource] Ambient :=
  letI := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
  { (integralClosure Coefficients Ambient).val.toRingHom with
    commutes' := square }

private theorem closureEmbedding_injective (homomorphism : Fraction →ₐ[Base] Ambient)
    (square : ∀ element : IntegralSource,
      homomorphism (algebraMap IntegralSource Fraction element) =
        algebraMap IntegralSource Ambient element) :
    letI := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
    Function.Injective
      (closureEmbedding Base Coefficients IntegralSource Fraction Ambient homomorphism square) :=
  Subtype.val_injective

private theorem scalarAlgebra_ambient_tower (homomorphism : Fraction →ₐ[Base] Ambient)
    (square : ∀ element : IntegralSource,
      homomorphism (algebraMap IntegralSource Fraction element) =
        algebraMap IntegralSource Ambient element) :
    letI := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
    IsScalarTower IntegralSource (integralClosure Coefficients Ambient) Ambient := by
  let := scalarAlgebra Base Coefficients IntegralSource Fraction Ambient homomorphism
  exact IsScalarTower.of_algebraMap_eq fun element ↦ (square element).symm

end Stacks.DiscreteValuationRing.IntegralClosureAction


open Polynomial

namespace Stacks.DiscreteValuationRing.KummerRamificationDegree

universe uBase uTarget uBaseFraction uTargetFraction

variable (Base : Type uBase) (Target : Type uTarget)
variable (BaseFraction : Type uBaseFraction) (TargetFraction : Type uTargetFraction)
variable [CommRing Base] [IsDomain Base] [IsDiscreteValuationRing Base]
variable [CommRing Target] [IsDomain Target] [IsDiscreteValuationRing Target]
variable [Field BaseFraction] [Field TargetFraction]
variable [Algebra Base Target] [IsDiscreteValuationRing.IsExtension Base Target]
variable [Algebra Base BaseFraction] [IsFractionRing Base BaseFraction]
variable [Algebra Target TargetFraction] [IsFractionRing Target TargetFraction]
variable [Algebra Base TargetFraction] [Algebra BaseFraction TargetFraction]
variable [IsScalarTower Base Target TargetFraction] [IsScalarTower Base BaseFraction TargetFraction]
variable [Module.Finite BaseFraction TargetFraction]

private theorem ramificationIdx_eq_degree_of_integral_uniformizer_root
    (degree : ℕ) (dimension : Module.finrank BaseFraction TargetFraction = degree)
    (uniformizer : Base) (irreducible : Irreducible uniformizer)
    (root : Target) (equation : root ^ degree = algebraMap Base Target uniformizer) :
    (IsLocalRing.maximalIdeal Target).ramificationIdx Base = degree := by
  obtain ⟨targetUniformizer, targetIrreducible⟩ := IsDiscreteValuationRing.exists_irreducible Target
  obtain ⟨unit, unitEquation⟩ :=
    (IsDiscreteValuationRing.ramificationIndex_characterization Base Target).2.2.2
      uniformizer irreducible targetUniformizer targetIrreducible
  have index := IsDiscreteValuationRing.ramificationIndex_eq_ramificationIdx Base Target
  have valuationEquation : IsDiscreteValuationRing.addVal Target
      (algebraMap Base Target uniformizer) =
      ((IsLocalRing.maximalIdeal Target).ramificationIdx Base : ℕ∞) := by
    rw [← index]
    exact IsDiscreteValuationRing.addVal_def _ unit targetIrreducible _ unitEquation
  rw [← equation, IsDiscreteValuationRing.addVal_pow] at valuationEquation
  have divides : degree ∣ (IsLocalRing.maximalIdeal Target).ramificationIdx Base := by
    refine ⟨(IsDiscreteValuationRing.addVal Target root).toNat, ?_⟩
    simpa only [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast] using
      (congrArg ENat.toNat valuationEquation).symm
  have indexPositive : 0 < (IsLocalRing.maximalIdeal Target).ramificationIdx Base := by
    rw [← index]
    exact (IsDiscreteValuationRing.ramificationIndex_characterization Base Target).1
  obtain ⟨residueFinite, bound⟩ :=
    IsDiscreteValuationRing.residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank
      Base Target BaseFraction TargetFraction
  let := residueFinite
  have residuePositive : 0 < Module.finrank (IsLocalRing.ResidueField Base)
      (IsLocalRing.ResidueField Target) := Module.finrank_pos
  exact Nat.le_antisymm
    (((Nat.le_mul_of_pos_right _ residuePositive).trans bound).trans_eq dimension)
    (Nat.le_of_dvd indexPositive divides)

private theorem ramificationIdx_eq_degree_of_fraction_uniformizer_root
    (degree : ℕ) (positive : 0 < degree)
    (dimension : Module.finrank BaseFraction TargetFraction = degree)
    (uniformizer : Base) (irreducible : Irreducible uniformizer)
    (root : TargetFraction)
    (equation : root ^ degree = algebraMap Base TargetFraction uniformizer) :
    (IsLocalRing.maximalIdeal Target).ramificationIdx Base = degree := by
  have integral : IsIntegral Base root :=
    ⟨X ^ degree - C uniformizer, monic_X_pow_sub_C uniformizer (Nat.ne_of_gt positive),
      by simpa using sub_eq_zero.mpr equation⟩
  obtain ⟨integralRoot, rootEquation⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := Target) (K := TargetFraction)).mp integral.tower_top
  apply ramificationIdx_eq_degree_of_integral_uniformizer_root Base Target BaseFraction
    TargetFraction
    degree dimension uniformizer irreducible integralRoot
  apply IsFractionRing.injective Target TargetFraction
  rw [map_pow, rootEquation, equation, IsScalarTower.algebraMap_apply Base Target TargetFraction]

private theorem ramificationIdx_eq_prime_of_kummer_nondivisible
    (prime : ℕ) (primeCondition : prime.Prime)
    (dimension : Module.finrank BaseFraction TargetFraction = prime)
    (uniformizer : Base) (irreducible : Irreducible uniformizer)
    (unit : Baseˣ) (exponent : ℤ) (root : TargetFraction)
    (equation : root ^ prime = algebraMap BaseFraction TargetFraction
      (algebraMap Base BaseFraction unit * algebraMap Base BaseFraction uniformizer ^ exponent))
    (nondivisible : ¬ (prime : ℤ) ∣ exponent) :
    (IsLocalRing.maximalIdeal Target).ramificationIdx Base = prime := by
  have coprime : IsCoprime (prime : ℤ) exponent := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using
      primeCondition.coprime_iff_not_dvd.mpr (mt Int.natCast_dvd.mpr nondivisible)
  obtain ⟨leftCoefficient, rightCoefficient, bezout⟩ := coprime
  let newUniformizer : Base := (↑(unit ^ rightCoefficient) : Base) * uniformizer
  have newIrreducible : Irreducible newUniformizer :=
    (irreducible_isUnit_mul (unit ^ rightCoefficient).isUnit).mpr irreducible
  let newRoot := root ^ rightCoefficient * algebraMap Base TargetFraction uniformizer ^
    leftCoefficient
  have uniformizerNonzero : algebraMap Base TargetFraction uniformizer ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply Base BaseFraction TargetFraction]
    exact (map_ne_zero_iff _ (algebraMap BaseFraction TargetFraction).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective Base BaseFraction)).mpr irreducible.ne_zero)
  have newEquation : newRoot ^ prime = algebraMap Base TargetFraction newUniformizer := by
    have unitPower : algebraMap Base TargetFraction (↑(unit ^ rightCoefficient) : Base) =
        algebraMap Base TargetFraction (unit : Base) ^ rightCoefficient :=
      ((algebraMap Base TargetFraction).toMonoidHom.comp (Units.coeHom Base)).map_zpow unit
        rightCoefficient
    have rootEquation : root ^ prime = algebraMap Base TargetFraction (unit : Base) *
        algebraMap Base TargetFraction uniformizer ^ exponent := by
      simpa only [map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply Base BaseFraction
        TargetFraction]
        using equation
    dsimp [newRoot, newUniformizer]
    rw [mul_pow, ← zpow_natCast (root ^ rightCoefficient) prime, ← zpow_mul,
      mul_comm rightCoefficient (prime : ℤ), zpow_mul, zpow_natCast, rootEquation,
      mul_zpow, map_mul, unitPower]
    rw [← zpow_mul, ← zpow_natCast (algebraMap Base TargetFraction uniformizer ^ leftCoefficient)
      prime,
      ← zpow_mul, mul_assoc, ← zpow_add₀ uniformizerNonzero]
    have exponentEquation : exponent * rightCoefficient + leftCoefficient * (prime : ℤ) = 1 := by
      linarith [bezout]
    rw [exponentEquation, zpow_one]
  exact ramificationIdx_eq_degree_of_fraction_uniformizer_root Base Target BaseFraction
    TargetFraction
    prime primeCondition.pos dimension newUniformizer newIrreducible newRoot newEquation

end Stacks.DiscreteValuationRing.KummerRamificationDegree

namespace Stacks.DiscreteValuationRing.KummerRamificationDegree

universe uBase uFraction uExtension uMiddle uTarget

private theorem normalization_ramificationIdx_eq_degree
    (Base : Type uBase) [CommRing Base] [IsDomain Base] [IsDiscreteValuationRing Base]
    (Fraction : Type uFraction) [Field Fraction] [Algebra Base Fraction] [IsFractionRing Base
      Fraction]
    (Extension : Type uExtension) [Field Extension] [Algebra Fraction Extension]
    [Module.Finite Fraction Extension] [Algebra.IsSeparable Fraction Extension]
    [Algebra Base Extension] [IsScalarTower Base Fraction Extension]
    [IsDiscreteValuationRing (integralClosure Base Extension)]
    (totallyRamified : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo Base Fraction
      Extension)
    (degree : ℕ) (dimension : Module.finrank Fraction Extension = degree) :
    (IsLocalRing.maximalIdeal (integralClosure Base Extension)).ramificationIdx Base = degree := by
  let Normalization := integralClosure Base Extension
  have : Algebra.IsIntegral Base Normalization :=
    IsIntegralClosure.isIntegral_algebra Base Extension
  have injective : Function.Injective (algebraMap Base Normalization) := by
    intro left right equality
    apply IsFractionRing.injective Base Fraction
    apply (algebraMap Fraction Extension).injective
    simpa [IsScalarTower.algebraMap_apply Base Fraction Extension] using congrArg Subtype.val
      equality
  have : Module.IsTorsionFree Base Normalization :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr injective
  have contractedMaximal :
      ((IsLocalRing.maximalIdeal Normalization).comap (algebraMap Base Normalization)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal Normalization)
  let : (IsLocalRing.maximalIdeal Normalization).LiesOver (IsLocalRing.maximalIdeal Base) :=
    ⟨(IsLocalRing.eq_maximalIdeal contractedMaximal).symm⟩
  have nonzero : IsLocalRing.maximalIdeal Base ≠ ⊥ := IsDiscreteValuationRing.not_a_field Base
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal Base)
    (IsLocalRing.maximalIdeal Normalization) nonzero]
  exact (IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_totallyRamified Base Fraction
    Extension
    totallyRamified (IsLocalRing.maximalIdeal Normalization) inferInstance inferInstance).trans
      dimension

private theorem ramificationIdx_eq_of_weaklyUnramified_base
    (Base : Type uBase) (Middle : Type uMiddle) (Target : Type uTarget)
    [CommRing Base] [IsDomain Base] [IsDiscreteValuationRing Base]
    [CommRing Middle] [IsDomain Middle] [IsDiscreteValuationRing Middle]
    [CommRing Target] [IsDomain Target] [IsDiscreteValuationRing Target]
    [Algebra Base Middle] [Algebra Middle Target] [Algebra Base Target]
    [IsScalarTower Base Middle Target]
    [IsDiscreteValuationRing.IsExtension Base Middle] [IsDiscreteValuationRing.IsExtension Middle
      Target]
    (weaklyUnramified : IsDiscreteValuationRing.IsWeaklyUnramified Base Middle) :
    (IsLocalRing.maximalIdeal Target).ramificationIdx Base =
      (IsLocalRing.maximalIdeal Target).ramificationIdx Middle := by
  have : Module.Flat Middle Target := inferInstance
  let : (IsLocalRing.maximalIdeal Target).LiesOver (IsLocalRing.maximalIdeal Middle) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap Middle Target)).symm⟩
  rw [IsDiscreteValuationRing.isWeaklyUnramified_iff_ramificationIdx_eq_one]
    at weaklyUnramified
  have tower := Ideal.ramificationIdx_tower (R := Base)
    (IsLocalRing.maximalIdeal Middle) (IsLocalRing.maximalIdeal Target)
  simpa only [weaklyUnramified, one_mul] using tower

end Stacks.DiscreteValuationRing.KummerRamificationDegree


open scoped TensorProduct

namespace Stacks.WeakSolution.NonfieldKummer

open Stacks.DiscreteValuationRing.KummerRamificationDegree
open Stacks.Kummer.PrimeDegreeExtension

universe uBase uOriginal uBaseFraction uOriginalFraction uExtension uNormalization uIndex

private theorem exists_weakSolution_of_split_tensor
    (Base : Type uBase) (Original : Type uOriginal)
    (BaseFraction : Type uBaseFraction) (OriginalFraction : Type uOriginalFraction)
    (Extension : Type uExtension) (Normalization : Type uNormalization)
    [CommRing Base] [IsDomain Base] [IsDiscreteValuationRing Base]
    [CommRing Original] [IsDomain Original] [IsDiscreteValuationRing Original]
    [Field BaseFraction] [Field OriginalFraction] [Field Extension]
    [CommRing Normalization] [IsDomain Normalization] [IsDiscreteValuationRing Normalization]
    [Algebra Base Original] [Algebra Base BaseFraction] [Algebra Base OriginalFraction]
    [Algebra Original OriginalFraction] [Algebra BaseFraction OriginalFraction]
    [Algebra BaseFraction Extension] [Algebra Base Extension]
    [IsDiscreteValuationRing.IsExtension Base Original]
    [IsFractionRing Base BaseFraction] [IsFractionRing Original OriginalFraction]
    [IsScalarTower Base Original OriginalFraction]
    [IsScalarTower Base BaseFraction OriginalFraction] [IsScalarTower Base BaseFraction Extension]
    [Module.Finite BaseFraction Extension]
    [Algebra Base Normalization] [Algebra Normalization Extension]
    [IsScalarTower Base Normalization Extension]
    [IsIntegralClosure Normalization Base Extension] [IsFractionRing Normalization Extension]
    {Index : Type uIndex} [Finite Index]
    (splitting : OriginalFraction ⊗[BaseFraction] Extension ≃ₐ[OriginalFraction]
      (Index → OriginalFraction))
    (degree : ℕ) (positive : 0 < degree)
    (normalizationIndex : (IsLocalRing.maximalIdeal Normalization).ramificationIdx Base = degree)
    (originalIndex : (IsLocalRing.maximalIdeal Original).ramificationIdx Base = degree) :
    ∃ data : IsDiscreteValuationRing.IntegralClosureBaseChange.{uBase, uOriginal, uBaseFraction,
      uOriginalFraction, uExtension, max uOriginalFraction uExtension, uNormalization,
      max uOriginalFraction uExtension} Base Original BaseFraction OriginalFraction Extension,
      data.IsWeakSolution := by
  classical
  let TensorRing := OriginalFraction ⊗[BaseFraction] Extension
  let ClosureRing := integralClosure Original TensorRing
  have : Algebra.IsIntegral Base Normalization :=
    IsIntegralClosure.isIntegral_algebra Base Extension
  let : Algebra Extension TensorRing := Algebra.TensorProduct.rightAlgebra
  let : Algebra Normalization TensorRing :=
    ((algebraMap Extension TensorRing).comp (algebraMap Normalization Extension)).toAlgebra
  have : IsScalarTower Normalization Extension TensorRing :=
    IsScalarTower.of_algebraMap_eq' rfl
  let rightMap : Extension →ₐ[Base] TensorRing :=
    (Algebra.TensorProduct.includeRight : Extension →ₐ[BaseFraction] TensorRing).restrictScalars
      Base
  let : Algebra Normalization ClosureRing :=
    Stacks.DiscreteValuationRing.IntegralClosureAction.scalarAlgebra Base Original Normalization
      Extension
      TensorRing rightMap
  have : IsScalarTower Base Normalization ClosureRing :=
    Stacks.DiscreteValuationRing.IntegralClosureAction.scalarAlgebra_tower Base Original
      Normalization Extension
      TensorRing
      rightMap
  have square : ∀ element : Normalization,
      rightMap (algebraMap Normalization Extension element) =
        algebraMap Normalization TensorRing element := fun _ ↦ rfl
  have : IsScalarTower Normalization ClosureRing TensorRing :=
    Stacks.DiscreteValuationRing.IntegralClosureAction.scalarAlgebra_ambient_tower
      Base Original Normalization Extension TensorRing rightMap square
  let embedding : ClosureRing →ₐ[Normalization] TensorRing :=
    Stacks.DiscreteValuationRing.IntegralClosureAction.closureEmbedding
      Base Original Normalization Extension TensorRing rightMap square
  have : Module.Flat Normalization ClosureRing :=
    Stacks.RamificationTransport.flat_of_injective_into_field_algebra Normalization Extension
      ClosureRing TensorRing embedding
      (Stacks.DiscreteValuationRing.IntegralClosureAction.closureEmbedding_injective
        Base Original Normalization Extension TensorRing rightMap square)
  let closureComparison : ClosureRing ≃ₐ[Original] (Index → Original) :=
    Stacks.GaloisTensorSplitting.closureEquivOfSplitting Original OriginalFraction Index
      (splitting.restrictScalars Original)
  have weak : ∀ prime : Ideal ClosureRing, prime.IsMaximal → prime.ramificationIdx Normalization =
    1 := by
    intro prime maximal
    let := maximal
    obtain ⟨index, localComparison, _⟩ :=
      Stacks.ProductLocalizations.exists_component_algEquiv_atMaximal Original ClosureRing
        (fun _ : Index ↦ Original) closureComparison prime
    exact Stacks.RamificationTransport.ramificationIdx_eq_one_of_integral_tower
      Base ClosureRing Normalization Original prime localComparison degree positive
      normalizationIndex originalIndex
  have reduced : IsReduced TensorRing := isReduced_of_injective splitting splitting.injective
  let reductionComparison : TensorRing ≃ₐ[BaseFraction] (TensorRing ⧸ nilradical TensorRing) :=
    (AlgEquiv.quotientBot BaseFraction TensorRing).symm.trans
      (Ideal.quotientEquivAlg ⊥ (nilradical TensorRing)
        (AlgEquiv.refl : TensorRing ≃ₐ[BaseFraction] TensorRing)
        (by simp))
  let data : IsDiscreteValuationRing.IntegralClosureBaseChange Base Original BaseFraction
    OriginalFraction Extension :=
    { L₁ := TensorRing
      A₁ := Normalization
      B₁ := ClosureRing
      eL₁ := reductionComparison
      eL₁_left := fun _ ↦ rfl
      eL₁_right := fun _ ↦ rfl
      ringSquare := by
        intro element
        exact Stacks.DiscreteValuationRing.IntegralClosureAction.scalarHom_square
          Base Original Normalization Extension TensorRing rightMap element }
  exact ⟨data, weak⟩

universe uMiddleFraction

private theorem exists_weakSolution_of_primeDegreeKummer_nonfield
    (Base : Type uBase) (Original : Type uOriginal)
    (BaseFraction : Type uBaseFraction) (OriginalFraction : Type uOriginalFraction)
    (Extension : Type uExtension) (Normalization : Type uNormalization)
    (MiddleFraction : Type uMiddleFraction)
    [CommRing Base] [IsDomain Base] [IsDiscreteValuationRing Base]
    [CommRing Original] [IsDomain Original] [IsDiscreteValuationRing Original]
    [Field BaseFraction] [Field OriginalFraction] [Field Extension] [Field MiddleFraction]
    [CommRing Normalization] [IsDomain Normalization] [IsDiscreteValuationRing Normalization]
    [Algebra Base Original] [Algebra Base BaseFraction] [Algebra Base OriginalFraction]
    [Algebra Original OriginalFraction] [Algebra BaseFraction OriginalFraction]
    [Algebra BaseFraction Extension] [Algebra Base Extension]
    [IsDiscreteValuationRing.IsExtension Base Original]
    [IsFractionRing Base BaseFraction] [IsFractionRing Original OriginalFraction]
    [IsScalarTower Base Original OriginalFraction]
    [IsScalarTower Base BaseFraction OriginalFraction] [IsScalarTower Base BaseFraction Extension]
    [Module.Finite BaseFraction Extension]
    [Algebra Base Normalization] [Algebra Normalization Extension]
    [IsScalarTower Base Normalization Extension]
    [IsIntegralClosure Normalization Base Extension] [IsFractionRing Normalization Extension]
    [Algebra BaseFraction MiddleFraction] [Algebra MiddleFraction OriginalFraction]
    [IsScalarTower BaseFraction MiddleFraction OriginalFraction]
    [Module.Finite MiddleFraction OriginalFraction] [IsGalois MiddleFraction OriginalFraction]
    (prime : ℕ) (primeCondition : prime.Prime)
    (parameter : MiddleFraction) (generator : OriginalFraction)
    (generatorEquation : generator ^ prime = algebraMap MiddleFraction OriginalFraction parameter)
    (generates : Algebra.adjoin MiddleFraction {generator} = ⊤)
    (middleDegree : Module.finrank MiddleFraction OriginalFraction = prime)
    (extensionDegree : Module.finrank BaseFraction Extension = prime)
    (baseChangeField : IsField (MiddleFraction ⊗[BaseFraction] Extension))
    (notField : ¬ IsField (OriginalFraction ⊗[BaseFraction] Extension))
    (normalizationIndex : (IsLocalRing.maximalIdeal Normalization).ramificationIdx Base = prime)
    (originalIndex : (IsLocalRing.maximalIdeal Original).ramificationIdx Base = prime) :
    ∃ data : IsDiscreteValuationRing.IntegralClosureBaseChange.{uBase, uOriginal, uBaseFraction,
      uOriginalFraction, uExtension, max uOriginalFraction uExtension, uNormalization,
      max uOriginalFraction uExtension} Base Original BaseFraction OriginalFraction Extension,
      data.IsWeakSolution := by
  let := baseChangeField.toField
  obtain ⟨identification⟩ :=
    nonempty_baseChange_algEquiv_of_generator_of_tensor_not_isField
      MiddleFraction OriginalFraction BaseFraction Extension prime primeCondition parameter
        generator
      generatorEquation generates middleDegree extensionDegree baseChangeField notField
  let splitting := Stacks.GaloisTensorSplitting.baseChangeSplittingEquiv
    MiddleFraction OriginalFraction BaseFraction Extension identification
  exact exists_weakSolution_of_split_tensor Base Original BaseFraction OriginalFraction Extension
    Normalization splitting prime primeCondition.pos normalizationIndex originalIndex

universe uMiddle

theorem exists_weakSolution_of_nondivisible_kummer_nonfield
    (Base : Type uBase) (Middle : Type uMiddle) (Original : Type uOriginal)
    (BaseFraction : Type uBaseFraction) (MiddleFraction : Type uMiddleFraction)
    (OriginalFraction : Type uOriginalFraction) (Extension : Type uExtension)
    [CommRing Base] [CommRing Middle] [CommRing Original]
    [IsDomain Base] [IsDomain Middle] [IsDomain Original]
    [IsDiscreteValuationRing Base] [IsDiscreteValuationRing Middle] [IsDiscreteValuationRing
      Original]
    [Field BaseFraction] [Field MiddleFraction] [Field OriginalFraction] [Field Extension]
    [Algebra Base Middle] [Algebra Middle Original] [Algebra Base Original]
    [Algebra Base BaseFraction] [Algebra Middle MiddleFraction] [Algebra Original OriginalFraction]
    [Algebra BaseFraction MiddleFraction] [Algebra MiddleFraction OriginalFraction]
    [Algebra BaseFraction OriginalFraction] [Algebra Base MiddleFraction]
    [Algebra Base OriginalFraction] [Algebra Middle OriginalFraction]
    [Algebra BaseFraction Extension] [Algebra Base Extension]
    [IsScalarTower Base Middle Original] [IsScalarTower Base Middle MiddleFraction]
    [IsScalarTower Middle Original OriginalFraction] [IsScalarTower Middle MiddleFraction
      OriginalFraction]
    [IsScalarTower Base Original OriginalFraction] [IsScalarTower Base BaseFraction MiddleFraction]
    [IsScalarTower Base BaseFraction OriginalFraction] [IsScalarTower BaseFraction MiddleFraction
      OriginalFraction]
    [IsScalarTower Base BaseFraction Extension]
    [IsDiscreteValuationRing.IsExtension Base Middle] [IsDiscreteValuationRing.IsExtension Middle
      Original]
    [IsDiscreteValuationRing.IsExtension Base Original]
    [IsFractionRing Base BaseFraction] [IsFractionRing Middle MiddleFraction]
    [IsFractionRing Original OriginalFraction]
    [Module.Finite MiddleFraction OriginalFraction] [IsGalois MiddleFraction OriginalFraction]
    [Module.Finite BaseFraction Extension] [Algebra.IsSeparable BaseFraction Extension]
    [IsDiscreteValuationRing (integralClosure Base Extension)]
    (weaklyUnramified : IsDiscreteValuationRing.IsWeaklyUnramified Base Middle)
    (prime : ℕ) (primeCondition : prime.Prime)
    (middleDegree : Module.finrank MiddleFraction OriginalFraction = prime)
    (extensionDegree : Module.finrank BaseFraction Extension = prime)
    (uniformizer : Middle) (irreducible : Irreducible uniformizer)
    (unit : Middleˣ) (exponent : ℤ) (generator : OriginalFraction)
    (generatorEquation : generator ^ prime = algebraMap MiddleFraction OriginalFraction
      (algebraMap Middle MiddleFraction unit * algebraMap Middle MiddleFraction uniformizer ^
        exponent))
    (nondivisible : ¬ (prime : ℤ) ∣ exponent)
    (generates : Algebra.adjoin MiddleFraction {generator} = ⊤)
    (totallyRamified : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo Base BaseFraction
      Extension)
    (baseChangeField : IsField (MiddleFraction ⊗[BaseFraction] Extension))
    (notField : ¬ IsField (OriginalFraction ⊗[BaseFraction] Extension)) :
    ∃ data : IsDiscreteValuationRing.IntegralClosureBaseChange.{uBase, uOriginal, uBaseFraction,
      uOriginalFraction, uExtension, max uOriginalFraction uExtension, uExtension,
      max uOriginalFraction uExtension} Base Original BaseFraction OriginalFraction Extension,
      data.IsWeakSolution := by
  let : IsFractionRing (integralClosure Base Extension) Extension :=
    integralClosure.isFractionRing_of_finite_extension BaseFraction Extension
  have normalizationIndex :=
    Stacks.DiscreteValuationRing.KummerRamificationDegree.normalization_ramificationIdx_eq_degree
    Base BaseFraction Extension totallyRamified prime extensionDegree
  have middleIndex :=
    ramificationIdx_eq_prime_of_kummer_nondivisible
    Middle Original MiddleFraction OriginalFraction prime primeCondition middleDegree
    uniformizer irreducible unit exponent generator generatorEquation nondivisible
  have originalIndex :=
    (ramificationIdx_eq_of_weaklyUnramified_base
      Base Middle Original weaklyUnramified).trans middleIndex
  exact exists_weakSolution_of_primeDegreeKummer_nonfield Base Original BaseFraction
    OriginalFraction
    Extension (integralClosure Base Extension) MiddleFraction prime primeCondition
    (algebraMap Middle MiddleFraction unit * algebraMap Middle MiddleFraction uniformizer ^
      exponent)
    generator generatorEquation generates middleDegree extensionDegree baseChangeField notField
    normalizationIndex originalIndex

end Stacks.WeakSolution.NonfieldKummer
