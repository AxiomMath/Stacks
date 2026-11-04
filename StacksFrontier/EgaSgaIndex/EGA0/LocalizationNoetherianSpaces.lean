module  -- shake: keep-all

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Group.Submonoid.Saturation
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.LocalRing.LocalSubring
import StacksCore.Algebra.Module.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA 0, §§1–2: references registered by name

Declarations realizing numbered items of EGA 0, §1 (rings of fractions) and §2 (irreducible
spaces, Noetherian spaces), from the EGA/SGA concept index, that are not tagged where they are
declared: Mathlib and core declarations without an `add_to_stacks` pointer in this library, and
(with `--draft-only`) those of `StacksCore/`.
Part of the EGA 0 index, split by section.
-/

add_to_ega "0 1.0.1" CommRing
add_to_ega "0 1.0.1" IsUnital
add_to_ega "0 1.0.1" Module
add_to_ega "0 1.0.1" Ring
add_to_ega "0 1.0.1" RingHom
add_to_ega "0 1.0.1" Subring
add_to_ega "0 1.0.1" "more general" Subring.one_mem
add_to_ega "0 1.0.2" LinearMap
add_to_ega "0 1.0.2" LinearMap.mk
add_to_ega "0 1.0.2" Module.compHom
add_to_ega "0 1.0.2" "special case" Module.restrictScalars
add_to_ega "0 1.0.2" "φ is the identity" ModuleCat.Hom
add_to_ega "0 1.0.2" ModuleCat.RestrictScalars.obj'
add_to_ega "0 1.0.2" "special case" ModuleCat.moduleCategory
add_to_ega "0 1.0.2" "special case" ModuleCat.moduleOfAlgebraModule
add_to_ega "0 1.0.2" ModuleCat.restrictScalars
add_to_ega "0 1.0.2" "partial" ModuleCat.restrictScalars.smul_def
add_to_ega "0 1.0.2" "partial" ModuleCat.restrictScalars.smul_def'
add_to_ega "0 1.0.2" ModuleCat.semilinearMapAddEquiv
add_to_ega "0 1.0.2" "partial" ModuleCat.smul_restrictScalars
add_to_ega "0 1.0.2" "special case" RestrictScalars.module
add_to_ega "0 1.0.2" "special case" RingHom.toModule
add_to_ega "0 1.0.2" SemilinearMapClass
add_to_ega "0 1.0.2" "special case" SemimoduleCat.Algebra.instModuleCarrier
add_to_ega "0 1.0.3" "special case" ClassGroup.extendedIdeal
add_to_ega "0 1.0.3" Ideal.map
add_to_ega "0 1.0.3" "special case" Ideal.map_includeLeft_eq
add_to_ega "0 1.0.3" "special case" Ideal.map_includeRight_eq
add_to_ega "0 1.0.3" "special case" Submodule.map_range_rTensor_subtype_lid
add_to_ega "0 1.0.3" "special case" TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
add_to_ega "0 1.0.4" Algebra
add_to_ega "0 1.0.4" Ideal.map
add_to_ega "0 1.0.4" "special case" Ideal.smul_restrictScalars
add_to_ega "0 1.0.4" "special case" Ideal.smul_top_eq_map
add_to_ega "0 1.0.4" "commutative target" RingHom.toAlgebra
add_to_ega "0 1.0.4" RingHom.toAlgebra'
add_to_ega "0 1.0.4" "partial" Set.algebraMap_mem_center
add_to_ega "0 1.0.4" "JB = BJ" Submodule.algebraIdeal
add_to_ega "0 1.0.4" Submodule.instSMul
add_to_ega "0 1.0.4" "special case" Submodule.restrictScalars_map_smul_eq
add_to_ega "0 1.0.5" AlgHom.Finite
add_to_ega "0 1.0.5" AlgHom.FiniteType
add_to_ega "0 1.0.5" Algebra.FiniteType
add_to_ega "0 1.0.5" Algebra.FiniteType.iff_exists_generators
add_to_ega "0 1.0.5" "partial" Algebra.Generators.finiteType
add_to_ega "0 1.0.5" Algebra.IsIntegral
add_to_ega "0 1.0.5" "partial" Algebra.IsIntegral.finite
add_to_ega "0 1.0.5" "partial, special case" Algebra.IsIntegral.of_finite
add_to_ega "0 1.0.5" "more general" Algebra.finite_adjoin_of_finite_of_isIntegral
add_to_ega "0 1.0.5" "partial" Algebra.finite_adjoin_simple_of_isIntegral
add_to_ega "0 1.0.5" CommAlgCat.finite
add_to_ega "0 1.0.5" IsIntegral
add_to_ega "0 1.0.5" "partial" IsIntegral.fg_adjoin_singleton
add_to_ega "0 1.0.5" "partial, special case" IsIntegral.of_finite
add_to_ega "0 1.0.5" "partial" IsIntegral.of_mem_of_fg
add_to_ega "0 1.0.5" Module.Finite
add_to_ega "0 1.0.5" "partial" Module.Finite.finiteType
add_to_ega "0 1.0.5" Module.FinitePresentation
add_to_ega "0 1.0.5" "partial" Module.FinitePresentation.of_exact_third
add_to_ega "0 1.0.5" "partial" Module.Presentation.finite
add_to_ega "0 1.0.5" "partial" Module.Presentation.finitePresentation
add_to_ega "0 1.0.5" "partial" Module.exists_finite_presentation
add_to_ega "0 1.0.5" Module.finitePresentation_iff_exists_presentation
add_to_ega "0 1.0.5" "more general" Module.finitePresentation_iff_finite
add_to_ega "0 1.0.5" "partial" Module.finitePresentation_of_free_of_surjective
add_to_ega "0 1.0.5" "partial" Module.finitePresentation_of_surjective
add_to_ega "0 1.0.5" ModuleCat.isFG
add_to_ega "0 1.0.5" "partial" RingHom.Finite.of_isIntegral_of_finiteType
add_to_ega "0 1.0.5" RingHom.FiniteType
add_to_ega "0 1.0.5" "partial" RingHom.IsIntegral.to_finite
add_to_ega "0 1.0.5" RingHom.finite_iff_isIntegral_and_finiteType
add_to_ega "0 1.0.5" Subalgebra.FG
add_to_ega "0 1.0.5" "partial" Subalgebra.fg_of_fg_toSubmodule
add_to_ega "0 1.0.5" "partial" Subalgebra.fg_of_submodule_fg
add_to_ega "0 1.0.5" Submodule.FG
add_to_ega "0 1.0.5" "more general" fg_adjoin_of_finite
add_to_ega "0 1.0.5" "partial" isIntegral_of_submodule_noetherian
add_to_ega "0 1.0.5" "special case" mem_integralClosure_iff_mem_fg
add_to_ega "0 1.0.6" Ideal.IsPrime
add_to_ega "0 1.0.6" "partial" Ideal.Quotient.isDomain
add_to_ega "0 1.0.6" "more general" Ideal.Quotient.isDomain_iff_prime
add_to_ega "0 1.0.6" "partial" Ideal.Quotient.noZeroDivisors
add_to_ega "0 1.0.6" "more general" Ideal.eq_bot_of_minimalPrimes_eq_empty
add_to_ega "0 1.0.6" "special case" Ideal.isPrime_bot
add_to_ega "0 1.0.6" "more general" Ideal.nonempty_minimalPrimes
add_to_ega "0 1.0.6" IsDomain
add_to_ega "0 1.0.6" "Zero-ideal case" IsDomain.of_bot_isPrime
add_to_ega "0 1.0.6" "partial" IsDomain.to_noZeroDivisors
add_to_ega "0 1.0.6" "binary condition" NoZeroDivisors
add_to_ega "0 1.0.6" "partial" NoZeroDivisors.to_isDomain
add_to_ega "0 1.0.6" "condition 0 ≠ 1" Nontrivial
add_to_ega "0 1.0.6" "necessity" PrimeSpectrum.nontrivial
add_to_ega "0 1.0.6" "more general" isDomain_iff_noZeroDivisors_and_nontrivial
add_to_ega "0 1.0.6" "more general" noZeroDivisors_iff_isDomain_or_subsingleton
add_to_ega "0 1.0.7" "more general" CommRingCat.isLocalHom_comp
add_to_ega "0 1.0.7" "more general" Ideal.ResidueField.map
add_to_ega "0 1.0.7" "more general" Ideal.ResidueField.mapₐ
add_to_ega "0 1.0.7" IsLocalHom
add_to_ega "0 1.0.7" IsLocalRing
add_to_ega "0 1.0.7" IsLocalRing.ResidueField
add_to_ega "0 1.0.7" IsLocalRing.ResidueField.instAlgebra
add_to_ega "0 1.0.7" "target is a field" IsLocalRing.ResidueField.lift
add_to_ega "0 1.0.7" "special case" IsLocalRing.ResidueField.lift_comp_residue
add_to_ega "0 1.0.7" IsLocalRing.ResidueField.map
add_to_ega "0 1.0.7" "algebra isomorphisms" IsLocalRing.ResidueField.mapAlgEquiv
add_to_ega "0 1.0.7" IsLocalRing.ResidueField.mapAlgHom
add_to_ega "0 1.0.7" "special case" IsLocalRing.ResidueField.mapAlgHom'
add_to_ega "0 1.0.7" "special case" IsLocalRing.ResidueField.mapAlgHom'_residue
add_to_ega "0 1.0.7" "partial" IsLocalRing.ResidueField.mapAlgHom_residue
add_to_ega "0 1.0.7" "partial" IsLocalRing.ResidueField.map_comp_residue
add_to_ega "0 1.0.7" "partial" IsLocalRing.ResidueField.map_residue
add_to_ega "0 1.0.7" "partial" IsLocalRing.eq_maximalIdeal
add_to_ega "0 1.0.7" "partial" IsLocalRing.instUniqueMaximalSpectrum
add_to_ega "0 1.0.7" "partial" IsLocalRing.isMaximal_iff
add_to_ega "0 1.0.7" "partial" IsLocalRing.le_maximalIdeal
add_to_ega "0 1.0.7" "special case" IsLocalRing.le_maximalIdeal_of_isPrime
add_to_ega "0 1.0.7" "more general" IsLocalRing.local_hom_TFAE
add_to_ega "0 1.0.7" "local implies φ(m)⊆n" IsLocalRing.map_maximalIdeal_le
add_to_ega "0 1.0.7" IsLocalRing.maximalIdeal
add_to_ega "0 1.0.7" "partial" IsLocalRing.maximalIdeal.isMaximal
add_to_ega "0 1.0.7" "local implies φ⁻¹(n)=m" IsLocalRing.maximalIdeal_comap
add_to_ega "0 1.0.7" "partial" IsLocalRing.maximal_ideal_unique
add_to_ega "0 1.0.7" "partial" IsLocalRing.mem_maximalIdeal
add_to_ega "0 1.0.7" "partial" IsLocalRing.notMem_maximalIdeal
add_to_ega "0 1.0.7" "partial" IsLocalRing.of_unique_max_ideal
add_to_ega "0 1.0.7" "more general" MonoidHom.isLocalHom_comp
add_to_ega "0 1.0.7" "more general" RingHom.isLocalHom_comp
add_to_ega "0 1.1.1" "more general" Ideal.comap_radical
add_to_ega "0 1.1.1" "more general" Ideal.finite_minimalPrimes_of_isNoetherianRing
add_to_ega "0 1.1.1" "more general" Ideal.isRadical_bot_iff
add_to_ega "0 1.1.1" "a ⊆ r(a)" Ideal.le_radical
add_to_ega "0 1.1.1" "r(r(a)) ⊆ r(a)" Ideal.mem_radical_of_pow_mem
add_to_ega "0 1.1.1" Ideal.radical
add_to_ega "0 1.1.1" "partial" Ideal.radicalInfTopHom
add_to_ega "0 1.1.1" "partial" Ideal.radical_eq_sInf
add_to_ega "0 1.1.1" "partial" Ideal.radical_iInf_le
add_to_ega "0 1.1.1" "more general" Ideal.radical_idem
add_to_ega "0 1.1.1" "binary intersection" Ideal.radical_inf
add_to_ega "0 1.1.1" "r(r(a)) ⊆ r(a)" Ideal.radical_isRadical
add_to_ega "0 1.1.1" "more general" Ideal.radical_le_radical_iff
add_to_ega "0 1.1.1" "more general" Ideal.radical_mono
add_to_ega "0 1.1.1" "more general" Ideal.sInf_minimalPrimes
add_to_ega "0 1.1.1" IsReduced
add_to_ega "0 1.1.1" "the ideal a = (0)" PrimeSpectrum.finite_setOfPred_isMin
add_to_ega "0 1.1.1" "the ideal a = (0)" PrimeSpectrum.finite_setOf_isMin
add_to_ega "0 1.1.1" "zero ideal, special case" PrimeSpectrum.nilradical_eq_iInf
add_to_ega "0 1.1.1" "more general" mem_nilradical
add_to_ega "0 1.1.1" "special case" nilpotent_iff_mem_prime
add_to_ega "0 1.1.1" nilradical
add_to_ega "0 1.1.1" "more general" nilradical_eq_bot_iff
add_to_ega "0 1.1.1" "special case" nilradical_eq_sInf
add_to_ega "0 1.1.1" "partial" nilradical_eq_zero
add_to_ega "0 1.1.2" "more general" Ideal.jacobson
add_to_ega "0 1.1.2" "more general" Module.jacobson
add_to_ega "0 1.1.2" "more general" Module.jacobson_quotient_jacobson
add_to_ega "0 1.1.2" Ring.jacobson
add_to_ega "0 1.1.2" Ring.jacobson_eq_sInf_isMaximal
add_to_ega "0 1.1.2" Ring.jacobson_quotient_jacobson
add_to_ega "0 1.1.2" "more general" Ring.jacobson_quotient_of_le
add_to_ega "0 1.1.2" "more general" TwoSidedIdeal.jacobson
add_to_ega "0 1.2.1" "partial" Ideal.IsPrime.mul_notMem
add_to_ega "0 1.2.1" Ideal.primeCompl
add_to_ega "0 1.2.1" Submonoid
add_to_ega "0 1.2.1" "more general" Submonoid.coe_powers
add_to_ega "0 1.2.1" Submonoid.powers
add_to_ega "0 1.2.2" "special case" FractionRing
add_to_ega "0 1.2.2" "partial" IsLocalization.mk'_add
add_to_ega "0 1.2.2" IsLocalizedModule.mk'
add_to_ega "0 1.2.2" "special case" IsLocalizedModule.mk'_add
add_to_ega "0 1.2.2" "addition formula" IsLocalizedModule.mk'_add_mk'
add_to_ega "0 1.2.2" "more general" IsLocalizedModule.mk'_eq_iff
add_to_ega "0 1.2.2" "partial" IsLocalizedModule.mk'_smul_mk'
add_to_ega "0 1.2.2" Localization
add_to_ega "0 1.2.2" "partial" Localization.add_mk
add_to_ega "0 1.2.2" "M = A, partial" Localization.add_mk_self
add_to_ega "0 1.2.2" "M = A" Localization.mk
add_to_ega "0 1.2.2" "M = A" Localization.mk_eq_mk_iff
add_to_ega "0 1.2.2" "M = A, partial" Localization.mk_mul
add_to_ega "0 1.2.2" "M = A, partial" Localization.mk_one_eq_algebraMap
add_to_ega "0 1.2.2" "M = A" Localization.r'
add_to_ega "0 1.2.2" "M = A" Localization.r_iff_exists
add_to_ega "0 1.2.2" LocalizedModule
add_to_ega "0 1.2.2" "more general" LocalizedModule.instRing
add_to_ega "0 1.2.2" "partial" LocalizedModule.mem_ker_mkLinearMap_iff
add_to_ega "0 1.2.2" LocalizedModule.mk
add_to_ega "0 1.2.2" LocalizedModule.mkLinearMap
add_to_ega "0 1.2.2" LocalizedModule.mkLinearMap_apply
add_to_ega "0 1.2.2" "partial" LocalizedModule.mk_add_mk
add_to_ega "0 1.2.2" "partial" LocalizedModule.mk_eq
add_to_ega "0 1.2.2" "partial" LocalizedModule.mk_mul_mk
add_to_ega "0 1.2.2" "partial" LocalizedModule.mk_smul_mk
add_to_ega "0 1.2.2" "partial, special case" LocalizedModule.numeratorRingHom
add_to_ega "0 1.2.2" LocalizedModule.r
add_to_ega "0 1.2.2" "more general" LocalizedModule.r.isEquiv
add_to_ega "0 1.2.2" LocalizedModule.r.setoid
add_to_ega "0 1.2.2" "partial" LocalizedModule.smul'_mk
add_to_ega "0 1.2.2" "partial" ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule
add_to_ega "0 1.2.2" ModuleCat.localizedModuleMkLinearMap
add_to_ega "0 1.2.2" "partial" OreLocalization.instDistribMulAction
add_to_ega "0 1.2.2" "partial" OreLocalization.instMul
add_to_ega "0 1.2.2" "partial" OreLocalization.instMulActionOreLocalization
add_to_ega "0 1.2.2" "partial" OreLocalization.instSMul
add_to_ega "0 1.2.2" "more general" OreLocalization.mul_inv
add_to_ega "0 1.2.2" "more general" OreLocalization.numeratorUnit
add_to_ega "0 1.2.2" "partial" OreLocalization.numerator_isUnit
add_to_ega "0 1.2.2" "more general" OreLocalization.oreEqv
add_to_ega "0 1.2.2" "partial" OreLocalization.smul
add_to_ega "0 1.2.3" Algebra.Presentation.localizationAway
add_to_ega "0 1.2.3" AlgebraicGeometry.StructureSheaf.Localizations
add_to_ega "0 1.2.3" "monomorphism A/p → A_p/q" Ideal.injective_algebraMap_quotient_residueField
add_to_ega "0 1.2.3" Ideal.primeCompl
add_to_ega "0 1.2.3" IsLocalization.AtPrime
add_to_ega "0 1.2.3" "contraction of q is p" IsLocalization.AtPrime.comap_maximalIdeal
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.comap_maximalIdeal_pow
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.equivQuotMaximalIdeal
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk
add_to_ega "0 1.2.3" "A_p is a local ring" IsLocalization.AtPrime.isLocalRing
add_to_ega "0 1.2.3" "partial" IsLocalization.AtPrime.isMaximal_map
add_to_ega "0 1.2.3" "partial" IsLocalization.AtPrime.map_eq_maximalIdeal
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.under_map_of_isMaximal
add_to_ega "0 1.2.3" "contraction of q is p" IsLocalization.AtPrime.under_maximalIdeal
add_to_ega "0 1.2.3" "special case" IsLocalization.AtPrime.under_maximalIdeal_pow
add_to_ega "0 1.2.3" IsLocalization.Away
add_to_ega "0 1.2.3" IsLocalization.Away.mvPolynomialQuotientEquiv
add_to_ega "0 1.2.3" "ring clause: A_1 ≅ A" IsLocalization.atOne
add_to_ega "0 1.2.3" "ring clause: A_1 ≅ A" IsLocalization.atUnit
add_to_ega "0 1.2.3" IsLocalizedModule.AtPrime
add_to_ega "0 1.2.3" Localization.AtPrime
add_to_ega "0 1.2.3" "contraction of q is p" Localization.AtPrime.comap_maximalIdeal
add_to_ega "0 1.2.3" "contraction of q is p" Localization.AtPrime.eq_maximalIdeal_iff_comap_eq
add_to_ega "0 1.2.3" "contraction of q is p" Localization.AtPrime.eq_maximalIdeal_iff_under_eq
add_to_ega "0 1.2.3" "A_p is a local ring" Localization.AtPrime.isLocalRing
add_to_ega "0 1.2.3" "partial" Localization.AtPrime.map_eq_maximalIdeal
add_to_ega "0 1.2.3" "contraction of q is p" Localization.AtPrime.under_maximalIdeal
add_to_ega "0 1.2.3" Localization.Away
add_to_ega "0 1.2.3" Localization.awayEquivAdjoin
add_to_ega "0 1.2.3" LocalizedModule.AtPrime
add_to_ega "0 1.2.3" "more general" LocalizedModule.subsingleton
add_to_ega "0 1.2.3" Submonoid.powers
add_to_ega "0 1.2.3" instIsFractionRingQuotientIdealResidueField
add_to_ega "0 1.2.4" "special case" IsLocalization.Away.lift
add_to_ega "0 1.2.4" IsLocalization.lift
add_to_ega "0 1.2.4" "uniqueness of u*" IsLocalization.lift_unique
add_to_ega "0 1.2.4" "uniqueness of u*" IsLocalization.ringHom_ext
add_to_ega "0 1.2.4" "uniqueness of v*" IsLocalizedModule.ext
add_to_ega "0 1.2.4" "partial" IsLocalizedModule.is_universal
add_to_ega "0 1.2.4" IsLocalizedModule.lift
add_to_ega "0 1.2.4" "uniqueness of v*" IsLocalizedModule.lift_unique
add_to_ega "0 1.2.4" "special case" Localization.awayLift
add_to_ega "0 1.2.4" LocalizedModule.lift
add_to_ega "0 1.2.4" "partial" LocalizedModule.lift_comp
add_to_ega "0 1.2.4" "uniqueness of v*" LocalizedModule.lift_unique
add_to_ega "0 1.2.4" OreLocalization.universalHom
add_to_ega "0 1.2.4" "partial" OreLocalization.universalHom_commutes
add_to_ega "0 1.2.4" "uniqueness of u*" OreLocalization.universalHom_unique
add_to_ega "0 1.2.5" "special case" IsLocalization.Away.tensorEquiv
add_to_ega "0 1.2.5" "special case" IsLocalization.tensor
add_to_ega "0 1.2.5" "special case" IsLocalization.tensorProductEquivOfMapIncludeRight
add_to_ega "0 1.2.5" "more general" IsLocalization.tensorProduct_isLocalizedModule
add_to_ega "0 1.2.5" LocalizedModule.equivTensorProduct
add_to_ega "0 1.2.5" "partial" LocalizedModule.equivTensorProduct_apply_mk
add_to_ega "0 1.2.5" "partial" LocalizedModule.equivTensorProduct_symm_apply_tmul
add_to_ega "0 1.2.5" "partial" LocalizedModule.equivTensorProduct_symm_apply_tmul_one
add_to_ega "0 1.2.6" Ideal.comap
add_to_ega "0 1.2.6" "partial" Ideal.localized'_eq_map
add_to_ega "0 1.2.6" "partial" Ideal.localized₀_eq_restrictScalars_map
add_to_ega "0 1.2.6" Ideal.map
add_to_ega "0 1.2.6" "partial" Ideal.under_map_of_isLocalizationAtPrime
add_to_ega "0 1.2.6" "S = A \\ I for a prime I" IsLocalization.AtPrime.orderIsoOfPrime
add_to_ega "0 1.2.6" "S = A \\ I for a prime I" IsLocalization.AtPrime.primeSpectrumOrderIso
add_to_ega "0 1.2.6" "partial" IsLocalization.comap_map_of_isPrimary_disjoint
add_to_ega "0 1.2.6" "partial" IsLocalization.comap_map_of_isPrime_disjoint
add_to_ega "0 1.2.6" "partial" IsLocalization.disjoint_comap_iff
add_to_ega "0 1.2.6" IsLocalization.isLocalization_atPrime_localization_atPrime
add_to_ega "0 1.2.6" "more general"
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
add_to_ega "0 1.2.6" "partial" IsLocalization.isPrime_iff_isPrime_disjoint
add_to_ega "0 1.2.6" IsLocalization.localizationLocalizationAtPrimeIsoLocalization
add_to_ega "0 1.2.6" "partial" IsLocalization.map_comap
add_to_ega "0 1.2.6" "partial" IsLocalization.map_under
add_to_ega "0 1.2.6" "partial" IsLocalization.orderEmbedding
add_to_ega "0 1.2.6" IsLocalization.orderIsoOfPrime
add_to_ega "0 1.2.6" IsLocalization.primeSpectrumOrderIso
add_to_ega "0 1.2.6" "partial" IsLocalization.under_le_under_iff
add_to_ega "0 1.2.6" "partial" IsLocalization.under_map_of_isPrimary_disjoint
add_to_ega "0 1.2.6" "partial" IsLocalization.under_map_of_isPrime_disjoint
add_to_ega "0 1.2.7" "S = A∖{0}" IsFractionRing.injective
add_to_ega "0 1.2.7" IsLocalization.AtPrime
add_to_ega "0 1.2.7" "A_p is local" IsLocalization.AtPrime.isLocalRing
add_to_ega "0 1.2.7" "pA_p is maximal" IsLocalization.AtPrime.isMaximal_map
add_to_ega "0 1.2.7" "partial" IsLocalization.AtPrime.map_eq_maximalIdeal
add_to_ega "0 1.2.7" "pA_p ∩ A = p" IsLocalization.AtPrime.under_maximalIdeal
add_to_ega "0 1.2.7" "more general" IsLocalization.injective
add_to_ega "0 1.2.7" "more general" IsLocalization.injective_iff_isRegular
add_to_ega "0 1.2.7" "more general" IsLocalization.injectiveₛ
add_to_ega "0 1.2.7" "more general" IsLocalization.map_injective_of_injective'
add_to_ega "0 1.2.7" "more general" IsLocalizedModule.injective_iff_isRegular
add_to_ega "0 1.2.7" "A_p is local, S = A∖P"
  LocalSubring.instAtPrimeSubtypeMemSubringToSubringOfPrime
add_to_ega "0 1.2.7" "A_p contains A" LocalSubring.le_ofPrime
add_to_ega "0 1.2.7" "A_p is local, S = A∖P" LocalSubring.ofPrime
add_to_ega "0 1.2.7" "A_p is local, S = A∖P" LocalSubring.ofPrimeEquiv
add_to_ega "0 1.2.7" Localization.AtPrime
add_to_ega "0 1.2.7" "pA_p ∩ A = p" Localization.AtPrime.comap_maximalIdeal
add_to_ega "0 1.2.7" "pA_p ∩ A = p" Localization.AtPrime.eq_maximalIdeal_iff_comap_eq
add_to_ega "0 1.2.7" "A_p is local" Localization.AtPrime.isLocalRing
add_to_ega "0 1.2.7" "more general" Localization.isLocalization_range_mapToFractionRing
add_to_ega "0 1.2.7" Localization.subalgebra
add_to_ega "0 1.2.7" Localization.subalgebra.isLocalization_ofField
add_to_ega "0 1.2.7" "more general" Localization.subalgebra.isLocalization_subalgebra
add_to_ega "0 1.2.7" Localization.subalgebra.ofField
add_to_ega "0 1.2.7" "more general" OreLocalization.numeratorHom_inj
add_to_ega "0 1.2.7" "more general" Submonoid.LocalizationMap.injective_iff
add_to_ega "0 1.2.8" instIsReducedLocalization
add_to_ega "0 1.2.8" isReduced_localizationPreserves
add_to_ega "0 1.3.1" "underlying map of S⁻¹u" IsLocalizedModule.map
add_to_ega "0 1.3.1" IsLocalizedModule.mapExtendScalars
add_to_ega "0 1.3.1" "partial" IsLocalizedModule.map_LocalizedModules
add_to_ega "0 1.3.1" "more general" IsLocalizedModule.map_lTensor
add_to_ega "0 1.3.1" "partial" IsLocalizedModule.map_mk'
add_to_ega "0 1.3.1" LocalizedModule.map
add_to_ega "0 1.3.1" ModuleCat.localizedModuleFunctor
add_to_ega "0 1.3.1" ModuleCat.localizedModuleMap
add_to_ega "0 1.3.2" "special case" IsLocalization.Away.mapₐ_surjective_of_surjective
add_to_ega "0 1.3.2" "Ideals I, special case" IsLocalization.map_inf
add_to_ega "0 1.3.2" "special case" IsLocalization.map_injective_of_injective
add_to_ega "0 1.3.2" "special case" IsLocalization.map_surjective_of_surjective
add_to_ega "0 1.3.2" "special case" IsLocalization.mapₐ_injective_of_injective
add_to_ega "0 1.3.2" "special case" IsLocalization.mapₐ_surjective_of_surjective
add_to_ega "0 1.3.2" "more general" IsLocalizedModule.map_exact
add_to_ega "0 1.3.2" "more general" IsLocalizedModule.map_injective
add_to_ega "0 1.3.2" "more general" IsLocalizedModule.map_surjective
add_to_ega "0 1.3.2" "more general" LocalizedModule.map_exact
add_to_ega "0 1.3.2" "more general" LocalizedModule.map_injective
add_to_ega "0 1.3.2" "more general" LocalizedModule.map_surjective
add_to_ega "0 1.3.2" ModuleCat.localizedModuleFunctor_map_exact
add_to_ega "0 1.3.2" "special case" RingHom.surjective_localRingHom_of_surjective
add_to_ega "0 1.3.2" "special case" RingHom.surjective_localizationPreserves
add_to_ega "0 1.3.2" "more general" Submodule.instIsLocalizedModuleSubtypeMemLocalized₀ToLocalized₀
add_to_ega "0 1.3.2" "more general" Submodule.isLocalizedModule
add_to_ega "0 1.3.2" Submodule.localized
add_to_ega "0 1.3.2" Submodule.localized'
add_to_ega "0 1.3.2" "more general" Submodule.localized'_iSup
add_to_ega "0 1.3.2" Submodule.localized'_inf
add_to_ega "0 1.3.2" Submodule.localizedEquiv
add_to_ega "0 1.3.2" Submodule.localized₀
add_to_ega "0 1.3.2" Submodule.localized₀FrameHom
add_to_ega "0 1.3.2" "more general" Submodule.localized₀_iSup
add_to_ega "0 1.3.2" Submodule.localized₀_inf
add_to_ega "0 1.3.2" "special case" localizationAlgebra_injective
add_to_ega "0 1.3.5" "partial" IsLocalizedModule.map
add_to_ega "0 1.3.5" "partial" LocalizedModule.map
add_to_ega "0 1.3.5" "partial" Module.FinitePresentation.exists_lift_of_isLocalizedModule
add_to_ega "0 1.3.5" "more general" Module.FinitePresentation.isLocalizedModule_map
add_to_ega "0 1.3.5" "more general" Module.FinitePresentation.isLocalizedModule_mapExtendScalars
add_to_ega "0 1.3.5" Module.FinitePresentation.linearEquivMap
add_to_ega "0 1.3.5" Module.FinitePresentation.linearEquivMapExtendScalars
add_to_ega "0 1.3.5" "partial" Module.FinitePresentation.linearEquivMapExtendScalars_apply
add_to_ega "0 1.3.5" "partial" Module.FinitePresentation.linearEquivMap_apply
add_to_ega "0 1.3.5" "more general" Module.finitePresentation_iff_finite
add_to_ega "0 1.3.5"
  instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePresentation
add_to_ega "0 1.4.1" "special case" IsLocalization.Away.awayToAwayRight
add_to_ega "0 1.4.1" IsLocalization.map
add_to_ega "0 1.4.1" "identity i_A^T = ρ_A^{T" IsLocalization.map_comp
add_to_ega "0 1.4.1" "identity i_A^T = ρ_A^{T" IsLocalization.map_eq
add_to_ega "0 1.4.1" IsLocalizedModule.map
add_to_ega "0 1.4.1" IsLocalizedModule.mapExtendScalars
add_to_ega "0 1.4.1" "partial" IsLocalizedModule.map_comp
add_to_ega "0 1.4.1" "partial, special case" IsLocalizedModule.map_mk'
add_to_ega "0 1.4.1" "partial" LocalizedModule.lift'
add_to_ega "0 1.4.1" OreLocalization.universalHom
add_to_ega "0 1.4.3" "partial, ring case M = A" IsLocalization.iff_of_le_of_exists_dvd
add_to_ega "0 1.4.3" "special case" IsLocalization.self
add_to_ega "0 1.4.3" IsLocalizedModule.of_exists_mul_mem
add_to_ega "0 1.4.3" SaturatedSubmonoid
add_to_ega "0 1.4.3" Submonoid.MulSaturated
add_to_ega "0 1.4.3" "partial" Submonoid.mem_saturation_iff
add_to_ega "0 1.4.3" "partial" Submonoid.mem_saturation_iff'
add_to_ega "0 1.4.3" "partial" Submonoid.mem_saturation_iff_exists_dvd
add_to_ega "0 1.4.3" Submonoid.saturation
add_to_ega "0 1.4.4" "special case" IsLocalization.map_comp
add_to_ega "0 1.4.5" "partial" CommRingCat.FilteredColimits.colimit
add_to_ega "0 1.4.5" "partial" CommRingCat.FilteredColimits.colimitCommRing
add_to_ega "0 1.4.5" "more general" Ring.DirectLimit
add_to_ega "0 1.4.5" "partial" RingCat.FilteredColimits.colimit
add_to_ega "0 1.4.5" "partial" RingCat.FilteredColimits.colimitRing
add_to_ega "0 1.4.6" "Ring case M = A with S₁" IsLocalization.Away.instHMulAwayCoeRingHomAlgebraMap
add_to_ega "0 1.4.6" "Ring case M = A with S₁" IsLocalization.Away.mul
add_to_ega "0 1.4.6" "special case" IsLocalization.localization_localization_isLocalization
add_to_ega "0 1.4.6" "partial" Submonoid.map
add_to_ega "0 1.5.1" "special case" IsLocalization.Away.map_surjective_iff
add_to_ega "0 1.5.1" "special case" IsLocalization.Away.mapₐ_surjective_of_surjective
add_to_ega "0 1.5.1" IsLocalization.map
add_to_ega "0 1.5.1" "partial" IsLocalization.map_comp
add_to_ega "0 1.5.1" "factorization" IsLocalization.map_eq
add_to_ega "0 1.5.1" "more general" IsLocalization.map_surjective_of_surjective
add_to_ega "0 1.5.1" "more general" IsLocalization.mapₐ_surjective_of_surjective
add_to_ega "0 1.5.1" "special case" Localization.awayMap_surjective_iff
add_to_ega "0 1.5.1" "special case" Localization.localAlgHom'
add_to_ega "0 1.5.1" "special case" Localization.localRingHom
add_to_ega "0 1.5.1" "special case" Localization.localRingHom_mk
add_to_ega "0 1.5.1" "special case" Localization.localRingHom_mk'
add_to_ega "0 1.5.1" "special case" Localization.localRingHom_to_map
add_to_ega "0 1.5.1" "special case" RingHom.surjectiveOnStalks_of_surjective
add_to_ega "0 1.5.1" "special case" RingHom.surjective_localRingHom_iff
add_to_ega "0 1.5.1" "special case" RingHom.surjective_localRingHom_of_surjective
add_to_ega "0 1.5.1" RingHom.surjective_localizationPreserves
add_to_ega "0 1.5.1" "partial" Submonoid.LocalizationMap.map
add_to_ega "0 1.5.1" "partial" Submonoid.LocalizationMap.map_comp
add_to_ega "0 1.5.1" "more general" Submonoid.LocalizationMap.map_surjective_of_surjective
add_to_ega "0 1.5.2" IsLocalizedModule.restrictScalars
add_to_ega "0 1.5.2" IsLocalizedModule.restrictScalars_iff
add_to_ega "0 1.5.2" "special case" IsLocalizedModule.restrictScalars_powers
add_to_ega "0 1.5.2" "partial" LocalizedModule.instCommRing
add_to_ega "0 1.5.2" "partial" LocalizedModule.instRing
add_to_ega "0 1.5.2" "partial, special case" isLocalizedModule_iff_isLocalization
add_to_ega "0 1.5.3" "special case" Module.FinitePresentation.linearEquivMapExtendScalars
add_to_ega "0 1.5.3" "special case"
  instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePresentation
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensor
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensorEquiv
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensorProductEquivTMulRight
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensorProductEquivTMulRight_tmul
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensorRight
add_to_ega "0 1.5.4" "special case" IsLocalization.Away.tensorRightEquiv
add_to_ega "0 1.5.4" "special case" IsLocalization.tensor
add_to_ega "0 1.5.4" "special case" IsLocalization.tensorProductEquivOfMapIncludeRight
add_to_ega "0 1.5.4" "special case" IsLocalization.tensorProductEquivOfMapIncludeRight_tmul
add_to_ega "0 1.5.4" "partial" IsLocalization.tensorProduct_isLocalizedModule
add_to_ega "0 1.5.4" "special case" IsLocalization.tensorProduct_tensorProduct
add_to_ega "0 1.5.4" "special case" IsLocalization.tensorProduct_tensorProduct_right
add_to_ega "0 1.5.4" "special case" Localization.tensorLeftAlgEquiv
add_to_ega "0 1.5.4" "partial" LocalizedModule.equivTensorProduct
add_to_ega "0 1.5.4" ModuleCat.ExtendScalars.obj'
add_to_ega "0 1.5.4" "partial" ModuleCat.ExtendScalars.smul_tmul
add_to_ega "0 1.5.5" "special case"
  instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePresentation
add_to_ega "0 1.5.7" "more general" IsLocalization.map_comp_map
add_to_ega "0 1.5.7" "more general" IsLocalization.map_map
add_to_ega "0 1.5.7" "special case" Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra_1
add_to_ega "0 1.5.7" "special case" Localization.localRingHom_comp
add_to_ega "0 1.5.7" ModuleCat.restrictScalarsComp
add_to_ega "0 1.5.7" ModuleCat.restrictScalarsComp'
add_to_ega "0 1.5.7" ModuleCat.restrictScalarsComp'App
add_to_ega "0 1.5.8" "existence of q₁" Ideal.exists_comap_eq_of_mem_minimalPrimes
add_to_ega "0 1.5.8" "existence of q₁" Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
add_to_ega "0 1.5.8" "more general" Ideal.minimalPrimes_comap_subset
add_to_ega "0 1.5.8" "more general" IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
add_to_ega "0 1.5.8" "injective localization" IsLocalization.minimalPrimes_comap
add_to_ega "0 1.5.8" "at most one prime in Aₚ"
  IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
add_to_ega "0 1.7.1" "special case" IsLocalRing.closedPoint_mem_support
add_to_ega "0 1.7.1" "partial" IsLocalizedModule.eq_zero_iff
add_to_ega "0 1.7.1" "partial" Module.eq_zero_of_localization_maximal
add_to_ega "0 1.7.1" "partial" Module.mem_support_iff_exists_annihilator
add_to_ega "0 1.7.1" Module.nonempty_support_iff
add_to_ega "0 1.7.1" "partial" Module.nonempty_support_of_nontrivial
add_to_ega "0 1.7.1" "partial" Module.notMem_support_iff'
add_to_ega "0 1.7.1" Module.supportDim_ne_bot_iff_nontrivial
add_to_ega "0 1.7.1" "partial" Module.support_eq_empty
add_to_ega "0 1.7.1" "special case" eq_zero_of_localization
add_to_ega "0 1.7.3" "more general" Submodule.localized'FrameHom
add_to_ega "0 1.7.3" "more general" Submodule.localized'_iSup
add_to_ega "0 1.7.3" "more general" Submodule.localized₀FrameHom
add_to_ega "0 1.7.3" "more general" Submodule.localized₀_iSup
add_to_ega "0 1.7.4" "two ideals" Ideal.IsPrime.inf_le
add_to_ega "0 1.7.4" "more general" Ideal.IsPrime.inf_le'
add_to_ega "0 1.7.4" "partial" Module.annihilator_le_of_mem_support
add_to_ega "0 1.7.4" Module.mem_support_iff_of_finite
add_to_ega "0 1.7.4" "more general" Module.mem_support_iff_of_span_eq_top
add_to_ega "0 1.7.4" "more general" Module.notMem_support_iff'
add_to_ega "0 1.7.4" "two ideals, special case" PrimeSpectrum.zeroLocus_inf
add_to_ega "0 1.7.5" "Nakayama step" IsLocalRing.map_mkQ_eq_top
add_to_ega "0 1.7.5" "Nakayama step" IsLocalRing.map_tensorProduct_mk_eq_top
add_to_ega "0 1.7.5" "Nakayama step" IsLocalRing.subsingleton_tensorProduct
add_to_ega "0 1.7.5" "principal ideal a = (x)" Module.support_quotSMulTop
add_to_ega "0 1.7.5" "partial" Module.support_quotient
add_to_ega "0 2.1.1" IrreducibleSpace
add_to_ega "0 2.1.1" "forward implication" IrreducibleSpace.connectedSpace
add_to_ega "0 2.1.1" IsIrreducible
add_to_ega "0 2.1.1" "forward implication" IsIrreducible.isConnected
add_to_ega "0 2.1.1" "open-density criterion" IsOpen.dense
add_to_ega "0 2.1.1" "forward implication" IsPreirreducible.isPreconnected
add_to_ega "0 2.1.1" "two-open criterion" PreirreducibleSpace.of_forall_nonempty_inter
add_to_ega "0 2.1.1" "forward implication" PreirreducibleSpace.preconnectedSpace
add_to_ega "0 2.1.1" "more general" isIrreducible_iff_sInter
add_to_ega "0 2.1.1" "more general" isIrreducible_iff_sUnion_isClosed
add_to_ega "0 2.1.1" "more general" isPreirreducible_iff_subset_closure_inter_open
add_to_ega "0 2.1.1" "two-open criterion" nonempty_preirreducible_inter
add_to_ega "0 2.1.1" "more general" preirreducibleSpace_iff_open_dense
add_to_ega "0 2.1.2" IsGenericPoint
add_to_ega "0 2.1.2" "more general" IsGenericPoint.disjoint_iff
add_to_ega "0 2.1.2" "more general" IsGenericPoint.isIrreducible
add_to_ega "0 2.1.2" "more general" IsGenericPoint.mem_closed_set_iff
add_to_ega "0 2.1.2" "more general" IsGenericPoint.mem_open_set_iff
add_to_ega "0 2.1.2" "partial" IsIrreducible.closure
add_to_ega "0 2.1.2" isIrreducible_iff_closure
add_to_ega "0 2.1.2" specializes_iff_closure_subset
add_to_ega "0 2.1.2" specializes_iff_mem_closure
add_to_ega "0 2.1.3" CompactSpace
add_to_ega "0 2.1.3" "partial" CompactSpace.iInter_nonempty
add_to_ega "0 2.1.3" "partial" CompactSpace.nonempty_sInter
add_to_ega "0 2.1.3" "partial" IsClosed.exists_closed_singleton
add_to_ega "0 2.1.3" IsClosed.exists_minimal_nonempty_closed_subset
add_to_ega "0 2.1.3" IsCompact
add_to_ega "0 2.1.3" "partial" IsCompact.elim_directed_family_closed
add_to_ega "0 2.1.3" "partial" IsCompact.elim_finite_subcover
add_to_ega "0 2.1.3" "partial" IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
add_to_ega "0 2.1.3" "partial" IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
add_to_ega "0 2.1.3" "more general" IsGenericPoint.eq
add_to_ega "0 2.1.3" T0Space
add_to_ega "0 2.1.3" "partial" TopologicalSpace.Closeds.coe_eq_singleton_of_isAtom
add_to_ega "0 2.1.3" "partial" TopologicalSpace.IsOpenCover.exists_finite_of_compactSpace
add_to_ega "0 2.1.3" closedPoints
add_to_ega "0 2.1.3" "partial" exists_isOpen_xor'_mem
add_to_ega "0 2.1.3" "partial" exists_isOpen_xor_mem
add_to_ega "0 2.1.3" "more general" genericPoints.component_injective
add_to_ega "0 2.1.3" "special case" genericPoints_eq_singleton
add_to_ega "0 2.1.3" "more general" isCompact_iff_finite_subcover
add_to_ega "0 2.1.3" "partial" isCompact_iff_finite_subfamily_closed
add_to_ega "0 2.1.3" mem_closedPoints_iff
add_to_ega "0 2.1.3" "partial" minimal_nonempty_closed_eq_singleton
add_to_ega "0 2.1.3" "partial" minimal_nonempty_closed_subsingleton
add_to_ega "0 2.1.3" t0Space_iff_exists_isOpen_xor'_mem
add_to_ega "0 2.1.3" t0Space_iff_exists_isOpen_xor_mem
add_to_ega "0 2.1.3" t0Space_iff_inseparable
add_to_ega "0 2.1.3" t0Space_iff_not_inseparable
add_to_ega "0 2.1.3" t0Space_iff_or_notMem_closure
add_to_ega "0 2.1.4" "special case" AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion
add_to_ega "0 2.1.4" "partial" IsGenericPoint.disjoint_iff
add_to_ega "0 2.1.4" "partial" IsGenericPoint.mem_open_set_iff
add_to_ega "0 2.1.4" "partial, sufficiency" IsPreirreducible.of_subset_iUnion
add_to_ega "0 2.1.4" "partial" IsPreirreducible.open_subset
add_to_ega "0 2.1.4" "more general" IsPreirreducible.subset_irreducible
add_to_ega "0 2.1.4" "sufficiency" PreirreducibleSpace.of_isOpenCover
add_to_ega "0 2.1.4" "more general" Topology.IsOpenEmbedding.irreducibleSpace
add_to_ega "0 2.1.4" "necessity" isIrreducible_iff_sInter
add_to_ega "0 2.1.5" "special case" Function.Surjective.irreducibleSpace
add_to_ega "0 2.1.5" "more general" IsGenericPoint.image
add_to_ega "0 2.1.5" "more general" IsIrreducible.image
add_to_ega "0 2.1.5" "partial" IsPreirreducible.image
add_to_ega "0 2.1.6" AlgebraicGeometry.Scheme.irreducibleComponentOpen
add_to_ega "0 2.1.6" "partial" IsIrreducible.closure
add_to_ega "0 2.1.6" "irreducibility of Z ∩ U" IsIrreducible.preimage
add_to_ega "0 2.1.6" "density of Z ∩ U in Z" IsOpen.dense
add_to_ega "0 2.1.6" "irreducibility of Z ∩ U" IsPreirreducible.open_subset
add_to_ega "0 2.1.6" "irreducibility of Z ∩ U" IsPreirreducible.subset_irreducible
add_to_ega "0 2.1.6" "existence" exists_mem_irreducibleComponents_subset_of_isIrreducible
add_to_ega "0 2.1.6" "special case" irreducibleComponent_property
add_to_ega "0 2.1.6" irreducibleComponents
add_to_ega "0 2.1.6" "closedness" irreducibleComponents_eq_maximals_closed
add_to_ega "0 2.1.6" "special case" isClosed_irreducibleComponent
add_to_ega "0 2.1.6" "closedness" isClosed_of_mem_irreducibleComponents
add_to_ega "0 2.1.6" "partial" isIrreducible_iff_closure
add_to_ega "0 2.1.6" "density" isPreirreducible_iff_subset_closure_inter_open
add_to_ega "0 2.1.6" "partial" preimage_mem_irreducibleComponents
add_to_ega "0 2.1.6" "existence for singletons" sUnion_irreducibleComponents
add_to_ega "0 2.1.6" "density" subset_closure_inter_of_isPreirreducible_of_isOpen
add_to_ega "0 2.1.7" "more general" isIrreducible_iff_sUnion_isClosed
add_to_ega "0 2.1.8" "more general" IsGenericPoint.image
add_to_ega "0 2.2.1" "partial" TopologicalSpace.instWellFoundedLTClosedsOfNoetherianSpace
add_to_ega "0 2.2.1" "more general" TopologicalSpace.noetherianSpace_TFAE
add_to_ega "0 2.2.2" "special case" IsNoetherian.induction
add_to_ega "0 2.2.2" "more general" WellFounded.induction
add_to_ega "0 2.2.2" "more general" WellFoundedLT.induction
add_to_ega "0 2.2.3" TopologicalSpace.NoetherianSpace.inter_of_left
add_to_ega "0 2.2.3" TopologicalSpace.NoetherianSpace.inter_of_right
add_to_ega "0 2.2.3" TopologicalSpace.NoetherianSpace.of_subset
add_to_ega "0 2.2.3" TopologicalSpace.NoetherianSpace.set
add_to_ega "0 2.2.4" "special case" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "0 2.2.4" "more general" TopologicalSpace.NoetherianSpace.isCompact
add_to_ega "0 2.2.4" "more general" TopologicalSpace.noetherianSpace_TFAE
add_to_ega "0 2.2.4" "more general" TopologicalSpace.noetherianSpace_iff_isCompact
add_to_ega "0 2.2.4" TopologicalSpace.noetherianSpace_iff_opens
add_to_ega "0 2.2.4" "more general" TopologicalSpace.noetherianSpace_set_iff
add_to_ega "0 2.2.5" "special case" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
