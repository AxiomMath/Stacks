module  -- shake: keep-all

import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Instances.TrivSqZeroExt
import StacksCore.FieldTheory.MvRatFunc.Basic
import StacksCore.RingTheory.AdjoinRoot
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA 0, §§18–23: references registered by name

Declarations realizing numbered items of EGA 0, §18 (extensions of algebras), §19 (formally
smooth algebras, Cohen rings), §20 (derivations and differentials), §21 (differentials in
characteristic p), §22 (differential criteria for smoothness and regularity) and §23 (Japanese
rings), from the EGA/SGA concept index, that are not tagged where they are declared: Mathlib
and core declarations without an `add_to_stacks` pointer in this library, and (with
`--draft-only`) those of `StacksCore/`.
Part of the EGA 0 index, split by section.
-/

add_to_ega "0 18.1.1" "special case" AlgCat.Hom
add_to_ega "0 18.1.1" "special case" AlgCat.restrictScalars
add_to_ega "0 18.1.1" "special case" AlgHom
add_to_ega "0 18.1.1" "partial" AlgHom.coe_restrictScalars
add_to_ega "0 18.1.1" "partial" AlgHom.restrictScalars
add_to_ega "0 18.1.1" "partial" Algebra.compHom_algebraMap_eq
add_to_ega "0 18.1.1" "more general" CategoryTheory.Under
add_to_ega "0 18.1.1" "special case" CommAlgCat.Hom
add_to_ega "0 18.1.1" "partial" RingHom.instIsTwoSidedKer
add_to_ega "0 18.1.1" "special case" RingHom.toAlgebra
add_to_ega "0 18.1.1" "special case" RingHom.toAlgebra'
add_to_ega "0 18.1.1" "partial" TwoSidedIdeal.ker
add_to_ega "0 18.1.2" "special case" CommRingCat.pullbackConeIsLimit
add_to_ega "0 18.1.2" "partial" RingHom.pullback
add_to_ega "0 18.1.2" "partial" RingHom.pullbackFst
add_to_ega "0 18.1.4" CategoryTheory.SplitEpi
add_to_ega "0 18.1.4" "partial" Function.Exact.splitSurjectiveEquiv
add_to_ega "0 18.1.4" RingHom.ker
add_to_ega "0 18.1.5" AlgHom.surjective_pullbackFst_of_surjective
add_to_ega "0 18.1.5" AlgHom.surjective_pullbackSnd_of_surjective
add_to_ega "0 18.1.5" "partial" RingHom.pullback
add_to_ega "0 18.1.5" "more general" RingHom.surjective_pullbackFst_of_surjective
add_to_ega "0 18.1.5" "more general" RingHom.surjective_pullbackSnd_of_surjective
add_to_ega "0 18.2.1" "partial, special case" isScalarTower_of_section_of_ker_sqZero
add_to_ega "0 18.2.3" TrivSqZeroExt
add_to_ega "0 18.2.3" "A-ring structure" TrivSqZeroExt.algebra'
add_to_ega "0 18.2.3" "partial" TrivSqZeroExt.algebraMap_eq_inl
add_to_ega "0 18.2.3" "partial" TrivSqZeroExt.algebraMap_eq_inlHom
add_to_ega "0 18.2.3" "special case" TrivSqZeroExt.commRing
add_to_ega "0 18.2.3" "special case" TrivSqZeroExt.commSemiring
add_to_ega "0 18.2.3" TrivSqZeroExt.fst
add_to_ega "0 18.2.3" "special case" TrivSqZeroExt.fstHom
add_to_ega "0 18.2.3" "surjectivity of f" TrivSqZeroExt.fst_surjective
add_to_ega "0 18.2.3" "special case" TrivSqZeroExt.inlAlgHom
add_to_ega "0 18.2.3" TrivSqZeroExt.inlHom
add_to_ega "0 18.2.3" "square-zero image of j" TrivSqZeroExt.inr_mul_inr
add_to_ega "0 18.2.3" "special case" TrivSqZeroExt.instAlgebra
add_to_ega "0 18.2.3" "product module structure" TrivSqZeroExt.module
add_to_ega "0 18.2.3" TrivSqZeroExt.mul
add_to_ega "0 18.2.3" TrivSqZeroExt.ring
add_to_ega "0 18.2.3" "more general" TrivSqZeroExt.semiring
add_to_ega "0 18.2.3" "partial" TrivSqZeroExt.snd_mul
add_to_ega "0 18.2.4" "partial" CategoryTheory.ShortComplex.Hom
add_to_ega "0 18.2.4" "partial" CategoryTheory.ShortComplex.Hom.comp
add_to_ega "0 18.2.4" "special case" LinearMap
add_to_ega "0 18.2.5" "partial" RingHom.map_pullbackSnd_ker_pullbackFst_eq
add_to_ega "0 18.2.5" RingHom.pullback
add_to_ega "0 18.2.5" RingHom.pullbackFst
add_to_ega "0 18.2.5" "surjectivity of p₂" RingHom.surjective_pullbackFst_of_surjective
add_to_ega "0 18.2.7" "more general"
  CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout
add_to_ega "0 18.2.7" CategoryTheory.Limits.PushoutCocone.IsColimit.desc
add_to_ega "0 18.2.7" "uniqueness of w" CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext
add_to_ega "0 18.2.7" "partial" CategoryTheory.Limits.pullback.desc'
add_to_ega "0 18.2.7" "more general" CategoryTheory.Limits.pushout
add_to_ega "0 18.2.7" CategoryTheory.Limits.pushout.desc
add_to_ega "0 18.2.7" "partial" CategoryTheory.Limits.pushout.desc'
add_to_ega "0 18.2.7" "uniqueness of w" CategoryTheory.Limits.pushout.hom_ext
add_to_ega "0 18.2.7" "uniqueness of w" CategoryTheory.Limits.pushout.hom_ext_iff
add_to_ega "0 18.2.7" "identity u = w∘j₁" CategoryTheory.Limits.pushout.inl_desc
add_to_ega "0 18.2.7" "identity v = w∘j₂" CategoryTheory.Limits.pushout.inr_desc
add_to_ega "0 18.2.8" "partial" Module.compHom
add_to_ega "0 18.2.8" "partial" ModuleCat.RestrictScalars.obj'
add_to_ega "0 18.2.9" "partial" TrivSqZeroExt.algHom_ext
add_to_ega "0 18.2.9" "uniqueness" TrivSqZeroExt.algHom_ext'
add_to_ega "0 18.2.9" "more general" TrivSqZeroExt.liftEquiv
add_to_ega "0 18.2.9" "L-injection diagram" TrivSqZeroExt.lift_apply_inr
add_to_ega "0 18.2.9" "partial" TrivSqZeroExt.lift_comp_inlHom
add_to_ega "0 18.2.9" "partial" TrivSqZeroExt.lift_comp_inrHom
add_to_ega "0 18.2.9" TrivSqZeroExt.map
add_to_ega "0 18.3.4" "partial" CategoryTheory.Functor.mapAddGrp
add_to_ega "0 18.3.4" CategoryTheory.Functor.mapCommGrp
add_to_ega "0 18.3.4" "partial" CategoryTheory.Functor.mapGrp
add_to_ega "0 18.3.8" "special case" Algebra.Extension.infinitesimal
add_to_ega "0 18.3.8" "partial" Algebra.Extension.toInfinitesimal
add_to_ega "0 18.3.8" "underlying object J/J²" Ideal.Cotangent
add_to_ega "0 18.3.8" "partial" Ideal.cotangentEquivIdeal
add_to_ega "0 18.3.8" "partial" Ideal.cotangentIdeal
add_to_ega "0 18.3.8" "square-zero kernel" Ideal.cotangentIdeal_square
add_to_ega "0 18.3.8" "special case" Ideal.instModuleQuotientCotangent
add_to_ega "0 18.3.8" "partial" Ideal.quotCotangent
add_to_ega "0 18.3.8" "special case" LinearMap
add_to_ega "0 18.3.8" "special case" LinearMap.addCommGroup
add_to_ega "0 18.3.8" "partial" Module.instQuotientIdealSubmoduleHSMulTop
add_to_ega "0 18.4.1" AlgCat
add_to_ega "0 18.4.1" "more general" AlgHom.pullback
add_to_ega "0 18.4.1" Algebra
add_to_ega "0 18.4.1" Algebra.mk
add_to_ega "0 18.4.1" RingHom.toAlgebra'
add_to_ega "0 18.4.1" "partial" Set.algebraMap_mem_center
add_to_ega "0 18.4.1" "partial" Set.algebraMap_mem_centralizer
add_to_ega "0 18.4.1" TrivSqZeroExt.algebra'
add_to_ega "0 18.4.1" "special case" TrivSqZeroExt.instAlgebra
add_to_ega "0 18.4.2" "partial" TrivSqZeroExt.algebra'
add_to_ega "0 18.4.2" "partial" TrivSqZeroExt.commRing
add_to_ega "0 18.4.2" "partial" TrivSqZeroExt.commSemiring
add_to_ega "0 18.4.2" "special case" TrivSqZeroExt.instAlgebra
add_to_ega "0 18.4.3" "more general" CategoryTheory.ShortComplex.ShortExact.splittingOfProjective
add_to_ega "0 18.4.3" "The case f = 0" TrivSqZeroExt
add_to_ega "0 18.5.1" "partial" Ideal.Quotient.algebraQuotientOfLEComap
add_to_ega "0 18.5.1" "special case" Ideal.quotientAlgebra
add_to_ega "0 18.5.3" "special case" ContinuousAddMonoidHom.instAddCommGroup
add_to_ega "0 18.5.3" "partial" TopModuleCat.Hom
add_to_ega "0 18.5.3" "special case" TopModuleCat.instAddCommGroupHom
add_to_ega "0 18.5.4" "partial" AdicCompletion.instModuleQuotientIdealHSMulTopSubmodule
add_to_ega "0 18.5.4" "partial" Ideal.Cotangent
add_to_ega "0 18.5.4" "partial" Ideal.instModuleQuotientCotangent
add_to_ega "0 18.5.4" "partial" Module.instQuotientIdealSubmoduleHSMulTop
add_to_ega "0 19.0.1" Algebra.FormallySmooth
add_to_ega "0 19.0.1" "partial" Algebra.FormallySmooth.comp_lift
add_to_ega "0 19.0.1" "partial" Algebra.FormallySmooth.comp_liftOfSurjective
add_to_ega "0 19.0.1" "square-zero ideals" Algebra.FormallySmooth.comp_surjective
add_to_ega "0 19.0.1" "partial" Algebra.FormallySmooth.exists_lift
add_to_ega "0 19.0.1" "partial" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "0 19.0.1" "partial" Algebra.FormallySmooth.of_comp_surjective
add_to_ega "0 19.0.1" CategoryTheory.Functor.IsRepresentable
add_to_ega "0 19.0.1" CategoryTheory.yoneda
add_to_ega "0 19.0.1" RingHom.FormallySmooth
add_to_ega "0 19.0.2" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 19.0.2" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "0 19.0.2" "special case" Algebra.FormallySmooth.adjoin_of_algebraicIndependent
add_to_ega "0 19.0.2" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_ega "0 19.0.2" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 19.0.2" "I, special case" Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
add_to_ega "0 19.0.2" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 19.0.2" "I, special case" Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
add_to_ega "0 19.0.2" "I, necessity of flatness" Algebra.Smooth.flat
add_to_ega "0 19.0.2" "I, necessity of flatness" Algebra.Smooth.flat_of_isNoetherianRing
add_to_ega "0 19.0.2" "IV, special case" Algebra.smoothLocus_eq_univ
add_to_ega "0 19.0.2" "IV, special case" Algebra.smoothLocus_eq_univ_iff
add_to_ega "0 19.0.2" "IV" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top
add_to_ega "0 19.0.2" "IV" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff
add_to_ega "0 19.0.3" "special case" Ideal.adic_module_basis
add_to_ega "0 19.1.1" ContinuousLinearMap.completion
add_to_ega "0 19.1.1" "û extends u" ContinuousLinearMap.completion_apply_coe
add_to_ega "0 19.1.1" "special case" ContinuousLinearMap.fromCompletion
add_to_ega "0 19.1.1" "û extends u" ContinuousLinearMap.fromCompletion_apply_coe
add_to_ega "0 19.1.1" DenseRange
add_to_ega "0 19.1.1" "partial" Topology.IsClosedEmbedding
add_to_ega "0 19.1.1" Topology.IsInducing
add_to_ega "0 19.1.1" "module structure on M̂" UniformSpace.Completion.instModule
add_to_ega "0 19.1.1" UniformSpace.Completion.map
add_to_ega "0 19.1.2" DenseRange
add_to_ega "0 19.1.2" Topology.IsInducing
add_to_ega "0 19.1.3" Submodule.mapQ
add_to_ega "0 19.1.3" Submodule.mapQLinear
add_to_ega "0 19.1.11" "special case" IsLocalRing.split_injective_iff_lTensor_residueField_injective
add_to_ega "0 19.1.15" "direction" ContinuousLinearEquiv.equivOfRightInverse
add_to_ega "0 19.1.15" "direction" ContinuousLinearMap.closedComplemented_ker_of_rightInverse
add_to_ega "0 19.3.1" Algebra.FormallySmooth
add_to_ega "0 19.3.1" "discrete case" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "0 19.3.2" "special case" Algebra.instFormallySmoothMvPolynomial
add_to_ega "0 19.3.2" "special case" Algebra.mvPolynomial
add_to_ega "0 19.3.3" "special case" Algebra.FormallySmooth.polynomial
add_to_ega "0 19.3.3" Algebra.instFormallySmoothMvPolynomial
add_to_ega "0 19.3.3" Algebra.mvPolynomial
add_to_ega "0 19.3.4" MvPowerSeries
add_to_ega "0 19.3.4" "partial" MvPowerSeries.WithPiTopology.instIsTopologicalRing
add_to_ega "0 19.3.4" "partial" MvPowerSeries.WithPiTopology.instIsTopologicalSemiring
add_to_ega "0 19.3.4" MvPowerSeries.WithPiTopology.instTopologicalSpace
add_to_ega "0 19.3.4" MvPowerSeries.instAlgebra
add_to_ega "0 19.3.4" MvPowerSeries.instCommRing
add_to_ega "0 19.3.4" MvPowerSeries.instModule
add_to_ega "0 19.3.4" MvPowerSeries.instRing
add_to_ega "0 19.3.4" MvPowerSeries.instSemiring
add_to_ega "0 19.3.4" "special case" PowerSeries
add_to_ega "0 19.3.4" "special case" PowerSeries.WithPiTopology.instIsTopologicalRing
add_to_ega "0 19.3.4" "special case" PowerSeries.WithPiTopology.instIsTopologicalSemiring
add_to_ega "0 19.3.4" "special case" PowerSeries.WithPiTopology.instTopologicalSpace
add_to_ega "0 19.3.4.1" "(ii)" MvPowerSeries.aeval_unique
add_to_ega "0 19.3.4.1" "(ii)" MvPowerSeries.continuous_aeval
add_to_ega "0 19.3.4.1" "(ii)" PowerSeries.aeval_unique
add_to_ega "0 19.3.4.1" "(ii)" PowerSeries.continuous_aeval
add_to_ega "0 19.3.4.1" "(ii)" PowerSeries.eval₂_unique
add_to_ega "0 19.3.5" "(ii), special case" Algebra.FormallySmooth.iff_restrictScalars
add_to_ega "0 19.3.5" "clause (i), special case" Algebra.FormallySmooth.inst
add_to_ega "0 19.3.5" "clause (v)" Algebra.FormallySmooth.instForallOfFinite
add_to_ega "0 19.3.5" "(iv), special case" Algebra.FormallySmooth.instLocalization
add_to_ega "0 19.3.5" "(iv), special case" Algebra.FormallySmooth.localization_base
add_to_ega "0 19.3.5" "(iv), special case" Algebra.FormallySmooth.localization_map
add_to_ega "0 19.3.5" "(i), special case" Algebra.FormallySmooth.of_isLocalization
add_to_ega "0 19.3.5" "clause (v)" Algebra.FormallySmooth.of_pi
add_to_ega "0 19.3.5" "clause (v), special case" Algebra.FormallySmooth.pi_iff
add_to_ega "0 19.3.5" "(ii), special case" Algebra.Smooth.comp
add_to_ega "0 19.3.5" "(iv), special case" Algebra.Smooth.of_isLocalization_Away
add_to_ega "0 19.3.5" "(ii), special case" RingHom.FormallySmooth.comp
add_to_ega "0 19.3.5" "(iv), special case" RingHom.FormallySmooth.holdsForLocalizationAway
add_to_ega "0 19.3.5" "(iii), special case" RingHom.FormallySmooth.isStableUnderBaseChange
add_to_ega "0 19.3.5" "(iv), special case" RingHom.FormallySmooth.localizationPreserves
add_to_ega "0 19.3.5" "(ii), special case" RingHom.FormallySmooth.stableUnderComposition
add_to_ega "0 19.3.5" "clause (i), special case" RingHom.Smooth.id
add_to_ega "0 19.3.5" "(iii), special case" RingHom.Smooth.isStableUnderBaseChange
add_to_ega "0 19.3.7" "special case" Algebra.FormallySmooth.instLocalization
add_to_ega "0 19.3.7" "special case" Algebra.FormallySmooth.localization_base
add_to_ega "0 19.3.7" "special case" Algebra.FormallySmooth.localization_map
add_to_ega "0 19.3.7" "special case" Algebra.FormallySmooth.of_isLocalization
add_to_ega "0 19.3.7" "special case" Algebra.Smooth.of_isLocalization_Away
add_to_ega "0 19.3.7" "special case" RingHom.FormallySmooth.holdsForLocalizationAway
add_to_ega "0 19.3.7" "special case" RingHom.FormallySmooth.localizationPreserves
add_to_ega "0 19.3.7" "special case" RingHom.Smooth.holdsForLocalizationAway
add_to_ega "0 19.3.10" "special case" Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
add_to_ega "0 19.3.10" "special case" Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.comp_lift
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.comp_liftOfSurjective
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.comp_surjective
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.exists_lift
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.liftOfSurjective_apply
add_to_ega "0 19.3.10.1" "special case" Algebra.FormallySmooth.mk_lift
add_to_ega "0 19.3.10.2" "special case" Ideal.quotientInfEquivQuotientProd
add_to_ega "0 19.3.10.2" "special case" Ideal.quotientInfRingEquivPiQuotient
add_to_ega "0 19.3.10.2" "special case" Ideal.quotientMulEquivQuotientProd
add_to_ega "0 19.3.11" "special case" Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
add_to_ega "0 19.3.12" "discrete B, special case"
  Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
add_to_ega "0 19.3.12" "discrete B, special case"
  Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
add_to_ega "0 19.4.3" "special case" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "0 19.4.3" "special case" Algebra.FormallySmooth.of_comp_surjective
add_to_ega "0 19.4.6" "special case" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_ega "0 19.4.6" "special case" RingHom.FormallySmooth.isStableUnderBaseChange
add_to_ega "0 19.4.6" "special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_ega "0 19.5.2" "partial" QuotientModule.Quotient.topologicalSpace
add_to_ega "0 19.5.2" TopologicalSpace.coinduced
add_to_ega "0 19.5.2" TopologicalSpace.induced
add_to_ega "0 19.5.2" topologicalRingQuotientTopology
add_to_ega "0 19.5.4.4" "special case" Algebra.FormallySmooth.comp_lift
add_to_ega "0 19.5.4.4" "more general" Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
add_to_ega "0 19.5.4.4" Algebra.FormallySmooth.exists_kerProj_comp_eq_id
add_to_ega "0 19.5.4.4" "special case" Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
add_to_ega "0 19.5.4.4" "special case" Algebra.instFormallySmoothMvPolynomial
add_to_ega "0 19.5.5" "partial" SymmetricAlgebra.IsSymmetricAlgebra.mvPolynomial
add_to_ega "0 19.5.5" SymmetricAlgebra.equivMvPolynomial
add_to_ega "0 19.5.6" "Cα = Bα/Jα" DoubleQuot.quotQuotEquivQuotSupₐ
add_to_ega "0 19.5.6.1" Algebra.Extension.infinitesimal
add_to_ega "0 19.5.6.4" "special case" Algebra.FormallySmooth.comp_lift
add_to_ega "0 19.5.6.4" "special case" Algebra.FormallySmooth.comp_liftOfSurjective
add_to_ega "0 19.5.6.4" "special case" Algebra.FormallySmooth.exists_lift
add_to_ega "0 19.5.6.4" Algebra.FormallySmooth.lift
add_to_ega "0 19.5.6.4" Algebra.FormallySmooth.liftOfSurjective
add_to_ega "0 19.5.6.4" "special case" Algebra.FormallySmooth.liftOfSurjective_apply
add_to_ega "0 19.5.6.4" "special case" Algebra.FormallySmooth.mk_lift
add_to_ega "0 19.6.1" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "0 19.6.1" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 19.6.1" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "0 19.6.1" "special case" Algebra.FormallySmooth.adjoin_of_algebraicIndependent
add_to_ega "0 19.6.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_ega "0 19.6.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 19.6.1" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 19.7.1" "a ⇒ flatness clause of b"
  Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing
add_to_ega "0 19.7.1" "b ⇒ a" Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
add_to_ega "0 19.7.1" "more general" Ideal.Fiber.algEquivAux₁
add_to_ega "0 19.8.2" "(i), special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 19.8.3" AdicCompletion
add_to_ega "0 19.8.3" IsLocalization.AtPrime
add_to_ega "0 19.8.3" LocalSubring.ofPrime
add_to_ega "0 19.8.3" Localization.AtPrime
add_to_ega "0 19.8.3" PadicInt
add_to_ega "0 19.10.2" Algebra.FormallyEtale
add_to_ega "0 19.10.2" "special case" Algebra.FormallyEtale.iff_comp_bijective
add_to_ega "0 19.10.2" "special case"
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth
add_to_ega "0 19.10.2" "partial" Algebra.FormallyEtale.instFormallySmooth
add_to_ega "0 19.10.2" "partial" Algebra.FormallyEtale.instFormallyUnramified
add_to_ega "0 19.10.2" "partial" Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
add_to_ega "0 19.10.2" RingHom.FormallyEtale
add_to_ega "0 19.10.2" RingHom.FormallyUnramified
add_to_ega "0 19.10.3" "special case" Algebra.Etale.instAway
add_to_ega "0 19.10.3" "special case" Algebra.Etale.of_isLocalizationAway
add_to_ega "0 19.10.3" "partial" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_ega "0 19.10.3" "partial" Algebra.FormallyEtale.iff_formallyUnramified_of_field
add_to_ega "0 19.10.3" "more general" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "0 19.10.3" "partial"
  Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPrime
add_to_ega "0 19.10.3" "more general" Algebra.FormallyEtale.instLocalization
add_to_ega "0 19.10.3" "partial" Algebra.FormallyEtale.of_formallyUnramified_of_field
add_to_ega "0 19.10.3" "more general" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 19.10.3" "more general" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "0 19.10.3" "partial" Algebra.FormallySmooth.instLocalization
add_to_ega "0 19.10.3" "more general" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 19.10.3" "partial" Algebra.FormallySmooth.of_isLocalization
add_to_ega "0 19.10.3" "perfect base field" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 19.10.3" "one variable" Algebra.FormallySmooth.polynomial
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.instLocalization
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.isSeparable
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "0 19.10.3" "more general" Algebra.FormallyUnramified.of_surjective
add_to_ega "0 19.10.3" "quotient algebras R ⧸ I" Algebra.FormallyUnramified.quotient
add_to_ega "0 19.10.3" "partial"
  Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
add_to_ega "0 19.10.3" "partial" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_ega "0 19.10.3" Algebra.instFormallySmoothMvPolynomial
add_to_ega "0 19.10.3" "special case" Algebra.instFormallyUnramifiedResidueField
add_to_ega "0 19.10.3" "partial" Algebra.instIsSeparableResidueFieldOfFormallyUnramified
add_to_ega "0 19.10.3" Algebra.mvPolynomial
add_to_ega "0 19.10.3" DiscreteTopology
add_to_ega "0 19.10.3" "(ii)" RingHom.FormallySmooth.holdsForLocalizationAway
add_to_ega "0 19.10.3" "(ii)" RingHom.FormallyUnramified.holdsForLocalization
add_to_ega "0 19.10.3" RingHom.FormallyUnramified.of_surjective
add_to_ega "0 19.10.4" "partial, special case"
  Algebra.FormallyUnramified.iff_comp_injective_of_small
add_to_ega "0 19.10.4" "partial" AlgebraicGeometry.FormallyUnramified.of_hom_ext
add_to_ega "0 20.1.1" "special case" ModuleCat.Derivation
add_to_ega "0 20.1.1" "special case" derivationToSquareZeroEquivLift
add_to_ega "0 20.1.1" "each v₀ + D is a lift" derivationToSquareZeroEquivLift_apply_coe_apply
add_to_ega "0 20.1.1" "partial" derivationToSquareZeroEquivLift_symm_apply_apply_coe
add_to_ega "0 20.1.1" derivationToSquareZeroOfLift
add_to_ega "0 20.1.1" "D = v − v₀" derivationToSquareZeroOfLift_apply
add_to_ega "0 20.1.1" "Forward inclusion" liftOfDerivationToSquareZero
add_to_ega "0 20.1.1" "partial" liftOfDerivationToSquareZero_apply
add_to_ega "0 20.1.1" "Lifting condition" liftOfDerivationToSquareZero_mk_apply
add_to_ega "0 20.1.2" "special case" ModuleCat.Derivation
add_to_ega "0 20.1.3" "nonempty case" derivationToSquareZeroEquivLift
add_to_ega "0 20.1.3" derivationToSquareZeroOfLift
add_to_ega "0 20.1.3" liftOfDerivationToSquareZero
add_to_ega "0 20.1.5" liftOfDerivationToSquareZero
add_to_ega "0 20.1.7" "Inclusion" derivationOfSectionOfKerSqZero
add_to_ega "0 20.1.7" "Commutative case" retractionKerToTensorEquivSection
add_to_ega "0 20.1.7" sectionOfRetractionKerToTensorAux
add_to_ega "0 20.1.7" "partial" sectionOfRetractionKerToTensorAux_algebraMap
add_to_ega "0 20.1.7" "partial" toAlgHom_comp_sectionOfRetractionKerToTensor
add_to_ega "0 20.1.7" "partial" toAlgHom_comp_sectionOfRetractionKerToTensorAux
add_to_ega "0 20.2.1" "partial" Derivation.coe_comp
add_to_ega "0 20.2.1" "partial" Derivation.coe_restrictScalars
add_to_ega "0 20.2.1" "special case" Derivation.compAlgebraMap
add_to_ega "0 20.2.1" "special case" Derivation.compAlgebraMapL
add_to_ega "0 20.2.1" "(x)" Derivation.compAlgebraMapL_apply_apply
add_to_ega "0 20.2.1" "special case" Derivation.llcomp
add_to_ega "0 20.2.1" "special case" Derivation.restrictScalars
add_to_ega "0 20.2.1" "(x)" Derivation.restrictScalars_apply
add_to_ega "0 20.2.1" "20.2.1.1, special case" LinearEquiv.compDer
add_to_ega "0 20.2.1" LinearMap.compDer
add_to_ega "0 20.3.1" "Hom. cont_A(B,C)" ContinuousAlgHom
add_to_ega "0 20.3.1" "Hom. cont(A,B)" TopCommRingCat.instCategory
add_to_ega "0 20.3.2" TrivSqZeroExt.instTopologicalSpace
add_to_ega "0 20.4.1" "partial" Algebra.TensorProduct.includeLeft
add_to_ega "0 20.4.1" "partial" Algebra.TensorProduct.includeLeftRingHom
add_to_ega "0 20.4.1" "partial" Algebra.TensorProduct.includeRight
add_to_ega "0 20.4.1" "formula j₂(b) = 1 ⊗ b" Algebra.TensorProduct.includeRight_apply
add_to_ega "0 20.4.1" "partial" Algebra.TensorProduct.lmul'
add_to_ega "0 20.4.1" "partial" Algebra.TensorProduct.lmul''
add_to_ega "0 20.4.1" "formula p(b ⊗ b') = bb'" Algebra.TensorProduct.lmul'_apply_tmul
add_to_ega "0 20.4.1" "surjectivity of p" Algebra.TensorProduct.lmul'_comp_includeLeft
add_to_ega "0 20.4.1" "surjectivity of p" Algebra.TensorProduct.lmul'_comp_includeRight
add_to_ega "0 20.4.1" "more general" Algebra.TensorProduct.productLeftAlgHom
add_to_ega "0 20.4.1" "more general" Algebra.TensorProduct.productMap_apply_tmul
add_to_ega "0 20.4.1" "more general" Algebra.TensorProduct.productMap_left_apply
add_to_ega "0 20.4.1" "more general" Algebra.TensorProduct.productMap_right_apply
add_to_ega "0 20.4.1" "partial" LinearMap.mul'
add_to_ega "0 20.4.1" "partial" LinearMap.mul'_apply
add_to_ega "0 20.4.1" "partial" Subalgebra.mulMap
add_to_ega "0 20.4.1" "formula p(b ⊗ b') = bb'" Subalgebra.mulMap_tmul
add_to_ega "0 20.4.7" "more general" Algebra.Presentation.differentials
add_to_ega "0 20.4.7" "more general" Algebra.Presentation.differentialsSolution_isPresentation
add_to_ega "0 20.4.7" "special case" KaehlerDifferential.span_range_derivation
add_to_ega "0 20.4.8" "(ii), derivation clause" CommRingCat.KaehlerDifferential.D
add_to_ega "0 20.4.8" "(ii)" CommRingCat.KaehlerDifferential.ext
add_to_ega "0 20.4.8" "(ii)" Derivation.liftKaehlerDifferential_comp
add_to_ega "0 20.4.8" "(ii)" Derivation.liftKaehlerDifferential_comp_D
add_to_ega "0 20.4.8" "(ii)" Derivation.liftKaehlerDifferential_unique
add_to_ega "0 20.4.8" "(ii)" Derivation.liftKaehlerDifferential_unique_iff
add_to_ega "0 20.4.9" "special case" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "0 20.4.13" "more general" Algebra.Generators.cotangentSpaceBasis
add_to_ega "0 20.4.13" "(i)" Algebra.Generators.cotangentSpaceBasis_apply
add_to_ega "0 20.4.13" "more general" Algebra.Presentation.differentials
add_to_ega "0 20.4.13" "more general" Algebra.Presentation.differentialsSolution_isPresentation
add_to_ega "0 20.4.13" "more general" Algebra.SubmersivePresentation.basisKaehler
add_to_ega "0 20.4.13" "more general" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_ega "0 20.4.13" KaehlerDifferential.mvPolynomialBasis_repr_D_X
add_to_ega "0 20.4.13" KaehlerDifferential.mvPolynomialBasis_repr_symm_single
add_to_ega "0 20.4.13" KaehlerDifferential.mvPolynomialEquiv
add_to_ega "0 20.4.13" "(i) one variable" KaehlerDifferential.polynomialEquiv
add_to_ega "0 20.4.13" "more general" MvPolynomial.mkDerivation_X
add_to_ega "0 20.4.13" "one polynomial generator" Polynomial.mkDerivation
add_to_ega "0 20.4.13" "one polynomial generator" Polynomial.mkDerivationEquiv
add_to_ega "0 20.4.13" "one polynomial generator" Polynomial.mkDerivation_X
add_to_ega "0 20.4.13" TrivSqZeroExt
add_to_ega "0 20.4.13" "more general" TrivSqZeroExt.algebra'
add_to_ega "0 20.4.13" TrivSqZeroExt.instAlgebra
add_to_ega "0 20.4.13" "partial" instFreeMvPolynomialKaehlerDifferential
add_to_ega "0 20.5.2" "more general" Algebra.Extension.Cotangent.map
add_to_ega "0 20.5.2" "special case" Algebra.Extension.CotangentSpace.map_tmul
add_to_ega "0 20.5.2" KaehlerDifferential.map
add_to_ega "0 20.5.2" KaehlerDifferential.mapBaseChange
add_to_ega "0 20.5.2" "partial" KaehlerDifferential.mapBaseChange_tmul
add_to_ega "0 20.5.2" "more general" KaehlerDifferential.map_D
add_to_ega "0 20.5.2" "more general" KaehlerDifferential.map_compDer
add_to_ega "0 20.5.3" "partial" Algebra.TensorProduct.mapOfCompatibleSMul_surjective
add_to_ega "0 20.5.3" "more general" KaehlerDifferential.map
add_to_ega "0 20.5.4" CommRingCat.KaehlerDifferential.map
add_to_ega "0 20.5.4" KaehlerDifferential.map
add_to_ega "0 20.5.4" "special case" KaehlerDifferential.mapBaseChange
add_to_ega "0 20.5.4" "partial" KaehlerDifferential.map_D
add_to_ega "0 20.5.4" "partial" KaehlerDifferential.map_compDer
add_to_ega "0 20.5.5" KaehlerDifferential.isBaseChange
add_to_ega "0 20.5.5" "partial" KaehlerDifferential.tensorKaehlerEquiv_left_inv
add_to_ega "0 20.5.7" KaehlerDifferential.mapBaseChange
add_to_ega "0 20.5.7" "partial" KaehlerDifferential.range_mapBaseChange
add_to_ega "0 20.5.7" "(ii), special case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "0 20.5.8" KaehlerDifferential.isBaseChange_of_formallyEtale
add_to_ega "0 20.5.8" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "0 20.5.9" KaehlerDifferential.isLocalizedModule_map
add_to_ega "0 20.5.9" "more general" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "0 20.5.11" KaehlerDifferential.kerCotangentToTensor
add_to_ega "0 20.5.11" "formula on classes" KaehlerDifferential.kerCotangentToTensor_toCotangent
add_to_ega "0 20.5.11" "partial" KaehlerDifferential.kerToTensor
add_to_ega "0 20.5.12" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "0 20.5.12" Algebra.Extension.infinitesimal
add_to_ega "0 20.5.12" "partial" Ideal.Algebra.kerSquareLift
add_to_ega "0 20.5.12" Ideal.Cotangent
add_to_ega "0 20.5.12" Ideal.cotangentEquivIdeal
add_to_ega "0 20.5.12" Ideal.cotangentIdeal
add_to_ega "0 20.5.12" "partial" Ideal.cotangentIdeal_square
add_to_ega "0 20.5.12" Ideal.quotCotangent
add_to_ega "0 20.5.12" KaehlerDifferential.kerCotangentToTensor
add_to_ega "0 20.5.12" retractionKerCotangentToTensorEquivSection
add_to_ega "0 20.5.12" "special case" retractionKerToTensorEquivSection
add_to_ega "0 20.5.12" "(iii) c)⇒a) when R² = 0" retractionOfSectionOfKerSqZero_comp_kerToTensor
add_to_ega "0 20.5.12" "more general" tensorKaehlerQuotKerSqEquiv
add_to_ega "0 20.5.12" "(iii) a)⇒c) when R² = 0" toAlgHom_comp_sectionOfRetractionKerToTensor
add_to_ega "0 20.5.12" "(iii) a)⇒c) when R² = 0" toAlgHom_comp_sectionOfRetractionKerToTensorAux
add_to_ega "0 20.5.13" Algebra.Generators.cotangentSpaceBasis
add_to_ega "0 20.5.13" "partial" Algebra.Generators.cotangentSpaceBasis_apply
add_to_ega "0 20.5.13" "partial" Algebra.Generators.instFreeCotangentSpaceToExtension
add_to_ega "0 20.5.13" Algebra.Presentation.differentials
add_to_ega "0 20.5.13" "partial" Algebra.Presentation.differentialsRelations
add_to_ega "0 20.5.13" "partial" Algebra.Presentation.differentialsSolution
add_to_ega "0 20.5.13" Algebra.Presentation.differentialsSolution_isPresentation
add_to_ega "0 20.5.13" "partial" KaehlerDifferential.kerTotal
add_to_ega "0 20.5.13" "coordinate vector of dP" KaehlerDifferential.mvPolynomialBasis_repr_D
add_to_ega "0 20.5.13" "partial" KaehlerDifferential.mvPolynomialBasis_repr_apply
add_to_ega "0 20.5.13" "partial" KaehlerDifferential.mvPolynomialBasis_repr_comp_D
add_to_ega "0 20.5.13" "special case" KaehlerDifferential.quotKerTotalEquiv
add_to_ega "0 20.5.14" "special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "0 20.5.14" "special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "0 20.6.5" "differential K₁ → K₀" KaehlerDifferential.mapBaseChange
add_to_ega "0 20.6.19" "(ii), case F/K algebraic" Algebra.isSeparable_tower_top_of_isSeparable
add_to_ega "0 20.6.19" "(ii), case F/K algebraic" IntermediateField.isSeparable_tower_top
add_to_ega "0 20.6.20" "more general" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 20.6.20" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "0 20.6.21" "special case" LinearMap.kerLTensorEquivOfSurjective
add_to_ega "0 20.6.21" LinearMap.tensorKer
add_to_ega "0 20.6.21" "partial" LinearMap.tensorKerEquiv
add_to_ega "0 20.6.21" "partial" Module.Flat.instPreservesFiniteLimitsModuleCatTensorLeftOfCarrier
add_to_ega "0 20.6.23" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "0 20.6.26" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 20.6.26" HomotopyCategory.quotient
add_to_ega "0 20.6.26" Ideal.Cotangent
add_to_ega "0 20.6.26" KaehlerDifferential.cotangentComplexBaseChange
add_to_ega "0 20.6.26" "more general" instCategoryHomotopyCategory
add_to_ega "0 20.7.6" "special case" KaehlerDifferential.isBaseChange_of_formallyEtale
add_to_ega "0 20.7.6" "special case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "0 20.7.7" "special case" KaehlerDifferential.isBaseChange_of_formallyEtale
add_to_ega "0 20.7.7" "special case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "0 20.7.8" "(ii), special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "0 20.7.8" "(ii), special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "0 20.7.9" "special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "0 20.7.9" "special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "0 20.7.14" "more general" Algebra.TensorProduct.map_ker
add_to_ega "0 20.7.14" "partial" ContinuousLinearMap.fromCompletion
add_to_ega "0 20.7.14" "partial" ContinuousLinearMap.fromCompletion_unique
add_to_ega "0 20.7.16" "special case" Differential.differentialAlgebraFiniteDimensional
add_to_ega "0 20.7.16" "special case" Differential.uniqueDifferentialAlgebraFiniteDimensional
add_to_ega "0 20.7.20" "special case" Ideal.Quotient.normedCommRing
add_to_ega "0 20.7.20" "special case" KaehlerDifferential.range_kerCotangentToTensor
add_to_ega "0 20.7.20" "special case" Submodule.Quotient.completeSpace
add_to_ega "0 21.1.1" Algebra
add_to_ega "0 21.1.1" CharP
add_to_ega "0 21.1.1" "more general" RingHom.injective
add_to_ega "0 21.1.2" "partial" CharP.cast_ne_zero_of_ne_of_prime
add_to_ega "0 21.1.2" "special case" CharP.charP_iff_prime_eq_zero
add_to_ega "0 21.1.2" "more general" CharP.eq
add_to_ega "0 21.1.2" "Uniqueness component" CharP.existsUnique
add_to_ega "0 21.1.2" "partial" CharP.ringChar_of_prime_eq_zero
add_to_ega "0 21.1.2" "more general" ExpChar.eq
add_to_ega "0 21.1.2" "special case" ExpChar.exists_unique
add_to_ega "0 21.1.2" "Uniqueness via ringChar" ringChar.eq
add_to_ega "0 21.1.3" "special case" Algebra.charP_iff
add_to_ega "0 21.1.3" "special case" Algebra.ringChar_eq
add_to_ega "0 21.1.3" "special case" CharP.of_ringHom_of_ne_zero
add_to_ega "0 21.1.3" "special case" EqualCharZero.nonempty_algebraRat_iff
add_to_ega "0 21.1.3" "special case" RingHom.charP_iff
add_to_ega "0 21.1.3" "special case" RingHom.charP_iff_charP
add_to_ega "0 21.1.3" "Clause 1, special case" charP_of_injective_algebraMap
add_to_ega "0 21.1.3" "Clause 1, special case" charP_of_injective_algebraMap'
add_to_ega "0 21.1.3" "Clause 1, special case" charP_of_injective_ringHom
add_to_ega "0 21.1.3" isEmpty_algebraRat_iff_mixedCharZero
add_to_ega "0 21.1.4" CharP
add_to_ega "0 21.1.4" "special case" CharTwo.sq_injective
add_to_ega "0 21.1.4" "more general" FiniteField.coe_frobeniusAlgHom
add_to_ega "0 21.1.4" "special case" FiniteField.frobeniusAlgEquiv
add_to_ega "0 21.1.4" "special case" FiniteField.frobeniusAlgEquiv_apply
add_to_ega "0 21.1.4" "more general" FiniteField.frobeniusAlgHom
add_to_ega "0 21.1.4" "partial" Module.compHom
add_to_ega "0 21.1.4" ModuleCat.ExtendScalars.obj'
add_to_ega "0 21.1.4" "partial" ModuleCat.ExtendScalars.smul_tmul
add_to_ega "0 21.1.4" "more general" MonoidHom.map_frobenius
add_to_ega "0 21.1.4" "finite reduced rings" PerfectRing.ofFiniteOfIsReduced
add_to_ega "0 21.1.4" "special case" PerfectRing.ofSurjective
add_to_ega "0 21.1.4" "more general" RingHom.frobenius_comm
add_to_ega "0 21.1.4" "more general" RingHom.iterateFrobenius_comm
add_to_ega "0 21.1.4" "ring endomorphisms" RingHom.iterate_map_frobenius
add_to_ega "0 21.1.4" "more general" RingHom.map_frobenius
add_to_ega "0 21.1.4" "more general" RingHom.map_iterateFrobenius
add_to_ega "0 21.1.4" "more general" RingHom.map_iterate_frobenius
add_to_ega "0 21.1.4" RingHom.range
add_to_ega "0 21.1.4" RingHom.toAlgebra
add_to_ega "0 21.1.4" "partial" TensorProduct
add_to_ega "0 21.1.4" "partial" TensorProduct.smul_tmul
add_to_ega "0 21.1.4" "more general" frobenius
add_to_ega "0 21.1.4" "more general" frobenius_inj
add_to_ega "0 21.1.4" "A^(p) for fields" instAlgebraAdjoinPthRoots
add_to_ega "0 21.1.4" "more general" iterateFrobenius
add_to_ega "0 21.1.4" "more general" iterateFrobenius_inj
add_to_ega "0 21.1.10" "more general" Algebra.Generators.comp
add_to_ega "0 21.2.5" "special case" KaehlerDifferential.mvPolynomialEquiv
add_to_ega "0 21.2.6" "more general" MonoidHom.map_frobenius
add_to_ega "0 21.2.6" "more general" MonoidHom.map_iterateFrobenius
add_to_ega "0 21.2.6" "more general" RingHom.frobenius_comm
add_to_ega "0 21.2.6" "more general" RingHom.iterateFrobenius_comm
add_to_ega "0 21.2.6" "more general" RingHom.map_frobenius
add_to_ega "0 21.2.6" "more general" RingHom.map_iterateFrobenius
add_to_ega "0 21.2.6" "more general" RingHom.map_iterate_frobenius
add_to_ega "0 21.2.7" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_ega "0 21.2.7" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 21.2.7" "special case" Algebra.instFormallySmoothMvPolynomial
add_to_ega "0 21.3.2" "partial" CommRingCat.KaehlerDifferential.map
add_to_ega "0 21.3.2" "partial" KaehlerDifferential.map
add_to_ega "0 21.3.2" "(b)" KaehlerDifferential.map_D
add_to_ega "0 21.3.6" "partial" KaehlerDifferential.isBaseChange
add_to_ega "0 21.5.1" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "0 21.5.1" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 21.5.1" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "0 21.5.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_ega "0 21.5.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 21.5.1" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 21.5.1" "special case"
  IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
add_to_ega "0 21.5.1" "special case" LinearIndependent.map_of_isPurelyInseparable_of_isSeparable
add_to_ega "0 21.5.1" "special case" LinearIndependent.map_pow_expChar_pow_of_isSeparable
add_to_ega "0 21.5.1" "special case" LinearIndependent.map_pow_expChar_pow_of_isSeparable'
add_to_ega "0 21.5.3" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 21.5.3" "more general" Algebra.FormallyUnramified.ext_of_iInf
add_to_ega "0 21.5.3" "special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "0 21.5.3" "necessity, special case" Algebra.FormallyUnramified.isSeparable
add_to_ega "0 21.5.3" "special case" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "0 21.7.1" "more general" KaehlerDifferential.finite
add_to_ega "0 21.7.4" "partial" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_ega "0 21.7.4" "b ⇔ c" Algebra.FormallyEtale.iff_formallyUnramified_of_field
add_to_ega "0 21.7.4" "a ⇒ c" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "0 21.7.4" "c ⇒ b" Algebra.FormallyEtale.instFormallyUnramified
add_to_ega "0 21.7.4" "partial"
  Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPrime
add_to_ega "0 21.7.4" "b ⇒ c" Algebra.FormallyEtale.of_formallyUnramified_of_field
add_to_ega "0 21.7.4" "a ⇒ c" Algebra.FormallyEtale.of_isSeparable
add_to_ega "0 21.7.4" "a ⇒ c" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "0 21.7.4" "a ⇒ b" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "0 21.7.4" "partial" Algebra.FormallyUnramified.isSeparable
add_to_ega "0 21.7.4" "a ⇒ b" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "0 21.7.4" "c ⇒ a" Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "0 21.7.4" "partial" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_ega "0 21.8.8" FractionRing
add_to_ega "0 21.8.8" "one variable" LaurentSeries.instIsFractionRingPowerSeries
add_to_ega "0 21.9.5" Module.finrank
add_to_ega "0 21.9.5" Module.rank
add_to_ega "0 21.9.7" MvRatFunc
add_to_ega "0 21.9.8" Ideal.ResidueField
add_to_ega "0 21.9.8" "𝔭 = 0 in a domain" instIsFractionRingResidueFieldBotIdeal
add_to_ega "0 22.1.3" DualNumber
add_to_ega "0 22.1.3" TrivSqZeroExt
add_to_ega "0 22.1.3" TrivSqZeroExt.fstHom
add_to_ega "0 22.1.3.2" DualNumber
add_to_ega "0 22.1.3.2" "more general" TrivSqZeroExt
add_to_ega "0 22.1.3.2" "special case" TrivSqZeroExt.algebra'
add_to_ega "0 22.1.3.2" "augmentation F → K" TrivSqZeroExt.fstHom
add_to_ega "0 22.1.3.2" "partial" TrivSqZeroExt.instAlgebra
add_to_ega "0 22.2.1" "more general" Algebra.Extension.homInfinitesimal
add_to_ega "0 22.2.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_ega "0 22.2.1" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_ega "0 22.2.1" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 22.2.9" KaehlerDifferential.kerCotangentToTensor
add_to_ega "0 22.3.1" "Noetherianity of A" Algebra.EssFiniteType.isNoetherianRing
add_to_ega "0 22.3.1" "Noetherianity of A" IsNoetherianRing.of_finite
add_to_ega "0 22.3.1" "Noetherianity of A" isNoetherianRing_of_fg
add_to_ega "0 22.4.1" "special case" AdjoinRoot.isAdjoinRootMonic
add_to_ega "0 22.4.1" Ideal.map
add_to_ega "0 22.4.1" "(ii)" Ideal.tensorCotangentEquiv
add_to_ega "0 22.4.1" Ideal.tensorCotangentHom
add_to_ega "0 22.4.1" "(ii)" Ideal.tensorCotangentHom_surjective
add_to_ega "0 22.4.1" "(F), special case" IsAdjoinRootMonic
add_to_ega "0 22.4.1" IsLocalRing
add_to_ega "0 22.4.1" IsLocalRing.ResidueField
add_to_ega "0 22.4.1" IsLocalRing.ResidueField.field
add_to_ega "0 22.4.1" IsLocalRing.instModuleResidueFieldCotangentSpace
add_to_ega "0 22.4.1" Module.Free
add_to_ega "0 22.4.1" Module.finrank
add_to_ega "0 22.4.1" Module.rank
add_to_ega "0 22.4.1" MvPolynomial
add_to_ega "0 22.4.1" Polynomial.Monic
add_to_ega "0 22.4.1" "(i), special case" Polynomial.Monic.finrank_adjoinRoot
add_to_ega "0 22.4.1" "(i), special case" Polynomial.Monic.free_adjoinRoot
add_to_ega "0 22.4.1" "(i), special case" Polynomial.Monic.free_quotient
add_to_ega "0 22.4.3" Polynomial.IsDistinguishedAt
add_to_ega "0 22.4.3" "partial" Polynomial.IsWeaklyEisensteinAt
add_to_ega "0 22.4.4.2" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "0 22.4.6" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "0 22.4.6" "special case" Algebra.FormallySmooth.of_perfectField
add_to_ega "0 22.4.6" "partial" Ideal.Quotient.maximal_ideal_iff_isField_quotient
add_to_ega "0 22.4.6" "partial" IsArtinianRing.fieldOfSubtypeIsMaximal
add_to_ega "0 22.4.6" IsLocalRing.instModuleResidueFieldCotangentSpace
add_to_ega "0 22.4.8" "partial" Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
add_to_ega "0 22.4.8" "more general" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_ega "0 22.4.8" "more general" Ideal.map_injective_of_faithfullyFlat
add_to_ega "0 22.4.8" "partial" KaehlerDifferential.range_kerCotangentToTensor
add_to_ega "0 22.4.8" "partial" Module.FaithfullyFlat.faithfulSMul
add_to_ega "0 22.4.8" "partial" Module.FaithfullyFlat.instOfNontrivialOfFree
add_to_ega "0 22.4.8" "partial" RingHom.FaithfullyFlat.injective
add_to_ega "0 22.5.2" "partial" Polynomial.lifts_and_natDegree_eq_and_monic
add_to_ega "0 22.5.3" "quotient A′ when r = 1" AdjoinRoot.isAdjoinRootMonic
add_to_ega "0 22.5.3" Ideal.Cotangent
add_to_ega "0 22.5.3" "special case" IsAdjoinRootMonic
add_to_ega "0 22.5.3" IsLocalRing
add_to_ega "0 22.5.3" IsLocalRing.ResidueField
add_to_ega "0 22.5.3" IsRegularLocalRing
add_to_ega "0 22.5.3" LinearIndependent
add_to_ega "0 22.5.3" MvPolynomial
add_to_ega "0 22.5.3" Polynomial.Monic
add_to_ega "0 22.5.5" "partial"
  PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
add_to_ega "0 22.6.1" "discrete local case"
  Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
add_to_ega "0 22.6.1" "discrete local case"
  Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
add_to_ega "0 22.6.1" "special case" Algebra.FormallySmooth.iff_injective_lTensor_residueField
add_to_ega "0 22.6.2" "special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "0 22.6.2" "special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "0 22.6.3" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "0 22.6.3" Algebra.FormallySmooth.iff_split_injection
add_to_ega "0 22.6.4" "special case" Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
add_to_ega "0 22.6.4" "special case"
  Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
add_to_ega "0 22.6.4" "special case" Algebra.FormallySmooth.iff_injective_lTensor_residueField
add_to_ega "0 22.6.4" "more general" Algebra.FormallySmooth.iff_restrictScalars
add_to_ega "0 22.6.4" "c ⇒ a′" Algebra.FormallySmooth.instLocalization
add_to_ega "0 22.6.4" "a′ ⇒ a" Algebra.FormallySmooth.localization_base
add_to_ega "0 22.6.4" "a′ ⇒ a" Algebra.FormallySmooth.localization_map
add_to_ega "0 22.6.4" "special case" Algebra.IsSmoothAt.exists_notMem_isStandardSmooth
add_to_ega "0 22.6.4" "partial" Algebra.basicOpen_subset_smoothLocus_iff
add_to_ega "0 22.6.4" "partial" KaehlerDifferential.kerCotangentToTensor
add_to_ega "0 22.6.4" "a′ ⇒ a" RingHom.FormallySmooth.localizationPreserves
add_to_ega "0 22.6.5" Algebra.IsSmoothAt
add_to_ega "0 22.6.5" "special case" Algebra.isOpen_smoothLocus
add_to_ega "0 22.6.5" Algebra.smoothLocus
add_to_ega "0 22.6.5" "special case" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "0 22.6.6" "a) ⇒ b)" Algebra.FormallySmooth.instLocalization
add_to_ega "0 22.6.6" "special case" Algebra.basicOpen_subset_smoothLocus_iff
add_to_ega "0 22.6.6" "special case" Algebra.smoothLocus_eq_univ_iff
add_to_ega "0 22.6.7" "(i), c ⇒ a, (ii)" Algebra.FormallySmooth.instLocalization
add_to_ega "0 22.6.7" "(i), a ⇒ c" Algebra.IsSmoothAt.exists_notMem_smooth
add_to_ega "0 22.6.7" "(ii), special case" Algebra.basicOpen_subset_smoothLocus_iff
add_to_ega "0 22.6.7" "(ii), special case" Algebra.basicOpen_subset_smoothLocus_iff_smooth
add_to_ega "0 22.6.7" "(i), openness clause" Algebra.isOpen_smoothLocus
add_to_ega "0 22.6.7" "(ii), a ⇔ b" Algebra.smoothLocus_eq_univ_iff
add_to_ega "0 22.6.7" "(i), special case" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "0 22.7.2.4" "partial" Ideal.mapCotangent
add_to_ega "0 23.1.3.1" "special case" IsLocalization.AtPrime.comap_maximalIdeal_pow
add_to_ega "0 23.1.3.1" "n = 1" IsLocalization.AtPrime.under_maximalIdeal
add_to_ega "0 23.1.3.1" "special case" IsLocalization.AtPrime.under_maximalIdeal_pow
add_to_ega "0 23.2.5" "Noetherian clause" Algebra.EssFiniteType.isNoetherianRing
add_to_ega "0 23.2.5" "Noetherian clause" IsNoetherianRing.of_finite
add_to_ega "0 23.2.5" "Noetherian clause" isNoetherianRing_of_fg
add_to_ega "0 23.2.8" "special case" integralClosure.isDedekindDomain_fractionRing
add_to_ega "0 23.2.9" "special case" IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot
