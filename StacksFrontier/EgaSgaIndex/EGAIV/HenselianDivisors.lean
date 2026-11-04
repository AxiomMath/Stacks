module  -- shake: keep-all

import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.LinearDisjoint
import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Inseparable
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sober
import StacksCore.CategoryTheory.Filtration.GradedExact
import StacksCore.FieldTheory.LiftEmbeddingsEquiv
import StacksCore.RingTheory.NormTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA IV references registered by name, §§18–21

Registrations for EGA IV §§18–21: étale morphisms and henselian rings, regular immersions,
meromorphic functions and pseudo-morphisms, divisors. Part of `StacksFrontier.EgaSgaIndex.EGAIV`,
whose module docstring describes the index.
-/

add_to_ega "IV 18.2.1" "special case" Algebra.det_traceMatrix_ne_zero
add_to_ega "IV 18.2.1" Algebra.trace
add_to_ega "IV 18.2.1" Algebra.trace'
add_to_ega "IV 18.2.1" Algebra.traceForm
add_to_ega "IV 18.2.1" "special case" Algebra.trace_localization
add_to_ega "IV 18.2.1" "more general" IsBaseChange.basis_apply
add_to_ega "IV 18.2.1" "more general" LinearMap.trace_baseChange
add_to_ega "IV 18.2.1" Module.Basis.baseChange
add_to_ega "IV 18.2.1" "more general" Module.Basis.baseChange_apply
add_to_ega "IV 18.2.1" "(18.2.1.2)" Subalgebra.LinearDisjoint.trace_algebraMap
add_to_ega "IV 18.2.1" "partial" det_traceForm_ne_zero
add_to_ega "IV 18.2.1" "partial" traceForm_nondegenerate
add_to_ega "IV 18.2.1" "special case" traceForm_nondegenerate_tfae
add_to_ega "IV 18.2.2" "the Γ(U" Algebra.trace
add_to_ega "IV 18.2.3" Algebra.Etale.iff_exists_algEquiv_prod
add_to_ega "IV 18.2.3" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_ega "IV 18.2.3" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "IV 18.2.3" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "IV 18.2.3" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "IV 18.2.4" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "IV 18.2.6" "special case" Algebra.trace_surjective
add_to_ega "IV 18.2.7" "partial" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.IsIntegralHom.instUniversallyClosed
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "IV 18.2.10" "more general" AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton
add_to_ega "IV 18.2.10" "more general"
  AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton
add_to_ega "IV 18.3.2.1" AdicCompletion.submodule
add_to_ega "IV 18.3.2.1" CategoryTheory.Limits.limit
add_to_ega "IV 18.3.2.1" IsAdicComplete
add_to_ega "IV 18.3.2.1" IsPrecomplete
add_to_ega "IV 18.3.2.1" Module.Finite
add_to_ega "IV 18.3.2.1" Module.Projective
add_to_ega "IV 18.3.2.1" TensorProduct
add_to_ega "IV 18.3.3" Algebra.Etale.iff_exists_algEquiv_prod
add_to_ega "IV 18.3.3" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_ega "IV 18.3.3" "more general" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_ega "IV 18.3.3" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "IV 18.3.3" "partial" Algebra.FormallyEtale.of_isSeparable
add_to_ega "IV 18.3.3" "partial" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "IV 18.3.3" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "IV 18.4.2" "(i), special case, (ii)" StandardEtalePair.instEtaleRing
add_to_ega "IV 18.4.3" "(F" StandardEtalePair.HasMap.isUnit_derivative_f
add_to_ega "IV 18.4.3" "(F)" StandardEtalePair.instEtaleRing
add_to_ega "IV 18.4.4" "special case" IsLocalRing.minpoly_map_residue
add_to_ega "IV 18.4.9" "(b) ⇒ (a), special case" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 18.4.9" "(b) ⇒ (a), special case" Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat
add_to_ega "IV 18.4.9" "(a) ⇔ (b), special case"
  AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 18.4.9" "(b) ⇒ (a), special case"
  AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 18.4.9" "(a) ⇔ (b), special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 18.4.12" "(ii), special case" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 18.4.12" "(ii), special case" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 18.4.12" "(ii)" AlgebraicGeometry.Etale.instFormallyUnramified
add_to_ega "IV 18.4.12" "(ii), special case" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 18.4.12" "(ii) necessity: flatness" AlgebraicGeometry.WeaklyEtale.instOfEtale
add_to_ega "IV 18.4.12" "(ii) necessity: flatness" AlgebraicGeometry.etale_le_weaklyEtale
add_to_ega "IV 18.4.12" "(ii), special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 18.4.14" "(ii)" Algebra.Etale.baseChange
add_to_ega "IV 18.4.14" "(i) when B is local" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_ega "IV 18.4.14" "(ii)" Localization.flat
add_to_ega "IV 18.4.14" "(ii)" Module.flat_of_isLocalized_maximal
add_to_ega "IV 18.4.14" "(ii)" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 18.5.1" "special case" AlgebraicGeometry.AffineSpace.coord
add_to_ega "IV 18.5.1" "special case" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_ega "IV 18.5.1" "partial" Module.Basis.eval_range
add_to_ega "IV 18.5.1" Module.Dual
add_to_ega "IV 18.5.1" Module.Dual.eval
add_to_ega "IV 18.5.1" "special case" Module.dual_free
add_to_ega "IV 18.5.1" "special case" MvPolynomial.rTensorAlgEquiv
add_to_ega "IV 18.5.1" "special case" MvPolynomial.rTensorAlgHom
add_to_ega "IV 18.5.1" "special case" MvPolynomial.scalarRTensorAlgEquiv
add_to_ega "IV 18.5.2" "special case" MvPolynomial.eval
add_to_ega "IV 18.5.2" "Al(X′, special case" MvPolynomial.zeroLocus
add_to_ega "IV 18.5.2" "special case" Polynomial.aeval
add_to_ega "IV 18.5.2" "partial" SymmetricAlgebra.lift
add_to_ega "IV 18.5.8" "special case" HenselianLocalRing
add_to_ega "IV 18.5.8" HenselianRing
add_to_ega "IV 18.5.16" IsIdempotentElem
add_to_ega "IV 18.6.1" "special case" Algebra.FinitePresentation.iff
add_to_ega "IV 18.6.1" "special case" Algebra.FinitePresentation.iff_quotient_mvPolynomial'
add_to_ega "IV 18.6.1" "partial" Algebra.FiniteType.iff_exists_generators
add_to_ega "IV 18.6.1" "partial" Algebra.FiniteType.iff_quotient_mvPolynomial
add_to_ega "IV 18.6.1" "partial" Algebra.FiniteType.iff_quotient_mvPolynomial'
add_to_ega "IV 18.6.1" "partial" Algebra.FiniteType.iff_quotient_mvPolynomial''
add_to_ega "IV 18.6.1" Algebra.FormallyEtale.comp
add_to_ega "IV 18.6.1" "more general" Algebra.FormallyEtale.iff_restrictScalars
add_to_ega "IV 18.6.1" "more general" Algebra.FormallyEtale.instLocalization
add_to_ega "IV 18.6.1" "special case" Algebra.IsEtaleAt.comp
add_to_ega "IV 18.6.1" "more general" Algebra.IsEtaleAt.exists_isStandardEtale
add_to_ega "IV 18.6.1" "more general" Algebra.exists_etale_of_isEtaleAt
add_to_ega "IV 18.6.1" IsLocalHom
add_to_ega "IV 18.6.1" RingHom.FormallyEtale.comp
add_to_ega "IV 18.6.9.2" "more general" TopologicalSpace.NoetherianSpace.discrete
add_to_ega "IV 18.6.9.2" "more general" TopologicalSpace.NoetherianSpace.finite
add_to_ega "IV 18.8.1" "(a)⇒(b), special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "IV 18.8.1" "(a)⇒(c), special case"
  AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed
add_to_ega "IV 18.8.6" "special case"
  Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPrime
add_to_ega "IV 18.8.6" "partial" Algebra.instFiniteResidueFieldOfIsUnramifiedAt
add_to_ega "IV 18.8.6" "partial" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_ega "IV 18.8.6" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
add_to_ega "IV 18.9.5" "special case" CommAlgCat.FiniteEtale.baseChange
add_to_ega "IV 18.9.7.6" "partial" AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant
add_to_ega "IV 18.10.1" "special case" Algebra.FormallyEtale.iff_formallyUnramified_of_field
add_to_ega "IV 18.10.1" "(i), special case" Algebra.FormallyEtale.of_formallyUnramified_of_field
add_to_ega "IV 18.10.5" "necessity" AlgebraicGeometry.IsOpenImmersion.le_monomorphisms
add_to_ega "IV 18.10.6" genericPoints
add_to_ega "IV 18.10.8" AlgebraicGeometry.Scheme.Hom.fromNormalization
add_to_ega "IV 18.10.8" "partial" AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso
add_to_ega "IV 18.10.8" AlgebraicGeometry.Scheme.Hom.normalizationObjIso
add_to_ega "IV 18.10.10" "partial" AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso
add_to_ega "IV 18.10.15" "partial" IsIntegralClosure.finite
add_to_ega "IV 18.10.15" "partial" IsIntegralClosure.isNoetherian
add_to_ega "IV 18.10.15" "partial" IsIntegralClosure.module_free
add_to_ega "IV 18.10.15" "special case" NumberField.not_dvd_discr_iff_forall_liesOver
add_to_ega "IV 18.10.15" "special case" NumberField.not_dvd_discr_iff_forall_mem
add_to_ega "IV 18.10.15" "special case" NumberField.not_dvd_discr_iff_isUnramifiedIn
add_to_ega "IV 18.10.19" AlgebraicGeometry.Scheme.RationalMap.IsOver
add_to_ega "IV 18.10.19" AlgebraicGeometry.Scheme.RationalMap.domain
add_to_ega "IV 18.11.4" AdicCompletion
add_to_ega "IV 18.11.6" "more general" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_ega "IV 18.11.6" "partial" Algebra.instIsSeparableResidueFieldOfFormallyUnramified
add_to_ega "IV 18.11.6" "partial" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_ega "IV 18.11.6" "more general" Algebra.isUnramifiedAt_iff_map_eq
add_to_ega "IV 18.11.6" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
add_to_ega "IV 18.11.12" FractionRing
add_to_ega "IV 18.11.12" IsFractionRing
add_to_ega "IV 18.12.1" AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt
add_to_ega "IV 18.12.1" "special case"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_ega "IV 18.12.4" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "IV 18.12.4" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "IV 18.12.4" "necessity" AlgebraicGeometry.IsFinite.instLocallyOfFiniteType
add_to_ega "IV 18.12.4" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_ega "IV 18.12.4" "necessity" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "IV 18.12.4" "necessity" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "IV 18.12.4" "necessity" AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite
add_to_ega "IV 18.12.6" "(a)⇔(b), special case"
  AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "IV 18.12.6" AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_ega "IV 18.12.6" "(a)⇔(b), special case"
  AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "IV 18.12.6" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "IV 18.12.7.1" "singleton fibre"
  AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
add_to_ega "IV 18.12.7.1" "singleton fibre" AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
add_to_ega "IV 18.12.7.1" "empty fibre" AlgebraicGeometry.isAffineOpen_bot
add_to_ega "IV 18.12.8" AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom
add_to_ega "IV 18.12.8" "necessity" AlgebraicGeometry.IsIntegralHom.instUniversallyClosed
add_to_ega "IV 18.12.9" "partial"
  AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom
add_to_ega "IV 18.12.13" "more general" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "IV 18.12.14" "partial" AlgebraicGeometry.Scheme.Hom.normalizationObjIso
add_to_ega "IV 18.12.14" "more general" TensorProduct.toIntegralClosure_injective_of_flat
add_to_ega "IV 18.12.15" "Nontrivial inclusion" mem_adjoin_map_integralClosure_of_isStandardEtale
add_to_ega "IV 18.12.17" "u is separated" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "IV 18.12.17" "partial" AlgebraicGeometry.IsSeparated.instMorphismRestrict
add_to_ega "IV 18.12.17" "partial" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "IV 18.12.17" "special case" AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_ega "IV 18.12.17" "u is separated" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "IV 18.12.17" "special case"
  AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "IV 18.12.17" "partial" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "IV 18.12.17" "partial" AlgebraicGeometry.Proj.isSeparated
add_to_ega "IV 18.12.17" AlgebraicGeometry.Proj.toSpecZero
add_to_ega "IV 19.3.2.1" "more general" CommRingCat.pullbackFst_isLocalHom
add_to_ega "IV 19.3.2.1" "more general" RingHom.isLocalHom_pullbackFst
add_to_ega "IV 19.3.2.1" "more general" RingHom.isLocalRing_pullback
add_to_ega "IV 19.3.2.1" RingHom.pullback
add_to_ega "IV 19.3.2.1" RingHom.pullbackFst
add_to_ega "IV 19.3.2.1" RingHom.pullbackSnd
add_to_ega "IV 19.4.10" "special case"
  instFiniteTypeSubtypePolynomialMemSubalgebraReesAlgebraOfIsNoetherianRing
add_to_ega "IV 19.4.10" "special case" reesAlgebra.fg
add_to_ega "IV 19.5.3" "a) ⇒ c), special case"
  QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
add_to_ega "IV 19.5.5" "more general" IsHausdorff.of_le_jacobson
add_to_ega "IV 19.6.1" "more general"
  CategoryTheory.FilteredObject.shortExact_subQuotShortComplex_cokernel_map_grMap
add_to_ega "IV 19.6.1" "more general"
  CategoryTheory.FilteredObject.shortExact_subQuotShortComplex_map_grMap
add_to_ega "IV 19.6.1" CategoryTheory.FilteredObject.subQuotShortComplex
add_to_ega "IV 19.6.1" Submodule.comap
add_to_ega "IV 19.6.1" Submodule.map
add_to_ega "IV 19.7.2" "(i), special case" IsSMulRegular.of_flat
add_to_ega "IV 19.7.2" "more general" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_lTensor
add_to_ega "IV 19.7.2" "more general" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_rTensor
add_to_ega "IV 19.7.2" "more general" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "IV 19.7.2" "more general" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "IV 19.7.3" "partial" PowerSeries.invOneSubPow
add_to_ega "IV 19.7.3" "partial" PowerSeries.mk_one_pow_eq_mk_choose_add
add_to_ega "IV 19.7.4" "affine case" Module.isLocallyConstant_rankAtStalk_freeLocus
add_to_ega "IV 19.7.5" "more general" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_ega "IV 19.7.5" "more general" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "IV 20.1.1" TopCat.Presheaf.SubmonoidPresheaf.localizationPresheaf
add_to_ega "IV 20.1.3.1" "partial"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "IV 20.1.3.1" "converse direction" Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes
add_to_ega "IV 20.1.3.1" "partial" notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
add_to_ega "IV 20.1.4" "partial" IsLocalization.injective_iff_isRegular
add_to_ega "IV 20.1.4" "partial" IsLocalization.injectiveₛ
add_to_ega "IV 20.1.4" "Injectivity"
  TopCat.Presheaf.instMonoCommRingCatToTotalQuotientPresheafPresheaf
add_to_ega "IV 20.1.5" "special case" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "IV 20.1.5" "special case" Module.Free.instIsTorsionFree
add_to_ega "IV 20.2.3" "special case" AlgebraicGeometry.Scheme.RationalMap.domain
add_to_ega "IV 20.2.3" "special case" AlgebraicGeometry.Scheme.RationalMap.mem_domain
add_to_ega "IV 20.2.5" "special case" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "IV 20.2.5" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "IV 20.2.5" "special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated
add_to_ega "IV 20.2.5"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsSeparatedTopMorphismProperty
add_to_ega "IV 20.2.7" "Direction" AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant
add_to_ega "IV 20.2.7" "partial" AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant
add_to_ega "IV 20.2.8" "special case" AlgebraicGeometry.Scheme.PartialMap.equiv
add_to_ega "IV 20.2.9" "more general"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "IV 20.2.9" "more general"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 20.2.9" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "IV 20.2.9" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 20.2.9" AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "IV 20.2.9" AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 20.2.9" "special case" PrimeSpectrum.basicOpen
add_to_ega "IV 20.2.13" "(ii), special case"
  AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "IV 20.2.13" "(ii), special case"
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
add_to_ega "IV 20.2.13" "more general" TrivSqZeroExt
add_to_ega "IV 20.2.13" "S" biUnion_associatedPrimes_eq_compl_nonZeroDivisors
add_to_ega "IV 20.2.16" "more general" AlgebraicGeometry.Scheme.GlueData.glued
add_to_ega "IV 20.2.16" "more general" AlgebraicGeometry.Scheme.GlueData.gluedScheme
add_to_ega "IV 20.2.16" "partial" TrivSqZeroExt
add_to_ega "IV 20.3.2" "For Y separated over S"
  AlgebraicGeometry.Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver
add_to_ega "IV 20.3.5" "more general" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_ega "IV 20.3.6" "open stability, case a)" AlgebraicGeometry.instIsLocallyNoetherianToScheme
add_to_ega "IV 20.3.6" "open stability" AlgebraicGeometry.instIsReducedToScheme
add_to_ega "IV 20.3.6" "partial" AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
add_to_ega "IV 20.4.1" "partial"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "IV 20.5.7" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_ega "IV 20.6.9" "flatness of X' over S'" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 20.6.9" "flatness of X' over S'" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 20.6.9" "special case"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeFppfPrecoverage
add_to_ega "IV 20.6.9" "affine flatness clause" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_ega "IV 20.6.9" "partial" IsSMulRegular.of_flat_of_isBaseChange
add_to_ega "IV 20.6.9" "partial" Module.Flat.isBaseChange
add_to_ega "IV 20.6.9" "partial" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 20.6.9" "partial" RingHom.Flat.isStableUnderBaseChange
add_to_ega "IV 20.6.9" "partial" RingHom.finitePresentation_isStableUnderBaseChange
add_to_ega "IV 20.6.9" "partial" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "IV 21.2.3" FractionalIdeal.instInvNonZeroDivisors
add_to_ega "IV 21.2.3" "(i), special case" FractionalIdeal.spanSingleton_inv
add_to_ega "IV 21.2.3" "(ii), special case" Module.Flat.tensorSubmoduleAlgebraEquivMul
add_to_ega "IV 21.2.3" "(ii), affine case" Submodule.tensorEquivMul
add_to_ega "IV 21.2.4" "Law of composition (J1" FractionalIdeal.instMul
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.coe_ideal_span_singleton_inv_mul
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.coe_ideal_span_singleton_mul_inv
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.invertible_iff_generator_nonzero
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.invertible_of_principal
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.mul_generator_self_inv
add_to_ega "IV 21.2.5" FractionalIdeal.spanSingleton
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.spanSingleton_inv_mul
add_to_ega "IV 21.2.5" "special case" FractionalIdeal.spanSingleton_mul_inv
add_to_ega "IV 21.2.5" "special case" toPrincipalIdeal
add_to_ega "IV 21.2.12" "more general" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "IV 21.3.1" "affine integral case" ClassGroup.mk_eq_one_iff
add_to_ega "IV 21.3.1" "affine integral case" FractionalIdeal.spanSingleton_eq_spanSingleton
add_to_ega "IV 21.3.2" "special case" CommRing.Pic
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.ext_iff
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.functor
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mapAlgebra
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mapRingHom
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mk
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mk.linearEquiv
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mk_eq_iff
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mk_eq_mk_iff
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mk_tensor
add_to_ega "IV 21.3.2" "special case" CommRing.Pic.mul_eq_tensor
add_to_ega "IV 21.3.2" "special case" instCommGroupPic
add_to_ega "IV 21.3.3" "(i), special case" ClassGroup.equivPic
add_to_ega "IV 21.3.3" "(i), special case" Submodule.unitsQuotEquivRelPic
add_to_ega "IV 21.4.1" "more general" RingHom.isUnit_map
add_to_ega "IV 21.4.1" "more general" Units.map
add_to_ega "IV 21.5.2" "special case" LinearMap.det_eq_zero_iff_ker_ne_bot
add_to_ega "IV 21.5.2" "special case" Matrix.Nondegenerate.of_det_ne_zero
add_to_ega "IV 21.5.2" "Sufficiency" Matrix.mulVec_injective_of_det_mem_nonZeroDivisors
add_to_ega "IV 21.5.2" "special case" Matrix.mulVec_injective_of_det_ne_zero
add_to_ega "IV 21.5.3" "partial" AlgebraicGeometry.IsFinite
add_to_ega "IV 21.5.3" "special case" IsLocalization.flat
add_to_ega "IV 21.5.3" "partial" IsSMulRegular.of_flat
add_to_ega "IV 21.5.3" "special case" Localization.flat
add_to_ega "IV 21.5.3" "partial" Module.Flat.iff_rTensor_preserves_injective_linearMap
add_to_ega "IV 21.5.3" "partial" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "IV 21.5.3" "partial" Module.Flat.isSMulRegular_of_nonZeroDivisors
add_to_ega "IV 21.5.3" "partial" Module.Flat.torsion_eq_bot
add_to_ega "IV 21.5.3" "partial" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_rTensor
add_to_ega "IV 21.5.7" "special case" Ideal.relNorm_relNorm
add_to_ega "IV 21.6.1" AlgebraicGeometry.AlgebraicCycle
add_to_ega "IV 21.6.1" "partial" LocallyFinite.closure
add_to_ega "IV 21.6.1" "more general" LocallyFinite.closure_iUnion
add_to_ega "IV 21.6.1" "more general" LocallyFinite.isClosed_iUnion
add_to_ega "IV 21.6.1" "special case" PrimeSpectrum.pointsEquivIrreducibleCloseds
add_to_ega "IV 21.6.1" TopologicalSpace.IrreducibleCloseds
add_to_ega "IV 21.6.1" "more general" locallyFinite_mulSupport_iff
add_to_ega "IV 21.6.1" "more general" locallyFinite_support_iff
add_to_ega "IV 21.6.5" "partial" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "IV 21.6.7" "special case" AlgebraicGeometry.Scheme.ordHom
add_to_ega "IV 21.6.9.2" "more general" UniqueFactorizationMonoid.of_isLocalization
add_to_ega "IV 21.6.9.2" "more general" instUniqueFactorizationMonoidLocalization
add_to_ega "IV 21.7.6" "special case" instSubsingletonPicOfIsDomainOfIsGCDMonoid
add_to_ega "IV 21.7.7" UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one
add_to_ega "IV 21.9.1" "partial" skyscraperPresheafStalkOfNotSpecializesIsTerminal
add_to_ega "IV 21.9.1" "partial" skyscraperPresheaf_isSheaf
add_to_ega "IV 21.9.8" "converse" IsDiscreteValuationRing.ringKrullDim_eq_one
add_to_ega "IV 21.9.8" "converse"
  IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing
add_to_ega "IV 21.9.13" "more general" IsLocalRing.closedPoint_mem_iff
add_to_ega "IV 21.9.13" "more general" IsLocalRing.closed_point_mem_iff
add_to_ega "IV 21.10.1" "partial" LocallyFinite
add_to_ega "IV 21.10.13" "(i) for M=A" isFiniteLength_quotient_span_singleton
add_to_ega "IV 21.10.14" "partial" AlgebraicGeometry.Scheme.Hom.finite_preimage
add_to_ega "IV 21.10.15" "Condition a)" AlgebraicGeometry.IsFinite.comp_iff
add_to_ega "IV 21.10.15" "Condition a)" AlgebraicGeometry.IsFinite.instCompScheme
add_to_ega "IV 21.10.15" "Condition a)" AlgebraicGeometry.IsFinite.instIsMultiplicativeScheme
add_to_ega "IV 21.12.8" "more general" AlgebraicGeometry.IsAffineOpen.biInf
add_to_ega "IV 21.12.8" "more general" AlgebraicGeometry.IsAffineOpen.iInf
add_to_ega "IV 21.12.8" "binary intersections" AlgebraicGeometry.IsAffineOpen.inf
add_to_ega "IV 21.12.9" "more general"
  UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one
add_to_ega "IV 21.12.9" "more general" UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
add_to_ega "IV 21.12.14" Algebra.etaleLocus
add_to_ega "IV 21.12.14" "special case" Algebra.exists_formallyUnramified_of_isUnramifiedAt
add_to_ega "IV 21.12.14" "special case" Algebra.exists_unramified_of_isUnramifiedAt
add_to_ega "IV 21.12.14" "special case" Algebra.isOpen_unramifiedLocus
add_to_ega "IV 21.12.14" Algebra.unramifiedLocus
add_to_ega "IV 21.12.17" "partial"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_ega "IV 21.13.3" CategoryTheory.Functor.Faithful
add_to_ega "IV 21.13.3" CategoryTheory.Functor.Full
add_to_ega "IV 21.13.9" MvPowerSeries
add_to_ega "IV 21.13.9" "(iv)" MvPowerSeries.instIsLocalRing
add_to_ega "IV 21.13.9" "(iv)" PowerSeries.instIsDomain
add_to_ega "IV 21.13.9" "(iv)" PowerSeries.instIsNoetherianRing
add_to_ega "IV 21.13.9" "(iv)" PowerSeries.instNoZeroDivisors
add_to_ega "IV 21.13.9" "partial"
  PowerSeries.instUniqueFactorizationMonoidOfIsPrincipalIdealRingOfIsDomain
add_to_ega "IV 21.13.9" TrivSqZeroExt
add_to_ega "IV 21.13.9" "more general" TrivSqZeroExt.isUnit_iff_isUnit_fst
add_to_ega "IV 21.13.9" TrivSqZeroExt.kerIdeal
add_to_ega "IV 21.13.9" "more general" TrivSqZeroExt.kerIdeal_sq
add_to_ega "IV 21.13.9" conductor
add_to_ega "IV 21.13.9" "partial" factorPowSucc.isUnit_of_isUnit_image
add_to_ega "IV 21.13.15" "partial" closure_singleton_eq_Iic
add_to_ega "IV 21.15.8" "special case" Module.free_of_flat_of_isLocalRing
add_to_ega "IV 21.15.9" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 21.15.9" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 21.15.9" "Flatness of X' over S'" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_ega "IV 21.15.9" "Flatness of X' over S'" RingHom.Flat.isStableUnderBaseChange
add_to_ega "IV 21.15.9" "partial" RingHom.finitePresentation_isStableUnderBaseChange
