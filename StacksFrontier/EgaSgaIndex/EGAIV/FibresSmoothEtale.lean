module  -- shake: keep-all

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.NoetherianSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA IV references registered by name, §§11–17

Registrations for EGA IV §§11–17: flat morphisms of finite presentation and their fibres,
equidimensionality, universally open morphisms, differential invariants, smooth, unramified and
étale morphisms. Part of `StacksFrontier.EgaSgaIndex.EGAIV`, whose module docstring describes the
index.
-/

add_to_ega "IV 11.1.6" "Case A = B = C" Module.isOpen_freeLocus
add_to_ega "IV 11.2.2" "more general" TensorProduct.directLimitLeft_rTensor_of
add_to_ega "IV 11.2.2.2" Finsupp
add_to_ega "IV 11.2.2.2" "special case" Finsupp.lmapDomain
add_to_ega "IV 11.2.2.2" "special case" Finsupp.mapDomain
add_to_ega "IV 11.2.2.2" "special case" ModuleCat.monoidAlgebraFree
add_to_ega "IV 11.2.3" CategoryTheory.Limits.kernelComparison
add_to_ega "IV 11.2.3" "partial" TensorProduct.map_ker
add_to_ega "IV 11.2.7" "special case" Algebra.Etale.exists_subalgebra_fg
add_to_ega "IV 11.2.8" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 11.2.8" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "IV 11.2.8" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "IV 11.2.8" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "IV 11.2.8" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "IV 11.2.8" "special case" AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso
add_to_ega "IV 11.2.9" "A = colim Aλ" CategoryTheory.Limits.colimit
add_to_ega "IV 11.2.9" "partial" Ideal.map
add_to_ega "IV 11.3.4" "special case" Algebra.Extension.ker_baseChange
add_to_ega "IV 11.3.4" Submodule.baseChange
add_to_ega "IV 11.3.10.2" "1°, special case" Localization.flat
add_to_ega "IV 11.3.10.2" "1°, special case" RingHom.Flat.stableUnderComposition
add_to_ega "IV 11.3.12" "more general" Module.freeLocus_eq_univ
add_to_ega "IV 11.3.12" "more general" Module.free_of_flat_of_finrank_eq
add_to_ega "IV 11.3.12" "more general" Module.free_of_flat_of_isLocalRing
add_to_ega "IV 11.3.13" "(ii), special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
add_to_ega "IV 11.3.13" "(ii), special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
add_to_ega "IV 11.3.13" "(ii), special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian
add_to_ega "IV 11.3.13" "(ii), special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian_1
add_to_ega "IV 11.4.1.1" "partial" Ideal.stableFiltration
add_to_ega "IV 11.4.11" "special case" Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
add_to_ega "IV 11.4.11" IntermediateField.eq_bot_of_isSepClosed_of_isSeparable
add_to_ega "IV 11.4.11" "special case" IsSepClosed.separableClosure_eq_bot_iff
add_to_ega "IV 11.5.4" "necessity" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 11.5.4" "necessity, affine case" RingHom.Flat.isStableUnderBaseChange
add_to_ega "IV 11.7.1" "partial" TensorProduct.quotientTensorQuotientEquiv
add_to_ega "IV 11.7.1" TrivSqZeroExt
add_to_ega "IV 11.7.2" "more general" Algebra.TensorProduct.quotIdealMapEquivQuotTensor
add_to_ega "IV 11.7.2" "more general" Algebra.TensorProduct.quotIdealMapEquivTensorQuot
add_to_ega "IV 11.7.5" "more general" Algebra.TensorProduct.quotIdealMapEquivQuotTensor
add_to_ega "IV 11.7.5" "more general" Algebra.TensorProduct.quotIdealMapEquivTensorQuot
add_to_ega "IV 11.7.5" "partial" Algebra.TensorProduct.quotIdealMapEquivTensorQuotAux
add_to_ega "IV 11.7.5" "more general" Algebra.TensorProduct.quotientTensorEquiv
add_to_ega "IV 11.7.5" "more general" Algebra.TensorProduct.tensorQuotientEquiv
add_to_ega "IV 11.7.5" "more general" Algebra.tensorQuotientTensorEquiv
add_to_ega "IV 11.9.4" "partial" IsDiscreteValuationRing.instIsHausdorffMaximalIdeal
add_to_ega "IV 11.9.4" "special case" LinearMap.ker_localizedMap_eq_localized'_ker
add_to_ega "IV 11.9.4" "special case" LinearMap.ker_localizedMap_eq_localized₀_ker
add_to_ega "IV 11.9.4" "special case" LinearMap.localized'_ker_eq_ker_localizedMap
add_to_ega "IV 11.9.4" "special case" LinearMap.toKerLocalized_isLocalizedModule
add_to_ega "IV 11.9.5" "partial"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_ega "IV 11.9.5" "partial"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left
add_to_ega "IV 11.9.5" "special case" AlgebraicGeometry.instIsOpenImmersionMorphismRestrict
add_to_ega "IV 11.9.5" "special case" RingHom.IsStandardOpenImmersion.isStableUnderBaseChange
add_to_ega "IV 11.9.7.1" "special case" Module.Flat.lTensor_preserves_injective_linearMap
add_to_ega "IV 11.9.9" "Parenthetical clause"
  AlgebraicGeometry.instIsArtinianSchemeSpecOfIsArtinianRingCarrier
add_to_ega "IV 11.9.10" "(i), special case" RingHom.FaithfullyFlat.codescendsAlong_injective
add_to_ega "IV 11.9.11" "special case" Module.support_quotient
add_to_ega "IV 11.9.14" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 11.9.14" "affine case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 11.9.17" AlgebraicGeometry.Scheme.Modules.restrictAdjunction
add_to_ega "IV 11.9.17" AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case" AlgebraicGeometry.ext_of_apply_eq
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case" AlgebraicGeometry.ext_of_isDominant
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_ega "IV 11.10.1" "(a) ⇒ (d), special case"
  AlgebraicGeometry.ext_of_isDominant_of_isSeparated'
add_to_ega "IV 11.10.2" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant
add_to_ega "IV 11.10.3" CategoryTheory.Limits.Sigma.desc
add_to_ega "IV 11.10.3" "partial" CategoryTheory.Limits.sigmaObj
add_to_ega "IV 11.10.4" "special case"
  AlgebraicGeometry.instIsDominantOfIsSchemeTheoreticallyDominantOfQuasiCompact
add_to_ega "IV 11.10.4" "special case"
  AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant
add_to_ega "IV 11.10.5" "(ii)(a), special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback
add_to_ega "IV 11.10.5" "(ii)(a), special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_ega "IV 11.10.5" "(ii)(a), special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd
add_to_ega "IV 11.10.6" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback
add_to_ega "IV 11.10.6" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_ega "IV 11.10.6" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd
add_to_ega "IV 11.10.7" "special case" Algebra.IsGeometricallyReduced.of_injective
add_to_ega "IV 12.0.2" "more general"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_ega "IV 12.0.2" "special case"
  PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
add_to_ega "IV 12.1.1.1" CategoryTheory.Limits.pullback.lift
add_to_ega "IV 12.1.1.1" "special case" IsSMulRegular.of_flat
add_to_ega "IV 12.1.1.1" "special case" IsSMulRegular.of_flat_of_isBaseChange
add_to_ega "IV 12.1.1.1" "special case"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_ega "IV 12.1.1.1" "special case" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "IV 12.1.1.1" "special case" Module.Flat.isSMulRegular_of_nonZeroDivisors
add_to_ega "IV 12.1.1.4" "special case" Ideal.Fiber
add_to_ega "IV 12.1.1.4" "clause" IsSMulRegular.of_flat
add_to_ega "IV 12.1.1.4" "clause"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_ega "IV 12.1.6" "(iii), special case" Algebra.isOpen_smoothLocus
add_to_ega "IV 12.1.6" "more general" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "IV 12.1.7" "(iv), affine case" Algebra.isOpen_smoothLocus
add_to_ega "IV 12.1.7" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "IV 12.1.7" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_ega "IV 12.2.2" "(iii)" AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank
add_to_ega "IV 12.3.1" "a ⇒ b" Module.Flat.of_projective
add_to_ega "IV 12.3.1" "b ⇒ a" Module.Flat.projective_of_finitePresentation
add_to_ega "IV 13.1.3" "Threshold n = 1" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "IV 13.1.4" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "IV 13.1.4" AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus
add_to_ega "IV 13.2.6" "X Noetherian" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "IV 13.2.6" "special case" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "IV 13.3.1" "affine base Y = Spec R" AlgebraicGeometry.AffineSpace.SpecIso
add_to_ega "IV 13.3.1" "affine base Y" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_ega "IV 13.3.1" AlgebraicGeometry.AffineSpace.over
add_to_ega "IV 14.1.2" "(i), special case" AlgebraicGeometry.isOpenMap_isZariskiLocalAtTarget
add_to_ega "IV 14.1.2" "(iii), special case" Homeomorph.comp_isOpenMap_iff'
add_to_ega "IV 14.1.2" "(iii), special case" Homeomorph.isOpenQuotient_comp_iff
add_to_ega "IV 14.1.2" "(i), special case" IsOpenMap.codRestrict
add_to_ega "IV 14.1.2" "(i), special case" IsOpenMap.mapsToRestrict
add_to_ega "IV 14.1.2" "(iii), special case" IsOpenMap.of_comp
add_to_ega "IV 14.1.2" "(i), special case" IsOpenMap.restrictPreimage
add_to_ega "IV 14.1.2" "(i), special case" IsOpenMap.subtype_map
add_to_ega "IV 14.1.2" "(i), special case" IsOpenMap.subtype_mk
add_to_ega "IV 14.1.2" "(iii), special case" IsOpenQuotientMap.isOpenMap_iff
add_to_ega "IV 14.1.2" "(iii), special case" IsOpenQuotientMap.of_comp
add_to_ega "IV 14.1.2" "(iii), special case" IsOpenQuotientMap.of_comp_iff
add_to_ega "IV 14.1.2" "(i), special case"
  TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage
add_to_ega "IV 14.1.6" "partial" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_ega "IV 14.3.1" AlgebraicGeometry.UniversallyOpen
add_to_ega "IV 14.3.4" "(ii), global form" AlgebraicGeometry.UniversallyOpen.fst
add_to_ega "IV 14.3.4" "(i), special case"
  AlgebraicGeometry.UniversallyOpen.instIsMultiplicativeScheme
add_to_ega "IV 14.3.4" "(i), special case"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderCompositionScheme
add_to_ega "IV 14.3.4" "(ii), global form" AlgebraicGeometry.UniversallyOpen.snd
add_to_ega "IV 14.3.12" "Only the morphisms g" CategoryTheory.Limits.Sigma.desc
add_to_ega "IV 14.4.9" AlgebraicGeometry.UniversallyOpen
add_to_ega "IV 14.5.5" "finiteness of A₁ over A" IsIntegralClosure.finite
add_to_ega "IV 14.5.5" "finiteness of A₁ over A" IsIntegralClosure.isNoetherian
add_to_ega "IV 14.5.5" Module.Finite
add_to_ega "IV 14.5.5" "partial" integralClosure.isIntegrallyClosedOfFiniteExtension
add_to_ega "IV 14.5.7" "more general" IsDiscreteValuationRing.TFAE
add_to_ega "IV 14.5.7" "more general" IsLocalRing.finrank_CotangentSpace_eq_one_iff
add_to_ega "IV 14.5.8" AlgebraicGeometry.Scheme.Hom.IsOver
add_to_ega "IV 15.1.1" "affine, special case" Ideal.Fiber
add_to_ega "IV 15.2.4" "Final clause" Module.algebraMap_bijective_of_rankAtStalk
add_to_ega "IV 15.2.4" "Freeness clause" Module.free_of_flat_of_finrank_eq
add_to_ega "IV 15.2.4" "Freeness clause" Module.free_of_flat_of_isLocalRing
add_to_ega "IV 15.4.1" AlgebraicGeometry.Scheme.Hom.asFiber
add_to_ega "IV 15.4.1" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 15.4.1" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "IV 15.4.1" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "IV 15.4.1" "special case" Ideal.Fiber
add_to_ega "IV 15.4.3" AlgebraicGeometry.AffineSpace.over
add_to_ega "IV 15.6.10" "special case" AlgebraicGeometry.smooth_of_grpObj
add_to_ega "IV 15.7.8" "partial" AlgebraicGeometry.Flat.isQuotientMap_of_surjective
add_to_ega "IV 15.7.8" Topology.IsQuotientMap
add_to_ega "IV 16.1.1" "special case" RingCon.quotientKerEquivOfSurjective
add_to_ega "IV 16.1.1" "special case" RingHom.ker
add_to_ega "IV 16.1.1" "special case" RingHom.quotientKerEquivOfSurjective
add_to_ega "IV 16.1.2" "special case" Ideal.Cotangent
add_to_ega "IV 16.1.3" "special case" AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
add_to_ega "IV 16.1.3" "special case" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app
add_to_ega "IV 16.1.11" AdicCompletion
add_to_ega "IV 16.2.1" "special case" Ideal.map_under_le_under_map
add_to_ega "IV 16.2.1" "special case" Ideal.quotientMap_comp_mk
add_to_ega "IV 16.2.3" "special case" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "IV 16.2.3" "more general" AlgebraicGeometry.IsImmersion.of_comp
add_to_ega "IV 16.3.1" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "IV 16.3.1" "special case" AlgebraicGeometry.IsImmersion.instLiftSchemeId
add_to_ega "IV 16.3.1" "more general" AlgebraicGeometry.IsImmersion.instMapDescScheme
add_to_ega "IV 16.3.3" CategoryTheory.Functor.relativelyRepresentable.symmetry
add_to_ega "IV 16.3.3" CategoryTheory.Functor.relativelyRepresentable.symmetryIso
add_to_ega "IV 16.3.3" "p₁ ∘ s = p₂ in 16.3.3.1"
  CategoryTheory.Functor.relativelyRepresentable.symmetry_fst
add_to_ega "IV 16.3.3" "p₂ ∘ s = p₁ in 16.3.3.1"
  CategoryTheory.Functor.relativelyRepresentable.symmetry_snd
add_to_ega "IV 16.3.3" "involutivity s ∘ s = id"
  CategoryTheory.Functor.relativelyRepresentable.symmetry_symmetry
add_to_ega "IV 16.3.3" CategoryTheory.Limits.pullbackSymmetry
add_to_ega "IV 16.3.3" "p₁ ∘ s = p₂ in 16.3.3.1" CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst
add_to_ega "IV 16.3.3" "p₁ ∘ s = p₂ in 16.3.3.1"
  CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc
add_to_ega "IV 16.3.3" "p₂ ∘ s = p₁ in 16.3.3.1" CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd
add_to_ega "IV 16.3.3" "p₂ ∘ s = p₁ in 16.3.3.1"
  CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc
add_to_ega "IV 16.3.7" Algebra.TensorProduct.includeLeft
add_to_ega "IV 16.3.7" Algebra.TensorProduct.includeRight
add_to_ega "IV 16.3.7" "partial" AlgebraicGeometry.diagonal_SpecMap
add_to_ega "IV 16.4.1" CategoryTheory.Limits.pullback.map
add_to_ega "IV 16.4.2" "more general" CategoryTheory.Limits.pullback.map_comp
add_to_ega "IV 16.4.3" "special case" KaehlerDifferential.map
add_to_ega "IV 16.4.3" "special case" KaehlerDifferential.map_D
add_to_ega "IV 16.4.4" "more general" Ideal.map_under_le_under_map
add_to_ega "IV 16.4.5" "special case" KaehlerDifferential.isBaseChange
add_to_ega "IV 16.4.21" "special case" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "IV 16.4.24" "(i), special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "IV 16.4.24" "(i), special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "IV 16.5.1" "more general" PresheafOfModulesOfCommRing.Derivation'
add_to_ega "IV 16.5.3" "(i), affine case" CommRingCat.KaehlerDifferential.D
add_to_ega "IV 16.5.3" "(ii)" CommRingCat.KaehlerDifferential.ext
add_to_ega "IV 16.5.3" "(ii)" Derivation.liftKaehlerDifferential_comp
add_to_ega "IV 16.5.3" "(ii)" Derivation.liftKaehlerDifferential_comp_D
add_to_ega "IV 16.5.3" "(ii)" Derivation.liftKaehlerDifferential_unique
add_to_ega "IV 16.5.3" "(ii)" Derivation.liftKaehlerDifferential_unique_iff
add_to_ega "IV 16.5.8" "partial" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_ega "IV 16.5.8" "partial, special case"
  Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
add_to_ega "IV 16.5.8" "partial"
  Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
add_to_ega "IV 16.5.8" "special case" Algebra.SubmersivePresentation.basisKaehler
add_to_ega "IV 16.5.8" "special case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_ega "IV 16.5.8" "special case" Algebra.SubmersivePresentation.basisKaehler_apply
add_to_ega "IV 16.5.8" "partial" Algebra.SubmersivePresentation.free_kaehlerDifferential
add_to_ega "IV 16.5.8" "special case" KaehlerDifferential.mvPolynomialBasis_repr_D
add_to_ega "IV 16.5.8" "special case" KaehlerDifferential.mvPolynomialBasis_repr_D_X
add_to_ega "IV 16.5.8" "special case" KaehlerDifferential.mvPolynomialBasis_repr_apply
add_to_ega "IV 16.5.8" "special case" KaehlerDifferential.mvPolynomialBasis_repr_comp_D
add_to_ega "IV 16.5.8" "special case" KaehlerDifferential.mvPolynomialBasis_repr_symm_single
add_to_ega "IV 16.5.9" "partial" Derivation.commutator_apply
add_to_ega "IV 16.5.9" "partial" Derivation.commutator_coe_linear_map
add_to_ega "IV 16.5.9" "partial" Derivation.couple
add_to_ega "IV 16.5.9" "partial" Derivation.instBracket
add_to_ega "IV 16.5.9" "Lie Γ(S, special case" Derivation.instLieAlgebra
add_to_ega "IV 16.5.9" "partial" Derivation.instLieRing
add_to_ega "IV 16.5.10" "special case" KaehlerDifferential.isBaseChange
add_to_ega "IV 16.5.14" "partial" CommRingCat.KaehlerDifferential.ext
add_to_ega "IV 16.5.14" "partial" CommRingCat.KaehlerDifferential.ext_iff
add_to_ega "IV 16.5.14" "partial" Derivation.liftKaehlerDifferential_comp
add_to_ega "IV 16.5.14" "the map Der_A(B" ModuleCat.Derivation.desc
add_to_ega "IV 16.5.14" "nonempty case" derivationToSquareZeroEquivLift
add_to_ega "IV 16.5.14" "partial" derivationToSquareZeroEquivLift_apply_coe_apply
add_to_ega "IV 16.5.14" "partial" derivationToSquareZeroEquivLift_symm_apply_apply_coe
add_to_ega "IV 16.5.14" "partial" derivationToSquareZeroOfLift
add_to_ega "IV 16.5.14" "partial" derivationToSquareZeroOfLift_apply
add_to_ega "IV 16.5.14" "local addition map" liftOfDerivationToSquareZero
add_to_ega "IV 16.5.14" "inclusion φ₁ + Der_A(B" liftOfDerivationToSquareZero_mk_apply
add_to_ega "IV 16.6.5" "special case" Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
add_to_ega "IV 16.6.5" "special case" Algebra.SubmersivePresentation.basisKaehler
add_to_ega "IV 16.6.5" "special case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_ega "IV 16.6.5" "partial" Module.Basis.ExteriorAlgebra
add_to_ega "IV 16.6.5" "partial" Module.Basis.exteriorPower
add_to_ega "IV 16.6.5" "Wedge-basis clause" exteriorPower.basis_apply
add_to_ega "IV 16.6.5" "Wedge-basis clause" exteriorPower.basis_repr
add_to_ega "IV 16.6.5" "Wedge-basis clause" exteriorPower.coe_basis
add_to_ega "IV 16.6.5" "Count clause" exteriorPower.finrank_eq
add_to_ega "IV 16.10.3" AdicCompletion
add_to_ega "IV 16.10.3" AdicCompletion.instAlgebra
add_to_ega "IV 16.10.3" SymmetricAlgebra
add_to_ega "IV 16.10.6" "special case" Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
add_to_ega "IV 16.10.6" "special case" Algebra.SubmersivePresentation.basisKaehler
add_to_ega "IV 16.10.6" "special case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_ega "IV 16.11.1" "special case" Commute.add_pow
add_to_ega "IV 16.11.1" "special case" Commute.add_pow'
add_to_ega "IV 16.11.1" Finsupp
add_to_ega "IV 16.11.1" Finsupp.prod
add_to_ega "IV 16.11.1" Finsupp.sum
add_to_ega "IV 16.11.1" "16.11.1, special case" Polynomial.derivation_ext
add_to_ega "IV 16.11.3" Finsupp.single
add_to_ega "IV 16.12.1" "special case" EqualCharZero.nonempty_algebraRat_iff
add_to_ega "IV 16.12.1" "special case" isEmpty_algebraRat_iff_mixedCharZero
add_to_ega "IV 17.1.1" Algebra.FormallyEtale
add_to_ega "IV 17.1.1" "partial" Algebra.FormallyEtale.comp_bijective
add_to_ega "IV 17.1.1" "special case" Algebra.FormallyEtale.iff_comp_bijective
add_to_ega "IV 17.1.1" "special case"
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth
add_to_ega "IV 17.1.1" "partial" Algebra.FormallyEtale.instFormallySmooth
add_to_ega "IV 17.1.1" "partial" Algebra.FormallyEtale.instFormallyUnramified
add_to_ega "IV 17.1.1" "partial" Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
add_to_ega "IV 17.1.1" Algebra.FormallySmooth
add_to_ega "IV 17.1.1" "special case" Algebra.FormallySmooth.iff_comp_surjective
add_to_ega "IV 17.1.1" AlgebraicGeometry.FormallyUnramified
add_to_ega "IV 17.1.1" "partial" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_ega "IV 17.1.1" "partial" AlgebraicGeometry.FormallyUnramified.of_hom_ext
add_to_ega "IV 17.1.1" RingHom.FormallyEtale
add_to_ega "IV 17.1.1" RingHom.FormallySmooth
add_to_ega "IV 17.1.1" RingHom.FormallyUnramified
add_to_ega "IV 17.1.2" "special case" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_ega "IV 17.1.2" "special case" Ideal.IsNilpotent.induction_on
add_to_ega "IV 17.1.3" "(ii), special case" Algebra.FormallyEtale.comp
add_to_ega "IV 17.1.3" "(ii), special case" Algebra.FormallyUnramified.comp
add_to_ega "IV 17.1.3" "special case" Algebra.FormallyUnramified.of_surjective
add_to_ega "IV 17.1.3" "(iii), special case" Algebra.FormallyUnramified.quotient_map
add_to_ega "IV 17.1.3" "clause (ii)" AlgebraicGeometry.FormallyUnramified.instIsMultiplicativeScheme
add_to_ega "IV 17.1.3" "clause (iii)"
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme
add_to_ega "IV 17.1.3" "clause (ii)"
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderCompositionScheme
add_to_ega "IV 17.1.3" AlgebraicGeometry.FormallyUnramified.of_comp
add_to_ega "IV 17.1.3" "(ii), special case" RingHom.FormallyEtale.comp
add_to_ega "IV 17.1.3" "(ii), special case" RingHom.FormallySmooth.comp
add_to_ega "IV 17.1.3" "(iii), special case" RingHom.FormallySmooth.isStableUnderBaseChange
add_to_ega "IV 17.1.3" "(ii), special case" RingHom.FormallySmooth.stableUnderComposition
add_to_ega "IV 17.1.3" "(ii), special case" RingHom.FormallyUnramified.comp
add_to_ega "IV 17.1.3" "(i), special case" RingHom.FormallyUnramified.holdsForLocalization
add_to_ega "IV 17.1.3" "(iii), special case" RingHom.FormallyUnramified.isStableUnderBaseChange
add_to_ega "IV 17.1.3" "(v) affine case" RingHom.FormallyUnramified.of_comp
add_to_ega "IV 17.1.3" "(ii), special case" RingHom.FormallyUnramified.stableUnderComposition
add_to_ega "IV 17.1.4" "special case" Algebra.FormallyEtale.of_restrictScalars
add_to_ega "IV 17.1.4" "special case" Algebra.FormallySmooth.of_restrictScalars
add_to_ega "IV 17.1.4" "special case" AlgebraicGeometry.Etale.of_comp
add_to_ega "IV 17.1.4" "special case" RingHom.FormallyEtale.of_comp
add_to_ega "IV 17.1.5" "special case" Algebra.FormallyEtale.comp
add_to_ega "IV 17.1.5" "special case" Algebra.FormallyEtale.of_restrictScalars
add_to_ega "IV 17.1.5" "special case" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
add_to_ega "IV 17.1.5" "special case"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_ega "IV 17.1.5" "special case" AlgebraicGeometry.Etale.of_comp
add_to_ega "IV 17.1.5" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderCompositionScheme
add_to_ega "IV 17.1.5" "partial" AlgebraicGeometry.FormallyUnramified.of_comp
add_to_ega "IV 17.1.5" "special case" RingHom.Etale.stableUnderComposition
add_to_ega "IV 17.1.5" "special case" RingHom.FormallyEtale.comp
add_to_ega "IV 17.1.5" "special case" RingHom.FormallyEtale.of_comp
add_to_ega "IV 17.1.5" "special case" RingHom.FormallyUnramified.comp
add_to_ega "IV 17.1.6" "(i), special case" RingHom.FormallyUnramified.ofLocalizationSpanTarget
add_to_ega "IV 17.1.6" "special case" RingHom.FormallyUnramified.propertyIsLocal
add_to_ega "IV 17.2.3" "(i), special case" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_ega "IV 17.2.3" "(i), special case" Algebra.SubmersivePresentation.free_kaehlerDifferential
add_to_ega "IV 17.2.4" "affine case" KaehlerDifferential.isBaseChange_of_formallyEtale
add_to_ega "IV 17.2.4" "affine case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_ega "IV 17.2.5" "affine middle exactness" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_ega "IV 17.2.5" "partial" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "IV 17.2.5" "partial" Algebra.FormallySmooth.iff_split_injection
add_to_ega "IV 17.3.1" "special case" Algebra.Etale.iff_formallyUnramified_and_smooth
add_to_ega "IV 17.3.1" "affine case" Algebra.Etale.mk
add_to_ega "IV 17.3.1" "affine case" Algebra.Smooth.mk
add_to_ega "IV 17.3.1" "affine case" Algebra.etale_iff
add_to_ega "IV 17.3.1" "étale implies smooth" AlgebraicGeometry.Etale.instSmooth
add_to_ega "IV 17.3.1" AlgebraicGeometry.Etale.mk
add_to_ega "IV 17.3.1" AlgebraicGeometry.Smooth.mk
add_to_ega "IV 17.3.1" "special case" RingHom.etale_iff_formallyUnramified_and_smooth
add_to_ega "IV 17.3.1" "affine case" RingHom.smooth_def
add_to_ega "IV 17.3.2" Algebra.Etale
add_to_ega "IV 17.3.2" Algebra.Smooth
add_to_ega "IV 17.3.2" CommAlgCat.etale
add_to_ega "IV 17.3.2" "étale case" RingHom.Etale.ofLocalizationSpan
add_to_ega "IV 17.3.2" "étale case" RingHom.Etale.ofLocalizationSpanTarget
add_to_ega "IV 17.3.2" "étale case" RingHom.Etale.propertyIsLocal
add_to_ega "IV 17.3.2" RingHom.Smooth
add_to_ega "IV 17.3.2" "smooth case" RingHom.Smooth.ofLocalizationSpanTarget
add_to_ega "IV 17.3.3" "(iii), special case" Algebra.Etale.baseChange
add_to_ega "IV 17.3.3" "(ii), étale case" AlgebraicGeometry.Etale.instIsMultiplicativeScheme
add_to_ega "IV 17.3.3" "(ii), special case"
  AlgebraicGeometry.instIsMultiplicativeSchemeSmoothOfRelativeDimensionOfNatNat
add_to_ega "IV 17.3.3" "smooth branch of (ii)"
  AlgebraicGeometry.instIsStableUnderCompositionSchemeSmooth
add_to_ega "IV 17.3.3" "(ii), special case"
  AlgebraicGeometry.instSmoothOfRelativeDimensionOfNatNatCompScheme
add_to_ega "IV 17.3.3" AlgebraicGeometry.instSmoothOfRelativeDimensionOfNatNatOfIsOpenImmersion
add_to_ega "IV 17.3.3" "(ii), special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_ega "IV 17.3.3" "(iii), special case"
  AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(iii), special case" RingHom.Etale.isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(ii), special case" RingHom.Etale.stableUnderComposition
add_to_ega "IV 17.3.3" "(iii), special case" RingHom.Smooth.isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(ii), special case" RingHom.Smooth.stableUnderComposition
add_to_ega "IV 17.3.3" "(iii), special case"
  RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(iii), special case" RingHom.isStandardSmooth_isStableUnderBaseChange
add_to_ega "IV 17.3.3" "(ii), special case" RingHom.isStandardSmooth_stableUnderComposition
add_to_ega "IV 17.3.4" "more general"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_ega "IV 17.3.4" "more general" AlgebraicGeometry.Etale.of_comp
add_to_ega "IV 17.3.5" "étale clause" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
add_to_ega "IV 17.3.5" "étale clause"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_ega "IV 17.3.5" "étale clause" AlgebraicGeometry.Etale.of_comp
add_to_ega "IV 17.3.5" "special case" RingHom.Etale.stableUnderComposition
add_to_ega "IV 17.4.1" "partial" Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing
add_to_ega "IV 17.4.1" "special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "IV 17.4.1" "e ⇔ (O_{X_y, partial" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_ega "IV 17.4.1" "e ⇒ O_{X_y" Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing
add_to_ega "IV 17.4.1" "a ⇒ b at every point"
  Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_ega "IV 17.4.1" "e ⇒ d', partial" Algebra.FormallyUnramified.isSeparable
add_to_ega "IV 17.4.1" "d' ⇒ e, d'' ⇒ e" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "IV 17.4.1" "d'' ⇒ e, local-ring form" Algebra.FormallyUnramified.of_map_maximalIdeal
add_to_ega "IV 17.4.1" "partial"
  Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
add_to_ega "IV 17.4.1" "a ⇒ d" Algebra.IsUnramifiedAt.residueField
add_to_ega "IV 17.4.1" "e ⇒ a, affine case" Algebra.exists_unramified_of_isUnramifiedAt
add_to_ega "IV 17.4.1" "partial" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_ega "IV 17.4.1" "partial" Algebra.instFiniteResidueFieldOfIsUnramifiedAt
add_to_ega "IV 17.4.1" "partial" Algebra.instIsSeparableResidueFieldOfFormallyUnramified
add_to_ega "IV 17.4.1" "partial" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_ega "IV 17.4.1" "e ⇔ d'', affine case" Algebra.isUnramifiedAt_iff_map_eq
add_to_ega "IV 17.4.1" "c ⇔ e, affine case" Algebra.unramifiedLocus_eq_compl_support
add_to_ega "IV 17.4.1" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
add_to_ega "IV 17.4.1" "b ⇒ a, global case"
  AlgebraicGeometry.FormallyUnramified.instOfIsOpenImmersionDiagonalScheme
add_to_ega "IV 17.4.1" "a ⇒ b" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_ega "IV 17.4.1" "a ⇒ e" AlgebraicGeometry.FormallyUnramified.stalkMap
add_to_ega "IV 17.4.1.2" "e ⇔ d''" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_ega "IV 17.4.1.2" "special case"
  Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
add_to_ega "IV 17.4.1.2" "partial" Algebra.basicOpen_subset_unramifiedLocus_iff
add_to_ega "IV 17.4.1.2" "e ⇒ a" Algebra.exists_formallyUnramified_of_isUnramifiedAt
add_to_ega "IV 17.4.1.2" "partial" Algebra.formallyUnramified_iff_forall
add_to_ega "IV 17.4.1.2" "partial" Algebra.unramified_iff_forall
add_to_ega "IV 17.4.1.2" "a ⇒ b" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_ega "IV 17.4.1.2" "a ⇒ e" AlgebraicGeometry.FormallyUnramified.stalkMap
add_to_ega "IV 17.4.1.2" "special case" KaehlerDifferential.finite
add_to_ega "IV 17.4.1.2" "partial" RingHom.FormallyUnramified.ofLocalizationPrime
add_to_ega "IV 17.4.2" "a) ⇔ d'), special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "IV 17.4.2" "a) ⇒ b), special case"
  Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_ega "IV 17.4.2" "a) ⇒ d'), special case" Algebra.FormallyUnramified.isSeparable
add_to_ega "IV 17.4.2" "d') ⇒ a), special case" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "IV 17.4.2" "a) ⇔ e), special case" Algebra.basicOpen_subset_unramifiedLocus_iff
add_to_ega "IV 17.4.2" "a) ⇔ e), special case" Algebra.formallyUnramified_iff_forall
add_to_ega "IV 17.4.2" "a) ⇔ e), special case" Algebra.unramifiedLocus_eq_univ_iff
add_to_ega "IV 17.4.2" "a) ⇔ e), special case" Algebra.unramified_iff_forall
add_to_ega "IV 17.4.2" "b) ⇒ a)"
  AlgebraicGeometry.FormallyUnramified.instOfIsOpenImmersionDiagonalScheme
add_to_ega "IV 17.4.2" "a) ⇒ b)" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_ega "IV 17.4.2" "a) ⇒ e)" AlgebraicGeometry.FormallyUnramified.stalkMap
add_to_ega "IV 17.4.2" "Affine case of e ⇒ a" RingHom.FormallyUnramified.ofLocalizationPrime
add_to_ega "IV 17.4.3" "affine case"
  Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
add_to_ega "IV 17.4.5" "partial" AlgebraicGeometry.IsImmersion.instιScheme
add_to_ega "IV 17.4.5" "special case" AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_ega "IV 17.4.5" AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
add_to_ega "IV 17.4.5" CategoryTheory.Limits.pullback
add_to_ega "IV 17.4.5" CategoryTheory.Limits.pullback.lift
add_to_ega "IV 17.4.6" "partial" Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_ega "IV 17.4.6" "partial, special case"
  AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_ega "IV 17.4.6" "closedness clause"
  AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_ega "IV 17.4.10" "special case" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_ega "IV 17.5.1" "b)⇒c) for local rings"
  Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
add_to_ega "IV 17.5.1" "c)⇒a)" Algebra.IsSmoothAt.exists_notMem_isStandardSmooth
add_to_ega "IV 17.5.1" "c)⇒a), affine case" Algebra.IsSmoothAt.exists_notMem_smooth
add_to_ega "IV 17.5.1" "a)" Algebra.Smooth.flat
add_to_ega "IV 17.5.1" "a)" Algebra.Smooth.flat_of_isNoetherianRing
add_to_ega "IV 17.5.1" "b)⇒a)" Algebra.Smooth.of_formallySmooth_fiber
add_to_ega "IV 17.5.1" "a)⇔c)" Algebra.basicOpen_subset_smoothLocus_iff
add_to_ega "IV 17.5.1" "a)⇔c)" Algebra.basicOpen_subset_smoothLocus_iff_smooth
add_to_ega "IV 17.5.1" "global affine a)⇔c)" Algebra.smoothLocus_eq_univ_iff
add_to_ega "IV 17.5.1" "a⇒c" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top
add_to_ega "IV 17.5.1" "a⇔c, special case" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff
add_to_ega "IV 17.5.1" "a)⇒flatness in b)" AlgebraicGeometry.instFlatOfSmooth
add_to_ega "IV 17.5.1" "a ⇒ b, special case" RingHom.Smooth.flat
add_to_ega "IV 17.5.2" "special case" Algebra.Smooth.flat
add_to_ega "IV 17.5.2" "necessity" AlgebraicGeometry.instFlatOfSmooth
add_to_ega "IV 17.5.2" "special case" RingHom.Smooth.flat
add_to_ega "IV 17.6.1" "a) ⇔ a'), special case" Algebra.Etale.iff_formallyUnramified_and_smooth
add_to_ega "IV 17.6.1" "c) ⇒ a)" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.6.1" "partial" Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat
add_to_ega "IV 17.6.1" "special case" Algebra.etaleLocus_eq_univ_iff_etale
add_to_ega "IV 17.6.1" "affine d) ⇒ a)" Algebra.exists_etale_of_isEtaleAt
add_to_ega "IV 17.6.1" "a) ⇔ c), special case"
  AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.6.1" "c) ⇒ a)" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.6.1" "a ⇔ a′, special case" RingHom.Etale.eq_formallyUnramified_and_smooth
add_to_ega "IV 17.6.1" "a ⇔ c, special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.6.1" "a ⇔ a′, special case" RingHom.etale_iff_formallyUnramified_and_smooth
add_to_ega "IV 17.6.2" "a ⇔ c', special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_ega "IV 17.6.2" "a ⇔ a', affine case" Algebra.Etale.iff_formallyUnramified_and_smooth
add_to_ega "IV 17.6.2" "partial" Algebra.Etale.instSmooth
add_to_ega "IV 17.6.2" "partial" Algebra.Etale.instUnramified
add_to_ega "IV 17.6.2" "c ⇒ a, affine case" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.6.2" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.6.2" "partial" AlgebraicGeometry.Etale.instFormallyUnramified
add_to_ega "IV 17.6.2" "partial" AlgebraicGeometry.Etale.instSmooth
add_to_ega "IV 17.6.2" "c ⇒ a" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.6.2" "a) ⇔ a'), affine case" RingHom.Etale.eq_formallyUnramified_and_smooth
add_to_ega "IV 17.6.2" "a) ⇔ c), affine case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.6.2" "a) ⇔ a'), affine case" RingHom.etale_iff_formallyUnramified_and_smooth
add_to_ega "IV 17.7.1" "(ii), special case" Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.1" "(ii), special case" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.1" "Clause (i), special case"
  Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.1" "(ii), special case"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 17.7.1" "Clause (i), special case"
  AlgebraicGeometry.instDescendsAlongSchemeFormallyUnramifiedMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 17.7.1" "(ii), special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_ega "IV 17.7.2" Algebra.unramifiedLocus
add_to_ega "IV 17.7.2" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_ega "IV 17.7.3" "(ii)" Algebra.Etale.baseChange
add_to_ega "IV 17.7.3" "(ii)" Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.3" "(i), (ii)"
  Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.3" "(ii)" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.3" "(i), (ii)" Algebra.Unramified.baseChange
add_to_ega "IV 17.7.3" "(i), (ii)" Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat
add_to_ega "IV 17.7.3" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme
add_to_ega "IV 17.7.3" "(ii)"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 17.7.3" "(i), (ii)"
  AlgebraicGeometry.instDescendsAlongSchemeFormallyUnramifiedMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 17.7.3" "(ii)"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 17.7.3" "(ii)" RingHom.Etale.codescendsAlong_faithfullyFlat
add_to_ega "IV 17.7.3" "(i), (ii)" RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat
add_to_ega "IV 17.7.3" "(i), (ii)" RingHom.FormallyUnramified.isStableUnderBaseChange
add_to_ega "IV 17.7.3" "(ii)" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_ega "IV 17.7.3" "(ii)" RingHom.Smooth.isStableUnderBaseChange
add_to_ega "IV 17.7.7" "special case" Algebra.IsUnramifiedAt.of_liesOver
add_to_ega "IV 17.7.9" "special case" Algebra.Etale.exists_subalgebra_fg
add_to_ega "IV 17.7.9" "special case" Algebra.Smooth.exists_finiteType
add_to_ega "IV 17.7.9" "special case" Algebra.Smooth.exists_subalgebra_fg
add_to_ega "IV 17.7.10" "special case" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.7.10" "special case" Algebra.FormallyEtale.iff_formallyUnramified_of_field
add_to_ega "IV 17.7.10" "special case" Algebra.FormallyEtale.of_formallyUnramified_of_field
add_to_ega "IV 17.7.10" "more general" Algebra.FormallyUnramified.flat_of_restrictScalars
add_to_ega "IV 17.7.10" "special case" Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat
add_to_ega "IV 17.7.10" "special case" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.7.10" "special case" AlgebraicGeometry.Etale.of_comp
add_to_ega "IV 17.7.10" "special case" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.7.10" "special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.7.11" "partial" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "IV 17.7.11" "partial" CategoryTheory.Limits.pullback
add_to_ega "IV 17.8.2" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_ega "IV 17.8.2" "special case" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "IV 17.8.2" "special case" AlgebraicGeometry.Scheme.instEtaleFiberToSpecResidueField
add_to_ega "IV 17.9.1" "(a)" AlgebraicGeometry.IsOpenImmersion.le_monomorphisms
add_to_ega "IV 17.9.3" "partial" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_ega "IV 17.9.3" "partial"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_ega "IV 17.10.3" "Affine, special case" Algebra.IsStandardSmoothOfRelativeDimension.trans
add_to_ega "IV 17.10.3" "special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_ega "IV 17.10.3" "Affine, special case" RingHom.IsStandardSmoothOfRelativeDimension.comp
add_to_ega "IV 17.11.3" AlgebraicGeometry.AffineSpace.homOfVector
add_to_ega "IV 17.11.3" "coordinate functions"
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord
add_to_ega "IV 17.11.3" "S-morphism" AlgebraicGeometry.AffineSpace.homOfVector_over
add_to_ega "IV 17.11.3" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_ega "IV 17.11.3" "S-morphism"
  AlgebraicGeometry.AffineSpace.instIsOverHomOfVectorOverSchemeInferInstanceOverClass
add_to_ega "IV 17.11.3" "base Spec ℤ" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv
add_to_ega "IV 17.11.5" "necessity" AlgebraicGeometry.IsOpenImmersion.le_monomorphisms
add_to_ega "IV 17.12.1" "(a)⇔(b), special case" Algebra.Extension.formallySmooth_iff_split_injection
add_to_ega "IV 17.12.1" "(a)⇔(b), special case" Algebra.FormallySmooth.iff_split_injection
add_to_ega "IV 17.13.1" AlgebraicGeometry.IsImmersion.instFstScheme
add_to_ega "IV 17.13.1" "special case" AlgebraicGeometry.IsImmersion.instMorphismRestrict
add_to_ega "IV 17.13.1" AlgebraicGeometry.IsImmersion.instSndScheme
add_to_ega "IV 17.13.1" "open immersions" AlgebraicGeometry.IsOpenImmersion.instFstScheme
add_to_ega "IV 17.13.1" "open immersions" AlgebraicGeometry.IsOpenImmersion.instSndScheme
add_to_ega "IV 17.13.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_ega "IV 17.13.1" "closed immersions" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_ega "IV 17.13.1" "closed immersions" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_ega "IV 17.13.1" "special case" Ideal.tensorCotangentHom_surjective
add_to_ega "IV 17.13.1" "affine closed immersions" RingHom.surjective_isStableUnderBaseChange
add_to_ega "IV 17.13.5" "more general" CategoryTheory.Limits.pullback_fst_map_snd_isPullback
add_to_ega "IV 17.13.5" "Case Z=X" CategoryTheory.Limits.pullback_lift_diagonal_isPullback
add_to_ega "IV 17.13.5" "more general" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_ega "IV 17.13.7" "partial" AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right
add_to_ega "IV 17.13.7" "underlying set" AlgebraicGeometry.Scheme.Pullback.range_fst_comp
add_to_ega "IV 17.13.7" "underlying set" AlgebraicGeometry.Scheme.Pullback.range_snd_comp
add_to_ega "IV 17.13.7" "special case" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "IV 17.13.7" "special case" AlgebraicGeometry.isPullback_opens_inf_le
add_to_ega "IV 17.13.9" "special case" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "IV 17.13.9" "special case" AlgebraicGeometry.IsImmersion.instLiftSchemeId
add_to_ega "IV 17.13.9" CategoryTheory.Limits.Pi.lift
add_to_ega "IV 17.13.9" "partial" CategoryTheory.Limits.Pi.lift_π
add_to_ega "IV 17.13.9" "binary relative diagonal" CategoryTheory.Limits.pullback.diagonal
add_to_ega "IV 17.13.9" "binary power X×_S X" CategoryTheory.Limits.pullback.diagonalObj
add_to_ega "IV 17.13.9" "binary case" CategoryTheory.Limits.pullback.diagonal_fst
add_to_ega "IV 17.13.9" "special case" CategoryTheory.Limits.pullback_fst_map_snd_isPullback
add_to_ega "IV 17.13.9" "special case" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_ega "IV 17.13.11" "two open sub-preschemes" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "IV 17.13.11" "special case" AlgebraicGeometry.isPullback_opens_inf_le
add_to_ega "IV 17.14.1" "partial" Algebra.FormallyEtale.comp_bijective
add_to_ega "IV 17.15.3" "more general" AlgebraicGeometry.AffineSpace.homOfVector
add_to_ega "IV 17.15.5" "a ⇒ c" Algebra.smoothLocus_eq_compl_support_inter
add_to_ega "IV 17.15.7" "Necessity direction" Algebra.smoothLocus_eq_compl_support_inter
add_to_ega "IV 17.15.8" Algebra.trdeg
add_to_ega "IV 17.15.8" IsLocalRing.maximalIdeal
add_to_ega "IV 17.15.9" "partial" Algebra.Extension.cotangentComplex_mk
add_to_ega "IV 17.15.9" KaehlerDifferential.kerCotangentToTensor
add_to_ega "IV 17.15.9" "partial" KaehlerDifferential.kerCotangentToTensor_toCotangent
add_to_ega "IV 17.15.11" "a ⇔ c, affine case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_ega "IV 17.15.11" "a ⇒ b, affine case" Algebra.Etale.instUnramified
add_to_ega "IV 17.15.11" "b ⇒ a, affine case" Algebra.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.15.11" "a ⇔ c, affine case" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_ega "IV 17.15.11" "a ⇔ b, affine case" Algebra.FormallyEtale.iff_formallyUnramified_of_field
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_ega "IV 17.15.11" "b ⇒ a, affine case" Algebra.FormallyEtale.of_formallyUnramified_of_field
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyUnramified.isSeparable
add_to_ega "IV 17.15.11" "special case" Algebra.FormallyUnramified.of_isSeparable
add_to_ega "IV 17.15.11" "a ⇒ c, special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "IV 17.15.11" "more general" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.15.11" "more general" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_ega "IV 17.15.11" "a ⇔ b, affine case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_ega "IV 17.15.12" "special case"
  AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
add_to_ega "IV 17.15.13" "special case"
  AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
add_to_ega "IV 17.15.15" "necessity" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_ega "IV 17.15.15" "necessity" Algebra.Smooth.flat
add_to_ega "IV 17.15.15" "necessity" Algebra.Smooth.flat_of_isNoetherianRing
add_to_ega "IV 17.15.15" "necessity: flatness" AlgebraicGeometry.instFlatOfSmooth
add_to_ega "IV 17.15.15" "necessity" RingHom.Smooth.flat
