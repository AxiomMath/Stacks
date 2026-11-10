module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Semi
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Yoneda
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.GradedAlgebra.AlgHom
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Maps.Strict.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import StacksCore.Algebra.Algebra.Opposite
import StacksCore.RingTheory.NormTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA II references registered by name

Declarations realizing numbered items of EGA II, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "II 1.1.1" "f_*F as an O_S-module" AlgebraicGeometry.Scheme.Modules.pushforward
add_to_ega "II 1.1.2" "partial" AlgebraicGeometry.Scheme.Hom.comp_app
add_to_ega "II 1.1.2" "partial" AlgebraicGeometry.Scheme.Hom.comp_appTop
add_to_ega "II 1.2.1" AlgebraicGeometry.IsAffineHom
add_to_ega "II 1.2.2" "more general" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "II 1.2.2" "more general" AlgebraicGeometry.IsClosedImmersion.hasAffineProperty
add_to_ega "II 1.2.2" "affine ambient scheme"
  AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
add_to_ega "II 1.2.2" "more general" AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion
add_to_ega "II 1.2.2" "more general" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_ega "II 1.2.3" "more general" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "II 1.2.3" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "II 1.2.3" "affine target" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_ega "II 1.2.4" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_ega "II 1.2.4" "special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsQuasiAffine
add_to_ega "II 1.2.7" "special case" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_ega "II 1.2.7" "partial" AlgebraicGeometry.AffineSpace.hom_ext
add_to_ega "II 1.2.7" "Injectivity of h ↦ A(h)" AlgebraicGeometry.ext_of_isAffine
add_to_ega "II 1.3.2" "partial" AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen
add_to_ega "II 1.3.4" "more general" AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine
add_to_ega "II 1.3.4" "sufficiency" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_ega "II 1.3.4" "necessity" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_ega "II 1.3.5" AlgebraicGeometry.IsAffineHom.comp_iff
add_to_ega "II 1.3.5" "Implication" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "II 1.3.5" "Implication"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "II 1.3.5" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeIsAffineHom
add_to_ega "II 1.3.6" "geometric equivalence" AlgebraicGeometry.IsAffineHom.comp_iff
add_to_ega "II 1.3.6" "more general" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "II 1.3.6" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "II 1.3.6" "partial" AlgebraicGeometry.instIsMultiplicativeSchemeIsAffineHom
add_to_ega "II 1.3.6" "special case" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_ega "II 1.3.6" "special case" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_ega "II 1.3.8" "special case" AlgebraicGeometry.affine_isReduced_iff
add_to_ega "II 1.3.8" "special case" AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier
add_to_ega "II 1.3.8" "special case" AlgebraicGeometry.isReduced_of_isAffine_isReduced
add_to_ega "II 1.4.3" "special case" AlgebraicGeometry.tilde
add_to_ega "II 1.4.3" "special case" AlgebraicGeometry.tildeEquiv
add_to_ega "II 1.4.6" "special case" AlgebraicGeometry.IsAffine.of_isPullback
add_to_ega "II 1.4.6" "special case"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "II 1.4.6" "Affine intermediate base"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_ega "II 1.4.6" "Affine intermediate base"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "II 1.4.6" "special case" AlgebraicGeometry.pullbackSpecIso
add_to_ega "II 1.4.6" "special case" AlgebraicGeometry.pullbackSpecIso'
add_to_ega "II 1.4.9" "more general" AlgebraicGeometry.IsAffineOpen.biSup_of_disjoint
add_to_ega "II 1.4.9" "more general" AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint
add_to_ega "II 1.4.9" AlgebraicGeometry.IsAffineOpen.sup_of_disjoint
add_to_ega "II 1.4.9" AlgebraicGeometry.instIsAffineCoprodScheme
add_to_ega "II 1.4.9" AlgebraicGeometry.instIsAffineHomDescScheme
add_to_ega "II 1.4.9" "more general" AlgebraicGeometry.instIsAffineSigmaObjScheme
add_to_ega "II 1.4.9" "more general" AlgebraicGeometry.instIsIsoSchemeCoprodSpec
add_to_ega "II 1.4.10" "special case" AlgebraicGeometry.IsClosedImmersion.Spec_iff
add_to_ega "II 1.4.10" "special case" AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
add_to_ega "II 1.4.10" "special case" AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine
add_to_ega "II 1.5.1" "more general"
  AlgebraicGeometry.HasAffineProperty.affineAnd_isStableUnderBaseChange
add_to_ega "II 1.5.1" "affine case" AlgebraicGeometry.affineAnd_isStableUnderBaseChange
add_to_ega "II 1.5.3" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "II 1.5.3" "partial" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "II 1.5.3" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "II 1.5.3" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "II 1.5.3" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "II 1.5.3" AlgebraicGeometry.instCanonicallyOverFiber
add_to_ega "II 1.5.4" "special case"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "II 1.5.4" AlgebraicGeometry.instIsAffineFiberOfIsAffineHom
add_to_ega "II 1.5.4" "more general" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_ega "II 1.5.4" "more general" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "II 1.5.5" "first clause, X affine" AlgebraicGeometry.IsAffine.of_isPullback
add_to_ega "II 1.5.5" "special case"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "II 1.5.5" "special case" AlgebraicGeometry.affineAnd_isStableUnderBaseChange
add_to_ega "II 1.5.5" "first clause, X affine"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_ega "II 1.5.5" "first clause, X affine"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "II 1.5.6" "special case" AlgebraicGeometry.Spec.map
add_to_ega "II 1.5.6" "special case" AlgebraicGeometry.instIsOverMapOfHomSpecOf
add_to_ega "II 1.5.6" "special case" AlgebraicGeometry.pullbackSpecIso
add_to_ega "II 1.5.6" "special case" AlgebraicGeometry.pullbackSpecIso'
add_to_ega "II 1.5.6" "affine canonical case" AlgebraicGeometry.pullbackSpecIso_inv_fst
add_to_ega "II 1.5.6" "affine canonical case" AlgebraicGeometry.pullbackSpecIso_inv_fst'_assoc
add_to_ega "II 1.5.6" "affine canonical case" AlgebraicGeometry.pullbackSpecIso_inv_fst_assoc
add_to_ega "II 1.6.1" AlgebraicGeometry.IsAffineHom
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.IsAffineHom.comp_iff
add_to_ega "II 1.6.2" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "II 1.6.2" "(i), affine target"
  AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion
add_to_ega "II 1.6.2" "(iii), special case"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "II 1.6.2" AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "II 1.6.2" "(iii), special case" AlgebraicGeometry.instIsAffineFiberOfIsAffineHom
add_to_ega "II 1.6.2" "(iii), special case"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeIsAffineHom
add_to_ega "II 1.6.2" "(v), special case" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_ega "II 1.6.2" "more general" AlgebraicGeometry.isClosedImmersion_iff_isAffineHom
add_to_ega "II 1.6.3" "more general" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "II 1.6.3" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "II 1.6.3" "affine target" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_ega "II 1.7.1" "partial" IsSymmetricAlgebra.algHom_ext
add_to_ega "II 1.7.1" "partial" IsSymmetricAlgebra.lift_unique
add_to_ega "II 1.7.1" SymmetricAlgebra
add_to_ega "II 1.7.1" "more general" SymmetricAlgebra.IsSymmetricAlgebra.mvPolynomial
add_to_ega "II 1.7.1" "partial" SymmetricAlgebra.algHom
add_to_ega "II 1.7.1" "partial" SymmetricAlgebra.algHom_ext
add_to_ega "II 1.7.1" "partial" SymmetricAlgebra.algHom_ext_iff
add_to_ega "II 1.7.1" "more general" SymmetricAlgebra.equivMvPolynomial
add_to_ega "II 1.7.1" "partial" SymmetricAlgebra.equivMvPolynomial_ι_apply
add_to_ega "II 1.7.1" "more general" SymmetricAlgebra.lift
add_to_ega "II 1.7.1" SymmetricAlgebra.ι
add_to_ega "II 1.7.2" "more general" IsSymmetricAlgebra.lift
add_to_ega "II 1.7.2" "partial" IsSymmetricAlgebra.lift_comp_linearMap
add_to_ega "II 1.7.2" LinearMap
add_to_ega "II 1.7.2" ModuleCat.semilinearMapAddEquiv
add_to_ega "II 1.7.12" AlgebraicGeometry.AffineSpace
add_to_ega "II 1.7.12" "special case" AlgebraicGeometry.AffineSpace.SpecIso
add_to_ega "II 1.7.12" "special case" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_ega "II 1.7.13" "partial" LinearMap
add_to_ega "II 1.7.14" "partial" IsSymmetricAlgebra.algHom_ext
add_to_ega "II 1.7.14" IsSymmetricAlgebra.lift
add_to_ega "II 1.7.14" "affine injectivity" SymmetricAlgebra.algHom_ext
add_to_ega "II 1.7.14" "affine injectivity" SymmetricAlgebra.algHom_ext_iff
add_to_ega "II 1.7.14" "special case" SymmetricAlgebra.lift
add_to_ega "II 2.1.1" DirectSum.instCommRingOfNat
add_to_ega "II 2.1.1" "partial" DirectSum.instCommSemiringOfNat
add_to_ega "II 2.1.1" "special case" DirectSum.instModuleOfNat
add_to_ega "II 2.1.1" DirectSum.instRingOfNat
add_to_ega "II 2.1.1" "partial" DirectSum.instSemiringOfNat
add_to_ega "II 2.1.1" GradedRing
add_to_ega "II 2.1.1" "partial" HomogeneousIdeal.irrelevant_eq_iSup
add_to_ega "II 2.1.1" "partial" HomogeneousIdeal.irrelevant_eq_span
add_to_ega "II 2.1.1" SetLike.GradeZero.instCommRing
add_to_ega "II 2.1.1" SetLike.GradeZero.instRing
add_to_ega "II 2.1.1" "partial" SetLike.GradeZero.submonoid
add_to_ega "II 2.1.1" SetLike.GradeZero.subring
add_to_ega "II 2.1.1" "1 ∈ S₀" SetLike.GradeZero.subsemiring
add_to_ega "II 2.1.2" "partial" CategoryTheory.GradedObject.Monoidal.tensorObj
add_to_ega "II 2.1.2" "special case" DirectSum.GAlgebra
add_to_ega "II 2.1.2" "more general" GradedAlgHom
add_to_ega "II 2.1.2" "special case" GradedAlgebra
add_to_ega "II 2.1.2" "special case" GradedAlgebra.baseChange
add_to_ega "II 2.1.2" "more general" GradedRingHom
add_to_ega "II 2.1.5" "sufficiency" Algebra.EssFiniteType.isNoetherianRing
add_to_ega "II 2.1.5" "necessity" GradedRing.GradeZero.isNoetherianRing
add_to_ega "II 2.1.5" "sufficiency" isNoetherianRing_of_fg
add_to_ega "II 2.1.6" "(i), special case" MvPolynomial.homogeneousSubmodule_fg
add_to_ega "II 2.1.6" "special case" MvPolynomial.homogeneousSubmodule_one_pow
add_to_ega "II 2.1.6" "(vi), special case" MvPolynomial.mem_pow_idealOfVars_iff'
add_to_ega "II 2.1.6" "(i), special case" MvPolynomial.weightedHomogeneousSubmodule_fg
add_to_ega "II 2.1.10" "more general" Ideal.IsHomogeneous.radical
add_to_ega "II 2.1.11" "special case"
  MonomialOrder.mem_nonZeroDivisors_of_leadingCoeff_mem_nonZeroDivisors
add_to_ega "II 2.1.11" "special case" Polynomial.mem_nonZeroDivisors_of_leadingCoeff
add_to_ega "II 2.2.1" "more general" HomogeneousLocalization
add_to_ega "II 2.2.1" HomogeneousLocalization.Away
add_to_ega "II 2.2.2" "more general" HomogeneousLocalization.Away.isLocalization_mul
add_to_ega "II 2.2.3" "partial" HomogeneousLocalization.Away.isLocalization_mul
add_to_ega "II 2.2.3" "partial" HomogeneousLocalization.awayMap_mk
add_to_ega "II 2.2.7" HomogeneousLocalization
add_to_ega "II 2.2.7" HomogeneousLocalization.AtPrime
add_to_ega "II 2.2.7" "S_(f), special case" HomogeneousLocalization.Away
add_to_ega "II 2.3.1" ProjectiveSpectrum
add_to_ega "II 2.3.2" "(E), special case" AlgebraicGeometry.Proj.basicOpen_mul
add_to_ega "II 2.3.2" "partial" AlgebraicGeometry.Proj.basicOpen_zero
add_to_ega "II 2.3.2" ProjectiveSpectrum.zeroLocus
add_to_ega "II 2.3.2" ProjectiveSpectrum.zeroLocus_bUnion
add_to_ega "II 2.3.2" "V₊(0)=Proj(S)" ProjectiveSpectrum.zeroLocus_bot
add_to_ega "II 2.3.2" "V₊(S)=∅" ProjectiveSpectrum.zeroLocus_empty_of_one_mem
add_to_ega "II 2.3.2" ProjectiveSpectrum.zeroLocus_iUnion
add_to_ega "II 2.3.2" "special case" ProjectiveSpectrum.zeroLocus_mul_homogeneousIdeal
add_to_ega "II 2.3.2" "special case" ProjectiveSpectrum.zeroLocus_mul_ideal
add_to_ega "II 2.3.2" "singleton subsets" ProjectiveSpectrum.zeroLocus_singleton_mul
add_to_ega "II 2.3.2" "V₊(0)=Proj(S)" ProjectiveSpectrum.zeroLocus_singleton_zero
add_to_ega "II 2.3.2" "special case" ProjectiveSpectrum.zeroLocus_span
add_to_ega "II 2.3.2" "two subsets" ProjectiveSpectrum.zeroLocus_union
add_to_ega "II 2.3.2" "V₊(S)=∅" ProjectiveSpectrum.zeroLocus_univ
add_to_ega "II 2.3.3" AlgebraicGeometry.Proj.basicOpen
add_to_ega "II 2.3.3" AlgebraicGeometry.Proj.basicOpen_mul
add_to_ega "II 2.3.3" ProjectiveSpectrum.basicOpen
add_to_ega "II 2.3.3" ProjectiveSpectrum.basicOpen_mul
add_to_ega "II 2.3.3" "D₊(fg) ⊆ D₊(f)" ProjectiveSpectrum.basicOpen_mul_le_left
add_to_ega "II 2.3.3" "D₊(fg) ⊆ D₊(g)" ProjectiveSpectrum.basicOpen_mul_le_right
add_to_ega "II 2.3.3" "(E)" ProjectiveSpectrum.isClosed_iff_zeroLocus
add_to_ega "II 2.3.3" "(E)" ProjectiveSpectrum.isClosed_zeroLocus
add_to_ega "II 2.3.3" "(E)" ProjectiveSpectrum.isOpen_iff
add_to_ega "II 2.3.3" ProjectiveSpectrum.top
add_to_ega "II 2.3.3" ProjectiveSpectrum.zariskiTopology
add_to_ega "II 2.3.5" "more general" AlgebraicGeometry.Proj.SpecMap_awayMap_awayι
add_to_ega "II 2.3.5" AlgebraicGeometry.Proj.basicOpenToSpec
add_to_ega "II 2.3.5" "more general" AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap
add_to_ega "II 2.3.5" AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier
add_to_ega "II 2.3.5" "partial" AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.isPrime_carrier
add_to_ega "II 2.3.5" "partial" AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier
add_to_ega "II 2.3.5" "partial" AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen
add_to_ega "II 2.3.5" AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.toFun
add_to_ega "II 2.3.5" AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec
add_to_ega "II 2.3.5" "partial" AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_preimage_basicOpen
add_to_ega "II 2.3.5" "partial" AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
add_to_ega "II 2.3.5" AlgebraicGeometry.projIsoSpec
add_to_ega "II 2.3.5" AlgebraicGeometry.projIsoSpecTopComponent
add_to_ega "II 2.3.6" "more general" AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_toSpec
add_to_ega "II 2.3.6" AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_isIso
add_to_ega "II 2.3.6" "more general" AlgebraicGeometry.projIsoSpec
add_to_ega "II 2.3.6" AlgebraicGeometry.projIsoSpecTopComponent
add_to_ega "II 2.3.9" "more general" Ideal.IsHomogeneous.radical_eq
add_to_ega "II 2.3.11" ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
add_to_ega "II 2.3.12" "partial" ProjectiveSpectrum.gc_homogeneousIdeal
add_to_ega "II 2.3.12" "partial" ProjectiveSpectrum.gc_ideal
add_to_ega "II 2.3.12" "partial" ProjectiveSpectrum.gc_set
add_to_ega "II 2.3.12" "more general" ProjectiveSpectrum.vanishingIdeal_iUnion
add_to_ega "II 2.3.12" "more general" ProjectiveSpectrum.vanishingIdeal_union
add_to_ega "II 2.3.12" "partial" ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
add_to_ega "II 2.3.14" "special case" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
add_to_ega "II 2.3.14" "special case" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
add_to_ega "II 2.4.1" "Spec(ω_{fg" AlgebraicGeometry.Proj.SpecMap_awayMap_awayι
add_to_ega "II 2.4.1" "partial" AlgebraicGeometry.Proj.affineOpenCover
add_to_ega "II 2.4.1" "partial" AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan
add_to_ega "II 2.4.1" "(f)" AlgebraicGeometry.Proj.awayι
add_to_ega "II 2.4.1" "(f)" AlgebraicGeometry.Proj.basicOpenIsoAway
add_to_ega "II 2.4.1" "(f)" AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap
add_to_ega "II 2.4.1" "partial" AlgebraicGeometry.Proj.instIsOpenImmersionAwayι
add_to_ega "II 2.4.1" "partial" AlgebraicGeometry.Proj.pullbackAwayιIso_hom_awayι
add_to_ega "II 2.4.1" AlgebraicGeometry.projIsoSpec
add_to_ega "II 2.4.2" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "II 2.4.2" AlgebraicGeometry.Proj.isSeparated
add_to_ega "II 2.4.3" "more general" AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan
add_to_ega "II 2.4.3" "more general" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
add_to_ega "II 2.4.3" "more general" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
add_to_ega "II 2.4.5" DirectSum.GAlgebra
add_to_ega "II 2.4.5" GradedAlgebra
add_to_ega "II 2.4.5" GradedRing
add_to_ega "II 2.4.5" "partial" SetLike.GradeZero.instAlgebra
add_to_ega "II 2.4.5" "partial" SetLike.GradeZero.subalgebra
add_to_ega "II 2.4.6" "special case" AlgebraicGeometry.Proj.toSpecZero
add_to_ega "II 2.5.2" "(f)" AlgebraicGeometry.Proj.basicOpenIsoAway
add_to_ega "II 2.5.5" "Case M = S" AlgebraicGeometry.Proj.stalkIso
add_to_ega "II 2.5.5" "Case M = S" AlgebraicGeometry.Proj.stalkIso'
add_to_ega "II 2.6.2" "partial" AlgebraicGeometry.Proj.awayMap_awayToSection
add_to_ega "II 2.6.2" "partial" AlgebraicGeometry.Proj.awayMap_awayToSection_assoc
add_to_ega "II 2.6.2" "partial" HomogeneousLocalization.awayMap_fromZeroRingHom
add_to_ega "II 2.6.2" "partial" HomogeneousLocalization.fromZeroRingHom
add_to_ega "II 2.7.1" "base A = S₀"
  AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 2.7.1" "partial" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "II 2.7.1" "locally of finite type"
  AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 2.7.1" "quasi-compactness"
  AlgebraicGeometry.Proj.instQuasiCompactToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.Proj.awayToSection_comp_appLE
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.Proj.awayToSection_comp_appLE_assoc
add_to_ega "II 2.8.1" "Φ_f, special case" AlgebraicGeometry.Proj.awayι_comp_map
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.Proj.awayι_comp_map_assoc
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.Proj.map
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.Proj.map_preimage_basicOpen
add_to_ega "II 2.8.1" "special case"
  AlgebraicGeometry.Proj.sheafedSpaceMap_hom_base_hom_apply_asHomogeneousIdeal_carrier
add_to_ega "II 2.8.1" "special case" AlgebraicGeometry.ProjectiveSpectrum.comap
add_to_ega "II 2.8.1" "Underlying point map" AlgebraicGeometry.ProjectiveSpectrum.comapFun
add_to_ega "II 2.8.2" "partial" AlgebraicGeometry.Proj.awayToSection_comp_appLE
add_to_ega "II 2.8.2" "partial" AlgebraicGeometry.Proj.awayToSection_comp_appLE_assoc
add_to_ega "II 2.8.2" "partial" AlgebraicGeometry.Proj.awayι_comp_map
add_to_ega "II 2.8.2" "partial" AlgebraicGeometry.Proj.awayι_comp_map_assoc
add_to_ega "II 2.8.2" "special case" AlgebraicGeometry.Proj.map
add_to_ega "II 2.8.4" "special case" AlgebraicGeometry.Proj.map_comp
add_to_ega "II 2.8.6" "partial" Module.compHom
add_to_ega "II 2.8.6" "partial" Module.restrictScalars
add_to_ega "II 2.8.6" "partial" ModuleCat.RestrictScalars.obj'
add_to_ega "II 2.8.6" "partial" RestrictScalars.module
add_to_ega "II 2.8.6" "partial" SemimoduleCat.Algebra.instModuleCarrier
add_to_ega "II 2.8.9" "partial" Algebra.TensorProduct.includeLeft
add_to_ega "II 2.8.9" "partial" Algebra.TensorProduct.includeLeftRingHom
add_to_ega "II 2.8.9" GradedAlgHom.includeRight
add_to_ega "II 2.8.9" "value formula for φ" GradedAlgHom.includeRight_apply
add_to_ega "II 2.8.9" GradedAlgebra.baseChange
add_to_ega "II 2.9.5" IsSymmetricAlgebra.lift
add_to_ega "II 2.9.5" SymmetricAlgebra.lift
add_to_ega "II 3.1.1" "partial" CategoryTheory.GradedObject.hasShift
add_to_ega "II 3.1.1" "partial" CategoryTheory.GradedObject.shiftFunctor_obj_apply
add_to_ega "II 3.1.3" "special case" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "II 3.1.3" "partial"
  AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 3.1.3" "partial"
  AlgebraicGeometry.Proj.instQuasiCompactToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 3.1.3" "special case" AlgebraicGeometry.Proj.isSeparated
add_to_ega "II 3.1.4" "special case" AlgebraicGeometry.Proj.basicOpen
add_to_ega "II 3.1.4" "coordinate ring of X_f" AlgebraicGeometry.Proj.basicOpenIsoAway
add_to_ega "II 3.1.4" "special case" AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_toSpec
add_to_ega "II 3.1.4" "special case" AlgebraicGeometry.projIsoSpec
add_to_ega "II 3.1.4" "partial" AlgebraicGeometry.projIsoSpecTopComponent
add_to_ega "II 3.1.5" "affine base" AlgebraicGeometry.Proj.basicOpen_mul
add_to_ega "II 3.1.5" "special case" ProjectiveSpectrum.basicOpen_mul
add_to_ega "II 3.1.6" "special case" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
add_to_ega "II 3.1.6" "special case" AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
add_to_ega "II 3.1.7" "partial" MvPolynomial.algebraTensorAlgEquiv
add_to_ega "II 3.1.7" "special case" MvPolynomial.gradedAlgebra
add_to_ega "II 3.1.12" "special case" AlgebraicGeometry.Scheme.nilradical
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf <|
    "instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpenToOpenₗ"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "II 3.2.1" "special case" $decl:ident))
add_to_ega "II 3.4.1" "special case"
  AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 3.4.1" "partial"
  AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 3.4.1" "partial"
  AlgebraicGeometry.Proj.instQuasiCompactToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 3.5.1" "special case" AlgebraicGeometry.Proj.map
add_to_ega "II 3.5.1" "special case" AlgebraicGeometry.Proj.mapAffineOpenCover
add_to_ega "II 3.5.5" "special case" Algebra.FiniteType.baseChange
add_to_ega "II 3.5.5" "partial" AlgebraicGeometry.instLocallyOfFiniteTypeFstScheme
add_to_ega "II 3.5.5" "partial" AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme
add_to_ega "II 3.5.6" "special case" AlgebraicGeometry.Proj.map
add_to_ega "II 3.5.6" "special case" GradedAlgHom
add_to_ega "II 3.5.6" "special case" GradedAlgHom.liftEquiv
add_to_ega "II 3.7.1" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections
add_to_ega "II 3.7.1" "special case" GradedAlgHom.liftEquiv
add_to_ega "II 3.7.2" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict
add_to_ega "II 3.7.2" "(f), special case"
  AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
add_to_ega "II 3.7.2" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections_resLE
add_to_ega "II 3.7.2" "more general" AlgebraicGeometry.Proj.map_preimage_basicOpen
add_to_ega "II 3.7.3" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict
add_to_ega "II 3.7.3" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
add_to_ega "II 3.7.3" "special case" AlgebraicGeometry.Proj.fromOfGlobalSections_resLE
add_to_ega "II 3.8.1" "more general" AlgebraicGeometry.IsImmersion.instIsZariskiLocalAtTarget
add_to_ega "II 3.8.1" "Immersion clause" AlgebraicGeometry.IsImmersion.instMorphismRestrict
add_to_ega "II 3.8.1" "Closed-immersion clause"
  AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "II 3.8.1" "Open-immersion clause" AlgebraicGeometry.instIsOpenImmersionMorphismRestrict
add_to_ega "II 4.5.9" "special case" CommRing.Pic
add_to_ega "II 4.5.9" "special case" CommRing.Pic.mk
add_to_ega "II 4.5.9" "special case" CommRing.Pic.mk_eq_mk_iff
add_to_ega "II 4.6.15" "j is a closed immersion" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "II 4.6.15" "Z is defined by J" AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι
add_to_ega "II 4.6.18" "special case"
  AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 4.6.18" "partial"
  AlgebraicGeometry.Proj.instLocallyOfFiniteTypeToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 4.6.18" "partial"
  AlgebraicGeometry.Proj.instQuasiCompactToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 5.1.1" AlgebraicGeometry.Scheme.IsQuasiAffine
add_to_ega "II 5.1.2" "more general" AlgebraicGeometry.LocallyRingedSpace.toΓSpec
add_to_ega "II 5.1.2" "b ⇒ d, b ⇒ d′" AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen
add_to_ega "II 5.1.2" "d′ ⇒ b" AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen
add_to_ega "II 5.1.2" "b) ⇒ a)" AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion
add_to_ega "II 5.1.2" AlgebraicGeometry.Scheme.openCoverBasicOpenTop
add_to_ega "II 5.1.2" AlgebraicGeometry.Scheme.toSpecΓ
add_to_ega "II 5.1.2" "a) ⇒ d), affine X" AlgebraicGeometry.isBasis_basicOpen
add_to_ega "II 5.1.2" "special case" AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "II 5.1.3" "special case" AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion
add_to_ega "II 5.1.6" "a ⇒ b, special case"
  AlgebraicGeometry.Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine
add_to_ega "II 5.1.6" "a ⇒ d, special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsQuasiAffine
add_to_ega "II 5.1.10" "(ii), special case" AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom
add_to_ega "II 5.1.10" "special case" AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion
add_to_ega "II 5.1.10" "(i), special case" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_ega "II 5.2.1" "b ⇒ a" AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen
add_to_ega "II 5.2.1" "b ⇒ a" AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen
add_to_ega "II 5.4.1" AlgebraicGeometry.IsProper
add_to_ega "II 5.4.1" AlgebraicGeometry.UniversallyClosed
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.comp_iff
add_to_ega "II 5.4.2" AlgebraicGeometry.IsProper.instCompScheme
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.instFstScheme
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.instIsMultiplicativeScheme
add_to_ega "II 5.4.2" "(iii), open base change" AlgebraicGeometry.IsProper.instMorphismRestrict
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.instSndScheme
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "II 5.4.3" "(i), special case" AlgebraicGeometry.IsProper.comp_iff
add_to_ega "II 5.4.3" AlgebraicGeometry.IsProper.of_comp
add_to_ega "II 5.4.3" AlgebraicGeometry.instHasOfPostcompPropertySchemeIsProperIsSeparated
add_to_ega "II 5.4.9" "more general" AlgebraicGeometry.IsIntegralHom.instUniversallyClosed
add_to_ega "II 5.4.9" AlgebraicGeometry.UniversallyClosed
add_to_ega "II 5.4.9" "5.4.3(i)" AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated
add_to_ega "II 5.4.9" "5.4.3(i)"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeUniversallyClosedIsSeparated
add_to_ega "II 5.4.9" "(ii)" AlgebraicGeometry.instIsMultiplicativeSchemeUniversallyClosed
add_to_ega "II 5.4.9" "5.4.2(iii), special case"
  AlgebraicGeometry.instUniversallyClosedMorphismRestrict
add_to_ega "II 5.4.9" "5.4.3(i), special case" AlgebraicGeometry.instUniversallyClosedToImage
add_to_ega "II 5.4.9" "5.4.3(i), special case"
  AlgebraicGeometry.instUniversallyClosedToNormalization
add_to_ega "II 5.4.9" "5.4.2(ii)" AlgebraicGeometry.universallyClosedTypeComp
add_to_ega "II 5.4.9" "5.4.2(iii)" AlgebraicGeometry.universallyClosed_snd
add_to_ega "II 5.5.3" "Clause (i), special case"
  AlgebraicGeometry.Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 5.5.7" "Case Y = X affine" AlgebraicGeometry.IsAffineOpen.basicOpen
add_to_ega "II 5.5.7" "Case Y = X affine"
  AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
add_to_ega "II 5.5.8" "special case" AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
add_to_ega "II 6.1.1" AlgebraicGeometry.IsFinite
add_to_ega "II 6.1.1" "special case" AlgebraicGeometry.IsFinite.SpecMap_iff
add_to_ega "II 6.1.1" AlgebraicGeometry.IsFinite.eq_inf
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpens" ++
      "CarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "II 6.1.1" "Finite morphism" $decl:ident))
add_to_ega "II 6.1.1" "partial" AlgebraicGeometry.IsFinite.instIsIntegralHom
add_to_ega "II 6.1.1" "partial" AlgebraicGeometry.IsFinite.instLocallyOfFiniteType
add_to_ega "II 6.1.1" AlgebraicGeometry.IsIntegralHom
add_to_ega "II 6.1.1" "special case" AlgebraicGeometry.IsIntegralHom.SpecMap_iff
add_to_ega "II 6.1.1" "Integral morphism" AlgebraicGeometry.IsIntegralHom.hasAffineProperty
add_to_ega "II 6.1.2" Algebra.IsIntegral.finite
add_to_ega "II 6.1.2" "special case" Algebra.IsIntegral.of_finite
add_to_ega "II 6.1.2" "more general" Algebra.finite_adjoin_of_finite_of_isIntegral
add_to_ega "II 6.1.2" "monogenic algebras" Algebra.finite_adjoin_simple_of_isIntegral
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpens" ++
      "CarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "II 6.1.2" "finite branch" $decl:ident))
add_to_ega "II 6.1.2" "special case" AlgebraicGeometry.IsIntegralHom.SpecMap_iff
add_to_ega "II 6.1.2" "partial" AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom
add_to_ega "II 6.1.2" "integral branch" AlgebraicGeometry.IsIntegralHom.hasAffineProperty
add_to_ega "II 6.1.2" AlgebraicGeometry.IsIntegralHom.toIsAffineHom
add_to_ega "II 6.1.2" RingHom.Finite.of_isIntegral_of_finiteType
add_to_ega "II 6.1.2" RingHom.IsIntegral.to_finite
add_to_ega "II 6.1.2" "more general" RingHom.finite_iff_isIntegral_and_finiteType
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpens" ++
      "CarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "II 6.1.4" $decl:ident))
add_to_ega "II 6.1.4" AlgebraicGeometry.IsIntegralHom.hasAffineProperty
add_to_ega "II 6.1.4" "partial" AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen
add_to_ega "II 6.1.4.1" "more general" Module.Finite.of_localizationSpan
add_to_ega "II 6.1.4.1" "more general" Module.Finite.of_localizationSpan'
add_to_ega "II 6.1.4.1" "more general" Module.Finite.of_localizationSpan_finite
add_to_ega "II 6.1.4.1" "more general" Module.Finite.of_localizationSpan_finite'
add_to_ega "II 6.1.4.1" "more general" Submodule.of_localizationSpan
add_to_ega "II 6.1.4.1" "more general" Submodule.of_localizationSpan'
add_to_ega "II 6.1.5" "(i), finite clause" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "II 6.1.5" "(i), finite clause" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "II 6.1.5" "partial" AlgebraicGeometry.IsFinite.comp_iff
add_to_ega "II 6.1.5" "(ii), finite branch" AlgebraicGeometry.IsFinite.instCompScheme
add_to_ega "II 6.1.5" "(v), finite branch"
  AlgebraicGeometry.IsFinite.instHasOfPostcompPropertySchemeIsSeparated
add_to_ega "II 6.1.5" "(ii), finite branch" AlgebraicGeometry.IsFinite.instIsMultiplicativeScheme
add_to_ega "II 6.1.5" "(iii), special case" AlgebraicGeometry.IsFinite.instMorphismRestrict
add_to_ega "II 6.1.5" "(i), finite clause" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_ega "II 6.1.5" "(iii), finite branch" AlgebraicGeometry.IsFinite.instSndScheme
add_to_ega "II 6.1.5" "(v), finite branch" AlgebraicGeometry.IsFinite.of_comp
add_to_ega "II 6.1.5" "partial" AlgebraicGeometry.IsIntegralHom.comp_iff
add_to_ega "II 6.1.5" "(ii), integral branch" AlgebraicGeometry.IsIntegralHom.instCompScheme
add_to_ega "II 6.1.5" "(iii), integral branch" AlgebraicGeometry.IsIntegralHom.instFstScheme
add_to_ega "II 6.1.5" "(v), integral branch"
  AlgebraicGeometry.IsIntegralHom.instHasOfPostcompPropertySchemeIsSeparated
add_to_ega "II 6.1.5" "(ii), integral branch"
  AlgebraicGeometry.IsIntegralHom.instIsMultiplicativeScheme
add_to_ega "II 6.1.5" "(ii), integral branch"
  AlgebraicGeometry.IsIntegralHom.instIsMultiplicativeScheme_1
add_to_ega "II 6.1.5" "(iii), special case" AlgebraicGeometry.IsIntegralHom.instMorphismRestrict
add_to_ega "II 6.1.5" "(i), integral clause" AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion
add_to_ega "II 6.1.5" "(iii), integral branch" AlgebraicGeometry.IsIntegralHom.instSndScheme
add_to_ega "II 6.1.5" "(v), integral branch" AlgebraicGeometry.IsIntegralHom.of_comp
add_to_ega "II 6.1.5" "(ii), special case" RingHom.Finite.comp
add_to_ega "II 6.1.5" "(iii), special case" RingHom.finite_isStableUnderBaseChange
add_to_ega "II 6.1.5" "(ii), special case" RingHom.finite_stableUnderComposition
add_to_ega "II 6.1.5" "(iii), special case" RingHom.isIntegral_isStableUnderBaseChange
add_to_ega "II 6.1.5" "(ii), special case" RingHom.isIntegral_stableUnderComposition
add_to_ega "II 6.1.6" "finite clause" AlgebraicGeometry.IsFinite.instMorphismRestrict
add_to_ega "II 6.1.6" "integral clause" AlgebraicGeometry.IsIntegralHom.instMorphismRestrict
add_to_ega "II 6.1.7" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "II 6.1.7" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "II 6.1.7" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "II 6.1.7" "more general" AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton
add_to_ega "II 6.1.7" "more general" AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton
add_to_ega "II 6.1.7" "more general"
  AlgebraicGeometry.instIsFiniteFiberToSpecResidueFieldOfLocallyQuasiFiniteOfQuasiCompact
add_to_ega "II 6.1.7" "more general" AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber
add_to_ega "II 6.1.8" "special case" isAlgebraic_of_isFractionRing
add_to_ega "II 6.1.10" "more general"
  AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom
add_to_ega "II 6.1.10" AlgebraicGeometry.IsIntegralHom.instUniversallyClosed
add_to_ega "II 6.2.1" "(a) ⇒ (b), special case" Algebra.QuasiFiniteAt.of_isOpen_singleton
add_to_ega "II 6.2.1" "(a) ⇒ (b), affine case" Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber
add_to_ega "II 6.2.1" "(a) ⇒ (b), affine case" Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
add_to_ega "II 6.2.1" "(a) ⇒ (b)"
  AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
add_to_ega "II 6.2.2" "(b) ⇒ (a), affine case"
  Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
add_to_ega "II 6.2.2" "(a) ⇒ (c), special case" Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber
add_to_ega "II 6.2.2" "(a) ⇒ (c), special case" Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
add_to_ega "II 6.2.2" "(a) ⇒ (c)"
  AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
add_to_ega "II 6.2.3" "more general"
  AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton
add_to_ega "II 6.2.3" "more general" AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber
add_to_ega "II 6.2.4" "(iii), special case" Algebra.QuasiFinite.baseChange
add_to_ega "II 6.2.4" "(i)" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_ega "II 6.2.4" "(ii), (v)" AlgebraicGeometry.LocallyQuasiFinite.comp_iff
add_to_ega "II 6.2.4" "(ii)" AlgebraicGeometry.instIsMultiplicativeSchemeLocallyQuasiFinite
add_to_ega "II 6.2.4" "(ii)" AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyQuasiFinite
add_to_ega "II 6.2.4" "(ii)" AlgebraicGeometry.instLocallyQuasiFiniteCompScheme
add_to_ega "II 6.2.4" "(iii)" AlgebraicGeometry.instLocallyQuasiFiniteFstScheme
add_to_ega "II 6.2.4" "(iii), special case" AlgebraicGeometry.instLocallyQuasiFiniteMorphismRestrict
add_to_ega "II 6.2.4" "(i)" AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion
add_to_ega "II 6.2.4" "(i)" AlgebraicGeometry.instLocallyQuasiFiniteOfIsPreimmersion
add_to_ega "II 6.3.1" "special case" Algebra.IsIntegral.of_finite
add_to_ega "II 6.3.1" Algebra.adjoin
add_to_ega "II 6.3.1" "special case" Algebra.finite_adjoin_simple_of_isIntegral
add_to_ega "II 6.3.1" IsIntegral
add_to_ega "II 6.3.1" "special case" IsIntegral.fg_adjoin_singleton
add_to_ega "II 6.3.1" "special case" IsIntegral.of_finite
add_to_ega "II 6.3.1" "special case" IsIntegral.of_mem_of_fg
add_to_ega "II 6.3.1" Module.Finite
add_to_ega "II 6.3.1" Submodule.span
add_to_ega "II 6.3.1" "special case" isIntegral_of_submodule_noetherian
add_to_ega "II 6.3.1" "special case" mem_integralClosure_iff_mem_fg
add_to_ega "II 6.3.3" "special case" AlgEquiv.mapIntegralClosure
add_to_ega "II 6.3.3" "special case" AlgHom.mapIntegralClosure
add_to_ega "II 6.3.3" "Second step of the proof" IsIntegral.algebraMap
add_to_ega "II 6.3.3" "Second step of the proof" IsIntegral.map
add_to_ega "II 6.3.3" "special case" galRestrict'
add_to_ega "II 6.3.3" "special case" integralClosure_map_algEquiv
add_to_ega "II 6.3.3" "special case" isIntegral_algEquiv
add_to_ega "II 6.3.5" "special case" AlgEquiv.mapIntegralClosure
add_to_ega "II 6.3.5" "special case" AlgHom.mapIntegralClosure
add_to_ega "II 6.3.5" "special case" galRestrict'
add_to_ega "II 6.3.6" "more general"
  AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso_inv_coprodDesc_fromNormalization
add_to_ega "II 6.3.6" "more general"
  AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso_inv_coprodDesc_fromNormalization_assoc
add_to_ega "II 6.3.6" "partial" IsIntegral.pair
add_to_ega "II 6.3.6" "special case" IsIntegral.pair_iff
add_to_ega "II 6.3.7" "partial" AlgebraicGeometry.Scheme.Hom.instIsIntegralNormalization
add_to_ega "II 6.3.7" "X = affine line over F"
  FunctionField.ringOfIntegers.instIsFractionRingSubtypeMemSubalgebraPolynomial
add_to_ega "II 6.3.7" "X = affine line over F"
  FunctionField.ringOfIntegers.instIsIntegrallyClosedSubtypeMemSubalgebraPolynomial
add_to_ega "II 6.3.7" "special case" IsIntegralClosure.isFractionRing_of_finite_extension
add_to_ega "II 6.3.9" "partial" AlgebraicGeometry.Scheme.Hom.instIsIntegralNormalization
add_to_ega "II 6.3.9" "special case" IsIntegrallyClosed.algebraMap_eq_of_integral
add_to_ega "II 6.3.9" "special case" IsIntegrallyClosed.instIsIntegralClosure
add_to_ega "II 6.3.9" "special case" IsIntegrallyClosed.integralClosure_eq_bot
add_to_ega "II 6.3.9" "special case" IsIntegrallyClosed.integralClosure_eq_bot_iff
add_to_ega "II 6.3.9" "special case" IsIntegrallyClosed.isIntegral_iff
add_to_ega "II 6.3.9" "special case" integralClosure.isIntegrallyClosedOfFiniteExtension
add_to_ega "II 6.3.9" "special case" isIntegrallyClosed_iff_isIntegralClosure
add_to_ega "II 6.3.9" "special case" isIntegrallyClosed_iff_isIntegrallyClosedIn
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpens" ++
      "CarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "II 6.3.10" $decl:ident))
add_to_ega "II 6.3.10" "partial" AlgebraicGeometry.IsFinite.instMorphismRestrict
add_to_ega "II 6.3.10" "special case" IsField.of_isDomain_of_finite
add_to_ega "II 6.3.10" "special case" IsIntegralClosure.finite
add_to_ega "II 6.3.10" "special case" IsIntegralClosure.isNoetherian
add_to_ega "II 6.3.10" "special case" fieldOfFiniteDimensional
add_to_ega "II 6.4.1" "special case" Algebra.aeval_self_charpoly_lmul
add_to_ega "II 6.4.1" "determinant" IsBaseChange.det_endHom
add_to_ega "II 6.4.1" "more general" LinearMap.aeval_eq_aeval_mod_charpoly
add_to_ega "II 6.4.1" LinearMap.aeval_self_charpoly
add_to_ega "II 6.4.1" LinearMap.baseChange
add_to_ega "II 6.4.1" LinearMap.charpoly
add_to_ega "II 6.4.1" LinearMap.charpoly_baseChange
add_to_ega "II 6.4.1" "monicity in 6.4.1.2" LinearMap.charpoly_monic
add_to_ega "II 6.4.1" "degree n in 6.4.1.2" LinearMap.charpoly_natDegree
add_to_ega "II 6.4.1" "partial" LinearMap.charpoly_toMatrix
add_to_ega "II 6.4.1" "determinant" LinearMap.det_baseChange
add_to_ega "II 6.4.1" "σ_n(u) = det u" LinearMap.det_eq_sign_charpoly_coeff
add_to_ega "II 6.4.1" "special case" LinearMap.eval_charpoly
add_to_ega "II 6.4.1" "more general" LinearMap.polyCharpoly
add_to_ega "II 6.4.1" "partial" LinearMap.polyCharpolyAux_coeff_eval
add_to_ega "II 6.4.1" "partial" LinearMap.polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff
add_to_ega "II 6.4.1" "partial" LinearMap.polyCharpolyAux_map_eq_toMatrix_charpoly
add_to_ega "II 6.4.1" "more general" Matrix.aeval_eq_aeval_mod_charpoly
add_to_ega "II 6.4.1" Matrix.aeval_self_charpoly
add_to_ega "II 6.4.1" Matrix.charpoly
add_to_ega "II 6.4.1" "partial" Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous
add_to_ega "II 6.4.1" Matrix.charpoly.univ
add_to_ega "II 6.4.1" "partial" Matrix.charpoly.univ_coeff_card
add_to_ega "II 6.4.1" "partial" Matrix.charpoly.univ_coeff_eval₂Hom
add_to_ega "II 6.4.1" "degree-i homogeneity" Matrix.charpoly.univ_coeff_isHomogeneous
add_to_ega "II 6.4.1" "integer universality" Matrix.charpoly.univ_map_map
add_to_ega "II 6.4.1" "partial" Matrix.charpoly.univ_monic
add_to_ega "II 6.4.1" "more general" Matrix.charpoly_coeff_eq_sum_minors
add_to_ega "II 6.4.1" Matrix.charpoly_map
add_to_ega "II 6.4.1" "monicity in 6.4.1.2" Matrix.charpoly_monic
add_to_ega "II 6.4.1" "partial" Matrix.charpoly_mulVecLin
add_to_ega "II 6.4.1" "σ_n(u) = det u" Matrix.det_eq_sign_charpoly_coeff
add_to_ega "II 6.4.1" "σ_1(u) = Tr u" Matrix.trace_eq_neg_charpoly_coeff
add_to_ega "II 6.4.1" "σ_1(u) = Tr u" Matrix.trace_eq_neg_charpoly_nextCoeff
add_to_ega "II 6.4.1" "more general" Polynomial.Monic.nextCoeff_det_polyTomatrix
add_to_ega "II 6.4.1" "more general" Polynomial.coeff_det_X_add_C_card
add_to_ega "II 6.4.1" "more general" Polynomial.coeff_det_polyTomatrix_natDegree_prod_card
add_to_ega "II 6.4.1" "more general" Polynomial.leadingCoeff_det_X_one_add_C
add_to_ega "II 6.4.2" "partial" LinearMap.aeval_self_charpoly
add_to_ega "II 6.4.2" LinearMap.baseChange
add_to_ega "II 6.4.2" LinearMap.charpoly
add_to_ega "II 6.4.2" "more general" LinearMap.charpoly_baseChange
add_to_ega "II 6.4.2" LinearMap.det
add_to_ega "II 6.4.2" "more general" LinearMap.det_baseChange
add_to_ega "II 6.4.2" "partial" LinearMap.det_eq_one_of_finrank_eq_zero
add_to_ega "II 6.4.2" "partial" LinearMap.det_eq_one_of_subsingleton
add_to_ega "II 6.4.2" Matrix.charpoly
add_to_ega "II 6.4.2" Module.finrank
add_to_ega "II 6.4.2" Module.rank
add_to_ega "II 6.4.5" "special case" LinearEquiv.coe_ofIsUnitDet
add_to_ega "II 6.4.5" "necessity, special case" LinearEquiv.isUnit_det
add_to_ega "II 6.4.5" "necessity, special case" LinearEquiv.isUnit_det'
add_to_ega "II 6.4.5" "special case" LinearEquiv.ofIsUnitDet_apply
add_to_ega "II 6.4.5" "special case" LinearMap.coe_equivOfIsUnitDet
add_to_ega "II 6.4.5" "special case" LinearMap.equivOfIsUnitDet_apply
add_to_ega "II 6.4.5" "necessity, special case" LinearMap.isUnit_det
add_to_ega "II 6.4.5" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_ega "II 6.4.5" "necessity, special case" Matrix.isUnit_det_of_invertible
add_to_ega "II 6.4.5" "special case" Matrix.isUnit_iff_isUnit_det
add_to_ega "II 6.4.5" "necessity, special case" Matrix.isUnits_det_units
add_to_ega "II 6.4.5.1" RingHom.IsIntegral.isLocalHom
add_to_ega "II 6.4.5.1" "special case" isField_of_isIntegral_of_isField
add_to_ega "II 6.4.6" "special case" LinearEquiv.isUnit_det'
add_to_ega "II 6.4.6" "special case" LinearEquiv.ofIsUnitDet
add_to_ega "II 6.4.6" "special case" LinearMap.coe_equivOfIsUnitDet
add_to_ega "II 6.4.6" "sufficiency over a field" LinearMap.equivOfDetNeZero
add_to_ega "II 6.4.6" "special case" LinearMap.equivOfIsUnitDet_apply
add_to_ega "II 6.4.6" "special case" LinearMap.isUnit_det
add_to_ega "II 6.4.6" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_ega "II 6.4.7" "special case" IsArtinianRing.equivPi
add_to_ega "II 6.4.7" "partial" IsIntegral.coeff
add_to_ega "II 6.4.7" "partial" IsIntegral.pair
add_to_ega "II 6.4.7" "special case" IsIntegral.pair_iff
add_to_ega "II 6.4.7" "necessity, special case" LinearEquiv.isUnit_det'
add_to_ega "II 6.4.7" "special case" LinearEquiv.ofIsUnitDet
add_to_ega "II 6.4.7" "partial" LinearMap.aeval_self_charpoly
add_to_ega "II 6.4.7" LinearMap.baseChange
add_to_ega "II 6.4.7" LinearMap.charpoly
add_to_ega "II 6.4.7" "special case" LinearMap.coe_equivOfIsUnitDet
add_to_ega "II 6.4.7" LinearMap.det
add_to_ega "II 6.4.7" "determinant component" LinearMap.det_baseChange
add_to_ega "II 6.4.7" "special case" LinearMap.isUnit_det
add_to_ega "II 6.4.7" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_ega "II 6.4.7" "necessity for E = A^I" Matrix.isUnit_det_of_invertible
add_to_ega "II 6.4.7" "E = A^I for finite I" Matrix.isUnit_iff_isUnit_det
add_to_ega "II 6.4.8" "(v), special case" IsBaseChange.det_endHom
add_to_ega "II 6.4.8" "special case" LinearEquiv.det_mul_det_symm
add_to_ega "II 6.4.8" "(6.4.8.2) det(1_E) = 1" LinearEquiv.det_refl
add_to_ega "II 6.4.8" "special case" LinearEquiv.det_symm_mul_det
add_to_ega "II 6.4.8" "special case" LinearEquiv.det_trans
add_to_ega "II 6.4.8" "special case" LinearEquiv.isUnit_det'
add_to_ega "II 6.4.8" "special case" LinearMap.aeval_self_charpoly
add_to_ega "II 6.4.8" "special case" LinearMap.charpoly
add_to_ega "II 6.4.8" "special case" LinearMap.charpoly_baseChange
add_to_ega "II 6.4.8" "special case" LinearMap.coe_equivOfIsUnitDet
add_to_ega "II 6.4.8" "special case" LinearMap.det
add_to_ega "II 6.4.8" "special case" LinearMap.detAux
add_to_ega "II 6.4.8" "special case" LinearMap.detAux_comp
add_to_ega "II 6.4.8" "special case" LinearMap.detAux_id
add_to_ega "II 6.4.8" "special case" LinearMap.det_baseChange
add_to_ega "II 6.4.8" "special case" LinearMap.det_comp
add_to_ega "II 6.4.8" "special case" LinearMap.det_eq_one_of_finrank_eq_zero
add_to_ega "II 6.4.8" "det(0) = 1 in rank zero" LinearMap.det_eq_one_of_subsingleton
add_to_ega "II 6.4.8" "special case" LinearMap.det_id
add_to_ega "II 6.4.8" "special case" LinearMap.det_smul
add_to_ega "II 6.4.8" "special case" LinearMap.det_zero
add_to_ega "II 6.4.8" "special case" LinearMap.det_zero'
add_to_ega "II 6.4.8" "special case" LinearMap.det_zero''
add_to_ega "II 6.4.8" "special case" LinearMap.equivOfIsUnitDet_apply
add_to_ega "II 6.4.8" "partial" LinearMap.isUnit_det
add_to_ega "II 6.4.8" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_ega "II 6.4.8" "special case" LinearMap.polyCharpolyAux_baseChange
add_to_ega "II 6.4.8" "special case" LinearMap.polyCharpoly_baseChange
add_to_ega "II 6.4.8" "σ_1 = Tr is A-linear" LinearMap.trace
add_to_ega "II 6.4.8" "σ_1 = Tr is A-linear" LinearMap.traceAux
add_to_ega "II 6.4.8" "special case" Matrix.GeneralLinearGroup.det
add_to_ega "II 6.4.8" "special case" Matrix.aeval_self_charpoly
add_to_ega "II 6.4.8" "special case" Matrix.coe_det_isEmpty
add_to_ega "II 6.4.8" "special case" Matrix.detMonoidHom
add_to_ega "II 6.4.8" "special case" Matrix.det_eq_one_of_card_eq_zero
add_to_ega "II 6.4.8" "special case" Matrix.det_eq_zero_of_column_eq_zero
add_to_ega "II 6.4.8" "special case" Matrix.det_eq_zero_of_row_eq_zero
add_to_ega "II 6.4.8" "special case" Matrix.det_fin_zero
add_to_ega "II 6.4.8" "special case" Matrix.det_isEmpty
add_to_ega "II 6.4.8" "(6.4.8.1) for E = 𝒜^n" Matrix.det_mul
add_to_ega "II 6.4.8" "(6.4.8.3) for E = 𝒜^n" Matrix.det_mul_row
add_to_ega "II 6.4.8" "(6.4.8.2) for E = 𝒜^n" Matrix.det_one
add_to_ega "II 6.4.8" "(6.4.8.3) for E = 𝒜^n" Matrix.det_smul
add_to_ega "II 6.4.8" "(6.4.8.3) for E = 𝒜^n" Matrix.det_smul_of_tower
add_to_ega "II 6.4.8" "special case" Matrix.det_zero
add_to_ega "II 6.4.8" "σ_1 = Tr is A-linear" Matrix.traceLinearMap
add_to_ega "II 6.4.8" "affine case" Module.isLocallyConstant_rankAtStalk
add_to_ega "II 6.4.8" "special case" SheafOfModules.freeFunctorCompPullbackIso
add_to_ega "II 6.4.8" "special case" SheafOfModules.pullbackObjFreeIso
add_to_ega "II 6.4.9" "special case" IsBaseChange.rank_eq_of_le_nonZeroDivisors
add_to_ega "II 6.4.9" "special case" LinearEquiv.det_refl
add_to_ega "II 6.4.9" "special case" LinearEquiv.isUnit_det'
add_to_ega "II 6.4.9" "special case" LinearMap.coe_equivOfIsUnitDet
add_to_ega "II 6.4.9" "special case" LinearMap.det
add_to_ega "II 6.4.9" "special case" LinearMap.detAux
add_to_ega "II 6.4.9" "special case" LinearMap.detAux_id
add_to_ega "II 6.4.9" "special case" LinearMap.det_baseChange
add_to_ega "II 6.4.9" "special case" LinearMap.det_comp
add_to_ega "II 6.4.9" "special case" LinearMap.det_id
add_to_ega "II 6.4.9" "special case" LinearMap.det_smul
add_to_ega "II 6.4.9" "special case" LinearMap.det_zero
add_to_ega "II 6.4.9" "special case" LinearMap.equivOfIsUnitDet_apply
add_to_ega "II 6.4.9" "special case" LinearMap.isUnit_det
add_to_ega "II 6.4.9" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_ega "II 6.5.1" "special case" Algebra.lmul
add_to_ega "II 6.5.1" "special case" Algebra.lsmul
add_to_ega "II 6.5.1" "special case" Algebra.norm
add_to_ega "II 6.5.1" "special case" Algebra.norm_apply
add_to_ega "II 6.5.1" "special case" Algebra.rmul
add_to_ega "II 6.5.1" "special case" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "II 6.5.1" "special case" IsArtinianRing.equivPi
add_to_ega "II 6.5.1" "special case" IsArtinianRing.quotNilradicalEquivPi
add_to_ega "II 6.5.1" "special case" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "II 6.5.3" "more general" PresheafOfModules.unitHomEquiv
add_to_ega "II 6.5.3" "more general" SheafOfModules.freeHomEquiv
add_to_ega "II 6.5.3" "more general" SheafOfModules.unitHomEquiv
add_to_ega "II 6.5.4" "special case" IsBaseChange.finrank_eq_of_le_nonZeroDivisors
add_to_ega "II 6.5.4" "special case" IsBaseChange.lift_rank_eq_of_le_nonZeroDivisors
add_to_ega "II 6.5.4" "special case" IsBaseChange.rank_eq
add_to_ega "II 6.5.4" "special case" IsBaseChange.rank_eq_of_le_nonZeroDivisors
add_to_ega "II 6.5.8" CategoryTheory.Limits.pullback
add_to_ega "II 6.6.8" "special case" Algebra.norm
add_to_ega "II 6.6.8" "special case" LinearMap.det
add_to_ega "II 6.6.8" "special case" LinearMap.detAux
add_to_ega "II 7.1.1" "special case" IsDiscreteValuationRing.TFAE
add_to_ega "II 7.1.1" "nonfield property of A_p" IsLocalization.AtPrime.not_isField
add_to_ega "II 7.1.1" "partial" LocalSubring.exists_valuationRing_of_isMax
add_to_ega "II 7.1.1" LocalSubring.isMax_iff
add_to_ega "II 7.1.1" "more general" Valuation.Integers.integralClosure
add_to_ega "II 7.1.1" "more general" Valuation.Integers.isIntegrallyClosed
add_to_ega "II 7.1.1" "more general" Valuation.Integers.isIntegrallyClosed_integers
add_to_ega "II 7.1.1" "more general" Valuation.Integers.mem_of_integral
add_to_ega "II 7.1.1" ValuationRing
add_to_ega "II 7.1.1" "partial" ValuationSubring.isMax_toLocalSubring
add_to_ega "II 7.1.1" ValuationSubring.ofPrime
add_to_ega "II 7.1.1" "A_P is a valuation ring" ValuationSubring.ofPrime_localization
add_to_ega "II 7.1.1" "more general" instIsIntegrallyClosedSubtypeMemSubring
add_to_ega "II 7.1.1" "more general" instIsIntegrallyClosedSubtypeMemValuationSubring
add_to_ega "II 7.1.1" "special case" tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
add_to_ega "II 7.1.2" "special case" LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
add_to_ega "II 7.1.3" "special case" Subring.eq_iInf_of_isIntegrallyClosedIn
add_to_ega "II 7.1.3" "partial" Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
add_to_ega "II 7.1.3" "more general" iInf_valuationSubring_superset
add_to_ega "II 7.1.5" "j_b = (0)" AlgebraicGeometry.genericPoint_eq_bot_of_affine
add_to_ega "II 7.1.5" FractionRing
add_to_ega "II 7.1.5" "domain case, partial" Ideal.IsPrime.isMaximal_of_ne_bot
add_to_ega "II 7.1.5" "domain case, partial" Ideal.isMaximal_of_isPrime_of_ne_bot
add_to_ega "II 7.1.5" "j_a = m" IsLocalRing.PrimeSpectrum.asIdeal_top
add_to_ega "II 7.1.5" IsLocalRing.ResidueField
add_to_ega "II 7.1.5" "partial" IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top
add_to_ega "II 7.1.5" IsLocalRing.closedPoint
add_to_ega "II 7.1.5" "partial" IsLocalRing.closedPoint_mem_iff
add_to_ega "II 7.1.5" "partial" IsLocalRing.closed_point_mem_iff
add_to_ega "II 7.1.5" "a is closed" IsLocalRing.isClosed_singleton_closedPoint
add_to_ega "II 7.1.5" Ring.DimensionLEOne
add_to_ega "II 7.1.5" "upper-bound clause" Ring.KrullDimLE.mk₁
add_to_ega "II 7.1.5" "upper-bound clause" Ring.krullDimLE_one_iff
add_to_ega "II 7.1.5" genericPoint
add_to_ega "II 7.1.5" "partial" ringKrullDim_eq_one_iff_of_isLocalRing_isDomain
add_to_ega "II 7.1.6" "a ⇔ c, partial" IsDiscreteValuationRing.TFAE
add_to_ega "II 7.1.6" "regular ⇒ DVR" IsLocalRing.finrank_CotangentSpace_eq_one_iff
add_to_ega "II 7.1.6" "a ⇔ c" tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
add_to_ega "II 7.2.1" AlgebraicGeometry.isClosedMap_iff_specializingMap
add_to_ega "II 7.2.1" "a ⇒ b" IsClosedMap.specializingMap
add_to_ega "II 7.2.1" SpecializingMap
add_to_ega "II 7.2.2" "more general" AlgebraicGeometry.isClosedMap_iff_specializingMap
add_to_ega "II 7.2.2" "Necessity" IsClosed.stableUnderSpecialization
add_to_ega "II 7.2.3" AlgebraicGeometry.IsSeparated.eq_valuativeCriterion
add_to_ega "II 7.2.3" "a⇒b" AlgebraicGeometry.IsSeparated.instQuasiSeparated
add_to_ega "II 7.2.3" "b⇒a" AlgebraicGeometry.IsSeparated.of_valuativeCriterion
add_to_ega "II 7.2.3" "a⇒b" AlgebraicGeometry.IsSeparated.valuativeCriterion
add_to_ega "II 7.2.3" "more general" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_ega "II 7.2.3" "more general" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_ega "II 7.2.4" "partial"
  AlgebraicGeometry.instQuasiCompactLiftSchemeIdOfQuasiSeparatedSpaceCarrierCarrierCommRingCat
add_to_ega "II 7.2.4" "absolute case"
  AlgebraicGeometry.quasiSeparatedSpace_iff_quasiCompact_prod_lift
add_to_ega "II 7.2.4" "absolute case" AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated
add_to_ega "II 7.3.2" "more general" AlgebraicGeometry.IsSeparated.eq_valuativeCriterion
add_to_ega "II 7.3.2" "more general" AlgebraicGeometry.IsSeparated.valuativeCriterion
add_to_ega "II 7.3.2" "partial" AlgebraicGeometry.Scheme.RationalMap.fromFunctionField
add_to_ega "II 7.3.2" "more general" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_ega "II 7.3.3" "partial" AlgebraicGeometry.IsSeparated.eq_valuativeCriterion
add_to_ega "II 7.3.3" "partial" AlgebraicGeometry.IsSeparated.valuativeCriterion
add_to_ega "II 7.3.8" "(a)⇒(b)" AlgebraicGeometry.IsProper.eq_valuativeCriterion
add_to_ega "II 7.3.8" "more general" AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion
add_to_ega "II 7.3.8" "(b)⇒(a)" AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion
add_to_ega "II 7.3.9" "(ii), special case"
  AlgebraicGeometry.Proj.instUniversallyClosedToSpecZeroOfFiniteTypeSubtypeMemOfNatNat
add_to_ega "II 7.3.9" "more general" CategoryTheory.yoneda
add_to_ega "II 7.3.10" "(i), proper case" AlgebraicGeometry.IsProper.eq_valuativeCriterion
add_to_ega "II 7.3.10" "more general" AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion
add_to_ega "II 7.3.11" "special case"
  AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom
add_to_ega "II 7.3.11" "more general" AlgebraicGeometry.isIntegral_appTop_of_universallyClosed
add_to_ega "II 7.3.12" "more general" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_ega "II 7.3.12" "special case" IsIntegralClosure.finite
add_to_ega "II 7.3.12" "special case" IsIntegralClosure.isNoetherian
add_to_ega "II 7.4.6" AlgebraicGeometry.Scheme.Hom.fromNormalization
add_to_ega "II 7.4.6" AlgebraicGeometry.Scheme.Hom.normalization
add_to_ega "II 7.4.7" AlgebraicGeometry.IsProper
add_to_ega "II 7.4.14" "partial" AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "II 7.4.14" "partial" AlgebraicGeometry.genericPoint_eq_bot_of_affine
add_to_ega "II 7.4.14" "partial" AlgebraicGeometry.projIsoSpec
add_to_ega "II 7.4.17" FunctionField
add_to_ega "II 8.1.1" "special case" Ideal.Filtration.pow_smul_le
add_to_ega "II 8.1.1" "special case" Ideal.Filtration.pow_smul_le_pow_smul
add_to_ega "II 8.1.1" "special case" Submodule.galgebra
add_to_ega "II 8.1.1" "special case" Submodule.tensorEquivMul
add_to_ega "II 8.2.1" "more general" HomogeneousLocalization
add_to_ega "II 8.2.1" HomogeneousLocalization.Away
add_to_ega "II 8.2.2" "special case" MvPolynomial.gradedAlgebra
add_to_ega "II 8.2.2" "special case" MvPolynomial.isHomogeneous_C_mul_X
add_to_ega "II 8.2.2" "8.2.2.2, special case" MvPolynomial.isHomogeneous_C_mul_X_pow
add_to_ega "II 8.2.2" "special case" MvPolynomial.isHomogeneous_X
add_to_ega "II 8.2.2" "8.2.2.2, special case" MvPolynomial.isHomogeneous_monomial
add_to_ega "II 8.2.2" "8.2.2.1" Polynomial
add_to_ega "II 8.2.4" "partial" PolynomialModule
add_to_ega "II 8.2.6" "S_[1] = S_+" HomogeneousIdeal.irrelevant
add_to_ega "II 8.3.1" "partial" AlgebraicGeometry.Scheme.Over
add_to_ega "II 8.3.9" "reverse direction" CategoryTheory.GrpObj.ofRepresentableBy
add_to_ega "II 8.3.9" "forward direction" CategoryTheory.Hom.group
add_to_ega "II 8.3.9" "partial" CategoryTheory.yonedaAddGrpObj
add_to_ega "II 8.3.9" "forward direction" CategoryTheory.yonedaGrp
add_to_ega "II 8.3.9" "forward direction" CategoryTheory.yonedaGrpObj
add_to_ega "II 8.3.9" "reverse direction" CategoryTheory.yonedaGrpObjIsoOfRepresentableBy
add_to_ega "II 8.5.1" "special case" AlgebraicGeometry.Spec.locallyRingedSpaceMap
add_to_ega "II 8.5.1" "special case" AlgebraicGeometry.Spec.map
add_to_ega "II 8.5.1" "(8.5.1.2), special case" AlgebraicGeometry.instIsOverMapOfHomSpecOf
open AlgebraicGeometry in
add_to_ega "II 8.8.6.1" "integral-domain clause"
  instIsDomainCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfIsIntegral
add_to_ega "II 8.10.1" "special case" Algebra.Extension.infinitesimal
add_to_ega "II 8.10.1" "special case" Ideal.Cotangent
add_to_ega "II 8.10.1" "special case" Ideal.cotangentIdeal
add_to_ega "II 8.10.3" AdicCompletion
add_to_ega "II 8.10.3" IsDomain
add_to_ega "II 8.10.3" IsRegularLocalRing
add_to_ega "II 8.10.3" PowerSeries
add_to_ega "II 8.10.3" irreducibleComponents
add_to_ega "II 8.10.6" "partial" AlgebraicGeometry.IsSeparated.hasAffineProperty
add_to_ega "II 8.11.1" Homeomorph.quotientKerEquivRange
add_to_ega "II 8.11.1" "partial" IsClosedMap.isQuotientMap
add_to_ega "II 8.11.1" "partial" IsOpenMap.isQuotientMap
add_to_ega "II 8.11.1" "partial" IsOpenQuotientMap.iff_isOpenMap_isQuotientMap
add_to_ega "II 8.11.1" "partial" IsOpenQuotientMap.isQuotientMap
add_to_ega "II 8.11.1" Topology.IsQuotientMap
add_to_ega "II 8.11.1" Topology.IsQuotientMap.homeomorph
add_to_ega "II 8.11.1" instTopologicalSpaceQuot
add_to_ega "II 8.11.3" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "II 8.11.3" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "II 8.11.3" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_ega "II 8.11.3" "locally Artinian target" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_ega "II 8.12.4" "special case" AlgebraicGeometry.Proj.map
add_to_ega "II 8.12.4" "special case" AlgebraicGeometry.Proj.sheafedSpaceMap
add_to_ega "II 8.13.2" "partial" Polynomial.homogenize
add_to_ega "II 8.13.2" "partial" Polynomial.isHomogeneous_homogenize
add_to_ega "II 8.13.4" "partial" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "II 8.13.4" "partial" AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData
add_to_ega "II 8.13.4" "partial" AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι
add_to_ega "II 8.13.4" "(ii), special case" Polynomial.coeff_homogenize
add_to_ega "II 8.13.4" "(ii), special case" Polynomial.homogenize
add_to_ega "II 8.14.1" "special case" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "II 8.14.1" "special case" AlgebraicGeometry.Proj.isSeparated
add_to_ega "II 8.14.6" "partial" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "II 8.14.6" "more general" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "II 8.14.6" "special case" AlgebraicGeometry.isIso_fromTildeΓ_pushforward
