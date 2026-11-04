module  -- shake: keep-all

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Galois.Action
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.EssSurj
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Inseparable
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.Opens
import StacksCore.RingTheory.NormTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 1 references registered by name

Declarations realizing numbered items of SGA 1, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "1 I 2.1" AdicCompletion
add_to_sga "1 I 2.1" IsLocalRing.ResidueField
add_to_sga "1 I 2.1" IsNoetherianRing
add_to_sga "1 I 2.1" Module.Finite
add_to_sga "1 I 2.2" "special case" Algebra.QuasiFinite.iff_of_isArtinianRing
add_to_sga "1 I 2.2" "special case" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_sga "1 I 2.2" "finite ⇒ quasi-finite" AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite
add_to_sga "1 I 2.2" "special case" Module.Finite.of_quasiFinite
add_to_sga "1 I 2.2" "finite ⇒ quasi-finite" RingHom.QuasiFinite.of_finite
add_to_sga "1 I 3.1" "special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_sga "1 I 3.1" "(i) ⇔ (ii), special case" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_sga "1 I 3.1" "(ii)" Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_sga "1 I 3.1" "(ii)" Algebra.FormallyUnramified.isSeparable
add_to_sga "1 I 3.1" "field case: (i) ⇒ (ii)" Algebra.FormallyUnramified.of_isSeparable
add_to_sga "1 I 3.1" "(i) ⇒ (ii)" Algebra.FormallyUnramified.of_map_maximalIdeal
add_to_sga "1 I 3.1" "(ii)" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_sga "1 I 3.1" "(ii)" Algebra.instFiniteResidueFieldOfIsUnramifiedAt
add_to_sga "1 I 3.1" "(ii)" Algebra.instIsSeparableResidueFieldOfFormallyUnramified
add_to_sga "1 I 3.1" "(ii)" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_sga "1 I 3.1" "special case" Algebra.isUnramifiedAt_iff_map_eq
add_to_sga "1 I 3.1" "(ii)"
  AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
add_to_sga "1 I 3.1" "global (iii) ⇒ (ii)"
  AlgebraicGeometry.FormallyUnramified.instOfIsOpenImmersionDiagonalScheme
add_to_sga "1 I 3.1" "global (ii) ⇒ (iii)"
  AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_sga "1 I 3.2" "special case" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_sga "1 I 3.2" "partial" Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing
add_to_sga "1 I 3.2" "partial" Algebra.FormallyUnramified.of_map_maximalIdeal
add_to_sga "1 I 3.2" "special case" Algebra.IsUnramifiedAt
add_to_sga "1 I 3.2" "partial" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_sga "1 I 3.2" "partial" Algebra.instFiniteResidueFieldOfIsUnramifiedAt
add_to_sga "1 I 3.2" "partial" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_sga "1 I 3.2" "special case" Algebra.isUnramifiedAt_iff_map_eq
add_to_sga "1 I 3.3" "affine case" Algebra.exists_formallyUnramified_of_isUnramifiedAt
add_to_sga "1 I 3.3" "affine case" Algebra.exists_unramified_of_isUnramifiedAt
add_to_sga "1 I 3.3" "special case" Algebra.isOpen_unramifiedLocus
add_to_sga "1 I 3.4" "affine identity graph" Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_sga "1 I 3.4" "special case" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_sga "1 I 3.4" "special case" CategoryTheory.Limits.pullback.diagonal
add_to_sga "1 I 3.4" "more general" CategoryTheory.Limits.pullback.lift
add_to_sga "1 I 3.5" "(iii), affine case" Algebra.Unramified.baseChange
add_to_sga "1 I 3.5" "(ii), affine case" Algebra.Unramified.comp
add_to_sga "1 I 3.6" "(v)" AlgebraicGeometry.FormallyUnramified.of_comp
add_to_sga "1 I 4.1" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_sga "1 I 4.5" "affine case" Algebra.exists_etale_of_isEtaleAt
add_to_sga "1 I 4.5" "affine case" Algebra.isOpen_etaleLocus
add_to_sga "1 I 4.6" "(iii), affine case" Algebra.Etale.baseChange
add_to_sga "1 I 4.6" "(ii), affine case" Algebra.Etale.comp
add_to_sga "1 I 4.6" "more general" AlgebraicGeometry.Etale.instIsMultiplicativeScheme
add_to_sga "1 I 4.6" "(iii), special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "1 I 4.6" "special case" AlgebraicGeometry.Etale.instResLE
add_to_sga "1 I 4.6" "(iii), affine case" RingHom.Etale.isStableUnderBaseChange
add_to_sga "1 I 4.6" "(ii), affine case" RingHom.Etale.stableUnderComposition
add_to_sga "1 I 4.8" "more general"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_sga "1 I 4.8" "more general" AlgebraicGeometry.Etale.of_comp
add_to_sga "1 I 4.10" "special case" Algebra.discr
add_to_sga "1 I 4.10" "partial" Algebra.discr_isUnit_of_basis
add_to_sga "1 I 4.10" "étale implies nonzero" Algebra.discr_not_zero_of_basis
add_to_sga "1 I 4.10" "special case" Algebra.trace
add_to_sga "1 I 4.10" "special case" Algebra.trace'
add_to_sga "1 I 4.10" "special case" Algebra.traceForm
add_to_sga "1 I 5.4" AlgebraicGeometry.Scheme.Hom.residueFieldMap
add_to_sga "1 I 5.6" "special case" Algebra.FormallyEtale.comp_bijective
add_to_sga "1 I 5.6" "special case" Algebra.FormallyUnramified.lift_unique
add_to_sga "1 I 5.6" "special case" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_sga "1 I 5.6" "special case"
  StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
add_to_sga "1 I 5.8" "Net clause, special case" Algebra.IsUnramifiedAt.residueField
add_to_sga "1 I 5.8" "special case" Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
add_to_sga "1 I 6.2" "special case" Algebra.FormallyEtale.comp_bijective
add_to_sga "1 I 7.3" "special case" IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
add_to_sga "1 I 7.3" "partial" StandardEtalePair.instEtaleRing
add_to_sga "1 I 7.4" "partial" StandardEtalePair.instEtaleRing
add_to_sga "1 I 7.5" "more general" AlgebraicGeometry.LocallyRingedSpace.residueField
add_to_sga "1 I 7.5" "more general" AlgebraicGeometry.Scheme.residueField
add_to_sga "1 I 7.5" "more general" Ideal.ResidueField
add_to_sga "1 I 7.5" IsLocalRing.ResidueField
add_to_sga "1 I 7.5" "more general" Module.finrank
add_to_sga "1 I 7.5" "partial" StandardEtalePair.instEtaleRing
add_to_sga "1 I 7.7" "Sufficiency in Cor. 7.7" Algebra.FormallyUnramified.quotient
add_to_sga "1 I 7.8" "special case" Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn
add_to_sga "1 I 9.3" "special case" Algebra.FormallyUnramified.isReduced_of_field
add_to_sga "1 I 9.6" AdjoinRoot
add_to_sga "1 I 9.6" Algebra.trace
add_to_sga "1 I 9.6" IsUnit
add_to_sga "1 I 9.6" "special case" Module.Basis.traceDual_powerBasis_eq
add_to_sga "1 I 9.6" Polynomial.Monic
add_to_sga "1 I 9.6" Polynomial.Separable
add_to_sga "1 I 9.6" Polynomial.derivative
add_to_sga "1 I 9.8" Submodule.traceDual
add_to_sga "1 I 9.8" "special case" traceForm_dualSubmodule_adjoin
add_to_sga "1 I 9.9" "special case" IsIntegralClosure.range_le_span_dualBasis
add_to_sga "1 I 9.9" "special case" integralClosure_le_span_dualBasis
add_to_sga "1 I 10.1" "special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "1 I 10.1" "partial, special case" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "1 I 10.1" "partial" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "1 I 10.1" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "1 I 10.3" "special case" AlgebraicGeometry.Scheme.functionField
add_to_sga "1 I 10.11" AlgebraicGeometry.IsReduced
add_to_sga "1 I 10.12" IsNoetherianRing
add_to_sga "1 II 1.1" Algebra.IsSmoothAt
add_to_sga "1 II 1.1" Algebra.Smooth
add_to_sga "1 II 1.1" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_sga "1 II 1.1" RingHom.Smooth
add_to_sga "1 II 1.2" "more general" Algebra.isOpen_smoothLocus
add_to_sga "1 II 1.3" "clause (i), special case" Algebra.Etale.iff_formallyUnramified_and_smooth
add_to_sga "1 II 1.3" "clause (i), affine case" Algebra.Etale.instSmooth
add_to_sga "1 II 1.3" "(ii), special case" Algebra.IsStandardSmooth.baseChange
add_to_sga "1 II 1.3" "(iii), special case" Algebra.IsStandardSmooth.trans
add_to_sga "1 II 1.3" "(ii), special case" Algebra.IsStandardSmoothOfRelativeDimension.baseChange
add_to_sga "1 II 1.3" "(iii), special case" Algebra.Smooth.comp
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.Etale.instSmooth
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.Etale.instSmoothOfRelativeDimensionOfNatNat
add_to_sga "1 II 1.3" "more general"
  AlgebraicGeometry.instIsMultiplicativeSchemeSmoothOfRelativeDimensionOfNatNat
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.instIsStableUnderCompositionSchemeSmooth
add_to_sga "1 II 1.3" "(iii), special case"
  AlgebraicGeometry.instRespectsSchemeSmoothIsOpenImmersion
add_to_sga "1 II 1.3" "(ii), special case" AlgebraicGeometry.instSmoothMorphismRestrict
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.instSmoothOfIsOpenImmersion
add_to_sga "1 II 1.3" "(iii), special case"
  AlgebraicGeometry.instSmoothOfRelativeDimensionOfNatNatCompScheme
add_to_sga "1 II 1.3" "more general"
  AlgebraicGeometry.instSmoothOfRelativeDimensionOfNatNatOfIsOpenImmersion
add_to_sga "1 II 1.3" "(iii), special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_sga "1 II 1.3" "(ii), special case"
  AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "1 II 1.3" "clause (i), affine case" RingHom.Etale.eq_formallyUnramified_and_smooth
add_to_sga "1 II 1.3" "(i), special case" RingHom.Smooth.id
add_to_sga "1 II 1.3" "(ii), special case" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "1 II 1.3" "(iii), special case" RingHom.Smooth.stableUnderComposition
add_to_sga "1 II 1.3" "(i), special case" RingHom.etale_iff_formallyUnramified_and_smooth
add_to_sga "1 II 1.4" "étale ⇒ smooth" Algebra.Etale.instSmooth
add_to_sga "1 II 1.4" "partial" AlgebraicGeometry.Etale.instSmooth
add_to_sga "1 II 1.5" "special case" Algebra.IsStandardSmooth.relativeDimension
add_to_sga "1 II 1.5" "special case" Algebra.IsStandardSmoothOfRelativeDimension
add_to_sga "1 II 1.5" "special case"
  AlgebraicGeometry.instIsMultiplicativeSchemeSmoothOfRelativeDimensionOfNatNat
add_to_sga "1 II 1.5" "special case"
  AlgebraicGeometry.instSmoothOfRelativeDimensionOfNatNatCompScheme
add_to_sga "1 II 1.5" "special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_sga "1 II 1.5" "special case" RingHom.IsStandardSmoothOfRelativeDimension
add_to_sga "1 II 2.1" "sufficiency" Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
add_to_sga "1 II 2.1" "sufficiency at a point" Algebra.IsSmoothAt.of_formallySmooth_fiber
add_to_sga "1 II 2.1" "(a)" Algebra.Smooth.flat
add_to_sga "1 II 2.1" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "1 II 2.1" "necessity of (a)" AlgebraicGeometry.instFlatOfSmooth
add_to_sga "1 II 2.1" "(a)" RingHom.Smooth.flat
add_to_sga "1 II 2.2" "special case" Algebra.IsSmoothAt.of_formallySmooth_fiber
add_to_sga "1 II 2.2" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "1 II 2.4" AdicCompletion
add_to_sga "1 II 2.4" AlgebraicGeometry.IsReduced
add_to_sga "1 II 2.4" AlgebraicGeometry.Scheme.Hom.fiber
add_to_sga "1 II 3.1" "reduced case" AlgebraicGeometry.AffineSpace.instIsReduced
add_to_sga "1 II 4.1" "special case" KaehlerDifferential.isBaseChange_of_formallyEtale
add_to_sga "1 II 4.1" "special case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_sga "1 II 4.2" "Affine case" Algebra.SubmersivePresentation.basisKaehler
add_to_sga "1 II 4.2" "Affine case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_sga "1 II 4.3" "(ii), special case" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_sga "1 II 4.8" AlgebraicGeometry.AffineSpace.homOfVector
add_to_sga "1 II 4.8" "coordinate pullbacks" AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord
add_to_sga "1 II 4.8" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_sga "1 II 4.8" "partial" AlgebraicGeometry.AffineSpace.hom_ext
add_to_sga "1 II 4.8" "partial" AlgebraicGeometry.AffineSpace.hom_ext_iff
add_to_sga "1 II 4.8" "S-morphism"
  AlgebraicGeometry.AffineSpace.instIsOverHomOfVectorOverSchemeInferInstanceOverClass
add_to_sga "1 II 4.8" "base Spec Z" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv
add_to_sga "1 II 4.8" "more general" Ideal.Fiber
add_to_sga "1 II 4.9" "special case" Algebra.SubmersivePresentation.basisCotangent_apply
add_to_sga "1 II 4.10" "(i)⇔(iv)" Algebra.FormallySmooth.iff_injective_lTensor_residueField
add_to_sga "1 II 4.11" "(i)⇒(ii), special case" Algebra.SubmersivePresentation.basisCotangent
add_to_sga "1 II 4.11" "(i)⇒(ii), special case" Algebra.SubmersivePresentation.basisCotangent_apply
add_to_sga "1 II 4.13" "affine descent" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_sga "1 II 4.13" "global descent"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "1 II 4.13" "global ascent" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "1 II 4.13" CategoryTheory.Limits.pullback
add_to_sga "1 II 4.13" "affine descent" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_sga "1 II 4.13" "affine ascent" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "1 II 4.14" AdicCompletion
add_to_sga "1 II 4.14" AdicCompletion.instAlgebra
add_to_sga "1 II 4.14" AdicCompletion.instCommRing
add_to_sga "1 II 4.14" AdicCompletion.subalgebra
add_to_sga "1 II 4.14" AdicCompletion.subring
add_to_sga "1 II 4.14" "étale implies smooth" Algebra.Etale.instSmooth
add_to_sga "1 II 4.14" "(iii), special case"
  Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
add_to_sga "1 II 4.14" "(iii), special case"
  Algebra.FormallySmooth.iff_injective_lTensor_residueField
add_to_sga "1 II 4.14" "partial" AlgebraicGeometry.Etale.instSmooth
add_to_sga "1 II 4.14" "partial" Ideal.Cotangent
add_to_sga "1 II 4.14" "special case" MvPowerSeries.toAdicCompletion
add_to_sga "1 II 4.14" "special case" MvPowerSeries.toAdicCompletionAlgEquiv
add_to_sga "1 II 4.14" "partial" Submodule.spanFinrank
add_to_sga "1 II 4.17" "more general" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_sga "1 II 5.6" AdicCompletion
add_to_sga "1 II 5.6" "(i) ⇒ (ii)" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "1 II 5.6" "(i) ⇒ (ii)" Algebra.FormallyEtale.of_isSeparable
add_to_sga "1 II 5.6" "(i) ⇒ (ii)" Algebra.FormallyEtale.of_isSeparable_aux
add_to_sga "1 II 5.6" "(iv)⇒(i)"
  exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
add_to_sga "1 II 5.6" "(iv)⇒(i), special case"
  exists_isTranscendenceBasis_and_isSeparable_of_perfectField
add_to_sga "1 II 5.7" "special case" Algebra.IsAlgebraic.isSeparable_of_perfectField
add_to_sga "1 II 5.7" "special case" Algebra.IsSeparable.of_integral
add_to_sga "1 II 5.7" PerfectField
add_to_sga "1 II 5.8" "p = dim O_{X" AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
add_to_sga "1 II 5.9" "more general" Algebra.Extension.cotangentComplex_mk
add_to_sga "1 II 5.9" "p = codim_X closure{x}" AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
add_to_sga "1 II 5.9" Ideal.Cotangent
add_to_sga "1 II 5.9" IsRegularLocalRing
add_to_sga "1 II 5.9" KaehlerDifferential.kerCotangentToTensor
add_to_sga "1 II 5.9" "partial" KaehlerDifferential.kerCotangentToTensor_toCotangent
add_to_sga "1 III 1.1" "partial" AdicCompletion
add_to_sga "1 III 1.2" Algebra.EssFiniteType
add_to_sga "1 III 1.2" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_sga "1 III 1.2" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_sga "1 III 1.2" "special case" Algebra.FormallySmooth.of_algebraicIndependent
add_to_sga "1 III 1.2" "special case" Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
add_to_sga "1 III 1.2" "special case" Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
add_to_sga "1 III 1.2" "special case" Algebra.FormallySmooth.of_perfectField
add_to_sga "1 III 1.4" "partial" Algebra.EssFiniteType.isNoetherianRing
add_to_sga "1 III 1.4" Localization.AtPrime
add_to_sga "1 III 1.4" "partial" RingHom.finite_isStableUnderBaseChange
add_to_sga "1 III 1.7" Ideal.Fiber
add_to_sga "1 III 1.7" IsLocalRing.ResidueField
add_to_sga "1 III 2.2" "special case" IsLocalRing.CotangentSpace
add_to_sga "1 III 2.2" IsLocalRing.instModuleResidueFieldCotangentSpace
add_to_sga "1 III 5.2" "partial" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_sga "1 III 5.2" "rank-zero case"
  Algebra.IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential
add_to_sga "1 III 5.2" "partial" Algebra.SubmersivePresentation.free_kaehlerDifferential
add_to_sga "1 III 5.2" "special case"
  StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
add_to_sga "1 III 7.1" "partial" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_sga "1 IV 1.2" "(i), special case" IsLocalization.flat
add_to_sga "1 IV 1.2" "(i) with M=B" Localization.flat
add_to_sga "1 IV 1.2" "(i), special case" Module.Flat.instLocalizationAlgebraMapSubmonoid
add_to_sga "1 IV 1.2" "(i), special case" Module.Flat.localizedModule
add_to_sga "1 IV 1.2" "(i), special case" Module.Flat.of_isLocalizedModule
add_to_sga "1 IV 1.2" "(ii)" Module.flat_iff_of_isLocalization
add_to_sga "1 IV 1.2" "(ii)" Module.flat_of_isLocalized_maximal
add_to_sga "1 IV 1.2" "(ii), detection with A=B" Module.flat_of_localized_maximal
add_to_sga "1 IV 1.2" "(i), special case" RingHom.Flat.holdsForLocalizationAway
add_to_sga "1 IV 1.2" "(i), special case" RingHom.Flat.localRingHom
add_to_sga "1 IV 1.2" "(ii), special case" RingHom.Flat.ofLocalizationPrime
add_to_sga "1 IV 1.2" "(i), special case" RingHom.Flat.propertyIsLocal
add_to_sga "1 IV 1.3" "(ii), special case" IsDedekindDomain.flat_iff_torsion_eq_bot
add_to_sga "1 IV 1.3" "(ii)" Module.Flat.flat_iff_torsion_eq_bot_of_isBezout
add_to_sga "1 IV 1.3" "more general"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_sga "1 IV 1.3" "(ii), special case" Module.Flat.instOfIsDedekindDomainOfIsTorsionFree
add_to_sga "1 IV 1.3" "more general" Module.Flat.isSMulRegular_of_isRegular
add_to_sga "1 IV 1.3" Module.Flat.isSMulRegular_of_nonZeroDivisors
add_to_sga "1 IV 1.3" Module.Flat.torsion_eq_bot
add_to_sga "1 IV 1.3" "(i), special case" Module.Free.instIsTorsionFree
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_exact_iff_rTensor_exact
add_to_sga "1 IV 2.1" "(i) ⇒ (i ter)" Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_flat_and_lTensor_faithful
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality
add_to_sga "1 IV 2.1" "(i) ⇒ (i ter)" Module.FaithfullyFlat.iff_flat_and_proper_ideal
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_flat_and_rTensor_faithful
add_to_sga "1 IV 2.1" Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality
add_to_sga "1 IV 2.1" "(i) ⇒ (ii)" Module.FaithfullyFlat.lTensor_exact_iff_exact
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.lTensor_nontrivial
add_to_sga "1 IV 2.1" "(i) ⇒ (ii)" Module.FaithfullyFlat.lTensor_reflects_exact
add_to_sga "1 IV 2.1" "(ii), special case" Module.FaithfullyFlat.lTensor_surjective_iff_surjective
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left._simp_1
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right._simp_1
add_to_sga "1 IV 2.1" "(i) ⇒ (ii)" Module.FaithfullyFlat.rTensor_exact_iff_exact
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.rTensor_nontrivial
add_to_sga "1 IV 2.1" "(i) ⇒ (ii)" Module.FaithfullyFlat.rTensor_reflects_exact
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left._simp_1
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
add_to_sga "1 IV 2.1" "(i)" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right._simp_1
add_to_sga "1 IV 2.1" "faithfulness half of (i)" Module.FaithfullyFlat.zero_iff_lTensor_zero
add_to_sga "1 IV 2.1" "faithfulness half of (i)" Module.FaithfullyFlat.zero_iff_rTensor_zero
add_to_sga "1 IV 2.3" "M = B" Ideal.exists_isPrime_liesOver_of_faithfullyFlat
add_to_sga "1 IV 2.3" "M = B" PrimeSpectrum.comap_surjective_of_faithfullyFlat
add_to_sga "1 IV 2.3" "M = B" RingHom.FaithfullyFlat.eq_and
add_to_sga "1 IV 2.3" "M = B" RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_sga "1 IV 2.4" Module.support
add_to_sga "1 IV 2.6" AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
add_to_sga "1 IV 2.6" AlgebraicGeometry.flat_and_surjective_SpecMap_iff
add_to_sga "1 IV 2.6" "(i)" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_sga "1 IV 2.6" "(i)" Ideal.comap_surjective_of_faithfullyFlat
add_to_sga "1 IV 2.6" "partial" Ideal.exists_isPrime_liesOver_of_faithfullyFlat
add_to_sga "1 IV 2.6" LinearMap.baseChange
add_to_sga "1 IV 2.6" "(i)⇒(iii)" Module.FaithfullyFlat.faithfulSMul
add_to_sga "1 IV 2.6" "(i)⇒(iv)" Module.FaithfullyFlat.iff_exact_iff_rTensor_exact
add_to_sga "1 IV 2.6" "(i)⇒(iv)" Module.FaithfullyFlat.lTensor_exact_iff_exact
add_to_sga "1 IV 2.6" "(ii)⇒(i)" Module.FaithfullyFlat.of_comap_surjective
add_to_sga "1 IV 2.6" "(i)⇒(iv)" Module.FaithfullyFlat.rTensor_exact_iff_exact
add_to_sga "1 IV 2.6" "(i)⇒(iv)" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_sga "1 IV 2.6" ModuleCat.ExtendRestrictScalarsAdj.Unit.map
add_to_sga "1 IV 2.6" ModuleCat.ExtendRestrictScalarsAdj.unit
add_to_sga "1 IV 2.6" ModuleCat.ExtendScalars.map'
add_to_sga "1 IV 2.6" ModuleCat.ExtendScalars.obj'
add_to_sga "1 IV 2.6" ModuleCat.extendScalars
add_to_sga "1 IV 2.6" "partial" PrimeSpectrum.comap_surjective_of_faithfullyFlat
add_to_sga "1 IV 2.6" RingHom.FaithfullyFlat.eq_and
add_to_sga "1 IV 2.6" RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_sga "1 IV 2.6" "(i)⇒(iii)" RingHom.FaithfullyFlat.injective
add_to_sga "1 IV 3.1" AdicCompletion
add_to_sga "1 IV 3.1" AdicCompletion.instCommRing
add_to_sga "1 IV 3.1" AdicCompletion.subalgebra
add_to_sga "1 IV 3.1" AdicCompletion.submodule
add_to_sga "1 IV 3.1" AdicCompletion.subring
add_to_sga "1 IV 4.1" "special case" Module.free_of_maximalIdeal_rTensor_injective
add_to_sga "1 IV 4.1" "special case" Module.free_quotSMulTop_iff_free
add_to_sga "1 IV 4.3" "(i) ⇒ (iii)" Module.FaithfullyFlat.instOfNontrivialOfFree
add_to_sga "1 IV 4.3" Module.Flat
add_to_sga "1 IV 4.3" "(i) ⇒ (iii)" Module.Flat.of_free
add_to_sga "1 IV 4.3" "(ii) ⇒ (iii)" Module.Flat.of_projective
add_to_sga "1 IV 4.3" "case (b): (iii) ⇒ (ii)" Module.Flat.projective_of_finitePresentation
add_to_sga "1 IV 4.3" Module.Free
add_to_sga "1 IV 4.3" Module.Projective
add_to_sga "1 IV 4.3" "(i) ⇒ (ii)" Module.Projective.of_free
add_to_sga "1 IV 4.3" "case (b): (iii) ⇒ (i)" Module.free_of_flat_of_finrank_eq
add_to_sga "1 IV 4.3" "case (b): (iii) ⇒ (i)" Module.free_of_flat_of_isLocalRing
add_to_sga "1 IV 4.4" "more general" IsLocalRing.spanFinrank_eq_finrank_quotient
add_to_sga "1 IV 4.4" Module.finrank
add_to_sga "1 IV 4.4" Module.rank
add_to_sga "1 IV 4.4" "(i)⇒(vi)" Submodule.rank_eq_spanRank_of_free
add_to_sga "1 IV 5.7" "(ii)⇒(i), special case"
  Module.IsLocalRing.linearCombination_bijective_of_flat
add_to_sga "1 IV 5.7" "(ii)⇒(i)" Module.IsLocalRing.linearIndependent_of_flat
add_to_sga "1 IV 5.8" "partial" AdicCompletion
add_to_sga "1 IV 5.8" "partial" AdicCompletion.module
add_to_sga "1 IV 5.8" "partial" AdicCompletion.subalgebra
add_to_sga "1 IV 5.8" "partial" AdicCompletion.subring
add_to_sga "1 IV 6.2" "more general" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_sga "1 IV 6.2" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_sga "1 IV 6.3" specializes_iff_mem_closure
add_to_sga "1 IV 6.4" "(a)" IsOpen.stableUnderGeneralization
add_to_sga "1 IV 6.4" "special case"
  PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
add_to_sga "1 IV 6.5" "partial" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "1 IV 6.6" IsOpenMap
add_to_sga "1 IV 6.8" "more general" Module.flat_iff_of_isLocalization
add_to_sga "1 IV 6.9" "partial" Module.flat_iff_of_isLocalization
add_to_sga "1 IX 1.2" "special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "1 IX 1.2" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "1 IX 1.2" "special case" Algebra.WeaklyEtale.instOfEtale
add_to_sga "1 IX 1.2" "special case" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_sga "1 IX 1.2" "special case" AlgebraicGeometry.WeaklyEtale.instOfEtale
add_to_sga "1 IX 1.2" "more general" AlgebraicGeometry.instFlatOfSmooth
add_to_sga "1 IX 1.2" "special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_sga "1 IX 1.3" "affine schemes" Algebra.Etale.baseChange
add_to_sga "1 IX 1.3" "special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "1 IX 1.3" "special case" AlgebraicGeometry.Etale.instResLE
add_to_sga "1 IX 1.3" "affine schemes" RingHom.Etale.isStableUnderBaseChange
add_to_sga "1 IX 1.7" "special case" AlgebraicGeometry.Scheme.support_nilradical
add_to_sga "1 IX 1.8" "more general" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "1 IX 1.8" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_sga "1 IX 1.8" "more general" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "1 IX 1.8" "one-factor case" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "1 IX 1.8" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "1 IX 1.9" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "1 IX 1.9" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_sga "1 IX 1.9" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "1 IX 1.9" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "1 IX 1.9" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "1 IX 1.9" "special case" CommAlgCat.FiniteEtale
add_to_sga "1 IX 1.9" "special case" CommAlgCat.finiteEtale
add_to_sga "1 IX 2.1" "partial" Topology.IsQuotientMap
add_to_sga "1 IX 2.2" "partial" AlgebraicGeometry.Flat.isQuotientMap_of_surjective
add_to_sga "1 IX 2.3" "more general" TopologicalSpace.Opens
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.UniversallyOpen.fst
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.UniversallyOpen.snd
add_to_sga "1 IX 2.4" "special case"
  AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
add_to_sga "1 IX 2.4" "special case"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.universallyClosed_snd
add_to_sga "1 IX 3.4" AlgebraicGeometry.GeometricallyConnected
add_to_sga "1 IX 3.4" "special case" AlgebraicGeometry.GeometricallyConnected.connectedSpace
add_to_sga "1 IX 3.4" "special case" AlgebraicGeometry.Scheme.Hom.connectedComponentsHomeomorph
add_to_sga "1 IX 3.4" "special case" AlgebraicGeometry.Scheme.Hom.isConnected_preimage
add_to_sga "1 IX 3.4" "special case"
  AlgebraicGeometry.instConnectedSpaceCarrierCarrierCommRingCatPullbackSchemeOfGeometricallyConnectedOfUniversallyOpen
add_to_sga "1 IX 4.2" "special case" Algebra.Etale.baseChange
add_to_sga "1 IX 4.2" "more general" CategoryTheory.Pseudofunctor.DescentData.pullFunctor
add_to_sga "1 IX 4.2" "more general" CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj
add_to_sga "1 IX 4.2" "special case" RingHom.Etale.isStableUnderBaseChange
add_to_sga "1 IX 4.7" "special case" Algebra.FinitePresentation.of_finiteType
add_to_sga "1 IX 4.7" "partial"
  AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType
add_to_sga "1 IX 4.7" "special case" RingHom.FinitePresentation.of_finiteType
add_to_sga "1 IX 4.10" "affine Noetherian base" Algebra.FinitePresentation.of_finiteType
add_to_sga "1 IX 4.10" "more general"
  AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType
add_to_sga "1 IX 4.10" "affine Noetherian base" RingHom.FinitePresentation.of_finiteType
add_to_sga "1 IX 4.12" "partial"
  AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType
add_to_sga "1 IX 5.1" ConnectedComponents
add_to_sga "1 IX 5.6" "Connectedness of S′" AlgebraicGeometry.GeometricallyConnected.connectedSpace
add_to_sga "1 IX 5.6" "Connectedness of S′" AlgebraicGeometry.Scheme.Hom.isConnected_preimage
add_to_sga "1 IX 5.6" "Connectedness of S′"
  AlgebraicGeometry.instConnectedSpaceCarrierCarrierCommRingCatPullbackSchemeOfGeometricallyConnectedOfUniversallyOpen
add_to_sga "1 IX 5.6" "Connectedness of S′"
  AlgebraicGeometry.instConnectedSpaceCarrierCarrierCommRingCatPullbackSchemeOfGeometricallyConnectedOfUniversallyOpen_1
add_to_sga "1 IX 6.1" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_sga "1 IX 6.1" "special case" AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso
add_to_sga "1 IX 6.2" "special case" Algebra.IsFiniteSplit
add_to_sga "1 V 1.1" "more general" Algebra.IsInvariant.isIntegral
add_to_sga "1 V 1.1" "more general" Algebra.IsInvariant.isIntegral_of_profinite
add_to_sga "1 V 1.1" "more general" Algebra.IsInvariant.orbit_eq_primesOver
add_to_sga "1 V 1.1" "field case of (i)" FixedPoints.isIntegral
add_to_sga "1 V 1.1" "special case" FixedPoints.toAlgAut_surjective
add_to_sga "1 V 1.1" "closed points" Ideal.Quotient.normal
add_to_sga "1 V 1.1" "closed points" Ideal.Quotient.stabilizerHom_surjective
add_to_sga "1 V 1.1" "(iii)" instIsAlgebraicResidueFieldOfIsIntegral
add_to_sga "1 V 1.1" "(iii), special case"
  instNonemptyObjOpenNormalSubgroupStabilizerHomSurjectiveAuxFunctor
add_to_sga "1 V 1.3" "(i), special case" Algebra.IsInvariant.isIntegral
add_to_sga "1 V 1.3" "(i), special case" Algebra.IsInvariant.isIntegral_of_profinite
add_to_sga "1 V 1.3" "field case, partial" FixedPoints.isIntegral
add_to_sga "1 V 1.3" "special case" Ideal.Quotient.normal
add_to_sga "1 V 1.3" "special case" Ideal.Quotient.stabilizerHom_surjective
add_to_sga "1 V 1.3" "special case" Ideal.Quotient.stabilizerQuotientInertiaEquiv
add_to_sga "1 V 2.4" "special case" FixedPoints.toAlgAutMulEquiv
add_to_sga "1 V 2.4" "partial" FixedPoints.toAlgAut_surjective
add_to_sga "1 V 2.4" "special case" Ideal.Quotient.stabilizerQuotientInertiaEquiv
add_to_sga "1 V 2.4" "special case" IsFractionRing.stabilizerQuotientInertiaEquiv
add_to_sga "1 V 3.3" "special case" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
add_to_sga "1 V 3.3" "special case"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_sga "1 V 3.3" "special case" AlgebraicGeometry.Etale.instIsMultiplicativeScheme
add_to_sga "1 V 3.3" "special case" AlgebraicGeometry.Etale.of_comp
add_to_sga "1 V 3.3" "special case" AlgebraicGeometry.Scheme.instEtaleLeftDiscretePUnit
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsOpenImmersion.le_monomorphisms
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.IsPreimmersion.instMonoScheme
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono
add_to_sga "1 V 3.6" "monomorphism" AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMono
add_to_sga "1 V 3.6" CategoryTheory.EffectiveEpi
add_to_sga "1 V 3.6" CategoryTheory.IsRegularMono
add_to_sga "1 V 3.6" CategoryTheory.RegularEpi
add_to_sga "1 V 3.6" CategoryTheory.RegularMono
add_to_sga "1 V 3.7" "partial" AlgebraicGeometry.Scheme.pointSmallEtale
add_to_sga "1 V 4.1" "partial" CategoryTheory.PreGaloisCategory.continuousSMul_aut_fiber
add_to_sga "1 V 4.1" "partial" CategoryTheory.PreGaloisCategory.exists_lift_of_continuous
add_to_sga "1 V 4.1" "partial"
  CategoryTheory.PreGaloisCategory.instFaithfulContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 4.1" "partial"
  CategoryTheory.PreGaloisCategory.instFullContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 4.1"
  CategoryTheory.PreGaloisCategory.instIsEquivalenceContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 4.1" "partial"
  CategoryTheory.PreGaloisCategory.instIsTopologicalGroupAutFunctorFintypeCat
add_to_sga "1 V 4.2" CategoryTheory.Limits.HasFiniteColimits
add_to_sga "1 V 4.2" CategoryTheory.Limits.PreservesFiniteColimits
add_to_sga "1 V 4.2" CategoryTheory.rightExactFunctor
add_to_sga "1 V 4.2" CategoryTheory.rightExactFunctor_iff
add_to_sga "1 V 5.1" "special case" CategoryTheory.FintypeCat.instGaloisCategoryActionFintypeCat
add_to_sga "1 V 5.1" "special case" CategoryTheory.FintypeCat.instPreGaloisCategoryActionFintypeCat
add_to_sga "1 V 5.1" CategoryTheory.GaloisCategory
add_to_sga "1 V 5.1" CategoryTheory.PreGaloisCategory.FiberFunctor
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.PointedGaloisObject.isColimit
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.autMulEquivAutGalois
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.endMulEquivAutGalois
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.exists_lift_of_continuous
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.functorToAction
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.functorToAction_comp_forget₂_eq
add_to_sga "1 V 5.1" "partial" CategoryTheory.PreGaloisCategory.functorToContAction
add_to_sga "1 V 5.1" "partial"
  CategoryTheory.PreGaloisCategory.instEssSurjContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 5.1" "partial"
  CategoryTheory.PreGaloisCategory.instEssSurjContActionFintypeCatFunObjFiniteAutFunctorFunctorToContActionOfFiberFunctor
add_to_sga "1 V 5.1" "partial"
  CategoryTheory.PreGaloisCategory.instFaithfulActionFintypeCatAutFunctorFunctorToAction
add_to_sga "1 V 5.1" "partial"
  CategoryTheory.PreGaloisCategory.instFaithfulContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 5.1" "partial"
  CategoryTheory.PreGaloisCategory.instFullContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 5.1"
  CategoryTheory.PreGaloisCategory.instIsEquivalenceContActionFintypeCatFunObjFiniteAutFunctorFunctorToContAction
add_to_sga "1 V 5.1" ProfiniteAddGrp
add_to_sga "1 V 5.1" "partial" ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor
add_to_sga "1 V 5.1" "partial" ProfiniteGrp.isIso_toLimit
add_to_sga "1 V 5.1" "partial" ProfiniteGrp.isoLimittoFiniteQuotientFunctor
add_to_sga "1 V 5.3" "special case" CategoryTheory.FintypeCat.Action.isConnected_iff_transitive
add_to_sga "1 V 5.3" "special case" CategoryTheory.FintypeCat.Action.isConnected_of_transitive
add_to_sga "1 V 5.3" "special case" CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected
add_to_sga "1 V 5.3" "Forward implication"
  CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected
add_to_sga "1 V 5.3" "special case"
  CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isGalois
add_to_sga "1 V 5.3" "partial" CategoryTheory.PreGaloisCategory.isPretransitive_of_surjective
add_to_sga "1 V 5.4" "(i) ⇔ (ii), special case"
  CategoryTheory.FintypeCat.Action.isConnected_iff_transitive
add_to_sga "1 V 5.4" "(i)"
  CategoryTheory.PreGaloisCategory.instIsPretransitiveObjFiniteObjFintypeCatOfIsConnected
add_to_sga "1 V 5.4" "(i) ⇒ F(X) ≠ ∅" CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected
add_to_sga "1 V 5.5" "(i) ⇒ (ii)"
  CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPreservesFiniteCoproducts
add_to_sga "1 V 5.5" "partial" MulAction.fixedPoints
add_to_sga "1 V 5.5" "partial" MulActionHom.map_mem_fixedPoints
add_to_sga "1 V 5.10" "partial" CategoryTheory.InducedCategory.groupoid
add_to_sga "1 V 5.10" "partial" CategoryTheory.InducedCategory.isGroupoid
add_to_sga "1 V 5.11" "special case" Action.trivial
add_to_sga "1 V 5.11" "more general" CategoryTheory.Equivalence.mapAction
add_to_sga "1 V 5.11" "Standard case C ≃ C(π)"
  CategoryTheory.PreGaloisCategory.stabilizer_normal_of_isGalois
add_to_sga "1 V 5.11" "special case" MulActionHom.End.equivMulOpposite
add_to_sga "1 V 6.1" CategoryTheory.exactFunctor
add_to_sga "1 V 6.9" CategoryTheory.Functor.FullyFaithful
add_to_sga "1 V 6.9" CategoryTheory.PreGaloisCategory.PreservesIsConnected
add_to_sga "1 V 6.10" CategoryTheory.Functor.EssSurj
add_to_sga "1 V 6.10" CategoryTheory.PreGaloisCategory.PreservesIsConnected
add_to_sga "1 V 6.13" CategoryTheory.toOver
add_to_sga "1 V 6.13" OpenSubgroup
add_to_sga "1 VI 4.5" "special case" CategoryTheory.Equivalence.congrLeft
add_to_sga "1 VI 4.5" "special case" CategoryTheory.Equivalence.congrRight
add_to_sga "1 VI 4.5" "special case" CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft
add_to_sga "1 VI 4.5" "special case" CategoryTheory.Functor.instIsEquivalenceObjWhiskeringRight
add_to_sga "1 VI 5.1" CategoryTheory.Functor.IsCartesian
add_to_sga "1 VI 5.4" "special case" CategoryTheory.Equivalence.congrLeft
add_to_sga "1 VI 5.4" "special case" CategoryTheory.Equivalence.congrRight
add_to_sga "1 VI 5.4" "special case" CategoryTheory.Functor.instIsEquivalenceObjWhiskeringLeft
add_to_sga "1 VI 5.4" "special case" CategoryTheory.Functor.instIsEquivalenceObjWhiskeringRight
add_to_sga "1 VI 6.1" CategoryTheory.Functor.IsFibered
add_to_sga "1 VI 6.1" CategoryTheory.Functor.IsPreFibered
add_to_sga "1 VI 6.11" "Necessity"
  CategoryTheory.Functor.IsFibered.isStronglyCartesian_of_isCartesian
add_to_sga "1 VI 6.11" "Sufficiency" CategoryTheory.Functor.IsFibered.of_exists_isStronglyCartesian
add_to_sga "1 VI 6.12" "Converse" CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
add_to_sga "1 VI 6.12" "partial" CategoryTheory.Functor.IsStronglyCartesian.of_isIso
add_to_sga "1 VI 6.12" "partial" CategoryTheory.Functor.IsStronglyCartesian.of_iso
add_to_sga "1 VI 6.12" "partial" CategoryTheory.Functor.map_isIso
add_to_sga "1 VI 6.13" "more general" CategoryTheory.Functor.IsStronglyCartesian.comp
add_to_sga "1 VI 6.13" "more general" CategoryTheory.Functor.IsStronglyCartesian.of_comp
add_to_sga "1 VI 7.3" "special case" CategoryTheory.Over.instIsEquivalenceMapOfIsIso
add_to_sga "1 VIII 1.2" "special case"
  Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
add_to_sga "1 VIII 1.2" "special case" CommRingCat.isLimitForkPushoutSelfOfFaithfullyFlat
add_to_sga "1 VIII 1.4" "case M = N = A" CommRingCat.isLimitForkPushoutSelfOfFaithfullyFlat
add_to_sga "1 VIII 1.5" "case N = A"
  Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
add_to_sga "1 VIII 1.5" "partial" Module.FaithfullyFlat.one_tmul_eq_zero_iff
add_to_sga "1 VIII 1.5" "partial" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_sga "1 VIII 1.11" "special case" Ideal.FG.of_FG_map_of_faithfullyFlat
add_to_sga "1 VIII 1.11" "descent direction" Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
add_to_sga "1 VIII 2.1" AlgebraicGeometry.IsAffineHom
add_to_sga "1 VIII 2.1" CategoryTheory.Arrow
add_to_sga "1 VIII 3.1" "Surjectivity clause"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeJointlySurjectivePrecoverage
add_to_sga "1 VIII 3.1" "Surjectivity clause" AlgebraicGeometry.Surjective.instSndScheme
add_to_sga "1 VIII 3.3" "special case"
  Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
add_to_sga "1 VIII 3.3" "quasi-compact clause" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_sga "1 VIII 3.3" "special case" RingHom.FiniteType.codescendsAlong_faithfullyFlat
add_to_sga "1 VIII 3.4" "forward implication" Algebra.FiniteType.baseChange
add_to_sga "1 VIII 3.4" "reverse implication"
  Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
add_to_sga "1 VIII 3.4" "reverse implication" RingHom.FiniteType.codescendsAlong_faithfullyFlat
add_to_sga "1 VIII 3.6" AlgHom.FinitePresentation
add_to_sga "1 VIII 3.6" "affine morphisms" AlgHom.FinitePresentation.comp
add_to_sga "1 VIII 3.6" Algebra.FinitePresentation
add_to_sga "1 VIII 3.6" "partial" Algebra.FinitePresentation.baseChange
add_to_sga "1 VIII 3.6" Algebra.FinitePresentation.iff
add_to_sga "1 VIII 3.6" Algebra.FinitePresentation.iff_quotient_mvPolynomial'
add_to_sga "1 VIII 3.6" "partial" Algebra.Presentation.exists_presentation_fin
add_to_sga "1 VIII 3.6" "partial" Algebra.Presentation.finitePresentation_of_isFinite
add_to_sga "1 VIII 3.6" "partial" Algebra.Presentation.instFinitePresentationQuotientOfFinite
add_to_sga "1 VIII 3.6" Algebra.Presentation.ofFinitePresentation
add_to_sga "1 VIII 3.6" "partial" AlgebraicGeometry.IsSeparated.eq_valuativeCriterion
add_to_sga "1 VIII 3.6" "more general" AlgebraicGeometry.IsSeparated.instQuasiSeparated
add_to_sga "1 VIII 3.6" "affine case" AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff
add_to_sga "1 VIII 3.6" RingHom.FinitePresentation
add_to_sga "1 VIII 3.6" "special case" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_sga "1 VIII 3.6" "special case" RingHom.FinitePresentation.comp
add_to_sga "1 VIII 3.6" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_sga "1 VIII 3.6" "special case" RingHom.finitePresentation_stableUnderComposition
add_to_sga "1 VIII 4.2" "special case" AlgebraicGeometry.Flat.isQuotientMap_of_surjective
add_to_sga "1 VIII 4.3" AlgebraicGeometry.Flat.isQuotientMap_of_surjective
add_to_sga "1 VIII 4.4" TopologicalSpace.Closeds
add_to_sga "1 VIII 4.4" TopologicalSpace.Opens
add_to_sga "1 VIII 4.5" "necessity" IsLocallyClosed.preimage
add_to_sga "1 VIII 4.6" "special case"
  AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
add_to_sga "1 VIII 4.6" "special case"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_sga "1 VIII 4.7" "necessity" AlgebraicGeometry.UniversallyOpen.fst
add_to_sga "1 VIII 4.7" "necessity" AlgebraicGeometry.UniversallyOpen.snd
add_to_sga "1 VIII 4.7" "sufficiency"
  AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
add_to_sga "1 VIII 4.7" "sufficiency"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_sga "1 VIII 4.8" "partial" AlgebraicGeometry.IsProper.instFstScheme
add_to_sga "1 VIII 4.8" "partial" AlgebraicGeometry.IsProper.instSndScheme
add_to_sga "1 VIII 4.8" "partial" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_sga "1 VIII 4.9" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "1 VIII 5.1" "a), special case" AlgebraicGeometry.Flat.epi_of_flat_of_surjective
add_to_sga "1 VIII 5.1" "b), special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfLocallyOfFinitePresentationOfSurjectiveOfFlat
add_to_sga "1 VIII 5.1" "b), special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "1 VIII 5.1" "a), special case"
  AlgebraicGeometry.SheafedSpace.epi_of_base_surjective_of_stalk_mono
add_to_sga "1 VIII 5.1" CategoryTheory.EffectiveEpi
add_to_sga "1 VIII 5.1" "more general" CategoryTheory.EffectiveEpiFamily
add_to_sga "1 VIII 5.1" CategoryTheory.EffectiveEpiStruct
add_to_sga "1 VIII 5.2" AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "1 VIII 5.2" "more general" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "1 VIII 5.2" "injectivity of Hom_S(X"
  AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfQuasiCompact
add_to_sga "1 VIII 5.2" "partial" CategoryTheory.Arrow
add_to_sga "1 VIII 5.2" "partial" CategoryTheory.instCategoryArrow
add_to_sga "1 VIII 5.3" "epimorphism clause" AlgebraicGeometry.Flat.epi_of_flat_of_surjective
add_to_sga "1 VIII 5.3" "special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfLocallyOfFinitePresentationOfSurjectiveOfFlat
add_to_sga "1 VIII 5.3" "partial"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "1 VIII 5.3" "partial"
  AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfQuasiCompact
add_to_sga "1 VIII 5.4" "Sufficiency"
  AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
add_to_sga "1 VIII 5.4" "Necessity"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms
add_to_sga "1 VIII 5.5" "open-immersion clause"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_sga "1 VIII 5.5" "open-immersion clause"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left
add_to_sga "1 VIII 5.5" "open-immersion clause"
  AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'
add_to_sga "1 VIII 5.7" "preservation (integral)" AlgebraicGeometry.IsIntegralHom.instFstScheme
add_to_sga "1 VIII 5.7" "preservation (integral)" AlgebraicGeometry.IsIntegralHom.instSndScheme
add_to_sga "1 VIII 5.7" "special case" RingHom.finite_isStableUnderBaseChange
add_to_sga "1 VIII 5.7" "special case" RingHom.isIntegral_isStableUnderBaseChange
add_to_sga "1 VIII 6.1" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_sga "1 VIII 6.1" "more general"
  AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_sga "1 VIII 6.1" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_sga "1 VIII 6.1" "Locally Artinian base" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_sga "1 VIII 6.1" "more general"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_sga "1 VIII 6.6" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_sga "1 VIII 6.6" "more general"
  AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_sga "1 VIII 6.6" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_sga "1 VIII 6.6" "partial"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_sga "1 VIII 7.1" CategoryTheory.EffectiveEquivalenceRelation
add_to_sga "1 VIII 7.1" CategoryTheory.IsEffectiveEquivalenceRelation
add_to_sga "1 VIII 7.6" "partial"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfLocallyOfFinitePresentationOfSurjectiveOfFlat
add_to_sga "1 VIII 7.6" "partial"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "1 X 1.1" AlgebraicGeometry.GeometricallyReduced
add_to_sga "1 XI 1.2" AlgebraicGeometry.Scheme.IsRationalOver
add_to_sga "1 XI 2.1" "partial" AddSubgroup.torsionBy
add_to_sga "1 XI 5.2" "partial" LinearMap.BilinForm.IsAlt
add_to_sga "1 XI 5.2" "special case" LinearMap.BilinForm.toDual
add_to_sga "1 XI 6.3" "special case" IsPrimitiveRoot
add_to_sga "1 XI 6.4" AddSubgroup.torsionBy
add_to_sga "1 XI 6.4" ModN
add_to_sga "1 XI 6.5" "partial" CommRing.Pic.instSubsingletonOfFiniteMaximalSpectrum
add_to_sga "1 XI 6.5" "partial" CommRing.Pic.instSubsingletonOfIsLocalRing
add_to_sga "1 XI 6.5" "partial" instSubsingletonPicOfIsDomainOfIsGCDMonoid
add_to_sga "1 XII 5.2" ProfiniteAddGrp.ProfiniteCompletion.etaFn
add_to_sga "1 XII 5.2" ProfiniteGrp.ProfiniteCompletion.etaFn
add_to_sga "1 XII 5.6" Group.ResiduallyFinite
add_to_sga "1 XII 5.6" "partial" Group.residuallyFinite_iff_exists_finiteIndex
add_to_sga "1 XII 5.6" "partial" Group.residuallyFinite_iff_forall_finiteIndex
add_to_sga "1 XII 5.6" "partial"
  ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
add_to_sga "1 XII 5.6" "partial" ProfiniteGrp.ProfiniteCompletion.mono_eta_iff_residuallyFinite
add_to_sga "1 XIII 1.5" AlgebraicGeometry.QuasiSeparated
add_to_sga "1 XIII 2.0" "more general" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "1 XIII 2.0" "partial" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "1 XIII 2.0" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "1 XIII 2.1.3" "special case" CommAlgCat.FiniteEtale.fiber
add_to_sga "1 XIII 2.4.2" MulAction.fixedPoints
add_to_sga "1 XIII 5.3.0" autAdjoinRootXPowSubC
add_to_sga "1 XIII 5.3.0" "special case" autAdjoinRootXPowSubCEquiv
add_to_sga "1 XIII 5.3.0" "special case" autAdjoinRootXPowSubCEquiv_root
add_to_sga "1 XIII 5.3.0" "special case" autAdjoinRootXPowSubCEquiv_symm_smul
add_to_sga "1 XIII 5.3.0" "special case" autAdjoinRootXPowSubC_root
add_to_sga "1 XIII 5.3.0" "special case" autEquivRootsOfUnity
add_to_sga "1 XIII 5.3.0" "special case" autEquivRootsOfUnity_apply_rootOfSplit
add_to_sga "1 XIII 5.3.0" "special case" autEquivRootsOfUnity_smul
add_to_sga "1 XIII 5.3.0" rootsOfUnity
add_to_sga "1 XIII 6.1" CategoryTheory.Limits.pullback
