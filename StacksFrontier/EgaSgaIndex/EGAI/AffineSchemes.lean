module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Submonoid.Saturation
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalClosure
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.OverClass
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.JointlySurjective
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Prod
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.MonoidLocalization.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Irreducible
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import StacksCore.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA I references registered by name: Chapter 1

The part of `StacksFrontier.EgaSgaIndex.EGAI` covering EGA I, Chapter 1 (affine schemes).

Declarations realizing numbered items of EGA I, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "I 1.1.1" AlgebraicGeometry.PrimeSpectrum.Top
add_to_ega "I 1.1.1" AlgebraicGeometry.Spec.toTop_obj_carrier
add_to_ega "I 1.1.1" AlgebraicGeometry.Spec.topObj_forget
add_to_ega "I 1.1.1" AlgebraicGeometry.Spec_carrier
add_to_ega "I 1.1.1" AlgebraicGeometry.StructureSheaf.Localizations
add_to_ega "I 1.1.1" "partial"
  AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialCarrier
add_to_ega "I 1.1.1" "partial" AlgebraicGeometry.spec_punit_isEmpty
add_to_ega "I 1.1.1" "f(x)=0 iff f ∈ j_x" Ideal.Quotient.eq_zero_iff_mem
add_to_ega "I 1.1.1" Ideal.Quotient.mk
add_to_ega "I 1.1.1" Ideal.ResidueField
add_to_ega "I 1.1.1" "partial" Ideal.algebraMap_quotient_residueField_mk
add_to_ega "I 1.1.1" Ideal.radical
add_to_ega "I 1.1.1" "more general" Ideal.radical_eq_sInf
add_to_ega "I 1.1.1" IsLocalRing.ResidueField
add_to_ega "I 1.1.1" "k(x) is a field" IsLocalRing.ResidueField.field
add_to_ega "I 1.1.1" IsLocalRing.maximalIdeal
add_to_ega "I 1.1.1" "maximality of m_x" IsLocalRing.maximalIdeal.isMaximal
add_to_ega "I 1.1.1" IsLocalization.AtPrime
add_to_ega "I 1.1.1" "A_x is a local ring" IsLocalization.AtPrime.isLocalRing
add_to_ega "I 1.1.1" Localization.AtPrime
add_to_ega "I 1.1.1" "A_x is a local ring" Localization.AtPrime.isLocalRing
add_to_ega "I 1.1.1" "more general" LocalizedModule
add_to_ega "I 1.1.1" LocalizedModule.AtPrime
add_to_ega "I 1.1.1" PrimeSpectrum
add_to_ega "I 1.1.1" PrimeSpectrum.asIdeal
add_to_ega "I 1.1.1" PrimeSpectrum.basicOpen
add_to_ega "I 1.1.1" "more general" PrimeSpectrum.basicOpen_eq_zeroLocus_compl
add_to_ega "I 1.1.1" "more general" PrimeSpectrum.iUnion_basicOpen_eq_compl_zeroLocus
add_to_ega "I 1.1.1" PrimeSpectrum.instCoeIdeal
add_to_ega "I 1.1.1" "partial" PrimeSpectrum.instIsEmptyOfSubsingleton
add_to_ega "I 1.1.1" "partial" PrimeSpectrum.instNonemptyOfNontrivial
add_to_ega "I 1.1.1" "more general" PrimeSpectrum.isEmpty_iff_subsingleton
add_to_ega "I 1.1.1" PrimeSpectrum.mk
add_to_ega "I 1.1.1" "more general" PrimeSpectrum.nonempty_iff_nontrivial
add_to_ega "I 1.1.1" "special case" PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical
add_to_ega "I 1.1.1" PrimeSpectrum.zeroLocus
add_to_ega "I 1.1.1" "special case" PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
add_to_ega "I 1.1.1" "special case" PrimeSpectrum.zeroLocus_subset_zeroLocus_singleton_iff
add_to_ega "I 1.1.1" "partial" instIsFractionRingQuotientIdealResidueField
add_to_ega "I 1.1.2" "(iii): V(⋃E_λ)=⋂V(E_λ)" AlgebraicGeometry.Scheme.zeroLocus_iUnion
add_to_ega "I 1.1.2" "more general" AlgebraicGeometry.Scheme.zeroLocus_mono
add_to_ega "I 1.1.2" "(iv), special case" AlgebraicGeometry.Scheme.zeroLocus_mul
add_to_ega "I 1.1.2" "(v) for ideals" AlgebraicGeometry.Scheme.zeroLocus_radical
add_to_ega "I 1.1.2" "more general" AlgebraicGeometry.Scheme.zeroLocus_setMul
add_to_ega "I 1.1.2" "(iii): V(⋃E_λ)=V(ΣE_λ)" AlgebraicGeometry.Scheme.zeroLocus_span
add_to_ega "I 1.1.2" "more general" PrimeSpectrum.zeroLocus_anti_mono
add_to_ega "I 1.1.2" "(ii) for ideals" PrimeSpectrum.zeroLocus_anti_mono_ideal
add_to_ega "I 1.1.2" "(iii): V(⋃E_λ)=⋂V(E_λ)" PrimeSpectrum.zeroLocus_bUnion
add_to_ega "I 1.1.2" "(i), first half: V(0)=X" PrimeSpectrum.zeroLocus_bot
add_to_ega "I 1.1.2" "(i), second half: V(1)=∅" PrimeSpectrum.zeroLocus_empty_of_one_mem
add_to_ega "I 1.1.2" "(iii), special case" PrimeSpectrum.zeroLocus_iSup
add_to_ega "I 1.1.2" "(iii): V(⋃E_λ)=⋂V(E_λ)" PrimeSpectrum.zeroLocus_iUnion
add_to_ega "I 1.1.2" "(iii): V(⋃E_λ)=⋂V(E_λ)" PrimeSpectrum.zeroLocus_iUnion₂
add_to_ega "I 1.1.2" "(iv), special case" PrimeSpectrum.zeroLocus_mul
add_to_ega "I 1.1.2" "(v) for ideals" PrimeSpectrum.zeroLocus_radical
add_to_ega "I 1.1.2" "(iv) for E={f}, E'={g}" PrimeSpectrum.zeroLocus_singleton_mul
add_to_ega "I 1.1.2" "(i), second half: V(1)=∅" PrimeSpectrum.zeroLocus_singleton_one
add_to_ega "I 1.1.2" "(i), first half: V(0)=X" PrimeSpectrum.zeroLocus_singleton_zero
add_to_ega "I 1.1.2" "(ii) for ideals" PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
add_to_ega "I 1.1.2" "(iii), special case" PrimeSpectrum.zeroLocus_union
add_to_ega "I 1.1.3" "partial" PrimeSpectrum.coe_vanishingIdeal
add_to_ega "I 1.1.3" "partial" PrimeSpectrum.mem_vanishingIdeal
add_to_ega "I 1.1.3" PrimeSpectrum.vanishingIdeal
add_to_ega "I 1.1.3" "more general" PrimeSpectrum.vanishingIdeal_anti_mono
add_to_ega "I 1.1.3" "more general" PrimeSpectrum.vanishingIdeal_iUnion
add_to_ega "I 1.1.3" "more general" PrimeSpectrum.vanishingIdeal_singleton
add_to_ega "I 1.1.3" "special case" PrimeSpectrum.vanishingIdeal_union
add_to_ega "I 1.1.4" "(i), special case" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top
add_to_ega "I 1.1.4" "more general" PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical
add_to_ega "I 1.1.4" "more general" PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
add_to_ega "I 1.1.5" "more general" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_iSup
add_to_ega "I 1.1.5" "more general" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_sSup
add_to_ega "I 1.1.5" "more general" AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_sup
add_to_ega "I 1.1.5" Ideal.IsRadical
add_to_ega "I 1.1.5" Ideal.radical
add_to_ega "I 1.1.5" "partial" Ideal.radical_eq_sInf
add_to_ega "I 1.1.5" "partial" PrimeSpectrum.closedsEmbedding
add_to_ega "I 1.1.5" "V and j are decreasing" PrimeSpectrum.gc
add_to_ega "I 1.1.5" "V and j are decreasing" PrimeSpectrum.gc_set
add_to_ega "I 1.1.5" "partial" PrimeSpectrum.isClosed_iff_zeroLocus_ideal
add_to_ega "I 1.1.5" "j(Y) is a radical ideal" PrimeSpectrum.isRadical_vanishingIdeal
add_to_ega "I 1.1.5" "more general" PrimeSpectrum.union_zeroLocus
add_to_ega "I 1.1.5" PrimeSpectrum.vanishingIdeal
add_to_ega "I 1.1.5" "more general" PrimeSpectrum.vanishingIdeal_iUnion
add_to_ega "I 1.1.5" "more general" PrimeSpectrum.vanishingIdeal_union
add_to_ega "I 1.1.5" "partial" PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical
add_to_ega "I 1.1.5" PrimeSpectrum.zeroLocus
add_to_ega "I 1.1.5" "more general" PrimeSpectrum.zeroLocus_inf
add_to_ega "I 1.1.5" "V(j(Y)) = Y for closed Y" PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
add_to_ega "I 1.1.6"
  AlgebraicGeometry.instNoetherianSpaceCarrierCarrierCommRingCatSpecOfIsNoetherianRingCarrier
add_to_ega "I 1.1.6" AlgebraicGeometry.noetherianSpace_of_isAffine
add_to_ega "I 1.1.6" "more general" AlgebraicGeometry.noetherianSpace_of_isAffineOpen
add_to_ega "I 1.1.7" "closed ⇒ maximal"
  AlgebraicGeometry.IsAffineOpen.primeIdealOf_isMaximal_of_isClosed
add_to_ega "I 1.1.7" "special case" IsLocalRing.isClosed_singleton_closedPoint
add_to_ega "I 1.1.7" MaximalSpectrum.toPrimeSpectrum_range
add_to_ega "I 1.1.7" "more general" PrimeSpectrum.closure_singleton
add_to_ega "I 1.1.7" "more general" PrimeSpectrum.isClosed_singleton_iff_isMaximal
add_to_ega "I 1.1.7" "more general" PrimeSpectrum.le_iff_mem_closure
add_to_ega "I 1.1.7" "more general" PrimeSpectrum.stableUnderSpecialization_singleton
add_to_ega "I 1.1.7" "maximal ⇒ closed" PrimeSpectrum.zeroLocus_eq_singleton
add_to_ega "I 1.1.7" "more general" PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
add_to_ega "I 1.1.8" "more general" AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat
add_to_ega "I 1.1.8" "more general" PrimeSpectrum.instSpectralSpace
add_to_ega "I 1.1.8" "more general" PrimeSpectrum.instT0Space
add_to_ega "I 1.1.9" "more general" AlgebraicGeometry.RingedSpace.basicOpen_mul
add_to_ega "I 1.1.9" "more general" AlgebraicGeometry.Scheme.basicOpen_mul
add_to_ega "I 1.1.9" "(f)" Ideal.radical_minimalPrimes
add_to_ega "I 1.1.9" "(f)" Ideal.sInf_minimalPrimes
add_to_ega "I 1.1.9" "more general" PrimeSpectrum.basicOpen_mul
add_to_ega "I 1.1.9" "partial" PrimeSpectrum.zeroLocus_eq_iff
add_to_ega "I 1.1.10" AlgebraicGeometry.isBasis_basicOpen
add_to_ega "I 1.1.10" "more general" AlgebraicGeometry.isCompact_iff_exists
add_to_ega "I 1.1.10" "more general" PrimeSpectrum.compactSpace
add_to_ega "I 1.1.10" "more general" PrimeSpectrum.instSpectralSpace
add_to_ega "I 1.1.10" "more general" PrimeSpectrum.isBasis_basic_opens
add_to_ega "I 1.1.10" "more general" PrimeSpectrum.isCompact_basicOpen
add_to_ega "I 1.1.10" "more general" PrimeSpectrum.isTopologicalBasis_basic_opens
add_to_ega "I 1.1.11" "partial" AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
add_to_ega "I 1.1.11" "partial" Ideal.primeSpectrumQuotientOrderIsoZeroLocus
add_to_ega "I 1.1.12" "partial" PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
add_to_ega "I 1.1.13" "special case"
  AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsDomainCarrier
add_to_ega "I 1.1.13" "special case" PrimeSpectrum.irreducibleSpace
add_to_ega "I 1.1.13" "more general" PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical
add_to_ega "I 1.1.13" "more general" PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime
add_to_ega "I 1.1.13" "more general" PrimeSpectrum.isIrreducible_zeroLocus_iff
add_to_ega "I 1.1.13" "more general" PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical
add_to_ega "I 1.1.14" "more general" Ideal.minimalPrimes.equivIrreducibleComponents
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.isIrreducible_zeroLocus_iff
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical
add_to_ega "I 1.1.14" PrimeSpectrum.pointsEquivIrreducibleCloseds
add_to_ega "I 1.1.14" PrimeSpectrum.vanishingIdeal_irreducibleComponents
add_to_ega "I 1.1.14" PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.vanishingIdeal_isIrreducible
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.vanishingIdeal_mem_minimalPrimes
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.zeroLocusEquivIrreducibleCloseds
add_to_ega "I 1.1.14" "more general" PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents
add_to_ega "I 1.1.14" PrimeSpectrum.zeroLocus_minimalPrimes
add_to_ega "I 1.1.14" minimalPrimes.equivIrreducibleComponents
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality_apply
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality_assoc
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality
add_to_ega "I 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality_apply
add_to_ega "I 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_naturality_assoc
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.Scheme.evaluation_naturality
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.Scheme.evaluation_naturality_apply
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.Scheme.evaluation_naturality_assoc
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.Scheme.Γevaluation_naturality
add_to_ega "I 1.2.1" "more general" AlgebraicGeometry.Scheme.Γevaluation_naturality_assoc
add_to_ega "I 1.2.1" AlgebraicGeometry.Spec.coe_toTop_map_hom_apply_asIdeal
add_to_ega "I 1.2.1" AlgebraicGeometry.Spec.map_apply
add_to_ega "I 1.2.1" AlgebraicGeometry.Spec.map_base
add_to_ega "I 1.2.1" AlgebraicGeometry.Spec.topMap
add_to_ega "I 1.2.1" "more general" Ideal.IsPrime.comap
add_to_ega "I 1.2.1" "more general" Ideal.IsPrime.under
add_to_ega "I 1.2.1" Ideal.ResidueField.map
add_to_ega "I 1.2.1" "more general" Ideal.comap_isPrime
add_to_ega "I 1.2.1" "more general" Ideal.isPrime_of_liesOver
add_to_ega "I 1.2.1" "more general" Ideal.quotientMap_injective
add_to_ega "I 1.2.1" "more general" Ideal.quotientMap_injective'
add_to_ega "I 1.2.1" PrimeSpectrum.comap
add_to_ega "I 1.2.1" "more general" PrimeSpectrum.comap_asIdeal
add_to_ega "I 1.2.1" "partial" RingHom.kerLift_injective
add_to_ega "I 1.2.1" "more general" RingHom.ker_isPrime
add_to_ega "I 1.2.2" "more general" AlgebraicGeometry.Scheme.Hom.preimage_basicOpen
add_to_ega "I 1.2.2" "more general" AlgebraicGeometry.Scheme.preimage_basicOpen
add_to_ega "I 1.2.2" AlgebraicGeometry.SpecMap_preimage_basicOpen
add_to_ega "I 1.2.2" "more general" PrimeSpectrum.BasicConstructibleSetData.toSet_map
add_to_ega "I 1.2.2" "more general" PrimeSpectrum.ConstructibleSetData.toSet_map
add_to_ega "I 1.2.2" PrimeSpectrum.closure_image_comap_zeroLocus
add_to_ega "I 1.2.2" "more general" PrimeSpectrum.comap_basicOpen
add_to_ega "I 1.2.2" "more general" PrimeSpectrum.preimage_comap_zeroLocus
add_to_ega "I 1.2.2" "more general" PrimeSpectrum.preimage_comap_zeroLocus_aux
add_to_ega "I 1.2.3" AlgebraicGeometry.Spec.topMap
add_to_ega "I 1.2.3" "more general" PrimeSpectrum.continuous_comap
add_to_ega "I 1.2.4" "more general" AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
add_to_ega "I 1.2.4" "partial" PrimeSpectrum.comap_isInducing_of_surjective
add_to_ega "I 1.2.4" "more general" PrimeSpectrum.isClosedEmbedding_comap_of_surjective
add_to_ega "I 1.2.4" "more general" PrimeSpectrum.isEmbedding_comap_of_surjective
add_to_ega "I 1.2.5" "partial" AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
add_to_ega "I 1.2.5" "partial" Ideal.primeSpectrumQuotientOrderIsoZeroLocus
add_to_ega "I 1.2.6" "special case" IsLocalization.AtPrime.primeSpectrumOrderIso
add_to_ega "I 1.2.6" "partial" IsLocalization.primeSpectrumOrderIso
add_to_ega "I 1.2.6" "partial" PrimeSpectrum.localization_comap_injective
add_to_ega "I 1.2.6" "partial" PrimeSpectrum.localization_comap_range
add_to_ega "I 1.2.7" "more general" PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
add_to_ega "I 1.3.1" "more general" IsLocalization
add_to_ega "I 1.3.1" IsLocalization.Away
add_to_ega "I 1.3.1" "more general" IsLocalizedModule
add_to_ega "I 1.3.1" IsLocalizedModule.Away
add_to_ega "I 1.3.1" Localization.Away
add_to_ega "I 1.3.1" "more general" LocalizedModule
add_to_ega "I 1.3.1" LocalizedModule.Away
add_to_ega "I 1.3.1" "more general" Submonoid.mem_saturation_iff
add_to_ega "I 1.3.1" "more general" Submonoid.mem_saturation_iff'
add_to_ega "I 1.3.1" "more general" Submonoid.mem_saturation_iff_exists_dvd
add_to_ega "I 1.3.1" Submonoid.powers
add_to_ega "I 1.3.1" Submonoid.saturation
add_to_ega "I 1.3.2" "(c) ⇔ (f)" PrimeSpectrum.basicOpen_le_basicOpen_iff
add_to_ega "I 1.3.2" "more general" PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
add_to_ega "I 1.3.2" "(c) ⇔ (e)" PrimeSpectrum.zeroLocus_subset_zeroLocus_singleton_iff
add_to_ega "I 1.3.3" "special case" IsLocalization.map_comp_map
add_to_ega "I 1.3.3" "special case" IsLocalization.map_map
add_to_ega "I 1.3.3" "special case" Submonoid.LocalizationMap.map_comp_map
add_to_ega "I 1.3.3" "special case" Submonoid.LocalizationMap.map_map
add_to_ega "I 1.3.4" AlgebraicGeometry.Spec.structureSheaf
add_to_ega "I 1.3.4" AlgebraicGeometry.structurePresheafInCommRingCat
add_to_ega "I 1.3.4" "partial" AlgebraicGeometry.structureSheafInType
add_to_ega "I 1.3.4" AlgebraicGeometry.tilde
add_to_ega "I 1.3.5" "partial" AlgebraicGeometry.tilde
add_to_ega "I 1.3.5" "partial" AlgebraicGeometry.tilde.map
add_to_ega "I 1.3.5" "partial" AlgebraicGeometry.tilde.map_comp
add_to_ega "I 1.3.5" "partial" AlgebraicGeometry.tilde.map_id
add_to_ega "I 1.3.6" "partial" AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway
add_to_ega "I 1.3.6" "partial" AlgebraicGeometry.Scheme.instIsOpenImmersionMapOfHomAwayAlgebraMap
add_to_ega "I 1.3.6" "partial" AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
add_to_ega "I 1.3.6" AlgebraicGeometry.basicOpenIsoSpecAway
add_to_ega "I 1.3.6" "partial" AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap
add_to_ega "I 1.3.6" "partial" PrimeSpectrum.localization_away_isOpenEmbedding
-- The auto-generated instance names below are longer than a line, so each identifier is
-- assembled from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsAffineOpen <|
      "instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCat" ++
      "SpecPresheafOpOpensBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.3.7" "Case M = A" $decl:ident))
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf <|
      "instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheaf" ++
      "GrothendieckTopologyStructureSheafInTypeOpBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.3.7" "Case M = A" $decl:ident))
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf <|
      "instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheaf" ++
      "GrothendieckTopologyStructureSheafInTypeOpBasicOpenToOpenₗ"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.3.7" $decl:ident))
add_to_ega "I 1.3.7" AlgebraicGeometry.StructureSheaf.toOpenₗ_top_bijective
add_to_ega "I 1.3.7" "Case M = A" AlgebraicGeometry.isIso_toSpecΓ
add_to_ega "I 1.3.7" AlgebraicGeometry.tilde.isIso_toOpen_top
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry <|
      "instCommRingObjOppositeOpensCarrierTopObjFunctorTypeIsSheaf" ++
      "GrothendieckTopologyStructureSheafInType"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.3.13" "partial" $decl:ident))
add_to_ega "I 1.3.13" CategoryTheory.ModObj.mk
add_to_ega "I 1.3.13" CategoryTheory.Mod_
add_to_ega "I 1.3.13" CommAlgCat
add_to_ega "I 1.3.13" Module
add_to_ega "I 1.3.14" "partial" Algebra.adjoin_toSubmodule_le
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsAffineOpen <|
      "instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCat" ++
      "SpecPresheafOpOpensBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.4.1" "special case" $decl:ident))
add_to_ega "I 1.4.1" "c ⇒ a for V = Spec A"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf <|
      "instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheaf" ++
      "GrothendieckTopologyStructureSheafInTypeOpBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.4.1" "special case" $decl:ident))
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen
add_to_ega "I 1.4.1" "special case"
  AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.exists_of_res_eq_of_qcqs
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.exists_of_res_eq_of_qcqs_of_top
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs
add_to_ega "I 1.4.1" "special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs_of_top
add_to_ega "I 1.4.1" "special case"
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
add_to_ega "I 1.4.1" "special case"
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
add_to_ega "I 1.4.1" "c ⇔ canonical form of a"
  AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "I 1.4.1.1" "special case"
  AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
add_to_ega "I 1.4.1.1" "special case" AlgebraicGeometry.exists_of_res_eq_of_qcqs
add_to_ega "I 1.4.1.1" "special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs
add_to_ega "I 1.4.1.1" "special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs_of_top
add_to_ega "I 1.4.1.1" "special case"
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
add_to_ega "I 1.4.3" "special case"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
add_to_ega "I 1.4.3" "special case" AlgebraicGeometry.essImage_tilde
add_to_ega "I 1.4.3" "special case" AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "I 1.4.3" "special case" AlgebraicGeometry.tildeEquiv
add_to_ega "I 1.6.1" "more general" AlgebraicGeometry.IsAffineOpen.arrowStalkMapIso
add_to_ega "I 1.6.1" "more general" AlgebraicGeometry.Scheme.Hom.preimage_basicOpen
add_to_ega "I 1.6.1" AlgebraicGeometry.Scheme.arrowStalkMapSpecIso
add_to_ega "I 1.6.1" AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso
add_to_ega "I 1.6.1" AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso_apply
add_to_ega "I 1.6.1" AlgebraicGeometry.Spec.locallyRingedSpaceMap
add_to_ega "I 1.6.1" AlgebraicGeometry.Spec.map
add_to_ega "I 1.6.1" "partial" AlgebraicGeometry.Spec.map_app
add_to_ega "I 1.6.1" "partial" AlgebraicGeometry.Spec.map_appLE
add_to_ega "I 1.6.1" AlgebraicGeometry.Spec.sheafedSpaceMap
add_to_ega "I 1.6.1" "more general" AlgebraicGeometry.Spec.toSheafedSpace
add_to_ega "I 1.6.1" AlgebraicGeometry.SpecMap_preimage_basicOpen
add_to_ega "I 1.6.1" "partial" AlgebraicGeometry.StructureSheaf.comap
add_to_ega "I 1.6.1" "partial" AlgebraicGeometry.StructureSheaf.comap_basicOpen
add_to_ega "I 1.6.1" AlgebraicGeometry.localRingHom_comp_stalkIso
add_to_ega "I 1.6.1" AlgebraicGeometry.localRingHom_comp_stalkIso_apply
add_to_ega "I 1.6.1" "more general" PrimeSpectrum.BasicConstructibleSetData.toSet_map
add_to_ega "I 1.6.1" "more general" PrimeSpectrum.comap_basicOpen
add_to_ega "I 1.6.2" "special case" AlgebraicGeometry.Scheme.Hom.opensRange_localizationAway
add_to_ega "I 1.6.2" "special case"
  AlgebraicGeometry.Scheme.instIsOpenImmersionMapOfHomAwayAlgebraMap
add_to_ega "I 1.6.2" "special case"
  AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
add_to_ega "I 1.6.2" "special case" AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap
add_to_ega "I 1.6.2" AlgebraicGeometry.isIso_SpecMap_stakMap_localization
add_to_ega "I 1.6.2" "partial" IsLocalization.AtPrime.primeSpectrumOrderIso
add_to_ega "I 1.6.2" "partial" IsLocalization.coe_primeSpectrumOrderIso_apply_coe_asIdeal
add_to_ega "I 1.6.2" "special case" PrimeSpectrum.localization_away_isOpenEmbedding
add_to_ega "I 1.6.2" "partial" PrimeSpectrum.localization_comap_isInducing
add_to_ega "I 1.6.2" "partial" PrimeSpectrum.localization_comap_range
add_to_ega "I 1.6.2" "partial" RingHom.surjectiveOnStalks_of_isLocalization
add_to_ega "I 1.6.10" AlgebraicGeometry.AffineScheme.Spec
add_to_ega "I 1.6.10" AlgebraicGeometry.Scheme.Spec
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.locallyRingedSpaceMap
add_to_ega "I 1.6.10" AlgebraicGeometry.Spec.locallyRingedSpaceMap_comp
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.map
add_to_ega "I 1.6.10" AlgebraicGeometry.Spec.map_comp
add_to_ega "I 1.6.10" "more general" AlgebraicGeometry.Spec.map_comp_assoc
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.sheafedSpaceMap
add_to_ega "I 1.6.10" AlgebraicGeometry.Spec.sheafedSpaceMap_comp
add_to_ega "I 1.6.10" AlgebraicGeometry.Spec.toLocallyRingedSpace
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.toPresheafedSpace
add_to_ega "I 1.6.10" AlgebraicGeometry.Spec.toSheafedSpace
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.toTop
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.Spec.topMap_comp
add_to_ega "I 1.6.10" "partial" AlgebraicGeometry.StructureSheaf.comap_comp
add_to_ega "I 1.6.10" "partial" PrimeSpectrum.comap_comp
add_to_ega "I 1.7.1" AlgebraicGeometry.AffineScheme
add_to_ega "I 1.7.1" AlgebraicGeometry.AffineScheme.Γ
add_to_ega "I 1.7.1" AlgebraicGeometry.Scheme.ΓSpecIso
add_to_ega "I 1.7.1" AlgebraicGeometry.Spec
add_to_ega "I 1.7.2" AlgebraicGeometry.AffineScheme.Spec
add_to_ega "I 1.7.2" AlgebraicGeometry.LocallyRingedSpace.SpecΓIdentity
add_to_ega "I 1.7.2" AlgebraicGeometry.Scheme.ΓSpecIso_naturality
add_to_ega "I 1.7.2" "partial" AlgebraicGeometry.Spec.fullyFaithfulToLocallyRingedSpace
add_to_ega "I 1.7.2" AlgebraicGeometry.Spec.locallyRingedSpaceMap
add_to_ega "I 1.7.2" AlgebraicGeometry.Spec.map
add_to_ega "I 1.7.2" "partial" AlgebraicGeometry.Spec.map_app
add_to_ega "I 1.7.2" "partial" AlgebraicGeometry.Spec.preimage_map
add_to_ega "I 1.7.2" AlgebraicGeometry.Spec.sheafedSpaceMap
add_to_ega "I 1.7.2" AlgebraicGeometry.arrowIsoΓSpecOfIsAffine
add_to_ega "I 1.7.2" "partial" PrimeSpectrum.comap
add_to_ega "I 1.7.4" "more general" AlgebraicGeometry.AffineScheme.equivCommRingCat
add_to_ega "I 1.7.4" "more general"
  AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatRightOpΓ
add_to_ega "I 1.7.4" "special case" AlgebraicGeometry.Spec.homEquiv
add_to_ega "I 1.8.1" "special case" AlgebraicGeometry.Spec.fullyFaithfulToLocallyRingedSpace
add_to_ega "I 1.8.2" "special case" AlgebraicGeometry.AffineScheme.Γ
add_to_ega "I 1.8.2" AlgebraicGeometry.LocallyRingedSpace
add_to_ega "I 1.8.2" AlgebraicGeometry.LocallyRingedSpace.Hom
add_to_ega "I 1.8.2" AlgebraicGeometry.LocallyRingedSpace.Hom.mk
add_to_ega "I 1.8.2" "composition" AlgebraicGeometry.LocallyRingedSpace.comp
add_to_ega "I 1.8.2" AlgebraicGeometry.LocallyRingedSpace.homMk
add_to_ega "I 1.8.2" "partial" AlgebraicGeometry.LocallyRingedSpace.id
add_to_ega "I 1.8.2" AlgebraicGeometry.LocallyRingedSpace.instCategory
add_to_ega "I 1.8.2" "Hom(X" AlgebraicGeometry.LocallyRingedSpace.instQuiver
add_to_ega "I 1.8.2" "partial" AlgebraicGeometry.LocallyRingedSpace.Γ
add_to_ega "I 1.8.2" "partial" AlgebraicGeometry.LocallyRingedSpace.Γ_map
add_to_ega "I 1.8.2" "special case" AlgebraicGeometry.Scheme.Hom.appTop
add_to_ega "I 1.8.3" "Necessity direction" AlgebraicGeometry.ext_of_isAffine
add_to_ega "I 1.8.8" "special case" AlgebraicGeometry.Spec.fullyFaithfulToLocallyRingedSpace
add_to_ega "I 1.8.8" "partial" AlgebraicGeometry.ext_of_isAffine
add_to_ega "I 1.8.9" "partial" AlgebraicGeometry.AffineScheme.Γ
add_to_ega "I 1.8.9" "ring component ρ'(u)" AlgebraicGeometry.Scheme.Hom.app
add_to_ega "I 1.8.9" "ring component ρ'(u)" AlgebraicGeometry.Scheme.Hom.appLE
add_to_ega "I 1.8.9" "ring component ρ'(u)" AlgebraicGeometry.Scheme.Hom.appTop
add_to_ega "I 1.8.9" "partial" AlgebraicGeometry.Scheme.Modules.Hom.app
