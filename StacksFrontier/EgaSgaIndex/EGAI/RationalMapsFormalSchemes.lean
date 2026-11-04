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
# EGA I references registered by name: Chapters 7 to 10

The part of `StacksFrontier.EgaSgaIndex.EGAI` covering EGA I, Chapters 7 to 10 (rational maps;
Chevalley schemes; complements on quasi-coherent sheaves; formal schemes).

Declarations realizing numbered items of EGA I, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "I 7.1.1" AlgebraicGeometry.Scheme.PartialMap.equiv
add_to_ega "I 7.1.1" AlgebraicGeometry.Scheme.PartialMap.instSetoid
add_to_ega "I 7.1.1" "partial" Dense.inter_of_isOpen_left
add_to_ega "I 7.1.1" "partial" Dense.inter_of_isOpen_right
add_to_ega "I 7.1.1" "partial" IsOpen.inter
add_to_ega "I 7.1.1" "density clause" Set.Finite.dense_sInter
add_to_ega "I 7.1.1" "openness clause" Set.Finite.isOpen_sInter
add_to_ega "I 7.1.1" "partial" isOpen_iInter_of_finite
add_to_ega "I 7.1.2" "canonical map Hom(X" AlgebraicGeometry.Scheme.Hom.toRationalMap
add_to_ega "I 7.1.2" AlgebraicGeometry.Scheme.PartialMap.equiv
add_to_ega "I 7.1.2" AlgebraicGeometry.Scheme.PartialMap.instSetoid
add_to_ega "I 7.1.2" AlgebraicGeometry.Scheme.PartialMap.toRationalMap
add_to_ega "I 7.1.2" AlgebraicGeometry.Scheme.RationalMap
add_to_ega "I 7.1.2" AlgebraicGeometry.Scheme.RationalMap.IsOver
add_to_ega "I 7.1.2" "partial" AlgebraicGeometry.Scheme.instIsOverToRationalMapOfIsOver
add_to_ega "I 7.1.4" "partial" IsGenericPoint.mem_open_set_iff
add_to_ega "I 7.1.4" "partial" IsOpen.dense
add_to_ega "I 7.1.4" "partial" preirreducibleSpace_iff_open_dense
add_to_ega "I 7.1.5" AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "I 7.1.5" "more general" AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
add_to_ega "I 7.1.5" AlgebraicGeometry.instFieldCarrierFunctionField
add_to_ega "I 7.1.5" "more general"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "I 7.1.6" AlgebraicGeometry.Scheme.irreducibleComponentOpen
add_to_ega "I 7.1.6" "Noetherian preschemes"
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "I 7.1.6" "more general" AlgebraicGeometry.nonempty_isColimit_cofanMk_of
add_to_ega "I 7.1.6" "more general" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "I 7.1.6" "partial" closure_sUnion_irreducibleComponents_sdiff_singleton
add_to_ega "I 7.1.9" "special case" AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "I 7.1.9" "Integral-domain case"
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
add_to_ega "I 7.1.10" AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem
add_to_ega "I 7.1.10" "partial" AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_ι
add_to_ega "I 7.1.10" AlgebraicGeometry.Scheme.RationalMap.fromFunctionField
add_to_ega "I 7.1.10" "partial" IsGenericPoint.mem_open_set_iff
add_to_ega "I 7.1.11" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.11" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.11" "Second clause"
  AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_ofFunctionField
add_to_ega "I 7.1.12" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.12" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.13" "partial" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.13" "partial" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.14" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.14" "special case" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.15" "more general" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.15" "more general" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.16" "Injectivity" AlgebraicGeometry.Scheme.RationalMap.eq_of_fromFunctionField_eq
add_to_ega "I 7.1.16" "more general" AlgebraicGeometry.Scheme.RationalMap.equivFunctionField
add_to_ega "I 7.1.16" "more general" AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver
add_to_ega "I 7.1.16" "Surjectivity"
  AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_ofFunctionField
add_to_ega "I 7.2.1" AlgebraicGeometry.Scheme.RationalMap.dense_domain
add_to_ega "I 7.2.1" AlgebraicGeometry.Scheme.RationalMap.domain
add_to_ega "I 7.2.1" AlgebraicGeometry.Scheme.RationalMap.mem_domain
add_to_ega "I 7.2.2" "Uniqueness"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated
add_to_ega "I 7.2.2" "Uniqueness clause"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated
add_to_ega "I 7.2.2" "Uniqueness clause"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_ega "I 7.2.2" AlgebraicGeometry.Scheme.RationalMap.toPartialMap
add_to_ega "I 7.2.2" "Existence" AlgebraicGeometry.Scheme.RationalMap.toRationalMap_toPartialMap
add_to_ega "I 7.2.2.1" AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated
add_to_ega "I 7.2.2.1" "more general"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_ega "I 7.2.2.1" "special case" AlgebraicGeometry.ext_of_apply_eq
add_to_ega "I 7.2.2.1" "more general" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_ega "I 7.2.3" "Injectivity"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_ega "I 7.2.4" AlgebraicGeometry.Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver
add_to_ega "I 7.2.5" "special case"
  AlgebraicGeometry.Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated
add_to_ega "I 7.2.5" "special case"
  AlgebraicGeometry.Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver
add_to_ega "I 7.2.8" "special case" AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem
add_to_ega "I 7.2.8" "special case" AlgebraicGeometry.Scheme.RationalMap.fromFunctionField
add_to_ega "I 7.2.8" "image of Spec(O_{X" AlgebraicGeometry.Scheme.range_fromSpecStalk
add_to_ega "I 7.2.8" "partial" AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
add_to_ega "I 7.2.8" "partial" AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced
add_to_ega "I 7.3.1" "Γ(U, special case"
  AlgebraicGeometry.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme
add_to_ega "I 7.3.3" "special case" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "I 7.3.3" "special case" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "I 7.3.6" "partial" AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
add_to_ega "I 7.3.6" "partial" AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced
add_to_ega "I 7.3.7" "special case" AlgebraicGeometry.Scheme.germToFunctionField_injective
add_to_ega "I 7.3.7" "special case" AlgebraicGeometry.germ_injective_of_isIntegral
add_to_ega "I 7.3.7" "special case" AlgebraicGeometry.isReduced_of_isIntegral
add_to_ega "I 7.4.1" "special case" LocalizedModule.mkLinearMap
add_to_ega "I 7.4.1" "special case" Module.IsTorsion'
add_to_ega "I 7.4.1" "special case" Submodule.QuotientTorsion.torsion_eq_bot
add_to_ega "I 7.4.1" "special case" Submodule.torsion'
add_to_ega "I 7.4.3" "special case" Module.Invertible.exists_linearEquiv_ideal
add_to_ega "I 7.4.5" "affine case" Module.IsTorsionFree.comap
add_to_ega "I 7.4.7" "special case" Module.IsTorsion'
add_to_ega "I 8.1.2" "partial" Ideal.under_map_of_isLocalizationAtPrime
add_to_ega "I 8.1.2" "partial" IsLocalization.AtPrime.comap_maximalIdeal
add_to_ega "I 8.1.2" "partial" IsLocalization.AtPrime.under_maximalIdeal
add_to_ega "I 8.1.2" "partial" LocalSubring.instAtPrimeSubtypeMemSubringToSubringOfPrime
add_to_ega "I 8.1.2" "partial" LocalSubring.le_ofPrime
add_to_ega "I 8.1.2" LocalSubring.ofPrime
add_to_ega "I 8.1.2" LocalSubring.ofPrimeEquiv
add_to_ega "I 8.1.2" "partial" Localization.AtPrime.comap_maximalIdeal
add_to_ega "I 8.1.2" "partial" Localization.AtPrime.eq_maximalIdeal_iff_comap_eq
add_to_ega "I 8.1.2" "partial" Localization.AtPrime.eq_maximalIdeal_iff_under_eq
add_to_ega "I 8.1.2" "partial" Localization.AtPrime.under_maximalIdeal
add_to_ega "I 8.1.5" Subring.closure
add_to_ega "I 8.2.1" AlgebraicGeometry.Scheme.functionField
add_to_ega "I 8.2.1" "affine case" AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "I 8.2.1" AlgebraicGeometry.instFieldCarrierFunctionField
add_to_ega "I 8.2.1"
  AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunctionField
add_to_ega "I 8.2.1" "more general"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "I 8.2.1" "partial" AlgebraicGeometry.stalkFunctionFieldAlgebra
add_to_ega "I 8.3.1" "more general"
  AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunctionField
add_to_ega "I 8.3.1" "(Sch. 1) for affine X" instIsFractionRingAtPrimeFractionRing
add_to_ega "I 8.3.2" "partial" Algebra.FiniteType
add_to_ega "I 9.1.7" "affine case" TensorProduct.AlgebraTensorModule.rid
add_to_ega "I 9.1.11" "special case" TensorProduct.AlgebraTensorModule.distribBaseChange
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.IsAffineOpen.instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpensBasicOpen
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen
add_to_ega "I 9.3.1" AlgebraicGeometry.RingedSpace.basicOpen
add_to_ega "I 9.3.1" AlgebraicGeometry.Scheme.affineBasicOpen
add_to_ega "I 9.3.1" AlgebraicGeometry.Scheme.basicOpen
add_to_ega "I 9.3.1" "special case" AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "I 9.3.1" "special case" AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "I 9.3.1" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpenToOpenₗ
add_to_ega "I 9.3.1" "(ii), special case" AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen
add_to_ega "I 9.3.1" "(ii), special case"
  AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
add_to_ega "I 9.3.1" "clause (i), special case" AlgebraicGeometry.exists_of_res_eq_of_qcqs
add_to_ega "I 9.3.1" "clause (i), special case" AlgebraicGeometry.exists_of_res_eq_of_qcqs_of_top
add_to_ega "I 9.3.1" "clause (i), special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs
add_to_ega "I 9.3.1" "clause (i), special case" AlgebraicGeometry.exists_of_res_zero_of_qcqs_of_top
add_to_ega "I 9.3.1" "clause (i), special case"
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
add_to_ega "I 9.3.1" "clause (i), special case"
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
add_to_ega "I 9.3.2" "special case"
  AlgebraicGeometry.IsAffineOpen.instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpensBasicOpen
add_to_ega "I 9.3.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen
add_to_ega "I 9.3.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen
add_to_ega "I 9.3.2" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpen
add_to_ega "I 9.3.2" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpenToOpenₗ
add_to_ega "I 9.3.2" "special case" AlgebraicGeometry.isLocalization_away_of_isAffine
add_to_ega "I 9.3.2" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "I 9.3.3" "special case"
  AlgebraicGeometry.IsAffineOpen.instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpensBasicOpen
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen
add_to_ega "I 9.3.3" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpen
add_to_ega "I 9.3.3" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpenToOpenₗ
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.isLocalization_away_of_isAffine
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "I 9.4.2" "special case"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "I 9.4.4" Module.fgSystem
add_to_ega "I 9.4.4" "module clause" Module.fgSystem.equiv
add_to_ega "I 9.4.4" "partial" Module.fgSystem.instIsDirectedOrderSubtypeSubmoduleFG
add_to_ega "I 9.4.4" "module clause" Submodule.FG.directLimit
add_to_ega "I 9.4.4" "Module clause only" Submodule.instIsCompactlyGenerated
add_to_ega "I 9.5.1" "factorization clause" AlgebraicGeometry.Scheme.Hom.toImageAux_spec
add_to_ega "I 9.5.2" AlgebraicGeometry.Scheme.Hom.ker
add_to_ega "I 9.5.2" "special case" AlgebraicGeometry.specTargetImage
add_to_ega "I 9.5.2" "special case" AlgebraicGeometry.specTargetImageFactorization
add_to_ega "I 9.5.2" "special case" AlgebraicGeometry.specTargetImageIdeal
add_to_ega "I 9.5.3" "special case" AlgebraicGeometry.specTargetImageFactorization
add_to_ega "I 9.5.4" "partial" AlgebraicGeometry.Scheme.Hom.range_subset_ker_support
add_to_ega "I 9.5.4" "partial" AlgebraicGeometry.Scheme.IdealSheafData.support_map
add_to_ega "I 9.5.5" "special case"
  AlgebraicGeometry.instIsMultiplicativeSchemeIsSchemeTheoreticallyDominant
add_to_ega "I 9.5.5" "Case Y' = Y and Z' = Z"
  AlgebraicGeometry.instIsSchemeTheoreticallyDominantCompScheme
add_to_ega "I 9.5.6" "special case"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_ega "I 9.5.6" "special case" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_ega "I 9.5.6" "special case" AlgebraicGeometry.ext_of_isDominant
add_to_ega "I 9.5.6" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_ega "I 9.5.6" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated'
add_to_ega "I 9.5.7" "special case" AlgebraicGeometry.Flat.epi_of_flat_of_surjective
add_to_ega "I 9.5.7" "special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_ega "I 9.5.9" "(i), case Y' = Y" AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced
add_to_ega "I 9.5.10" AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact
add_to_ega "I 9.5.11" "more general" AlgebraicGeometry.Scheme.Hom.app_injective
add_to_ega "I 9.5.11" "partial" AlgebraicGeometry.Scheme.Hom.toImage_app_injective
add_to_ega "I 9.5.11" "special case" AlgebraicGeometry.map_injective_of_isIntegral
add_to_ega "I 9.6.2" "partial" AlgHom.FiniteType
add_to_ega "I 9.6.2" "partial" Algebra.FiniteType
add_to_ega "I 9.6.2" "special case"
  AlgebraicGeometry.IsAffineOpen.instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpensBasicOpen
add_to_ega "I 9.6.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen
add_to_ega "I 9.6.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen
add_to_ega "I 9.6.2" "special case"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpen
add_to_ega "I 9.6.2" "Γ(D(f)"
  AlgebraicGeometry.StructureSheaf.instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopologyStructureSheafInTypeOpBasicOpenToOpenₗ
add_to_ega "I 9.6.2" "special case" AlgebraicGeometry.isLocalization_away_of_isAffine
add_to_ega "I 9.6.2" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "I 9.6.2" "partial" RingHom.finiteType_localizationPreserves
add_to_ega "I 9.6.2" "partial" instFiniteTypeAway
add_to_ega "I 10.1.3" "special case" AlgebraicGeometry.LocallyRingedSpace.SpecΓIdentity
add_to_ega "I 10.1.3" "special case" AlgebraicGeometry.Scheme.ΓSpecIso
add_to_ega "I 10.1.3" "special case" AlgebraicGeometry.isIso_toSpecΓ
add_to_ega "I 10.1.4" "special case" AlgebraicGeometry.basicOpenIsoSpecAway
add_to_ega "I 10.1.6" "special case" AlgebraicGeometry.Scheme.Spec.residueFieldIso
add_to_ega "I 10.1.6" "special case" AlgebraicGeometry.Spec.locallyRingedSpaceObj
add_to_ega "I 10.1.6" "special case"
  AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian
add_to_ega "I 10.2.1" "special case" AlgebraicGeometry.Spec.locallyRingedSpaceMap
add_to_ega "I 10.2.1" "special case" AlgebraicGeometry.Spec.sheafedSpaceMap
add_to_ega "I 10.2.1" "special case" AlgebraicGeometry.Spec.topMap
add_to_ega "I 10.2.1" "special case" AlgebraicGeometry.StructureSheaf.comap
add_to_ega "I 10.2.1" "special case" PrimeSpectrum.comap
add_to_ega "I 10.2.1" "special case" PrimeSpectrum.comap_basicOpen
add_to_ega "I 10.2.1" "special case" PrimeSpectrum.continuous_comap
add_to_ega "I 10.2.3" "partial" AlgebraicGeometry.Scheme.Hom.resLE
add_to_ega "I 10.2.3" "special case" AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap
add_to_ega "I 10.2.3" "partial" AlgebraicGeometry.morphismRestrict_ι
add_to_ega "I 10.3.1" "Γ(X, special case" AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine
add_to_ega "I 10.3.1" "special case" AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
add_to_ega "I 10.3.1" "Γ(D(f), special case"
  AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal
add_to_ega "I 10.3.2" "Discrete case" AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
add_to_ega "I 10.3.2" "Discrete affine case" AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine
add_to_ega "I 10.3.2" "Discrete affine case" AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjι
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.IsLocallyNoetherian
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.IsNoetherian
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.IsNoetherian.noetherianSpace
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.Scheme
add_to_ega "I 10.4.2" "affine ordinary case"
  AlgebraicGeometry.instNoetherianSpaceCarrierCarrierCommRingCatSpecOfIsNoetherianRingCarrier
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover
add_to_ega "I 10.4.2" "special case" AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top
add_to_ega "I 10.4.2" "ordinary schemes" AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
add_to_ega "I 10.4.3" "special case" AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen
add_to_ega "I 10.4.3" "special case" AlgebraicGeometry.Scheme.isBasis_affineOpens
add_to_ega "I 10.4.4" "special case" AlgebraicGeometry.instIsLocallyNoetherianToScheme
add_to_ega "I 10.4.4" "special case" AlgebraicGeometry.instIsLocallyNoetherianXScheme
add_to_ega "I 10.4.4" "special case" AlgebraicGeometry.isLocallyNoetherian_iff_openCover
add_to_ega "I 10.4.4" "special case" AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
add_to_ega "I 10.4.5" "special case" AlgebraicGeometry.LocallyRingedSpace.Hom
add_to_ega "I 10.4.5" "special case" AlgebraicGeometry.Scheme.Hom
add_to_ega "I 10.4.6" "special case" AlgebraicGeometry.AffineScheme.ΓIsEquiv
add_to_ega "I 10.4.6" "partial" AlgebraicGeometry.ext_of_isAffine
add_to_ega "I 10.4.7" CategoryTheory.Over.Hom
add_to_ega "I 10.6.4" "special case" AdicCompletion.pow_smul_top_eq_ker_eval
add_to_ega "I 10.6.5" "special case" AlgebraicGeometry.instIsNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 10.6.5" "special case" AlgebraicGeometry.instIsNoetherianSpecOfOfIsNoetherianRing
add_to_ega "I 10.6.5" "special case" AlgebraicGeometry.isNoetherian_Spec
add_to_ega "I 10.8.2" "special case" localCohomology.ideal_powers_initial
add_to_ega "I 10.8.5" AdicCompletion
add_to_ega "I 10.9.1" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap
add_to_ega "I 10.10.1" "Representation clause"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
add_to_ega "I 10.10.1" "Representation clause"
  AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "I 10.10.1" "partial" IsNoetherianRing
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.LocallyRingedSpace.SpecΓIdentity
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.Scheme.ΓSpecIso
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.StructureSheaf.toOpenₗ_top_bijective
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.isIso_toSpecΓ
add_to_ega "I 10.10.2" "(iii), special case" AlgebraicGeometry.tilde.fullyFaithfulFunctor
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.ΓSpec.isIso_adjunction_counit
add_to_ega "I 10.12.2" "more general" CategoryTheory.NatTrans.Equifibered
add_to_ega "I 10.13.5" "(ii)"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "I 10.13.5" "(ii)"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "I 10.13.5" "(i), special case"
  AlgebraicGeometry.instIsMultiplicativeSchemeLocallyOfFiniteType
add_to_ega "I 10.13.5" "(i), special case"
  AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType
add_to_ega "I 10.13.5" "(ii)" AlgebraicGeometry.instLocallyOfFiniteTypeFstScheme
add_to_ega "I 10.13.5" "(i), special case" RingHom.FiniteType.comp
add_to_ega "I 10.13.5" "(ii)" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "I 10.13.5" "(i), special case" RingHom.finiteType_stableUnderComposition
add_to_ega "I 10.14.3" "special case" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "I 10.14.3" "special case"
  AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_ega "I 10.14.3" "special case" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "I 10.14.3" "special case" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "I 10.14.3" "special case" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_ega "I 10.14.4" "partial" AlgebraicGeometry.IsClosedImmersion.hasAffineProperty
add_to_ega "I 10.14.5" "(i), ordinary schemes" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 10.14.5" "(i), ordinary schemes"
  AlgebraicGeometry.IsClosedImmersion.instIsMultiplicativeScheme
add_to_ega "I 10.14.5" "(ii), special case" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_ega "I 10.14.5" "(ii), ordinary schemes" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_ega "I 10.15.1" "Separated morphism X → S" AlgebraicGeometry.IsSeparated
add_to_ega "I 10.15.1" "special case" AlgebraicGeometry.Scheme.IsSeparated
add_to_ega "I 10.15.1" CategoryTheory.Limits.pullback.diagonal
add_to_ega "I 10.15.3" "special case" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "I 10.15.3" "(i), ordinary preschemes" AlgebraicGeometry.IsSeparated.instCompScheme
add_to_ega "I 10.15.3" "(iii), special case" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_ega "I 10.15.3" "(i), ordinary preschemes"
  AlgebraicGeometry.IsSeparated.instIsMultiplicativeScheme
add_to_ega "I 10.15.3" "(iii), special case" AlgebraicGeometry.IsSeparated.instMorphismRestrict
add_to_ega "I 10.15.3" "(iv), special case" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "I 10.15.3" "(iv), special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated
add_to_ega "I 10.15.3" "(iv), special case"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsSeparatedTopMorphismProperty
add_to_ega "I 10.15.4" "special case"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "I 10.15.4" "special case"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
