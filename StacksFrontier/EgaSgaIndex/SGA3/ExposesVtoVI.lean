module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Category.CoalgCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.OverClass
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Subfunctor.Equalizer
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Subfunctor.SubmonoidFunctor
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.CosetCover
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Constructible
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Semicontinuity.Defs
import StacksCore.RingTheory.Flat.TorsionFree
import StacksCore.RingTheory.NormTrace
import StacksCore.RingTheory.Support
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 3 references registered by name: Exposés V and VI

The `add_to_sga` registrations of SGA 3, Exposés V and VI, re-exported by
`StacksFrontier.EgaSgaIndex.SGA3`.
-/

add_to_sga "3 V 1.2" "more general" AlgebraicGeometry.LocallyRingedSpace.coequalizerCoforkIsColimit
add_to_sga "3 V 1.2" "special case" CategoryTheory.AddGrpObj.isPullback
add_to_sga "3 V 1.2" CategoryTheory.ChosenPullbacksAlong.pullbackCone
add_to_sga "3 V 1.2" CategoryTheory.ChosenPullbacksAlong.pullbackObj
add_to_sga "3 V 1.2" "special case" CategoryTheory.CommGrpObj
add_to_sga "3 V 1.2" "special case" CategoryTheory.Grp
add_to_sga "3 V 1.2" "special case" CategoryTheory.GrpObj
add_to_sga "3 V 1.2" "special case" CategoryTheory.GrpObj.instIsIsoInv
add_to_sga "3 V 1.2" "special case" CategoryTheory.GrpObj.inv_comp_inv
add_to_sga "3 V 1.2" "special case" CategoryTheory.GrpObj.isPullback
add_to_sga "3 V 1.2" "partial" CategoryTheory.IsGroupoid
add_to_sga "3 V 1.2" CategoryTheory.Limits.pullback
add_to_sga "3 V 3.1" AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage
add_to_sga "3 V 3.1" AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
add_to_sga "3 V 4.1" "special case" Algebra.IsInvariant.charpoly_mem_lifts
add_to_sga "3 V 4.1" "special case" Algebra.IsInvariant.isIntegral
add_to_sga "3 V 4.1" "special case" Algebra.IsInvariant.isIntegral_of_profinite
add_to_sga "3 V 4.1" Algebra.norm
add_to_sga "3 V 4.1" "special case" Algebra.norm_eq_zero_iff
add_to_sga "3 V 4.1" "special case" Algebra.norm_eq_zero_iff_of_basis
add_to_sga "3 V 4.1" "special case" Algebra.norm_ne_zero_iff
add_to_sga "3 V 4.1" "special case" Algebra.norm_ne_zero_iff_of_basis
add_to_sga "3 V 4.1" "special case" FixedPoints.subring
add_to_sga "3 V 4.1" "more general" Ideal.IntegralClosure.comap_lt_comap
add_to_sga "3 V 4.1" "more general" Ideal.IsIntegral.comap_lt_comap
add_to_sga "3 V 4.1" "more general" Ideal.IsIntegral.mem_minimalPrimes_map_under
add_to_sga "3 V 4.1" "more general" Ideal.IsIntegralClosure.comap_le_comap
add_to_sga "3 V 4.1" "special case" Ideal.card_primesOverFinset_le_finrank
add_to_sga "3 V 4.1" "more general" Ideal.comap_lt_comap_of_integral_mem_sdiff
add_to_sga "3 V 4.1" "more general" Ideal.subset_union_prime
add_to_sga "3 V 4.1" "more general" Ideal.subset_union_prime_finite
add_to_sga "3 V 4.1" "special case" LinearMap.charpoly
add_to_sga "3 V 4.1" "special case" LinearMap.charpoly_baseChange
add_to_sga "3 V 4.1" "partial" LinearMap.charpoly_monic
add_to_sga "3 V 4.1" "partial" LinearMap.charpoly_natDegree
add_to_sga "3 V 4.1" "special case" LinearMap.det
add_to_sga "3 V 4.1" "norm equals σₙ" LinearMap.det_eq_sign_charpoly_coeff
add_to_sga "3 V 4.1" "special case" Matrix.charpoly_map
add_to_sga "3 V 4.1" "monicity" Matrix.charpoly_monic
add_to_sga "3 V 4.1" "special case" MulSemiringAction.smul_charpoly
add_to_sga "3 V 4.1" "special case" MulSemiringAction.smul_coeff_charpoly
add_to_sga "3 V 4.1" "partial" NonUnitalRingHom.eqLocus
add_to_sga "3 V 4.1" RingHom.eqLocus
add_to_sga "3 V 4.1" "partial" norm_eq_neg_one_pow_finrank_mul_constantCoeff_charpoly
add_to_sga "3 V 4.1.1" "special case" Algebra.norm
add_to_sga "3 V 4.1.1" "partial" AlgebraicGeometry.LocallyRingedSpace.coequalizerCoforkIsColimit
add_to_sga "3 V 4.1.1" AlgebraicGeometry.Scheme.instCoeFunHomForallCarrierCarrierCommRingCat
add_to_sga "3 V 4.1.1" AlgebraicGeometry.Scheme.instCoeSortType
add_to_sga "3 V 4.1.1" "partial" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 V 4.1.2" AdjoinRoot
add_to_sga "3 V 4.1.2" AlgebraicGeometry.Scheme.instCoeFunHomForallCarrierCarrierCommRingCat
add_to_sga "3 V 4.1.2" AlgebraicGeometry.Scheme.instCoeSortType
add_to_sga "3 V 4.1.3" "more general" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_sga "3 V 4.1.3" "more general"
  AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_sga "3 V 4.1.3" "partial" AlgebraicGeometry.IsClosedImmersion.hasAffineProperty
add_to_sga "3 V 4.1.3" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_sga "3 V 4.1.3" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_sga "3 V 4.1.3" "partial"
  AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
add_to_sga "3 V 4.1.3" "partial" AlgebraicGeometry.isFinite_iff
add_to_sga "3 V 4.1.3" "more general" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "3 V 4.1.3" "more general" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_sga "3 V 4.1.3" "more general" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 V 4.1.3" "more general" LinearMap.surjective_of_surjective_comp_mkQ
add_to_sga "3 V 4.1.3" "more general" Module.eq_zero_of_localization_maximal
add_to_sga "3 V 4.1.3" "more general" Submodule.eq_bot_of_localization_maximal
add_to_sga "3 V 4.1.3" "more general" Submodule.eq_bot_of_localization₀_maximal
add_to_sga "3 V 4.1.3" "more general" Submodule.eq_of_localization₀_maximal
add_to_sga "3 V 4.1.3" "partial" Submodule.eq_top_of_localization_maximal
add_to_sga "3 V 4.1.3" "partial" Submodule.eq_top_of_localization₀_maximal
add_to_sga "3 V 4.1.3" "more general" Submodule.exists_mem_addIdeal_and_span_image_eq_top
add_to_sga "3 V 4.1.3" "more general" Submodule.mem_of_localization_maximal
add_to_sga "3 V 4.1.3" "partial" surjective_of_isLocalization_isMaximal
add_to_sga "3 V 4.1.3" "more general" surjective_of_isLocalized_maximal
add_to_sga "3 V 4.1.3" "more general" surjective_of_localized_maximal
add_to_sga "3 V 4.2" Algebra.TensorProduct.basis
add_to_sga "3 V 4.2" Ideal.jacobson
add_to_sga "3 V 4.2" "partial" Subspace.biUnion_ne_univ_of_top_notMem
add_to_sga "3 V 4.2" "partial" Subspace.top_mem_of_biUnion_eq_univ
add_to_sga "3 V 6.1" "special case" AlgHom.FinitePresentation.of_finiteType
add_to_sga "3 V 6.1" "affine case" Algebra.FinitePresentation.of_finiteType
add_to_sga "3 V 6.1" "partial" AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType
add_to_sga "3 V 6.1" "more general" AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage
add_to_sga "3 V 6.1" "more general" AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
add_to_sga "3 V 6.1" "more general" AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
add_to_sga "3 V 6.1"
  AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
add_to_sga "3 V 6.1" "special case" Module.FaithfullyFlat.bijective_of_tensorProduct
add_to_sga "3 V 6.1" "partial" Module.FaithfullyFlat.of_comap_surjective
add_to_sga "3 V 6.1" "special case" RingHom.FaithfullyFlat.codescendsAlong_bijective
add_to_sga "3 V 6.1" "affine case" RingHom.FinitePresentation.of_finiteType
add_to_sga "3 V 6.1" "(ii), special case" Subalgebra.fg_of_noetherian
add_to_sga "3 V 7.2" "partial" TopologicalSpace.instWellFoundedLTClosedsOfNoetherianSpace
add_to_sga "3 V 7.2" "In a Noetherian ring" biUnion_associatedPrimes_eq_compl_nonZeroDivisors
add_to_sga "3 V 7.3" "special case" Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber
add_to_sga "3 V 7.3" "special case" Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
add_to_sga "3 V 7.3" "partial" AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber
add_to_sga "3 V 7.3" "partial" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_sga "3 V 7.3" "partial"
  AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
add_to_sga "3 V 7.3" "partial"
  AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton
add_to_sga "3 V 7.4" "(ii), special case" Algebra.QuasiFiniteAt.baseChange
add_to_sga "3 V 7.4" "partial" Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber
add_to_sga "3 V 7.4" "special case" Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
add_to_sga "3 V 7.4" "partial" Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
add_to_sga "3 V 7.4" "partial" AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber
add_to_sga "3 V 7.4" "partial" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_sga "3 V 7.4" "partial"
  AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
add_to_sga "3 V 7.4" "(i), special case" Module.Flat.isBaseChange
add_to_sga "3 V 7.4" "(i), special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 V 7.4" "(ii), special case" RingHom.QuasiFinite.isStableUnderBaseChange
add_to_sga "3 V 8.1" "special case" Algebra.QuasiFinite.iff_of_isArtinianRing
add_to_sga "3 V 8.1" "Footnote (45)" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_sga "3 V 9.0" "(3): surjectivity of p"
  AlgebraicGeometry.SheafedSpace.instEpiTopCatBaseHomPresheafedSpaceπ
add_to_sga "3 V 9.1" Algebra.FinitePresentation.ker_fG_of_surjective
add_to_sga "3 V 9.1" "special case" Algebra.FinitePresentation.ker_fg_of_mvPolynomial
add_to_sga "3 V 9.1" "special case" Algebra.Generators.fg_ker_of_finitePresentation
add_to_sga "3 V 9.1" "more general" Algebra.TensorProduct.includeLeft_injective
add_to_sga "3 V 9.1" "more general" Algebra.TensorProduct.includeRight_injective
add_to_sga "3 V 9.1" "partial" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_sga "3 V 9.1" "partial" Ideal.map_injective_of_faithfullyFlat
add_to_sga "3 V 9.1" "more general" IsTensorProduct.map_id_injective_of_flat_left
add_to_sga "3 V 9.1" "B_j = B from C_j = C" Module.FaithfullyFlat.surjective_of_tensorProduct
add_to_sga "3 V 9.1" "more general" Module.Flat.lTensor_preserves_injective_linearMap
add_to_sga "3 V 9.1" "B_j = B from C_j = C" RingHom.FaithfullyFlat.codescendsAlong_bijective
add_to_sga "3 V 9.1" "B_j = B from C_j = C" RingHom.FaithfullyFlat.codescendsAlong_surjective
add_to_sga "3 V 9.1" "more general" TensorProduct.map_injective_of_flat_flat
add_to_sga "3 V 9.1" "more general" TensorProduct.map_injective_of_flat_flat'
add_to_sga "3 V 10.1.1" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 V 10.1.1" "Remark a)" CategoryTheory.IsKernelPair.cancel_right_of_mono
add_to_sga "3 V 10.1.1" "Remark a)" CategoryTheory.IsKernelPair.comp_of_mono
add_to_sga "3 V 10.1.1" CategoryTheory.IsKernelPair.equivalenceRelation
add_to_sga "3 V 10.4" "partial" MulAction.injective_ofQuotientStabilizer
add_to_sga "3 V 10.4" "partial" MulAction.orbitEquivQuotientStabilizer
add_to_sga "3 VIA 0.1" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIA 0.1" "pr₂" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIA 0.1" "partial" AlgebraicGeometry.instSmoothFstScheme
add_to_sga "3 VIA 0.1" "partial" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "3 VIA 0.1" CategoryTheory.GrpObj.inv
add_to_sga "3 VIA 0.1" "partial" CategoryTheory.GrpObj.inv_eq_inv
add_to_sga "3 VIA 0.1" "(x)" CategoryTheory.Hom.inv_def
add_to_sga "3 VIA 0.2" IsArtinianRing
add_to_sga "3 VIA 0.2" IsLocalRing
add_to_sga "3 VIA 0.2" IsLocalRing.ResidueField
add_to_sga "3 VIA 0.2" IsLocallyClosed
add_to_sga "3 VIA 0.2" PerfectClosure
add_to_sga "3 VIA 0.2" "k^{p^-∞} is a field" PerfectClosure.instField
add_to_sga "3 VIA 0.2" "partial" PerfectClosure.instPerfectField
add_to_sga "3 VIA 0.2" "partial" PerfectClosure.instPerfectRing
add_to_sga "3 VIA 0.2" PerfectField
add_to_sga "3 VIA 0.3" "special case" AlgebraicGeometry.instIsClosedImmersionLeftSchemeOneOverSpecOf
add_to_sga "3 VIA 0.4" CategoryTheory.AddGrpObj.addRight
add_to_sga "3 VIA 0.4" "special case" PrimeSpectrum.preimageHomeomorphFiber
add_to_sga "3 VIA 1.1.1" "more general" Module.freeLocus_eq_univ
add_to_sga "3 VIA 1.1.1" "more general" Module.free_of_flat_of_finrank_eq
add_to_sga "3 VIA 1.1.1" "more general" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIA 1.1.2" "partial"
  AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology
add_to_sga "3 VIA 1.1.2" "partial"
  AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology
add_to_sga "3 VIA 1.1.2" "partial"
  AlgebraicGeometry.IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
add_to_sga "3 VIA 1.1.2" "partial"
  AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero
add_to_sga "3 VIA 1.1.2" "partial"
  AlgebraicGeometry.instIsLocallyArtinianOfDiscreteTopologyCarrierCarrierCommRingCatOfIsReduced
add_to_sga "3 VIA 1.1.2" "partial" IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
add_to_sga "3 VIA 1.1.2" "partial" Module.finite_iff_isArtinianRing
add_to_sga "3 VIA 1.1.2" "(a), special case"
  Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
add_to_sga "3 VIA 1.1.2" "(a)" ringKrullDim_quotient_succ_le_of_nonZeroDivisor
add_to_sga "3 VIA 1.3.1" "(2), special case" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "3 VIA 1.3.2" "partial" Algebra.Extension.tensorCotangentSpace
add_to_sga "3 VIA 1.3.2" "more general" Algebra.Generators.cotangentSpaceBasis
add_to_sga "3 VIA 1.3.2" "Differentials clause" KaehlerDifferential.isBaseChange
add_to_sga "3 VIA 2.1" "partial" connectedComponent
add_to_sga "3 VIA 2.1" "more general" isClosed_connectedComponent
add_to_sga "3 VIA 2.1.2" "affine X, special case" AlgebraicGeometry.pullbackSpecIso
add_to_sga "3 VIA 2.1.2" "affine X, special case" AlgebraicGeometry.pullbackSpecIso'
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
add_to_sga "3 VIA 2.1.2" "affine case"
  PrimeSpectrum.exists_mul_eq_zero_add_eq_one_basicOpen_eq_of_isClopen
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.isClopen_iff
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.isClopen_iff_mul_add
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.isClopen_iff_mul_add_zeroLocus
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.isClopen_iff_zeroLocus
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.isIdempotentElemEquivClopens
add_to_sga "3 VIA 2.1.2" "affine case" PrimeSpectrum.mulZeroAddOneEquivClopens
add_to_sga "3 VIA 2.1.3" "more general" AlgebraicGeometry.RingedSpace.zeroLocus_isClosed
add_to_sga "3 VIA 2.1.3" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIA 2.1.3" "affine case" Module.support_of_algebra
add_to_sga "3 VIA 2.1.3" "open-image clause" PrimeSpectrum.exists_image_comap_of_finite_of_free
add_to_sga "3 VIA 2.2" "more general" AlgebraicGeometry.LocallyRingedSpace.toTopCat
add_to_sga "3 VIA 2.2" "more general" AlgebraicGeometry.PresheafedSpace.carrier
add_to_sga "3 VIA 2.2" "more general" AlgebraicGeometry.PresheafedSpace.coeCarrier
add_to_sga "3 VIA 2.2" AlgebraicGeometry.Scheme.hasCoeToTopCat
add_to_sga "3 VIA 2.3" "partial" IsOpen.connectedComponentIn
add_to_sga "3 VIA 2.3" LocallyConnectedSpace
add_to_sga "3 VIA 2.3" Subgroup.Normal
add_to_sga "3 VIA 2.3" connectedComponent
add_to_sga "3 VIA 2.3" "partial" isClopen_connectedComponent
add_to_sga "3 VIA 2.3" "partial" isOpen_connectedComponent
add_to_sga "3 VIA 2.3" "partial" locallyConnectedSpace_iff_connectedComponentIn_open
add_to_sga "3 VIA 2.5.4" "partial"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_sga "3 VIA 2.6.1" "(iii)" algebraicClosure
add_to_sga "3 VIA 2.6.3" "more general" IsCompact.isRetrocompact
add_to_sga "3 VIA 2.6.3" IsRetrocompact
add_to_sga "3 VIA 2.6.3" IsRetrocompact_iff_isSpectralMap_subtypeVal
add_to_sga "3 VIA 3.1" "flatness of pr₂" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIA 3.1" "flatness of pr₂" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIA 3.1" "special case"
  AlgebraicGeometry.instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCarrierCommRingCat
add_to_sga "3 VIA 3.1" "object component r_s" CategoryTheory.GrpObj.mulRight
add_to_sga "3 VIA 3.1" "more general" CategoryTheory.Limits.coequalizer
add_to_sga "3 VIA 3.2.1" "more general" Dense.preimage
add_to_sga "3 VIA 3.2.1" "more general" IsOpenQuotientMap.dense_preimage_iff
add_to_sga "3 VIA 3.3.3" "more general" AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage
add_to_sga "3 VIA 4.3" "partial" CategoryTheory.IsSplitEpi.EffectiveEpi
add_to_sga "3 VIA 4.6" "special case" AlgHom.tensorEqualizerEquiv
add_to_sga "3 VIA 4.6" "partial" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_sga "3 VIA 4.6" "partial" AlgebraicGeometry.instQuasiCompactOfIsAffineHom
add_to_sga "3 VIA 4.6" "special case" CommRingCat.Under.equalizerForkTensorProdIso
add_to_sga "3 VIA 4.6" "Affine case"
  CommRingCat.Under.instPreservesLimitsOfShapeUnderWalkingParallelPairTensorProdOfFlatCarrier
add_to_sga "3 VIA 4.6" "Affine module-level case" IsBaseChange.of_left_exact
add_to_sga "3 VIA 5.4.2" CategoryTheory.Abelian
add_to_sga "3 VIA 6.3" AlgebraicGeometry.IsSchemeTheoreticallyDominant
add_to_sga "3 VIA 6.4" "partial" AlgebraicGeometry.Scheme.instQuasiCompactToImage
add_to_sga "3 VIB 1.3" "partial" AlgebraicGeometry.locallyOfFinitePresentation_iff
add_to_sga "3 VIB 1.3" "special case"
  AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton
add_to_sga "3 VIB 1.3.0" Algebra.FinitePresentation.ker_fg_of_mvPolynomial
add_to_sga "3 VIB 1.3.0" "more general" Algebra.Generators.fg_ker_of_finitePresentation
add_to_sga "3 VIB 1.3.0" "special case"
  Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat
add_to_sga "3 VIB 1.4.1" "special case" Algebra.QuasiFinite.isDiscrete_comap_preimage
add_to_sga "3 VIB 1.4.1" "special case" Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
add_to_sga "3 VIB 1.4.1" "special case" Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber
add_to_sga "3 VIB 1.4.1" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_sga "3 VIB 1.4.1" "more general"
  AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_sga "3 VIB 1.4.1" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_sga "3 VIB 1.4.1" "(i) ⇒ (v), special case" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_sga "3 VIB 1.4.1" "(i) ⇒ (iii)" AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage
add_to_sga "3 VIB 1.4.1" "(i) ⇒ (iii)" AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton
add_to_sga "3 VIB 1.4.1" "(i) ⇒ (ii)" AlgebraicGeometry.Scheme.Hom.quasiFiniteAt
add_to_sga "3 VIB 1.4.1" "(iii) ⇒ (ii)"
  AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
add_to_sga "3 VIB 1.4.1" "more general" AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite
add_to_sga "3 VIB 1.4.2" "(i) ⇒ (ii)" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_sga "3 VIB 1.4.2" "(i) ⇒ (ii)"
  AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_sga "3 VIB 1.4.2" "(i) ⇒ (ii)" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_sga "3 VIB 1.4.2" "(i) ⇒ (ii)" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_sga "3 VIB 1.4.2" "(i) ⇒ (ii)" AlgebraicGeometry.IsPreimmersion.instMonoScheme
add_to_sga "3 VIB 1.4.2" "more general" AlgebraicGeometry.isAffineHom_of_isAffine
add_to_sga "3 VIB 2.0" "b)" AlgebraicGeometry.IsZariskiLocalAtTarget
add_to_sga "3 VIB 2.0" AlgebraicGeometry.Scheme.Over
add_to_sga "3 VIB 2.0" CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_sga "3 VIB 2.0" "partial" CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong
add_to_sga "3 VIB 2.0" CategoryTheory.Over.hom
add_to_sga "3 VIB 2.0" CategoryTheory.OverClass
add_to_sga "3 VIB 2.1.2" "special case" Algebra.Etale.baseChange
add_to_sga "3 VIB 2.1.2" "special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "3 VIB 2.1.2" "special case" AlgebraicGeometry.Etale.instResLE
add_to_sga "3 VIB 2.1.2" "special case" AlgebraicGeometry.Flat.instMorphismRestrict
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.UniversallyOpen.fst
add_to_sga "3 VIB 2.1.2" "special case" AlgebraicGeometry.UniversallyOpen.instIsZariskiLocalAtTarget
add_to_sga "3 VIB 2.1.2" "partial"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_sga "3 VIB 2.1.2" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 VIB 2.1.2" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 VIB 2.1.2" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 VIB 2.1.2" "special case" RingHom.Etale.isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "special case" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_sga "3 VIB 2.1.2" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_sga "3 VIB 2.1.2" "special case" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "special case" RingHom.finiteType_isStableUnderBaseChange
add_to_sga "3 VIB 2.2" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_sga "3 VIB 2.5" "special case" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_sga "3 VIB 2.7.1" "special case" Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_sga "3 VIB 2.7.1" "special case"
  AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_sga "3 VIB 2.8" "special case" Algebra.QuasiFinite.baseChange
add_to_sga "3 VIB 2.8" "special case" Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
add_to_sga "3 VIB 2.8" "special case" Algebra.Unramified.baseChange
add_to_sga "3 VIB 2.8" "(iii) ⇒ (iv)" AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage
add_to_sga "3 VIB 2.8" "(iii) ⇒ (iv)" AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton
add_to_sga "3 VIB 2.8" "(iii) ⇔ (iv)"
  AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton
add_to_sga "3 VIB 2.9.1" "partial" AlgebraicGeometry.affineAnd_isLocal
add_to_sga "3 VIB 2.9.1" "partial" AlgebraicGeometry.affineAnd_isLocal_of_propertyIsLocal
add_to_sga "3 VIB 2.9.1" AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen
add_to_sga "3 VIB 2.9.1" "more general" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_sga "3 VIB 2.11" "partial" CategoryTheory.IsKernelPair.mono_of_isIso_fst
add_to_sga "3 VIB 2.11" "partial" CategoryTheory.IsPullback.isIso_fst_of_mono
add_to_sga "3 VIB 2.11" "partial" CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit
add_to_sga "3 VIB 2.11" "partial" CategoryTheory.Limits.isIso_fst_of_mono
add_to_sga "3 VIB 2.11" "partial" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "3 VIB 2.11" "more general" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_sga "3 VIB 2.11" "more general" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 VIB 2.11" "more general" CategoryTheory.mono_iff_isIso_fst
add_to_sga "3 VIB 3.1" "more general" connectedComponent
add_to_sga "3 VIB 3.7" "special case" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_sga "3 VIB 3.7" "partial" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_sga "3 VIB 3.7" "partial" IsCompact.isRetrocompact
add_to_sga "3 VIB 3.7" IsRetrocompact
add_to_sga "3 VIB 3.7" Topology.IsConstructible
add_to_sga "3 VIB 3.7" Topology.IsLocallyConstructible
add_to_sga "3 VIB 3.7" "partial, special case"
  Topology.IsLocallyConstructible.iff_isConstructible_of_isOpenCover
add_to_sga "3 VIB 3.7" "partial, special case"
  Topology.IsLocallyConstructible.inter_of_isOpen_isCompact
add_to_sga "3 VIB 3.7" "partial, special case" Topology.IsLocallyConstructible.isConstructible
add_to_sga "3 VIB 3.7" "partial, special case"
  Topology.IsLocallyConstructible.isConstructible_of_subset_of_isCompact
add_to_sga "3 VIB 3.8" "partial"
  AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
add_to_sga "3 VIB 3.8" "more general" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_sga "3 VIB 3.8" "affine base S_0 = Spec R" AlgebraicGeometry.algSpec
add_to_sga "3 VIB 3.10" "special case" Algebra.IsSmoothAt.of_formallySmooth_fiber
add_to_sga "3 VIB 3.10" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 VIB 3.11" "fiber-flatness" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIB 3.11" "fiber-flatness" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIB 3.11" "partial"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_sga "3 VIB 3.11" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 VIB 4.1" "(i)" Semicontinuous.comp
add_to_sga "3 VIB 4.2" "more general" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_sga "3 VIB 4.2" "partial" AlgebraicGeometry.Scheme.Hom.isConstructible_preimage
add_to_sga "3 VIB 4.2" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_sga "3 VIB 4.4" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 VIB 5.1" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_sga "3 VIB 5.2" "special case" MaximalSpectrum.toPiLocalizationEquiv
add_to_sga "3 VIB 5.6.0" "more general" AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem
add_to_sga "3 VIB 5.6.0" "special case" Ideal.exists_comap_galRestrict_eq
add_to_sga "3 VIB 5.6.0" "more general" IsLocalRing.closedPoint_mem_iff
add_to_sga "3 VIB 5.6.0" "more general" IsLocalRing.closed_point_mem_iff
add_to_sga "3 VIB 5.6.1.0" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationFstScheme
add_to_sga "3 VIB 5.6.1.0" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme
add_to_sga "3 VIB 5.6.1.0" "special case" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (ii)" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii)" AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii)"
  AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le
add_to_sga "3 VIB 5.6.3" "special case" AlgebraicGeometry.ext_of_apply_eq
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii)" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii), S = Spec ℤ" AlgebraicGeometry.ext_of_isDominant
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii)" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (iii)" AlgebraicGeometry.ext_of_isDominant_of_isSeparated'
add_to_sga "3 VIB 5.6.3" "(i) ⇒ (ii)"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_sga "3 VIB 5.8.3" "more general" ProfiniteAddGrp.pi
add_to_sga "3 VIB 5.8.3" "more general" ProfiniteGrp.pi
add_to_sga "3 VIB 5.8.3" "partial" cantorSetHomeomorphNatToBool
add_to_sga "3 VIB 5.8.4" FreeGroup
add_to_sga "3 VIB 5.8.4" Monoid.Coprod
add_to_sga "3 VIB 5.8.4" "more general" Monoid.CoprodI
add_to_sga "3 VIB 6.1" CategoryTheory.Functor
add_to_sga "3 VIB 6.1" CategoryTheory.Subfunctor.image
add_to_sga "3 VIB 6.1" CategoryTheory.Subfunctor.range
add_to_sga "3 VIB 6.1" "special case" CategoryTheory.SubmonoidFunctor.image
add_to_sga "3 VIB 6.2.2" "special case" Module.IsLocalRing.linearCombination_bijective_of_flat
add_to_sga "3 VIB 6.2.2" "special case" Module.freeLocus_eq_univ
add_to_sga "3 VIB 6.2.2" "special case" Module.free_of_flat_of_finrank_eq
add_to_sga "3 VIB 6.2.2" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIB 6.2.4" "special case" AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_sga "3 VIB 6.2.4" "special case" AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
add_to_sga "3 VIB 6.2.4" "b" CategoryTheory.Limits.Types.equalizerIso
add_to_sga "3 VIB 6.2.4" CategoryTheory.Limits.equalizer
add_to_sga "3 VIB 6.2.4" CategoryTheory.Limits.equalizerSubobject
add_to_sga "3 VIB 6.2.4" "b" CategoryTheory.Limits.isPullback_equalizer_prod
add_to_sga "3 VIB 6.2.4" "more general" CategoryTheory.Subfunctor.equalizer
add_to_sga "3 VIB 6.2.4" "more general" CategoryTheory.Subfunctor.equalizer.forkIsLimit
add_to_sga "3 VIB 6.2.4" "more general" CategoryTheory.Subfunctor.equalizer_obj
add_to_sga "3 VIB 7.2.2" "more general" CategoryTheory.GrpObj.commutator
add_to_sga "3 VIB 8.1" "partial" AddSubgroup.addCommutator
add_to_sga "3 VIB 8.1" CategoryTheory.sheafify
add_to_sga "3 VIB 8.1" "partial" Subgroup.commutator
add_to_sga "3 VIB 8.1" "sectionwise Comm(G" addCommutator
add_to_sga "3 VIB 8.1" "sectionwise Comm(G,G)(S)" commutator
add_to_sga "3 VIB 8.1.1" "special case" AddSubgroup.Normal.quotient_commutative_iff_addCommutator_le
add_to_sga "3 VIB 8.1.1" "special case" Subgroup.Normal.quotient_commutative_iff_commutator_le
add_to_sga "3 VIB 8.2" "special case" AddSubgroup.lowerCentralSeries
add_to_sga "3 VIB 8.2" "special case" AddSubgroup.lowerCentralSeries_zero_eq_bot_iff
add_to_sga "3 VIB 8.2" "special case" Subgroup.lowerCentralSeries
add_to_sga "3 VIB 8.2" "(i), special case" Subgroup.lowerCentralSeries_one_eq_bot_iff
add_to_sga "3 VIB 8.2" "special case" derivedSeries
add_to_sga "3 VIB 8.2" "special case" lowerCentralSeries
add_to_sga "3 VIB 8.2.1" "special case" AddGroup.IsNilpotent
add_to_sga "3 VIB 8.2.1" "special case" AddSubgroup.isNilpotent_iff_lowerCentralSeries
add_to_sga "3 VIB 8.2.1" "partial" AddSubgroup.isNilpotent_of_lowerCentralSeries_eq_bot
add_to_sga "3 VIB 8.2.1" "Nilpotent of class n"
  AddSubgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
add_to_sga "3 VIB 8.2.1" "special case" AddSubgroup.nilpotent_iff_lowerCentralSeries
add_to_sga "3 VIB 8.2.1" "special case" Group.IsNilpotent
add_to_sga "3 VIB 8.2.1" "special case" Group.IsSolvable
add_to_sga "3 VIB 8.2.1" "special case" IsSolvable
add_to_sga "3 VIB 8.2.1" "special case" Subgroup.isNilpotent_iff_lowerCentralSeries
add_to_sga "3 VIB 8.2.1" "Nilpotent of class n"
  Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
add_to_sga "3 VIB 8.2.1" "special case" Subgroup.nilpotent_iff_lowerCentralSeries
add_to_sga "3 VIB 8.2.1" "Nilpotent of class n" lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
add_to_sga "3 VIB 8.2.1" "special case" nilpotent_iff_lowerCentralSeries
add_to_sga "3 VIB 8.4" "(ii), special case" Algebra.Smooth.flat
add_to_sga "3 VIB 8.4" "(ii), special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 VIB 8.4" "(ii)" AlgebraicGeometry.instFlatOfSmooth
add_to_sga "3 VIB 9.2.1" "more general" AlgebraicGeometry.IsImmersion.instιScheme
add_to_sga "3 VIB 9.2.1" "more general"
  AlgebraicGeometry.IsSeparated.instIsClosedImmersionMapDescScheme
add_to_sga "3 VIB 9.2.1" "more general" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_sga "3 VIB 10.0" "quasi-compactness of S" AlgebraicGeometry.Scheme.compactSpace_of_isLimit
add_to_sga "3 VIB 10.0" "(i)"
  AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_sga "3 VIB 10.0" "(i): injectivity"
  AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_sga "3 VIB 10.0" "(i): surjectivity"
  AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
add_to_sga "3 VIB 10.0" "more general" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_sga "3 VIB 10.0" "(i)" AlgebraicGeometry.exists_appTop_π_eq_of_isLimit
add_to_sga "3 VIB 10.0" "(ii), special case" AlgebraicGeometry.exists_isAffineOpen_preimage_eq
add_to_sga "3 VIB 10.0" "(ii), special case" AlgebraicGeometry.exists_preimage_eq
add_to_sga "3 VIB 10.0" "(i), special case"
  AlgebraicGeometry.instPreservesLimitSchemeOppositeCommRingCatRightOpΓOfIsAffineHomMapOfCompactSpaceOfQuasiSeparatedSpaceCarrierCarrierObj
add_to_sga "3 VIB 10.0" "(i), special case" AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone
add_to_sga "3 VIB 10.0" "(i)" RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
add_to_sga "3 VIB 10.1" "étaleness, special case" Algebra.Etale.baseChange
add_to_sga "3 VIB 10.1" "special case" Algebra.Unramified.baseChange
add_to_sga "3 VIB 10.1" "étaleness, special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIB 10.1" "flatness, special case" AlgebraicGeometry.Flat.instMorphismRestrict
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIB 10.1" "finiteness, special case" AlgebraicGeometry.IsFinite.instMorphismRestrict
add_to_sga "3 VIB 10.1" "immersions, special case"
  AlgebraicGeometry.IsImmersion.instMorphismRestrict
add_to_sga "3 VIB 10.1" "properness, special case" AlgebraicGeometry.IsProper.instMorphismRestrict
add_to_sga "3 VIB 10.1" "separatedness" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_sga "3 VIB 10.1" "Y is quasi-compact" AlgebraicGeometry.Scheme.Hom.isCompact_preimage
add_to_sga "3 VIB 10.1" "partial"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeJointlySurjectivePrecoverage
add_to_sga "3 VIB 10.1" "partial"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact
add_to_sga "3 VIB 10.1" "partial"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact_1
add_to_sga "3 VIB 10.1" "sufficiency" AlgebraicGeometry.instLocallyQuasiFiniteFstScheme
add_to_sga "3 VIB 10.1" "special case"
  AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "isomorphisms"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms
add_to_sga "3 VIB 10.1" "special case" Module.Flat.isBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.Etale.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.finite_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case"
  RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.isStandardSmooth_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "special case" RingHom.surjective_isStableUnderBaseChange
add_to_sga "3 VIB 10.8" "partial"
  AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact
add_to_sga "3 VIB 10.8" AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage
add_to_sga "3 VIB 10.8" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFinitePresentationMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 VIB 10.8" "affine case" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_sga "3 VIB 10.10" "more general" Algebra.EssFiniteType.isNoetherianRing
add_to_sga "3 VIB 10.10" "partial" AlgebraicGeometry.instFieldCarrierFunctionField
add_to_sga "3 VIB 10.10" "more general" isNoetherianRing_of_fg
add_to_sga "3 VIB 10.10" is_noetherian_subring_closure
add_to_sga "3 VIB 10.15" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "3 VIB 10.15" "partial" CategoryTheory.Sheaf.epi_of_isLocallySurjective'
add_to_sga "3 VIB 10.15" "more general" CategoryTheory.Sheaf.isLocallySurjective_iff_epi
add_to_sga "3 VIB 10.15" "more general" CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
add_to_sga "3 VIB 11.0" "special case" AlgHom.tensorEqualizerEquiv
add_to_sga "3 VIB 11.0" "special case"
  AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_left
add_to_sga "3 VIB 11.0" "special case" IsBaseChange.of_left_exact
add_to_sga "3 VIB 11.0" "more general" LinearMap.tensorEqLocusEquiv
add_to_sga "3 VIB 11.0" "more general" LinearMap.tensorKerEquiv
add_to_sga "3 VIB 11.1" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIB 11.1" "special case" AlgebraicGeometry.Flat.instMorphismRestrict
add_to_sga "3 VIB 11.1" "special case" AlgebraicGeometry.Flat.instResLE
add_to_sga "3 VIB 11.1" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIB 11.1" "partial" AlgebraicGeometry.QuasiCompact.of_comp
add_to_sga "3 VIB 11.1" "partial" AlgebraicGeometry.QuasiSeparated.of_comp
add_to_sga "3 VIB 11.1" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_sga "3 VIB 11.1" "special case"
  AlgebraicGeometry.instQuasiSeparatedToSpecΓOfQuasiSeparatedSpaceCarrierCarrierCommRingCat
add_to_sga "3 VIB 11.1" "(a), special case" AlgebraicGeometry.pullbackSpecIso'
add_to_sga "3 VIB 11.1" "special case" Module.Flat.instTensorProduct
add_to_sga "3 VIB 11.1" "special case" Module.Flat.isBaseChange
add_to_sga "3 VIB 11.1" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 11.1" "special case" RingHom.Flat.lTensor
add_to_sga "3 VIB 11.1" "special case" RingHom.Flat.tensorProductMap
add_to_sga "3 VIB 11.3" "special case" AlgebraicGeometry.Scheme.Hom.flat_appTop
add_to_sga "3 VIB 11.4" "(†)" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "3 VIB 11.7" "special case" Module.Flat.iff_lTensor_injectiveₛ
add_to_sga "3 VIB 11.7" "special case" Module.Flat.iff_lTensor_preserves_injective_linearMapₛ
add_to_sga "3 VIB 11.7" "special case" Module.Flat.iff_rTensor_injectiveₛ
add_to_sga "3 VIB 11.7" "affine base" Module.Flat.lTensor_preserves_injective_linearMap
add_to_sga "3 VIB 11.7" "special case" Module.Flat.tensorProduct_mapIncl_injective_of_left
add_to_sga "3 VIB 11.7" "special case" Module.Flat.tensorProduct_mapIncl_injective_of_right
add_to_sga "3 VIB 11.7" "special case" TensorProduct.map_injective_of_flat_flat
add_to_sga "3 VIB 11.8" "special case" TensorProduct.submodule_tensor_inf_tensor_submodule
add_to_sga "3 VIB 11.8.0" "special case" CoalgCat
add_to_sga "3 VIB 11.8.0" "special case" Coalgebra
add_to_sga "3 VIB 11.8.0" "CO 2, right counit law" Coalgebra.lTensor_counit_comp_comul
add_to_sga "3 VIB 11.8.0" "special case" Coalgebra.mk
add_to_sga "3 VIB 11.8.0" "CO 2, left counit law" Coalgebra.rTensor_counit_comp_comul
add_to_sga "3 VIB 11.8.0" "coalgebra data Δ" CoalgebraStruct
add_to_sga "3 VIB 11.8.0" "comultiplication Δ" CoalgebraStruct.comul
add_to_sga "3 VIB 11.8.0" "counit ε : C → O_S" CoalgebraStruct.counit
add_to_sga "3 VIB 11.8.0" "partial" CoalgebraStruct.mk
add_to_sga "3 VIB 11.8.0" "special case" FGModuleCat.FGModuleCatEvaluation_apply
add_to_sga "3 VIB 11.8.0" "more general" LinearMap.convAlgebra
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convMul
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convNonUnitalNonAssocRing
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convNonUnitalNonAssocSemiring
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convNonUnitalRing
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convNonUnitalSemiring
add_to_sga "3 VIB 11.8.0" "unit of C∨ given by ε" LinearMap.convOne
add_to_sga "3 VIB 11.8.0" "underlying ring of C∨" LinearMap.convRing
add_to_sga "3 VIB 11.8.0" "partial" LinearMap.convSemiring
add_to_sga "3 VIB 11.8.0" "partial" Module.Dual
add_to_sga "3 VIB 11.8.0" "partial" Module.Dual.eval
add_to_sga "3 VIB 11.8.0" "partial" Module.Dual.eval_apply
add_to_sga "3 VIB 11.10" "affine base" Module.fgSystem.equiv
add_to_sga "3 VIB 11.10" "special case" Submodule.FG.directLimit
add_to_sga "3 VIB 11.11" "(i) ⇒ (ii)" AlgebraicGeometry.Scheme.instIsQuasiAffineOfIsAffine
add_to_sga "3 VIB 11.14" "necessity"
  Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat
add_to_sga "3 VIB 11.14" "necessity" Module.FaithfullyFlat.faithfulSMul
add_to_sga "3 VIB 11.14" "necessity" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_sga "3 VIB 11.14" "necessity" RingHom.FaithfullyFlat.injective
add_to_sga "3 VIB 11.18.1" "more general" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_sga "3 VIB 11.18.1" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_sga "3 VIB 12.1" AlgebraicGeometry.Flat.isIso_of_surjective_of_mono
add_to_sga "3 VIB 12.1" "partial" AlgebraicGeometry.IsClosedImmersion.hasAffineProperty
add_to_sga "3 VIB 12.1" "partial" AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine
add_to_sga "3 VIB 12.1" "u is a homeomorphism" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_sga "3 VIB 12.1" "G is affine" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_sga "3 VIB 12.2" "partial" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_sga "3 VIB 12.2" "partial" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_sga "3 VIB 12.2" "partial" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_sga "3 VIB 12.3" "special case"
  AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed
add_to_sga "3 VIB 12.7" "partial" Module.flat_iff_of_isLocalization
add_to_sga "3 VIB 12.8" "more general" IsDedekindDomain.flat_iff_torsion_eq_bot
add_to_sga "3 VIB 12.8" "partial" IsSMulRegular.of_flat
add_to_sga "3 VIB 12.8" "more general" Module.Flat.flat_iff_torsion_eq_bot_of_isBezout
add_to_sga "3 VIB 12.8" "more general"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_sga "3 VIB 12.8" "more general" Module.Flat.instOfIsDedekindDomainOfIsTorsionFree
add_to_sga "3 VIB 12.9" "partial" AlgebraicGeometry.Flat.isIso_of_surjective_of_mono
add_to_sga "3 VIB 12.9" "Quasi-compactness of ρ" AlgebraicGeometry.QuasiCompact.of_comp
add_to_sga "3 VIB 12.9" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_sga "3 VIB 12.9" "special case" AlgebraicGeometry.quasiCompact_iff_compactSpace
add_to_sga "3 VIB 13.1" "special case" Module.freeLocus
add_to_sga "3 VIB 13.1" "(i), special case" Module.isOpen_freeLocus
