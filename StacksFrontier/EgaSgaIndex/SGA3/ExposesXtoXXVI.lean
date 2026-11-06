module  -- shake: keep-all

import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.EngelSubalgebra
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.CategoryTheory.Pullback
import StacksCore.FieldTheory.PurelyTranscendental
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 3 references registered by name: Exposés X to XXVI

The `add_to_sga` registrations of SGA 3, Exposés X to XXVI, re-exported by
`StacksFrontier.EgaSgaIndex.SGA3`.
-/

add_to_sga "3 X 1.1" DistribMulAction
add_to_sga "3 X 1.2" "partial" ContinuousSMul
add_to_sga "3 X 1.6" Matrix.GeneralLinearGroup.upperRightHom
add_to_sga "3 X 2.5" "partial" AlgebraicGeometry.UniversallyInjective.iff_diagonal
add_to_sga "3 X 2.5" "partial" AlgebraicGeometry.universallyInjective_eq_diagonal
add_to_sga "3 X 3.7" "special case" IsLocalRing.closedPoint_mem_iff
add_to_sga "3 X 3.8" "more general" CommRing.orzechProperty
add_to_sga "3 X 3.8" "more general" IsNoetherian.bijective_of_surjective_endomorphism
add_to_sga "3 X 3.8" "more general" IsNoetherian.injective_of_surjective_endomorphism
add_to_sga "3 X 3.8" "more general" IsNoetherian.injective_of_surjective_of_injective
add_to_sga "3 X 3.8" "more general" OrzechProperty.injective_of_surjective_endomorphism
add_to_sga "3 X 4.0" "partial" AdicCompletion.instIsAdicCompleteMaximalIdeal
add_to_sga "3 X 4.0" "partial" AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing
add_to_sga "3 X 4.2" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 X 4.3" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_sga "3 X 4.3" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_sga "3 X 4.3" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_sga "3 X 4.3" "more general"
  AlgebraicGeometry.exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
add_to_sga "3 X 4.3" "more general"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_sga "3 X 5.4" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 X 5.8" "special case" AddMonoidAlgebra.fg_of_finiteType
add_to_sga "3 X 5.8" "split affine case" AddMonoidAlgebra.finiteType_iff_fg
add_to_sga "3 X 5.8" "split affine case" AddMonoidAlgebra.finiteType_iff_group_fg
add_to_sga "3 X 5.8" "special case" MonoidAlgebra.fg_of_finiteType
add_to_sga "3 X 5.8" "split affine case" MonoidAlgebra.finiteType_iff_fg
add_to_sga "3 X 5.8" "split affine case" MonoidAlgebra.finiteType_iff_group_fg
add_to_sga "3 X 5.8" "special case" MonoidAlgebra.finiteType_of_fg
add_to_sga "3 X 5.11.0" "more general" isClosed_connectedComponent
add_to_sga "3 X 5.12" "more general" AddCommGroup.equiv_free_prod_directSum_zmod
add_to_sga "3 X 6.2" "partial" ProfiniteGrp.limit
add_to_sga "3 X 6.2" "partial" ProfiniteGrp.limitCone
add_to_sga "3 X 6.3" CategoryTheory.Arrow.augmentedCechNerve
add_to_sga "3 X 6.3" CategoryTheory.Arrow.cechNerve
add_to_sga "3 X 6.3" "simplicial operations" CategoryTheory.Arrow.cechNerve_map
add_to_sga "3 X 6.3" "partial" CategoryTheory.CechNerveTerminalFrom.iso
add_to_sga "3 X 6.3" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "3 X 6.3" "degreewise fiber powers"
  CategoryTheory.SimplicialObject.augmentedCechNerve_obj_left_obj
add_to_sga "3 X 6.3" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "3 X 6.3" "partial" CategoryTheory.SimplicialObject.cechNerve_map
add_to_sga "3 X 6.3" "partial" CategoryTheory.SimplicialObject.equivalenceLeftToRight
add_to_sga "3 X 6.3" "partial" ConnectedComponents
add_to_sga "3 X 6.3" "partial" SSet.stdSimplex.isTerminalObj₀
add_to_sga "3 X 6.3" "partial" SSet.π₀
add_to_sga "3 X 6.3" "class of a vertex in π₀" SSet.π₀.mk
add_to_sga "3 X 6.3" "partial" SSet.π₀.mk_eq_mk_iff
add_to_sga "3 X 6.3" "partial" SSet.π₀Functor
add_to_sga "3 X 7.0" AlgebraicGeometry.IsLocallyNoetherian
add_to_sga "3 X 7.0.2" "partial" CommAlgCat.FiniteEtale.fiber
add_to_sga "3 X 7.3" "more general" LinearEquiv.charpoly_conj
add_to_sga "3 X 7.3" LinearMap.charpoly
add_to_sga "3 X 7.3" "basis independence" LinearMap.charpoly_toMatrix
add_to_sga "3 X 7.3" Matrix.charpoly
add_to_sga "3 X 7.3" "basis independence" Matrix.charpoly_toLin
add_to_sga "3 X 7.3" "more general" Matrix.charpoly_units_conj
add_to_sga "3 X 7.3" "more general" Matrix.charpoly_units_conj'
add_to_sga "3 X 8.4" "partial" AlgebraicGeometry.Scheme.ordHom_of_isUnit
add_to_sga "3 X 8.4" "partial" AlgebraicGeometry.Scheme.ord_of_isUnit
add_to_sga "3 X 8.9" "special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
add_to_sga "3 X 8.9" "special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
add_to_sga "3 X 8.9" "partial" AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth
add_to_sga "3 X 8.9" "openness of G′" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_sga "3 X 8.9" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_sga "3 X 8.9" "special case" AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective
add_to_sga "3 X 8.9" "partial" TensorProduct.toIntegralClosure_bijective_of_smooth
add_to_sga "3 X 9.1.1" SSet.toTop
add_to_sga "3 X 9.2.1" CategoryTheory.Functor
add_to_sga "3 X 9.7.1" CategoryTheory.Arrow.augmentedCechNerve
add_to_sga "3 X 9.7.1" CategoryTheory.Arrow.cechNerve
add_to_sga "3 X 9.7.1" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "3 X 9.7.1" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "3 X 9.7.3" "first arrow"
  AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_surjective
add_to_sga "3 XI 1.1" Algebra.FormallyEtale
add_to_sga "3 XI 1.1" Algebra.FormallySmooth
add_to_sga "3 XI 1.1" "affine case" Algebra.FormallyUnramified.ext'
add_to_sga "3 XI 1.1" "affine case" Algebra.FormallyUnramified.lift_unique
add_to_sga "3 XI 1.1" Algebra.Smooth
add_to_sga "3 XI 1.1" Algebra.etale_iff
add_to_sga "3 XI 1.1" AlgebraicGeometry.FormallyUnramified
add_to_sga "3 XI 1.1" "partial" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_sga "3 XI 1.1" "partial" AlgebraicGeometry.FormallyUnramified.of_hom_ext
add_to_sga "3 XI 1.2" "(i)" Algebra.Smooth.flat
add_to_sga "3 XI 1.2" "(i)" Algebra.Smooth.flat_of_isNoetherianRing
add_to_sga "3 XI 1.2" "(i)" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 XI 1.2" "(i)" AlgebraicGeometry.instFlatOfSmooth
add_to_sga "3 XI 1.2" "(i)" RingHom.Smooth.flat
add_to_sga "3 XI 1.3" "special case" Algebra.FormallyUnramified.iff_isSeparable
add_to_sga "3 XI 1.3" "(ii)" Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
add_to_sga "3 XI 1.3" "(i) a) ⇒ d)" Algebra.FormallyUnramified.isField_of_isAlgClosed_of_isLocalRing
add_to_sga "3 XI 1.3" "(i) a) ⇒ b), affine case"
  Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul
add_to_sga "3 XI 1.3" "(i) a) ⇒ d)" Algebra.FormallyUnramified.isRadical_map_isMaximal
add_to_sga "3 XI 1.3" "(i) a) ⇒ d)" Algebra.FormallyUnramified.isReduced_of_field
add_to_sga "3 XI 1.3" "(i) e), (ii)" Algebra.FormallyUnramified.isSeparable
add_to_sga "3 XI 1.3" "special case" Algebra.FormallyUnramified.of_isSeparable
add_to_sga "3 XI 1.3" "(ii)" Algebra.FormallyUnramified.of_map_maximalIdeal
add_to_sga "3 XI 1.3" "(i)" Algebra.IsUnramifiedAt.residueField
add_to_sga "3 XI 1.3" "(ii)" Algebra.instFiniteResidueFieldOfFormallyUnramified
add_to_sga "3 XI 1.3" "(ii)" Algebra.instFiniteResidueFieldOfIsUnramifiedAt
add_to_sga "3 XI 1.3" "(ii)" Algebra.instIsSeparableResidueFieldOfFormallyUnramified
add_to_sga "3 XI 1.3" "(ii)" Algebra.instIsSeparableResidueFieldOfIsUnramifiedAt
add_to_sga "3 XI 1.3" "(ii), special case" Algebra.isUnramifiedAt_iff_map_eq
add_to_sga "3 XI 1.3" "(ii)"
  AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
add_to_sga "3 XI 1.3" "(i) b) ⇒ a)"
  AlgebraicGeometry.FormallyUnramified.instOfIsOpenImmersionDiagonalScheme
add_to_sga "3 XI 1.3" "(i) a) ⇒ b)" AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
add_to_sga "3 XI 1.4" "special case" Algebra.Etale.iff_formallyUnramified_and_smooth
add_to_sga "3 XI 1.4" "affine" Algebra.Etale.instSmooth
add_to_sga "3 XI 1.4" "affine" Algebra.Etale.instUnramified
add_to_sga "3 XI 1.4" "affine" Algebra.Etale.of_formallyUnramified_of_flat
add_to_sga "3 XI 1.4" "(i)" Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat
add_to_sga "3 XI 1.4" "more general" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_sga "3 XI 1.4" "étale implies unramified" AlgebraicGeometry.Etale.instFormallyUnramified
add_to_sga "3 XI 1.4" "étale implies smooth" AlgebraicGeometry.Etale.instSmooth
add_to_sga "3 XI 1.4" "(i)" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_sga "3 XI 1.4" "special case" RingHom.Etale.eq_formallyUnramified_and_smooth
add_to_sga "3 XI 1.4" "affine" RingHom.Etale.formallyUnramified
add_to_sga "3 XI 1.4" "(i), special case" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_sga "3 XI 1.4" "special case" RingHom.etale_iff_formallyUnramified_and_smooth
add_to_sga "3 XI 1.5" "partial" Algebra.FormallyUnramified.lift_unique
add_to_sga "3 XI 1.5" "partial" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_sga "3 XI 1.6" "special case" Algebra.FormallyEtale
add_to_sga "3 XI 1.6" "partial" Algebra.FormallyEtale.comp_bijective
add_to_sga "3 XI 1.6" "special case" Algebra.FormallyEtale.iff_comp_bijective
add_to_sga "3 XI 1.6" "partial" Algebra.FormallySmooth.exists_lift
add_to_sga "3 XI 1.6" "special case" Algebra.FormallySmooth.iff_comp_surjective
add_to_sga "3 XI 1.6" "partial" Algebra.FormallyUnramified.lift_unique
add_to_sga "3 XI 1.6" "special case" AlgebraicGeometry.FormallyUnramified
add_to_sga "3 XI 1.6" "represented functors" AlgebraicGeometry.FormallyUnramified.hom_ext
add_to_sga "3 XI 1.6" "partial"
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme
add_to_sga "3 XI 1.6" "represented functors" AlgebraicGeometry.FormallyUnramified.of_hom_ext
add_to_sga "3 XI 1.9" "special case" Algebra.IsStandardSmooth.free_kaehlerDifferential
add_to_sga "3 XI 1.9" "special case" Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
add_to_sga "3 XI 1.9" "partial" Algebra.SubmersivePresentation.free_kaehlerDifferential
add_to_sga "3 XI 1.9" "partial" DualNumber
add_to_sga "3 XI 1.9" "special case" RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
add_to_sga "3 XI 1.9" TrivSqZeroExt
add_to_sga "3 XI 1.9" TrivSqZeroExt.algebra'
add_to_sga "3 XI 1.9" TrivSqZeroExt.algebraBase
add_to_sga "3 XI 1.9" TrivSqZeroExt.fstHom
add_to_sga "3 XI 1.9" TrivSqZeroExt.inlAlgHom
add_to_sga "3 XI 1.9" TrivSqZeroExt.instAlgebra
add_to_sga "3 XI 1.9" TrivSqZeroExt.kerIdeal
add_to_sga "3 XI 1.9" "V² = 0" TrivSqZeroExt.kerIdeal_sq
add_to_sga "3 XI 3.2" "partial" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_sga "3 XI 3.2" "partial" AlgebraicGeometry.preservesLimitsOfSize_algSpec
add_to_sga "3 XI 3.2" "Affine case" CommRingCat.isFinitelyPresentable_under
add_to_sga "3 XI 3.2" "special case" CommRingCat.preservesFilteredColimits_coyoneda
add_to_sga "3 XI 3.4" "more general"
  AlgebraicGeometry.Scheme.LocalRepresentability.instIsIsoSheafZariskiTopologyTypeYonedaGluedToSheaf
add_to_sga "3 XI 3.4" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable
add_to_sga "3 XI 3.4" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.representableBy
add_to_sga "3 XI 3.4" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.yonedaIsoSheaf
add_to_sga "3 XI 3.4" "special case" AlgebraicGeometry.isSheaf_propQCTopology_iff
add_to_sga "3 XI 3.4" "special case" AlgebraicGeometry.isSheaf_type_propQCTopology_iff
add_to_sga "3 XI 3.4" "more general" CategoryTheory.Presheaf.IsSheaf.of_le
add_to_sga "3 XI 3.4" "more general" CategoryTheory.Presieve.isSheaf_of_le
add_to_sga "3 XI 3.6" "special case" AlgebraicGeometry.Surjective
add_to_sga "3 XI 3.7" "more general" CategoryTheory.Limits.limit
add_to_sga "3 XI 3.9" "partial" AlgebraicGeometry.Flat.epi_of_flat_of_surjective
add_to_sga "3 XI 3.9" "partial" AlgebraicGeometry.Flat.isIso_of_surjective_of_mono
add_to_sga "3 XI 3.9" AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "3 XI 3.9" "special case" CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
add_to_sga "3 XI 3.13" "For G = S[t], partial" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_sga "3 XI 4.3" "partial" Algebra.Smooth.exists_subalgebra_fg
add_to_sga "3 XI 4.3" "special case" AlgebraicGeometry.AffineScheme.createsLimitsForgetToScheme
add_to_sga "3 XI 4.3" "special case" AlgebraicGeometry.AffineScheme.Γ_preservesLimits
add_to_sga "3 XI 4.3" "partial" AlgebraicGeometry.IsSeparated.instIsMultiplicativeScheme
add_to_sga "3 XI 4.3" "special case" AlgebraicGeometry.IsSeparated.instMap
add_to_sga "3 XI 4.3" "F is separated over T" AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_sga "3 XI 4.3" "T is separated over S" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_sga "3 XI 6.9" "partial" Algebra.Smooth.exists_finiteType
add_to_sga "3 XI 6.9" "partial" Algebra.Smooth.exists_subalgebra_fg
add_to_sga "3 XII 1.16" "partial" Group.IsNilpotent
add_to_sga "3 XII 2.2" "special case" Subgroup.card_eq_iff_eq_top
add_to_sga "3 XII 2.2" "special case" Subgroup.eq_of_le_of_card_ge
add_to_sga "3 XII 2.2" "special case" Subgroup.eq_top_of_card_eq
add_to_sga "3 XII 2.2" "special case" Subgroup.eq_top_of_le_card
add_to_sga "3 XII 4.9" "Forward direction" LieAlgebra.isNilpotent_iff_forall
add_to_sga "3 XII 4.9" "partial" LieModule.isNilpotent_toEnd_of_isNilpotent
add_to_sga "3 XII 4.9" "Vanishing step" Module.End.eq_zero_of_isNilpotent_isSemisimple
add_to_sga "3 XII 4.9" "Vanishing step" Module.End.eq_zero_of_isNilpotent_of_isFinitelySemisimple
add_to_sga "3 XII 6.7" Group.IsNilpotent
add_to_sga "3 XII 9.8" "more general" FDRep.instInjectiveOfNeZeroCastCard
add_to_sga "3 XII 9.8" "more general" FDRep.instProjectiveOfNeZeroCastCard
add_to_sga "3 XII 9.8" "more general" MonoidAlgebra.Submodule.instIsSemisimpleModule
add_to_sga "3 XII 9.8" "more general" MonoidAlgebra.Submodule.instIsSemisimpleRepresentation
add_to_sga "3 XII 9.8" "more general" MonoidAlgebra.Submodule.instIsSemisimpleRingAddMonoidAlgebra
add_to_sga "3 XII 9.8" "more general" Rep.instInjective
add_to_sga "3 XII 9.8" "more general" Rep.instProjective
add_to_sga "3 XIII 4.1" "more general" LieAlgebra.zeroRootSubalgebra
add_to_sga "3 XIII 4.1" "more general" LieAlgebra.zeroRootSubalgebra_normalizer_eq_self
add_to_sga "3 XIII 4.1" LieSubalgebra.engel
add_to_sga "3 XIII 4.1" LieSubalgebra.normalizer_engel
add_to_sga "3 XIII 4.1" "special case" LieSubalgebra.normalizer_eq_self_of_engel_le
add_to_sga "3 XIII 4.2" "(a)" LinearMap.isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank
add_to_sga "3 XIII 4.2" "First assertion" LinearMap.nilRank_le_natTrailingDegree_charpoly
add_to_sga "3 XIII 4.3" "Forward implication" LieModule.maxGenEigenSpace_toEnd_eq_top
add_to_sga "3 XIII 4.4" "more general" LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq
add_to_sga "3 XIII 4.4" LieSubalgebra.IsCartanSubalgebra
add_to_sga "3 XIII 4.4" "(ii) ⇒ (iii)" LieSubalgebra.normalizer_engel
add_to_sga "3 XIII 4.4" "(ii bis) ⇒ (iii)" LieSubalgebra.normalizer_eq_self_of_engel_le
add_to_sga "3 XIII 4.7" "partial" LieSubmodule.baseChange
add_to_sga "3 XIV 1.2" "partial" LieAlgebra.exists_isCartanSubalgebra_engel
add_to_sga "3 XIV 1.2" "partial" LieAlgebra.exists_isCartanSubalgebra_engel_of_finrank_le_card
add_to_sga "3 XIV 1.2" "Over an infinite field k" LieAlgebra.exists_isRegular
add_to_sga "3 XIV 1.2" "Over an infinite field k" LieAlgebra.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 1.2" "Over an infinite field k" LieModule.exists_isRegular
add_to_sga "3 XIV 1.2" "Over an infinite field k" LieModule.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 1.5" AlgebraicClosure
add_to_sga "3 XIV 2.1" "partial" LieAlgebra.isEngelian_of_isNoetherian
add_to_sga "3 XIV 2.1" "more general" LieAlgebra.isNilpotent_iff_forall
add_to_sga "3 XIV 2.1" "partial" LieAlgebra.nilpotent_ad_of_nilpotent_algebra
add_to_sga "3 XIV 2.1" "more general" LieModule.IsNilpotent
add_to_sga "3 XIV 2.1" "partial" LieModule.exists_forall_pow_toEnd_eq_zero
add_to_sga "3 XIV 2.1" "more general" LieModule.isNilpotent_iff_forall
add_to_sga "3 XIV 2.1" "more general" LieModule.isNilpotent_iff_forall'
add_to_sga "3 XIV 2.1" "partial" LieModule.isNilpotent_toEnd_of_isNilpotent
add_to_sga "3 XIV 2.1" LieRing.IsNilpotent
add_to_sga "3 XIV 2.1" "partial" LieSubalgebra.isNilpotent_of_forall_le_engel
add_to_sga "3 XIV 2.2" "special case" LieModule.instIsNilpotentTensor
add_to_sga "3 XIV 2.4" "special case" LieSubalgebra.IsCartanSubalgebra
add_to_sga "3 XIV 2.5" "special case" LieAlgebra.IsRegular
add_to_sga "3 XIV 2.8" IsLocallyConstant
add_to_sga "3 XIV 2.8" "partial" IsLocallyConstant.continuous
add_to_sga "3 XIV 2.8" "partial" LocallyConstant.continuous
add_to_sga "3 XIV 2.11" "special case" LieAlgebra.exists_isCartanSubalgebra_engel
add_to_sga "3 XIV 2.13" "special case" IsNilpotent.charpoly_eq_X_pow_finrank
add_to_sga "3 XIV 2.13" "special case" LinearMap.aeval_eq_aeval_mod_charpoly
add_to_sga "3 XIV 2.13" "special case" LinearMap.aeval_self_charpoly
add_to_sga "3 XIV 2.13" "partial" LinearMap.charpoly_constantCoeff_eq_zero_iff
add_to_sga "3 XIV 2.13" "special case" LinearMap.charpoly_eq_X_pow_iff
add_to_sga "3 XIV 2.13" "special case" LinearMap.charpoly_nilpotent_tfae
add_to_sga "3 XIV 2.13" "partial" LinearMap.det_eq_sign_charpoly_coeff
add_to_sga "3 XIV 2.13" "special case" LinearMap.isNilpotent_iff_charpoly
add_to_sga "3 XIV 2.13" "special case" Matrix.aeval_self_charpoly
add_to_sga "3 XIV 2.13" "partial" Matrix.det_eq_sign_charpoly_coeff
add_to_sga "3 XIV 2.13" "special case" Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
add_to_sga "3 XIV 2.13" Module.AEval.instModulePolynomial
add_to_sga "3 XIV 2.13" Module.End.genEigenspace
add_to_sga "3 XIV 2.13" Module.End.maxGenEigenspace
add_to_sga "3 XIV 2.13" Polynomial.aeval
add_to_sga "3 XIV 2.13" "spanning clause" Submodule.iSup_torsionBy_eq_torsionBy_prod
add_to_sga "3 XIV 2.13" "directness clause" Submodule.supIndep_torsionBy
add_to_sga "3 XIV 2.13" "partial" Submodule.torsionBySet_isInternal
add_to_sga "3 XIV 2.13" "partial" Submodule.torsionBy_isInternal
add_to_sga "3 XIV 2.15" "more general"
  CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
add_to_sga "3 XIV 2.17" AlgebraicGeometry.Scheme.IsRationalOver
add_to_sga "3 XIV 2.17" "more general" LieAlgebra.exists_isRegular
add_to_sga "3 XIV 2.17" "more general" LieAlgebra.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 2.17" "more general" LieModule.exists_isRegular
add_to_sga "3 XIV 2.17" "more general" LieModule.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 2.17" PurelyTranscendental
add_to_sga "3 XIV 3.10" "more general" LieAlgebra.exists_isRegular
add_to_sga "3 XIV 3.10" "more general" LieAlgebra.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 3.10" "more general" LieModule.exists_isRegular
add_to_sga "3 XIV 3.10" "more general" LieModule.exists_isRegular_of_finrank_le_card
add_to_sga "3 XIV 3.18" "partial" RootPairing.Base.toWeightBasis
add_to_sga "3 XIV 3.18" "partial" RootPairing.Base.toWeightBasisInt
add_to_sga "3 XIV 3.21" "more general" IsAzumaya
add_to_sga "3 XIV 5.3" "h ⊆ Nil(a" LieAlgebra.le_zeroRootSubalgebra
add_to_sga "3 XIV 5.3" "h ⊆ Nil(a" LieAlgebra.toLieSubmodule_le_rootSpace_zero
add_to_sga "3 XIV 5.3" "more general" LieAlgebra.zeroRootSubalgebra
add_to_sga "3 XIV 5.3" LieSubalgebra.engel
add_to_sga "3 XIV 6.1" AlgebraicGeometry.Scheme.IsRationalOver
add_to_sga "3 XIV 6.1" PurelyTranscendental
add_to_sga "3 XIV Lemma5" "partial" RootPairing.Base.IsPos.reflectionPerm
add_to_sga "3 XIV Lemma5" "sign reversal of ±a_i" RootPairing.reflection_apply_self
add_to_sga "3 XIV Lemma5" "sign reversal of ±a_i" RootPairing.rootSpanMem_reflectionPerm_self
add_to_sga "3 XIX 2.1" "special case" Algebra.FinitePresentation.baseChange
add_to_sga "3 XIX 2.1" "special case" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 XIX 2.1" "special case" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_sga "3 XIX 2.1" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 XIX 2.1" "open base change" AlgebraicGeometry.Flat.instMorphismRestrict
add_to_sga "3 XIX 2.1" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 XIX 2.1" "partial"
  AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
add_to_sga "3 XIX 2.1" "more general"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 XIX 2.1" "base change to Spec κ(s)"
  AlgebraicGeometry.instGeometricallyIntegralFiberToSpecResidueField
add_to_sga "3 XIX 2.1" "more general" AlgebraicGeometry.instGeometricallyIntegralFstScheme
add_to_sga "3 XIX 2.1" "special case" AlgebraicGeometry.instGeometricallyIntegralMorphismRestrict
add_to_sga "3 XIX 2.1" "more general" AlgebraicGeometry.instGeometricallyIntegralSndScheme
add_to_sga "3 XIX 2.1" "(ii)" AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral
add_to_sga "3 XIX 2.1" "base change to Spec κ(y)" AlgebraicGeometry.instIsAffineFiberOfIsAffineHom
add_to_sga "3 XIX 2.1" "more general"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically
add_to_sga "3 XIX 2.1" "more general"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyIntegral
add_to_sga "3 XIX 2.1" "(i)" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "3 XIX 2.1" "more general" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "3 XIX 2.1" "affine case" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_sga "3 XIX 2.1" "special case" Module.Flat.isBaseChange
add_to_sga "3 XIX 2.1" "special case" Module.Flat.of_flat_tensorProduct
add_to_sga "3 XIX 2.1" "special case" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_sga "3 XIX 2.1" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 XIX 2.1" "special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_sga "3 XIX 2.1" "special case" RingHom.Smooth.ofLocalizationSpanTarget
add_to_sga "3 XIX 2.1" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_sga "3 XIX 4.11" "partial" Choose.gcd_choose_eq_minFac_of_isPrimePow
add_to_sga "3 XIX 4.11" "partial" Choose.gcd_choose_eq_one_of_not_isPrimePow
add_to_sga "3 XIX 5.2" LinearMap.toMatrix
add_to_sga "3 XIX 5.2" LinearMap.toMatrixAlgEquiv
add_to_sga "3 XIX 5.2" Matrix.Represents
add_to_sga "3 XIX 5.2" Matrix.toLinAlgEquiv
add_to_sga "3 XIX 5.13" "partial" AlgebraicGeometry.instIsAffineHomιBasicOpen
add_to_sga "3 XV 1.1" "partial" RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero
add_to_sga "3 XV 1.4" "partial" AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk
add_to_sga "3 XV 1.4" "partial" AlgebraicGeometry.SpecToEquivOfLocalRing
add_to_sga "3 XV 2.7" "partial" LaurentPolynomial
add_to_sga "3 XV 2.8" Ideal.map
add_to_sga "3 XV 2.10" "more general" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "3 XV 2.10" "more general" CategoryTheory.Abelian.Ext.covariant_sequence_exact₂
add_to_sga "3 XV 2.10" "more general" CategoryTheory.Abelian.Ext.covariant_sequence_exact₂'
add_to_sga "3 XV 2.10" IsReduced
add_to_sga "3 XV 2.10" IsRegular
add_to_sga "3 XV 2.10" LaurentPolynomial
add_to_sga "3 XV 3.3" "special case"
  PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
add_to_sga "3 XV 3.8" "special case" Ideal.map_injective_of_faithfullyFlat
add_to_sga "3 XV 3.8" "partial" Module.Flat.isBaseChange
add_to_sga "3 XV 4.6" "more general" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "3 XV 4.7" "more general" IsDedekindDomain.flat_iff_torsion_eq_bot
add_to_sga "3 XV 4.7" "more general" Module.Flat.flat_iff_torsion_eq_bot_of_isBezout
add_to_sga "3 XV 4.7" "more general"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_sga "3 XV 4.7" "partial" Module.Flat.instOfIsDedekindDomainOfIsTorsionFree
add_to_sga "3 XV 4.7" "partial" Module.Flat.torsion_eq_bot
add_to_sga "3 XV 5.5" "more general" AlgebraicGeometry.Scheme.GlueData.glued
add_to_sga "3 XV 5.5" "more general" AlgebraicGeometry.Scheme.IsLocallyDirected.glueData
add_to_sga "3 XV 5.5" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.glueData
add_to_sga "3 XV 5.5" "partial"
  AlgebraicGeometry.Scheme.LocalRepresentability.instIsOpenImmersionToGlued
add_to_sga "3 XV 5.5" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.representableBy
add_to_sga "3 XV 5.5" "more general" AlgebraicGeometry.Scheme.LocalRepresentability.toGlued
add_to_sga "3 XV 6.5" "partial" AlgebraicGeometry.instSmoothFstScheme
add_to_sga "3 XV 6.5" "partial" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "3 XV 8.10" "(iv)" AlgebraicGeometry.IsSeparated.valuativeCriterion
add_to_sga "3 XV 8.10" "(i)" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "3 XVI 2.1" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "3 XVI 2.1" "Remark a)" CategoryTheory.IsKernelPair.cancel_right_of_mono
add_to_sga "3 XVI 2.1" "Remark a)" CategoryTheory.IsKernelPair.comp_of_mono
add_to_sga "3 XVII 1.6" "Smoothness clause" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "3 XVII 3.2" "special case" Rep.quotientToInvariants
add_to_sga "3 XVII 3.2" "special case" Rep.quotientToInvariantsFunctor
add_to_sga "3 XVII 4.3.2" IsPurelyInseparable.iterateFrobenius
add_to_sga "3 XVII 4.3.2" IsPurelyInseparable.iterateFrobeniusₛₗ
add_to_sga "3 XVII 5.2.1" "partial" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "3 XVII 5.2.1" "partial" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "3 XVII 5.2.1" "partial"
  Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPrime
add_to_sga "3 XVII 5.2.1" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "3 XVII 5.3.1" "partial" AlgebraicGeometry.Scheme.isAffine_of_isLimit
add_to_sga "3 XVII 5.3.1" "partial" AlgebraicGeometry.Scheme.nonempty_of_isLimit
add_to_sga "3 XVII 5.3.1" "partial" AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty
add_to_sga "3 XVII 5.3.1" "partial" AlgebraicGeometry.exists_mem_of_isClosed_of_nonempty'
add_to_sga "3 XVII 5.9" "more general" groupCohomology.H1IsoOfIsTrivial
add_to_sga "3 XVIII 1.4" "special case" AlgebraicGeometry.ext_of_apply_eq
add_to_sga "3 XVIII 1.4" "special case" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_sga "3 XVIII 1.4" "special case" AlgebraicGeometry.ext_of_isDominant
add_to_sga "3 XVIII 1.4" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_sga "3 XVIII 1.4" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated'
add_to_sga "3 XVIII 1.4" CategoryTheory.Functor.relativelyRepresentable
add_to_sga "3 XVIII 1.4" CategoryTheory.MorphismProperty.relative
add_to_sga "3 XVIII 1.5" "representatives f" AlgebraicGeometry.Scheme.PartialMap
add_to_sga "3 XVIII 1.5" "special case" AlgebraicGeometry.Scheme.PartialMap.instSetoid
add_to_sga "3 XVIII 1.5" "special case" AlgebraicGeometry.Scheme.RationalMap.IsOver
add_to_sga "3 XVIII 2.1" CategoryTheory.GrothendieckTopology
add_to_sga "3 XX 1.10" AlgebraicGeometry.Spec
add_to_sga "3 XX 1.10" IsAdicComplete
add_to_sga "3 XX 1.13" MvPolynomial
add_to_sga "3 XX 1.13" MvPolynomial.IsHomogeneous
add_to_sga "3 XX 1.13" MvPolynomial.homogeneousSubmodule
add_to_sga "3 XXI 1.1.1" "partial" LinearMap.toPerfPair
add_to_sga "3 XXI 1.1.1" "partial" Module.Dual
add_to_sga "3 XXI 1.1.1" "partial" Module.Finite
add_to_sga "3 XXI 1.1.1" "partial" Module.Free
add_to_sga "3 XXI 1.1.1" Module.dualPairing
add_to_sga "3 XXI 1.1.1" "more general" Module.preReflection
add_to_sga "3 XXI 1.1.1" RootDatum
add_to_sga "3 XXI 1.1.1" "more general" RootPairing
add_to_sga "3 XXI 1.1.1" RootPairing.Equiv.reflection
add_to_sga "3 XXI 1.1.1" RootPairing.coroot
add_to_sga "3 XXI 1.1.1" RootPairing.coroot'
add_to_sga "3 XXI 1.1.1" RootPairing.mk'
add_to_sga "3 XXI 1.1.1" "(1)" RootPairing.reflection
add_to_sga "3 XXI 1.1.1" RootPairing.root
add_to_sga "3 XXI 1.1.2" "(2)" RootPairing.Equiv.reflection_inv
add_to_sga "3 XXI 1.1.2" "partial" RootPairing.coreflection_apply_self
add_to_sga "3 XXI 1.1.3" "R* = −R*" RootPairing.corootSpanMem_reflectionPerm_self
add_to_sga "3 XXI 1.1.3" "R* = −R*" RootPairing.coroot_eq_neg_iff
add_to_sga "3 XXI 1.1.3" "0 ∉ R" RootPairing.ne_zero
add_to_sga "3 XXI 1.1.3" "0 ∉ R*" RootPairing.ne_zero'
add_to_sga "3 XXI 1.1.3" "R* = −R*" RootPairing.neg_coroot_mem
add_to_sga "3 XXI 1.1.3" "R* = −R*" RootPairing.neg_mem_range_coroot_iff
add_to_sga "3 XXI 1.1.3" "R = −R" RootPairing.neg_mem_range_root_iff
add_to_sga "3 XXI 1.1.3" "R = −R" RootPairing.neg_root_mem
add_to_sga "3 XXI 1.1.3" "R = −R" RootPairing.root_eq_neg_iff
add_to_sga "3 XXI 1.1.3" "0 ∉ R*" RootPairing.zero_notMem_range_coroot
add_to_sga "3 XXI 1.1.3" "0 ∉ R" RootPairing.zero_notMem_range_root
add_to_sga "3 XXI 1.1.5" "more general" RootPairing.flip
add_to_sga "3 XXI 1.1.5" "more general" RootPairing.flip_coroot
add_to_sga "3 XXI 1.1.6" AddSubgroup.closure
add_to_sga "3 XXI 1.1.6" "rank(M*) = rank(M)" Module.Basis.dual_rank_eq
add_to_sga "3 XXI 1.1.6" "rank(M*) = rank(M)" Module.dual_rank_eq
add_to_sga "3 XXI 1.1.6" Module.finrank
add_to_sga "3 XXI 1.1.6" "more general" Module.finrank_quotient_add_finrank_le
add_to_sga "3 XXI 1.1.6" Module.rank
add_to_sga "3 XXI 1.1.6" RootPairing.corootSpan
add_to_sga "3 XXI 1.1.6" "special case" RootPairing.finrank_corootSpanIn_int
add_to_sga "3 XXI 1.1.6" "more general" RootPairing.finrank_corootSpan_eq
add_to_sga "3 XXI 1.1.6" "more general" RootPairing.finrank_corootSpan_eq'
add_to_sga "3 XXI 1.1.6" "special case" RootPairing.finrank_rootSpanIn_int
add_to_sga "3 XXI 1.1.6" RootPairing.rootSpan
add_to_sga "3 XXI 1.1.6" "special case" RootPairing.rootSpan_eq_top_iff
add_to_sga "3 XXI 1.1.6" "more general" Submodule.finrank_le
add_to_sga "3 XXI 1.1.6" "more general" Submodule.rank_le
add_to_sga "3 XXI 1.1.6" Submodule.span
add_to_sga "3 XXI 1.1.8" RootPairing.range_weylGroup_weightHom
add_to_sga "3 XXI 1.1.8" RootPairing.weylGroup
add_to_sga "3 XXI 1.1.8" "W(R) acts on M" RootPairing.weylGroupRootRep
add_to_sga "3 XXI 1.1.8" "W(R) acts on R" RootPairing.weylGroupToPerm
add_to_sga "3 XXI 1.1.8" "W(R) stabilizes R" RootPairing.weylGroup_apply_root
add_to_sga "3 XXI 1.1.9" "more general" RootPairing.reflection_dualMap_eq_coreflection
add_to_sga "3 XXI 1.1.11" "more general" RootPairing.reflection_dualMap_eq_coreflection
add_to_sga "3 XXI 1.1.12" "Image clause" RootPairing.range_weylGroup_coweightHom
add_to_sga "3 XXI 1.1.13" RootPairing.Equiv.reflection
add_to_sga "3 XXI 1.1.13" "partial" RootPairing.range_weylGroupToPerm
add_to_sga "3 XXI 1.1.13" "partial" RootPairing.range_weylGroup_coweightHom
add_to_sga "3 XXI 1.1.13" "partial" RootPairing.range_weylGroup_weightHom
add_to_sga "3 XXI 1.1.13" "Under N ≅ M*" RootPairing.reflection_dualMap_eq_coreflection
add_to_sga "3 XXI 1.1.13" RootPairing.weylGroup
add_to_sga "3 XXI 1.1.13" RootPairing.weylGroup.ofIdx
add_to_sga "3 XXI 1.1.13" "Action of W on M" RootPairing.weylGroupRootRep
add_to_sga "3 XXI 1.1.13" "partial" RootPairing.weylGroupToPerm
add_to_sga "3 XXI 1.1.13" "partial" RootPairing.weylGroup_apply_root
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.CoPolarization_apply
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.CorootForm
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.Polarization
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.Polarization_apply
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.RootForm
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.corootForm_self_smul_root
add_to_sga "3 XXI 1.2.1" "(10)" RootPairing.coroot_eq_polarizationEquiv_apply_root
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.exists_ge_zero_eq_rootForm
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.posRootForm_posForm_pos_of_ne_zero
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.posRootForm_rootFormIn_posDef
add_to_sga "3 XXI 1.2.1" "(9)" RootPairing.rootFormIn_isSymm
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.rootFormIn_self_smul_coroot
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.rootForm_pos_of_ne_zero
add_to_sga "3 XXI 1.2.1" "(8), special case" RootPairing.rootForm_reflection_reflection_apply
add_to_sga "3 XXI 1.2.1" "more general" RootPairing.rootForm_self_sum_of_squares
add_to_sga "3 XXI 1.2.1" RootPairing.rootForm_symmetric
add_to_sga "3 XXI 1.2.1" RootPairing.toLinearMap_apply_apply_Polarization
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.zero_le_posForm
add_to_sga "3 XXI 1.2.1" "(7)" RootPairing.zero_le_rootForm
add_to_sga "3 XXI 1.2.4" "more general" RootPairing.finrank_corootSpan_eq
add_to_sga "3 XXI 1.2.4" "more general" RootPairing.finrank_corootSpan_eq'
add_to_sga "3 XXI 1.2.6" "Positivity clause" RootPairing.exists_ge_zero_eq_rootForm
add_to_sga "3 XXI 1.2.6" "Nondegeneracy of (p(x)" RootPairing.posRootForm_posForm_nondegenerate
add_to_sga "3 XXI 1.2.6" "more general" RootPairing.posRootForm_posForm_pos_of_ne_zero
add_to_sga "3 XXI 1.2.6" "more general" RootPairing.posRootForm_rootFormIn_posDef
add_to_sga "3 XXI 1.2.6" "special case" RootPairing.rootForm_nondegenerate
add_to_sga "3 XXI 1.2.6" "more general" RootPairing.rootForm_pos_of_ne_zero
add_to_sga "3 XXI 1.2.6" "partial" RootPairing.rootForm_restrict_nondegenerate_of_ordered
add_to_sga "3 XXI 1.2.6" "Positivity (B(x" RootPairing.zero_le_posForm
add_to_sga "3 XXI 2.1.1" "inverse coroot scaling" RootPairing.coroot_eq_smul_coroot_iff
add_to_sga "3 XXI 2.1.1" "inverse coroot scaling" RootPairing.smul_coroot_eq_of_root_eq_smul
add_to_sga "3 XXI 2.1.3" RootPairing.IsReduced
add_to_sga "3 XXI 2.2.1" "more general"
  RootPairing.RootPositiveForm.pairingIn_mul_eq_pairingIn_mul_swap
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.IsOrthogonal.coreflection_apply_left
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.IsOrthogonal.coreflection_apply_right
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.IsOrthogonal.reflection_apply_left
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.IsOrthogonal.reflection_apply_right
add_to_sga "3 XXI 2.2.2" "(iii)" RootPairing.isFixedPt_reflectionPerm_iff
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.isFixedPt_reflection_of_isOrthogonal
add_to_sga "3 XXI 2.2.2" "(i) ⇔ ((i) and (i bis))" RootPairing.isOrthogonal_iff_pairing_eq_zero
add_to_sga "3 XXI 2.2.2" "(i)" RootPairing.pairingIn_eq_zero_iff
add_to_sga "3 XXI 2.2.2" "(i) ⇔ (i bis)" RootPairing.pairing_eq_zero_iff
add_to_sga "3 XXI 2.2.2" "(i) ⇔ (i bis)" RootPairing.pairing_eq_zero_iff'
add_to_sga "3 XXI 2.2.2" "(i) ⇒ (iii)" RootPairing.reflectionPerm_eq_of_pairing_eq_zero
add_to_sga "3 XXI 2.2.2" "(iii)" RootPairing.reflectionPerm_eq_of_pairing_eq_zero'
add_to_sga "3 XXI 2.2.3" RootPairing.IsOrthogonal
add_to_sga "3 XXI 2.2.3" "(i)" RootPairing.isOrthogonal_iff_pairing_eq_zero
add_to_sga "3 XXI 2.2.4" "forward implication" RootPairing.IsOrthogonal.flip
add_to_sga "3 XXI 2.2.6" RootPairing.CorootForm
add_to_sga "3 XXI 2.3.3" "more general" RootPairing.root_add_root_mem_of_pairingIn_neg
add_to_sga "3 XXI 2.3.3" "more general" RootPairing.root_sub_root_mem_of_pairingIn_pos
add_to_sga "3 XXI 2.3.4" "Simple-root case" RootPairing.Base.cartanMatrix_eq_neg_chainTopCoeff
add_to_sga "3 XXI 2.3.5" "special case" LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff
add_to_sga "3 XXI 2.3.5" "special case" LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff_mem
add_to_sga "3 XXI 2.3.5" "partial" RootPairing.Iic_chainBotCoeff_eq
add_to_sga "3 XXI 2.3.5" "more general"
  RootPairing.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx
add_to_sga "3 XXI 2.3.5" "partial" RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.root_add_zsmul_mem_range_iff
add_to_sga "3 XXI 2.3.5" "partial" RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.root_sub_zsmul_mem_range_iff
add_to_sga "3 XXI 2.3.5" "more general"
  RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.setOfPred_root_add_zsmul_mem_eq_Icc
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.setOfPred_root_sub_zsmul_mem_eq_Icc
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.setOf_root_add_zsmul_eq_Icc_of_linearIndependent
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.setOf_root_add_zsmul_mem_eq_Icc
add_to_sga "3 XXI 2.3.5" "more general" RootPairing.setOf_root_sub_zsmul_mem_eq_Icc
add_to_sga "3 XXI 2.3.7" "more general" RootPairing.rootFormIn_self_smul_coroot
add_to_sga "3 XXI 3.1.2" "special case" RootPairing.Base.exists_eq_sum_and_forall_sum_mem_of_isPos
add_to_sga "3 XXI 3.1.6" RootPairing.Base
add_to_sga "3 XXI 3.1.6" RootPairing.Base.mk'
add_to_sga "3 XXI 3.1.8" "partial" RootPairing.Base.spanIntRootSupport
add_to_sga "3 XXI 3.1.8" "special case" RootPairing.Base.toWeightBasisInt
add_to_sga "3 XXI 3.1.8" "Card(Δ) = rgss(R)" RootPairing.ncard_eq_finrank_of_linearIndepOn_of
add_to_sga "3 XXI 3.1.9" "partial" RootPairing.ncard_eq_finrank_of_linearIndepOn_of
add_to_sga "3 XXI 3.1.10" "Reduced case" RootPairing.Base.mk'
add_to_sga "3 XXI 3.1.10" "partial" RootPairing.coroot_mem_or_neg_mem_closure_of_root
add_to_sga "3 XXI 3.2.1" "special case" RootPairing.Base.IsPos.add
add_to_sga "3 XXI 3.2.5" RootPairing.Base.IsPos
add_to_sga "3 XXI 3.2.6" "partial" RootPairing.Base.IsPos.neg_iff_not
add_to_sga "3 XXI 3.2.6" "partial" RootPairing.Base.IsPos.or_neg
add_to_sga "3 XXI 3.2.6" "partial" RootPairing.Base.isPos_of_mem_support
add_to_sga "3 XXI 3.2.11" "special case" RootPairing.Base.pairingIn_le_zero_of_ne
add_to_sga "3 XXI 3.2.11" "special case" RootPairing.baseOf_pairwise_pairing_le_zero
add_to_sga "3 XXI 3.2.12" "𝒮(R₊*) = ind(𝒮(R₊)*)" RootPairing.baseOf_root_eq_baseOf_coroot
add_to_sga "3 XXI 3.2.13" RootPairing.Base.IsPos
add_to_sga "3 XXI 3.2.15" RootPairing.Base.height
add_to_sga "3 XXI 3.2.15" RootPairing.Base.height_eq_sum
add_to_sga "3 XXI 3.2.15" "partial" RootPairing.Base.height_one_of_mem_support
add_to_sga "3 XXI 3.2.16" "special case" RootPairing.Base.exists_eq_sum_and_forall_sum_mem_of_isPos
add_to_sga "3 XXI 3.2.16" "more general" RootPairing.Base.height_eq_sum
add_to_sga "3 XXI 3.3.1" "special case" RootPairing.Base.IsPos.add_zsmul
add_to_sga "3 XXI 3.3.1" "special case" RootPairing.Base.IsPos.reflectionPerm
add_to_sga "3 XXI 3.3.2" "Reduced case" RootPairing.Base.IsPos.reflectionPerm
add_to_sga "3 XXI 4.0" "The G₂ roots ±β" RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.long_eq_three_mul_short
add_to_sga "3 XXI 4.0" "Completeness" RootPairing.EmbeddedG2.mem_allRoots
add_to_sga "3 XXI 4.0" "G₂ row of the table" RootPairing.EmbeddedG2.pairingIn_short_long
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.setOfPred_index_eq_univ
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.setOf_index_eq_univ
add_to_sga "3 XXI 4.0" "The G₂ table entry α+β" RootPairing.EmbeddedG2.shortAddLongRoot_eq
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.shortAddLongRoot_shortRoot
add_to_sga "3 XXI 4.0" "The G₂ table entry 3α+2β" RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_longRoot
add_to_sga "3 XXI 4.0" "The G₂ table entry 2α+β" RootPairing.EmbeddedG2.twoShortAddLongRoot_eq
add_to_sga "3 XXI 4.0" "partial" RootPairing.EmbeddedG2.twoShortAddLongRoot_shortRoot
add_to_sga "3 XXI 4.0" "partial" RootPairing.InvariantForm.apply_eq_or
add_to_sga "3 XXI 4.0" "partial" RootPairing.InvariantForm.apply_eq_or_aux
add_to_sga "3 XXI 6.1.1" RootPairing.Hom
add_to_sga "3 XXI 6.1.1" RootPairing.Hom.mk
add_to_sga "3 XXI 6.1.2" "special case" RootPairing.Equiv.mk'
add_to_sga "3 XXI 6.1.4" "more general" RootPairing.Hom.comp
add_to_sga "3 XXI 6.8.1" "special case" RootPairing.Hom
add_to_sga "3 XXI 6.8.1" "special case" RootPairing.Hom.pairing
add_to_sga "3 XXI 7.1.4" RootPairing.IsIrreducible
add_to_sga "3 XXI 7.2.3" "partial" RootPairing.InvariantForm.apply_eq_or
add_to_sga "3 XXI 7.2.8" "more general"
  RootPairing.RootPositiveForm.pairingIn_mul_eq_pairingIn_mul_swap
add_to_sga "3 XXI 7.3.1" "(i), special case" RootPairing.Base.cartanMatrixIn_apply_same
add_to_sga "3 XXI 7.3.1" "(iii) nondegeneracy" RootPairing.Base.cartanMatrixIn_nondegenerate
add_to_sga "3 XXI 7.3.1" "(ii)" RootPairing.Base.cartanMatrix_apply_eq_zero_iff_symm
add_to_sga "3 XXI 7.3.1" "(i), special case" RootPairing.Base.cartanMatrix_apply_same
add_to_sga "3 XXI 7.3.1" "(i), (ii)" RootPairing.Base.cartanMatrix_isFiniteCartan
add_to_sga "3 XXI 7.3.1" "(i), special case" RootPairing.Base.cartanMatrix_le_zero_of_ne
add_to_sga "3 XXI 7.3.1" "(i), special case" RootPairing.Base.cartanMatrix_mem_of_ne
add_to_sga "3 XXI 7.3.1" "(iii) nondegeneracy" RootPairing.Base.cartanMatrix_nondegenerate
add_to_sga "3 XXI 7.3.1" "(iii)" RootPairing.Base.exists_cartanMatrix_mul_diagaonal_posDef
add_to_sga "3 XXI 7.3.1" "more general" RootPairing.pairing_eq_zero_iff
add_to_sga "3 XXI 7.3.1" "(v) root formula" RootPairing.reflection_apply
add_to_sga "3 XXI 7.3.1" "(v) root formula" RootPairing.reflection_apply_root
add_to_sga "3 XXI 7.3.1" "(v) root formula" RootPairing.reflection_apply_root'
add_to_sga "3 XXI 7.4.1" "linked-pair data" SimpleGraph
add_to_sga "3 XXI 7.4.1" "partial" SimpleGraph.Iso
add_to_sga "3 XXI 7.4.6" CartanMatrix.A
add_to_sga "3 XXI 7.4.6" CartanMatrix.B
add_to_sga "3 XXI 7.4.6" CartanMatrix.C
add_to_sga "3 XXI 7.4.6" CartanMatrix.D
add_to_sga "3 XXI 7.4.6" CartanMatrix.E
add_to_sga "3 XXI 7.4.6" CartanMatrix.F₄
add_to_sga "3 XXI 7.4.6" CartanMatrix.G₂
add_to_sga "3 XXI 7.4.6" CoxeterMatrix.A
add_to_sga "3 XXI 7.4.6" "partial" CoxeterMatrix.B
add_to_sga "3 XXI 7.4.6" "E₆" CoxeterMatrix.E₆
add_to_sga "3 XXI 7.4.6" "partial" CoxeterMatrix.F₄
add_to_sga "3 XXI 7.4.6" "partial" CoxeterMatrix.G₂
add_to_sga "3 XXI 7.4.6" "partial" RootPairing.IsG2.card_base_support_eq_two
add_to_sga "3 XXII 3.3" "more general" RootPairing.Equiv.reflection
add_to_sga "3 XXII 3.3" "W" RootPairing.range_weylGroup_weightHom
add_to_sga "3 XXII 3.3" "more general" RootPairing.reflection
add_to_sga "3 XXII 3.3" "more general" RootPairing.reflection_apply
add_to_sga "3 XXII 3.3" "special case" RootPairing.reflection_apply_root
add_to_sga "3 XXII 3.3" "special case" RootPairing.reflection_apply_root'
add_to_sga "3 XXII 3.3" RootPairing.weylGroup
add_to_sga "3 XXII 3.3" "more general" RootPairing.weylGroup.ofIdx
add_to_sga "3 XXII 3.3" "partial" RootPairing.weylGroup_toSubmonoid
add_to_sga "3 XXII 4.1.8" AddSubgroup.closure
add_to_sga "3 XXII 4.1.11" CategoryTheory.Presheaf.IsSeparated
add_to_sga "3 XXII 4.1.11" "partial" CategoryTheory.Presieve.IsSeparatedFor
add_to_sga "3 XXII 5.3.1" LieSubalgebra.normalizer
add_to_sga "3 XXII 5.3.1" LieSubmodule.normalizer
add_to_sga "3 XXII 5.3.1" Module.finrank
add_to_sga "3 XXII 5.4.9" RootPairing.chainTopCoeff
add_to_sga "3 XXII 5.4.9" "more general" RootPairing.setOf_root_sub_zsmul_mem_eq_Icc
add_to_sga "3 XXII 5.7.11" "partial" RootPairing.Base.IsPos.reflectionPerm
add_to_sga "3 XXII 5.9.5" RootPairing.Base.height
add_to_sga "3 XXII 5.9.10" "module reduction lifting" Ideal.pi_tensorProductMk_quotient_surjective
add_to_sga "3 XXII 5.9.10" "partial" Ideal.quotientInfRingEquivPiQuotient
add_to_sga "3 XXII 6.1.1" Submodule.dualAnnihilator
add_to_sga "3 XXII 6.2.2" "more general" CategoryTheory.Subfunctor.isSeparated
add_to_sga "3 XXII 6.2.2" "more general" Subgroup.commutator
add_to_sga "3 XXII 6.2.2" "partial" commutator
add_to_sga "3 XXIII 1.2" "partial" RootPairing.Base.IsPos
add_to_sga "3 XXIII 1.5" RootPairing.Base
add_to_sga "3 XXIII 1.8.2" "special case"
  AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
add_to_sga "3 XXIII 2.1.3" "partial" RootPairing.Base.IsPos.induction_on_reflect
add_to_sga "3 XXIII 3.4.1" RootPairing.EmbeddedG2
add_to_sga "3 XXIII 3.4.1" RootPairing.EmbeddedG2.allRoots
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.EmbeddedG2.allRoots_subset_range_root
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.EmbeddedG2.indexEquivAllRoots
add_to_sga "3 XXIII 3.4.1" RootPairing.EmbeddedG2.longRoot
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.EmbeddedG2.mem_allRoots
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.EmbeddedG2.setOfPred_index_eq_univ
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.EmbeddedG2.setOf_index_eq_univ
add_to_sga "3 XXIII 3.4.1" "Entry α+β of R⁺" RootPairing.EmbeddedG2.shortAddLongRoot_eq
add_to_sga "3 XXIII 3.4.1" RootPairing.EmbeddedG2.shortRoot
add_to_sga "3 XXIII 3.4.1" "Entry 3α+β of R⁺" RootPairing.EmbeddedG2.threeShortAddLongRoot_eq
add_to_sga "3 XXIII 3.4.1" "Entry 3α+2β of R⁺" RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq
add_to_sga "3 XXIII 3.4.1" "Entry 2α+β of R⁺" RootPairing.EmbeddedG2.twoShortAddLongRoot_eq
add_to_sga "3 XXIII 3.4.1" "partial" RootPairing.IsG2
add_to_sga "3 XXIII 3.4.2" "Clause (β*" RootPairing.EmbeddedG2.pairingIn_short_long
add_to_sga "3 XXIII 3.4.2" "Clause (β*" RootPairing.EmbeddedG2.pairing_short_long
add_to_sga "3 XXIII 4.1.4" "special case" neg_one_pow_char
add_to_sga "3 XXIII 4.1.4" "special case" neg_one_pow_char_pow
add_to_sga "3 XXIII 4.1.4" "special case" neg_one_pow_expChar
add_to_sga "3 XXIII 4.1.4" "special case" neg_one_pow_expChar_pow
add_to_sga "3 XXIII 4.1.8" "partial" RootPairing.EmbeddedG2.allRoots
add_to_sga "3 XXIII 4.1.8" "partial" RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs
add_to_sga "3 XXIII 4.1.8" "partial" RootPairing.EmbeddedG2.indexEquivAllRoots
add_to_sga "3 XXIII 4.1.8" "exhaustiveness" RootPairing.EmbeddedG2.mem_allRoots
add_to_sga "3 XXIII 4.1.8" "partial" RootPairing.EmbeddedG2.setOfPred_index_eq_univ
add_to_sga "3 XXIII 4.1.8" "partial" RootPairing.EmbeddedG2.setOf_index_eq_univ
add_to_sga "3 XXIII 4.1.8" "3α+β is a root" RootPairing.EmbeddedG2.threeShortAddLongRoot_eq
add_to_sga "3 XXIII 4.1.8" "3α+2β is a root" RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq
add_to_sga "3 XXIII 4.1.8" "2α+β is a root" RootPairing.EmbeddedG2.twoShortAddLongRoot_eq
add_to_sga "3 XXIII 6.4" RootPairing.chainBotCoeff
add_to_sga "3 XXIII 6.4" "special case" RootPairing.chainBotCoeff_add_chainTopCoeff_le_two
add_to_sga "3 XXIII 6.4" RootPairing.chainTopCoeff
add_to_sga "3 XXIII 6.4" "partial" RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff
add_to_sga "3 XXIII 6.4" "partial" RootPairing.setOf_root_sub_zsmul_mem_eq_Icc
add_to_sga "3 XXIV 3.9.1" "Final clause" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_sga "3 XXIV 3.9.1" "Final clause"
  AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_sga "3 XXIV 3.9.1" "partial" Ideal.quotientInfRingEquivPiQuotient
add_to_sga "3 XXIV 3.9.1" "one variable" Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
add_to_sga "3 XXIV 3.9.1" "one variable" Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
add_to_sga "3 XXIV 3.9.1" "one variable" Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
add_to_sga "3 XXIV 3.9.1" "special case" Polynomial.zero_of_eval_zero
add_to_sga "3 XXIV 4.2.3" "special case" CommRing.Pic.instSubsingletonOfIsLocalRing
add_to_sga "3 XXIV 4.4.4" SemidirectProduct.instMul
add_to_sga "3 XXIV 4.4.4" SemidirectProduct.mul_def
add_to_sga "3 XXIV 7.1.2" AlgebraicGeometry.affineAnd
add_to_sga "3 XXIV 7.1.5" "special case"
  AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_sga "3 XXIV 7.1.5" "more general" AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
add_to_sga "3 XXIV 7.1.9" CategoryTheory.Functor.relativelyRepresentable
add_to_sga "3 XXIV 7.1.9" CategoryTheory.MorphismProperty.relative
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.GeneralLinearGroup.injective_upperRightHom
add_to_sga "3 XXIV 7.4.1" "p on R-points" Matrix.GeneralLinearGroup.upperRightHom
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.SL2.transvection_induction
add_to_sga "3 XXIV 7.4.1" "R-valued points of SL₂" Matrix.SpecialLinearGroup
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.SpecialLinearGroup.diag2
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.SpecialLinearGroup.diag2_coe
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.SpecialLinearGroup.diag2_coe'
add_to_sga "3 XXIV 7.4.1" "partial" Matrix.SpecialLinearGroup.instGroup
add_to_sga "3 XXIV 7.4.1" "p on R-points" Matrix.SpecialLinearGroup.transvection
add_to_sga "3 XXIV 7.4.1" "Relation w² = α*(−1)" ModularGroup.S_mul_S_eq
add_to_sga "3 XXIV 7.4.1" "partial" ModularGroup.T_S_rel
add_to_sga "3 XXIV 8.1.2" "partial" AlgebraicGeometry.instSmoothFstScheme
add_to_sga "3 XXIV 8.1.2" "partial" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "3 XXIV 8.4" "special case" Algebra.IsFiniteSplit
add_to_sga "3 XXIV 8.4" "special case" Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
add_to_sga "3 XXIV 8.4" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "3 XXV 2.1" IsOrderedAddMonoid
add_to_sga "3 XXV 2.1" "partial" RootPairing.Base
add_to_sga "3 XXV 2.1" "partial" RootPairing.Base.IsPos
add_to_sga "3 XXV 4.3" "partial" AlgebraicGeometry.isAffineHom_of_isInducing
add_to_sga "3 XXVI 2.1.1" "special case" RootPairing.Base.height
add_to_sga "3 XXVI 2.1.1" "(iii), special case" RootPairing.Base.height_add
add_to_sga "3 XXVI 2.1.1" "(iii), special case" RootPairing.Base.height_add_zsmul
add_to_sga "3 XXVI 2.1.1" "(iii), special case" RootPairing.Base.height_reflectionPerm_self
add_to_sga "3 XXVI 2.1.1" "(iii), special case" RootPairing.Base.height_sub
add_to_sga "3 XXVI 5.1.6" Field.absoluteGaloisGroup
add_to_sga "3 XXVI 5.1.6" MulAction.IsPretransitive
add_to_sga "3 XXVI 5.1.6" "partial" MulAction.orbit
add_to_sga "3 XXVI 5.1.6" RootPairing.Base
add_to_sga "3 XXVI 5.1.6" RootPairing.Base.IsPos
add_to_sga "3 XXVI 5.1.10" "Ambient group SL₃" Matrix.SpecialLinearGroup
add_to_sga "3 XXVI 5.1.10" "partial" Matrix.SpecialLinearGroup.transvection
add_to_sga "3 XXVI 6.1" "partial" AddMemClass
add_to_sga "3 XXVI 6.1" AddSubmonoid
add_to_sga "3 XXVI 6.1" AddSubmonoid.mk
add_to_sga "3 XXVI 6.1" AddSubmonoidClass
add_to_sga "3 XXVI 6.1" AddSubmonoidClass.mk
add_to_sga "3 XXVI 6.1" "partial" AddSubsemigroup
add_to_sga "3 XXVI 7.4.5" RootPairing.range_weylGroup_weightHom
add_to_sga "3 XXVI 7.4.5" RootPairing.weylGroup
add_to_sga "3 XXVI 7.5" "special case" RootPairing.Base
add_to_sga "3 XXVI 7.15" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_sga "3 XXVI 7.15" AlgebraicGeometry.Scheme.instCanonicallyOverSpecResidueField
add_to_sga "3 XXVI 7.15" AlgebraicGeometry.Scheme.instOverSpecResidueField
add_to_sga "3 XXVI 7.15" "partial" AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion
add_to_sga "3 XXVI 7.15" IsLocalRing.closedPoint
