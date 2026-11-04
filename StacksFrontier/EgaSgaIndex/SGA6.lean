module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.WeakLimits.WeakPullbacks
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Grassmannian
import Mathlib.RingTheory.HahnSeries.Binomial
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Nilpotent
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import StacksCore.Algebra.Module.LocalizedModule.Submodule
import StacksCore.Algebra.Module.Projective
import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.RingTheory.NormTrace
import StacksCore.RingTheory.Support
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 6 references registered by name

Declarations realizing numbered items of SGA 6, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "6 0 2.1" "special case" Ideal.Cotangent
add_to_sga "6 0 2.3.Corollary2" "affine clause" Module.finrank
add_to_sga "6 0 2.3.Corollary2" "affine clause" Module.rank
add_to_sga "6 0 2.5" "partial" AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_sga "6 0 2.5" SheafOfModules.IsQuasicoherent
add_to_sga "6 0 2.5" SheafOfModules.isQuasicoherent
add_to_sga "6 0 2.9" "special case" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "6 0 2.9" "special case" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "6 0 2.9" "affine case" Module.Flat.iff_lTensor_exact'
add_to_sga "6 0 2.9" "affine case" Module.Flat.iff_rTensor_exact
add_to_sga "6 0 2.11" "affine step" Submodule.localized'_comap_restrictScalars
add_to_sga "6 0 4.3" "Map (4.1), special case" Algebra.Extension.cotangentComplex_mk
add_to_sga "6 0 4.4" "partial" Algebra.Extension.CotangentSpace
add_to_sga "6 0 4.4" "partial" Algebra.Extension.cotangentComplex_mk
add_to_sga "6 0 4.4" "Kernel J of C = A[T] → B" Algebra.Generators.ker
add_to_sga "6 0 4.4" "partial" Algebra.instFormallySmoothMvPolynomial
add_to_sga "6 0 4.4" "partial" Algebra.mvPolynomial
add_to_sga "6 0 4.4" "special case" MvPolynomial
add_to_sga "6 I 1.1.3" "partial" CategoryTheory.Functor.Additive
add_to_sga "6 I 1.1.3" "partial" CategoryTheory.Functor.IsTriangulated
add_to_sga "6 I 1.1.3" "partial" CategoryTheory.Functor.mapTriangle
add_to_sga "6 I 1.1.3" "partial" CategoryTheory.additiveFunctor
add_to_sga "6 I 1.1.5" "f*"
  CategoryTheory.Functor.instLiftingCochainComplexIntDerivedCategoryQQuasiIsoUpCompHomologicalComplexMapHomologicalComplexMapDerivedCategory
add_to_sga "6 I 1.1.5" "partial" CategoryTheory.Functor.mapHomologicalComplex
add_to_sga "6 I 1.1.5" "fiberwise D^b clause"
  CategoryTheory.Triangulated.TStructure.instIsTriangulatedBounded
add_to_sga "6 I 1.1.5" CochainComplex.of
add_to_sga "6 I 1.1.5" ComplexShape.up
add_to_sga "6 I 1.1.5" "D(C_X) is triangulated" DerivedCategory.instIsTriangulated
add_to_sga "6 I 1.1.5" "partial" DerivedCategory.instPretriangulated
add_to_sga "6 I 1.1.5" HasDerivedCategory.standard
add_to_sga "6 I 1.1.5" "partial" HomologicalComplex
add_to_sga "6 I 1.1.5" "partial" HomologicalComplex.instAbelian
add_to_sga "6 I 1.1.5" "K(C_X) is triangulated" HomotopyCategory.instIsTriangulatedIntUp
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.instIsTriangulatedIntUpPlus
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.instPreadditive
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.instPreadditiveQuotientHomologicalComplexHomotopic
add_to_sga "6 I 1.1.5" "partial" HomotopyCategory.instPretriangulatedIntUp
add_to_sga "6 I 1.1.5" "partial" instCategoryDerivedCategory
add_to_sga "6 I 1.1.5" "partial" instCategoryHomotopyCategory
add_to_sga "6 I 1.2" "special case" CategoryTheory.SplitEpiCategory
add_to_sga "6 I 1.2" "special case" Module.Finite
add_to_sga "6 I 1.3" "more general"
  FGModuleCat.instFiniteCarrierLimitModuleCatCompForget₂LinearMapIdObjIsFG
add_to_sga "6 I 1.3" "partial" FGModuleRepr.instFiniteRepr
add_to_sga "6 I 1.3" "partial" FGModuleRepr.ofFiniteEquiv
add_to_sga "6 I 1.3" "more general" IsProjective.iff_projective
add_to_sga "6 I 1.3" "special case" Module.Finite
add_to_sga "6 I 1.3" "partial" Module.Finite.exists_fin_quot_equiv
add_to_sga "6 I 1.3" "more general" Module.FinitePresentation.fg_ker
add_to_sga "6 I 1.3" "partial" Module.FinitePresentation.fg_ker_iff
add_to_sga "6 I 1.3" "partial" Module.Presentation.finite
add_to_sga "6 I 1.3" "more general" Module.projective_iff_lift_map_range_le
add_to_sga "6 I 1.3" "more general" Module.projective_lifting_property
add_to_sga "6 I 1.3" "special case" ModuleCat.isFG
add_to_sga "6 I 1.3" "more general" ModuleCat.projective_of_categoryTheory_projective
add_to_sga "6 I 2.8" "special case" Module.Finite
add_to_sga "6 I 2.8" "special case" Module.FinitePresentation
add_to_sga "6 I 2.8" "special case" Module.finitePresentation_iff_exists_presentation
add_to_sga "6 I 2.8" "special case" SheafOfModules.isFinitePresentation
add_to_sga "6 I 3.7" "special case" CommRingCat.flat
add_to_sga "6 I 4.5" "special case" CategoryTheory.Pseudofunctor.sheafHom
add_to_sga "6 I 4.12.2" "partial" HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic
add_to_sga "6 I 4.12.2" "partial" HomotopyCategory.subcategoryAcyclic
add_to_sga "6 I 4.14.1" "special case" CategoryTheory.HasProjectiveDimensionLE
add_to_sga "6 I 4.14.1" "special case" CategoryTheory.HasProjectiveDimensionLT
add_to_sga "6 I 4.14.1" "special case" CategoryTheory.projectiveDimension
add_to_sga "6 I 4.14.1" "special case" CategoryTheory.projectiveDimension_eq_zero_iff
add_to_sga "6 I 4.14.1" "n = 0" CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
add_to_sga "6 I 4.14.1" "n = 0" CategoryTheory.projective_iff_hasProjectiveDimensionLT_one
add_to_sga "6 I 5.6" "special case" Module.Flat.instTensorProduct
add_to_sga "6 I 5.7" "(i) ⇒ (ii)" CategoryTheory.Abelian.Ext.eq_zero_of_injective
add_to_sga "6 I 5.7" "(i) ⇒ (ii)" CategoryTheory.Abelian.Ext.subsingleton_of_injective
add_to_sga "6 I 5.7" CategoryTheory.HasInjectiveDimensionLE
add_to_sga "6 I 5.7" CategoryTheory.HasInjectiveDimensionLT
add_to_sga "6 I 5.7" "partial" CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X₁
add_to_sga "6 I 5.7" "(i)⇔(ii), special case"
  CategoryTheory.injective_iff_hasInjectiveDimensionLT_one
add_to_sga "6 I 5.7" "(i) ⇒ (ii)" CategoryTheory.instHasInjectiveDimensionLTOfNatNatOfInjective
add_to_sga "6 I 5.7" "(ii) ⇒ (i)" CategoryTheory.instInjectiveOfHasInjectiveDimensionLTOfNatNat
add_to_sga "6 I 5.7" "a)" Module.Flat.of_flat_tensorProduct
add_to_sga "6 I 5.8.3" "(ii) ⇒ (i)" Module.Flat.projective_of_finitePresentation
add_to_sga "6 I 5.8.3" "(ii) ⇒ (i)" Module.free_of_flat_of_isLocalRing
add_to_sga "6 I 6.0" "special case" Module.isLocallyConstant_rankAtStalk_freeLocus
add_to_sga "6 I 6.0" "(iii), special case" Module.rankAtStalk_self
add_to_sga "6 I 6.0" "(ii), special case" ModuleCat.free_shortExact_finrank_add
add_to_sga "6 I 6.0" "(ii), special case" ModuleCat.free_shortExact_rank_add
add_to_sga "6 I 6.3" "more general" Algebra.GrothendieckAddGroup
add_to_sga "6 I 6.3" "additive case" Algebra.GrothendieckAddGroup.lift
add_to_sga "6 I 6.3" "more general" Algebra.GrothendieckGroup
add_to_sga "6 I 6.3" "additive case" Algebra.GrothendieckGroup.lift
add_to_sga "6 I 6.6" "Fiber of C^is over X" CategoryTheory.Core
add_to_sga "6 I 6.6" "partial" CategoryTheory.Discrete
add_to_sga "6 I 6.11" "special case" Module.finrank
add_to_sga "6 I 6.11" "special case" Module.rankAtStalk
add_to_sga "6 I 6.12" "Clause a), special case" Module.rankAtStalk_tensorProduct
add_to_sga "6 I 7.0" CategoryTheory.Limits.terminal
add_to_sga "6 I 7.6" "special case" homTensorHomEquiv
add_to_sga "6 I 7.6" "special case" lTensorHomEquivHomLTensor
add_to_sga "6 I 7.6" "special case" rTensorHomEquivHomRTensor
add_to_sga "6 I 7.7" "special case" dualTensorHomEquiv
add_to_sga "6 I 7.7" "special case" dualTensorHomEquivOfBasis
add_to_sga "6 I 7.9" "more general" CategoryTheory.leftDualTensorIso
add_to_sga "6 I 7.9" "more general" CategoryTheory.rightDualTensorIso
add_to_sga "6 I 7.9" "special case" PiTensorProduct.dualDistribEquiv
add_to_sga "6 I 7.9" "special case" PiTensorProduct.dualDistribEquivOfBasis
add_to_sga "6 I 7.9" "special case" TensorProduct.dualDistribEquiv
add_to_sga "6 I 8.1.1" "E = A clause, via S = R" Algebra.trace_algebraMap
add_to_sga "6 I 8.1.1" "E = A clause" Algebra.trace_self
add_to_sga "6 I 8.1.1" "E = A clause" Algebra.trace_self'
add_to_sga "6 I 8.1.1" "E = A clause" Algebra.trace_self_apply
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_contract
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_contract'
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_contract_apply
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_contract_of_basis
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_contract_of_basis'
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_sum_trace_restrict
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_sum_trace_restrict'
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_eq_zero_of_mapsTo_ne
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_prodMap
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_prodMap'
add_to_sga "6 I 8.1.1" "special case" LinearMap.trace_smulRight
add_to_sga "6 I 8.3" "special case" LinearMap.trace_comp_comm
add_to_sga "6 I 8.3" "special case" LinearMap.trace_comp_comm'
add_to_sga "6 I 8.3" "special case" LinearMap.trace_comp_cycle
add_to_sga "6 I 8.3" "special case" LinearMap.trace_comp_cycle'
add_to_sga "6 I 8.3" "special case" LinearMap.trace_mul_comm
add_to_sga "6 I 8.3" "special case" LinearMap.trace_mul_cycle
add_to_sga "6 I 8.3" "special case" LinearMap.trace_mul_cycle'
add_to_sga "6 I 8.3" "special case" Matrix.trace_mul_cycle
add_to_sga "6 I 8.3" "special case" Matrix.trace_mul_cycle'
add_to_sga "6 I 8.4" "special case" LinearMap.trace_conj
add_to_sga "6 I 8.4" "special case" LinearMap.trace_conj'
add_to_sga "6 I 8.4" "special case" LinearMap.trace_map
add_to_sga "6 I 8.4" "special case" Matrix.trace_conj
add_to_sga "6 I 8.4" "special case" Matrix.trace_conj'
add_to_sga "6 I 8.4" "special case" Matrix.trace_map
add_to_sga "6 I 8.4" "special case" Matrix.trace_map'
add_to_sga "6 I 8.4" "special case" Matrix.trace_units_conj
add_to_sga "6 I 8.4" "special case" Matrix.trace_units_conj'
add_to_sga "6 I 8.5" CategoryTheory.Core
add_to_sga "6 I 8.5" "partial" CategoryTheory.Discrete
add_to_sga "6 I 8.6" "Punctual (affine) case" LinearMap.trace_tensorProduct
add_to_sga "6 I 8.6" "Punctual (affine) case" LinearMap.trace_tensorProduct'
add_to_sga "6 II 1.1" "c)" CategoryTheory.ProjectiveResolution.homotopyEquiv
add_to_sga "6 II 2.0" "special case" AlgebraicGeometry.Scheme.Modules
add_to_sga "6 II 2.0" "special case" ModuleCat
add_to_sga "6 II 2.1.1" SheafOfModules.GeneratingSections
add_to_sga "6 II 2.1.2" "partial" AlgebraicGeometry.isIso_fromTildeΓ_of_presentation
add_to_sga "6 II 2.1.2" "Clause a), special case"
  CategoryTheory.ShortComplex.ShortExact.splittingOfProjective
add_to_sga "6 II 2.1.3" CategoryTheory.Abelian.Ext.mapExactFunctor
add_to_sga "6 II 2.1.3" CategoryTheory.Functor.mapExtAddHom
add_to_sga "6 II 2.1.3" CategoryTheory.Functor.mapExtLinearMap
add_to_sga "6 II 2.2.1" SheafOfModules.IsQuasicoherent
add_to_sga "6 II 2.2.1" SheafOfModules.isQuasicoherent
add_to_sga "6 II 2.2.3.1" "special case"
  AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
add_to_sga "6 II 2.2.3.1" "Case L = O_X" AlgebraicGeometry.IsAffineOpen.ι_basicOpen_preimage
add_to_sga "6 II 2.2.3.1" "Case L = O_X" AlgebraicGeometry.instIsAffineHomιBasicOpen
add_to_sga "6 II 2.2.10" Module.Finite
add_to_sga "6 II 2.2.10" Module.Free
add_to_sga "6 II 2.2.10" Module.Projective
add_to_sga "6 II 2.2.10" ModuleCat
add_to_sga "6 II 2.4.3" "c), special case"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
add_to_sga "6 II 2.4.3" SheafOfModules.isFinitePresentation
add_to_sga "6 II 3.0" AlgebraicGeometry.QuasiSeparated
add_to_sga "6 II 3.0" AlgebraicGeometry.Scheme
add_to_sga "6 II 3.0" "more general" CategoryTheory.Functor.mapDerivedCategory
add_to_sga "6 II 3.0" "partial" CategoryTheory.ObjectProperty.faithful_ι
add_to_sga "6 II 3.1" CategoryTheory.AB5
add_to_sga "6 II 3.1" CategoryTheory.AB5OfSize
add_to_sga "6 II 3.1" CategoryTheory.Abelian
add_to_sga "6 II 3.1" "special case" instAB5AddCommGrpCat
add_to_sga "6 II 3.1" "special case" instAB5ModuleCat
add_to_sga "6 II 3.3" "more general"
  CategoryTheory.Functor.instIsRightDerivedFunctorPlusPlusRightDerivedFunctorPlusRightDerivedFunctorPlusUnitQuasiIso
add_to_sga "6 II 3.3" "more general" CategoryTheory.Functor.rightDerivedFunctorPlus
add_to_sga "6 II 3.3" "more general" CategoryTheory.Injective.injective_of_adjoint
add_to_sga "6 II AppI.1.2" "more general" AlgebraicGeometry.Scheme.GlueData.glued
add_to_sga "6 II AppI.1.2" "more general" AlgebraicGeometry.Scheme.GlueData.ι
add_to_sga "6 II AppI.1.2" "more general" AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion
add_to_sga "6 II AppII.1.2.4" SymmetricPower
add_to_sga "6 II AppII.3.0.1" ContinuousMap
add_to_sga "6 II AppII.3.0.1" TopCat.Hom
add_to_sga "6 II AppII.3.0.4" "partial" ContMDiffSection
add_to_sga "6 II AppII.3.1.2" "more general" ContinuousMap.uniformContinuous_comp
add_to_sga "6 II AppII.3.2.5" ContinuousLinearMap.IsFredholm
add_to_sga "6 III 1.1" HasDerivedCategory.standard
add_to_sga "6 III 1.14" "special case"
  AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFinitePresentation
add_to_sga "6 III 3.4" "special case" RingHom.Flat.stableUnderComposition
add_to_sga "6 III 3.5.2" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "6 III 3.6" "(ii), special case" Algebra.FormallyUnramified.flat_of_restrictScalars
add_to_sga "6 III 4.6" "partial" AlgebraicGeometry.Scheme.Hom.fiber
add_to_sga "6 III 4.6.1" AlgebraicGeometry.Scheme.Hom.fiber
add_to_sga "6 III 4.6.1" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_sga "6 III 5.4" "special case" IsLocallyConstant
add_to_sga "6 III 5.4.1" "special case" AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank
add_to_sga "6 III 5.4.1" "special case" Module.isLocallyConstant_rankAtStalk_freeLocus
add_to_sga "6 III 5.4.1" "special case" Submodule.exists_mem_addIdeal_and_span_image_eq_top
add_to_sga "6 IV 1.6" CategoryTheory.ObjectProperty.IsWeakSerreClass
add_to_sga "6 IV 2.1" HasDerivedCategory.standard
add_to_sga "6 IV 2.1" "partial" ModuleCat
add_to_sga "6 IV 2.6" "more general" Bimod
add_to_sga "6 IV 2.6" "more general" Bimod.instCategory
add_to_sga "6 IV 2.6" "special case" PresheafOfModules.Monoidal.tensorHom
add_to_sga "6 IV 2.6" "special case" PresheafOfModules.Monoidal.tensorObj
add_to_sga "6 IV 2.6" "special case" TensorProduct
add_to_sga "6 IX 1.2" "Generic-point clause"
  AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_sga "6 IX 1.7" "more general" Module.free_of_finite_type_torsion_free
add_to_sga "6 IX 1.7" "more general" Module.free_of_finite_type_torsion_free'
add_to_sga "6 V 1.2" "partial" AddMonoidAlgebra.gradeBy
add_to_sga "6 V 1.2" "partial" AddMonoidAlgebra.gradeBy.gradedAlgebra
add_to_sga "6 V 1.2" "partial" MvPolynomial.weightedDecomposition
add_to_sga "6 V 1.2" "partial" MvPolynomial.weightedGradedAlgebra
add_to_sga "6 V 1.2" "partial" MvPolynomial.weightedHomogeneousSubmodule
add_to_sga "6 V 1.3" FixedPoints.subalgebra
add_to_sga "6 V 1.3" "partial" HahnSeries.orderTopSubOnePos
add_to_sga "6 V 1.3" MulAction.fixedPoints
add_to_sga "6 V 1.3" "partial" MvPolynomial.symmetricSubalgebra
add_to_sga "6 V 1.4" MvPolynomial.eval
add_to_sga "6 V 1.4" MvPolynomial.killCompl
add_to_sga "6 V 1.4" "retraction identity" MvPolynomial.killCompl_comp_rename
add_to_sga "6 V 1.4" "partial" MvPolynomial.killCompl_rename_app
add_to_sga "6 V 1.4" Polynomial.evalRingHom
add_to_sga "6 V 1.5" MvPolynomial.IsSymmetric
add_to_sga "6 V 1.5" MvPolynomial.esymm
add_to_sga "6 V 1.5" MvPolynomial.esymmAlgEquiv
add_to_sga "6 V 1.5" "partial" MvPolynomial.esymmAlgEquiv_symm_apply
add_to_sga "6 V 1.5" MvPolynomial.esymmAlgHom
add_to_sga "6 V 1.5" "images of generators" MvPolynomial.esymmAlgHomMonomial_single
add_to_sga "6 V 1.5" MvPolynomial.esymmAlgHom_fin_bijective
add_to_sga "6 V 1.5" "more general" MvPolynomial.esymmAlgHom_fin_injective
add_to_sga "6 V 1.5" "more general" MvPolynomial.esymmAlgHom_fin_surjective
add_to_sga "6 V 1.5" "more general" MvPolynomial.esymmAlgHom_injective
add_to_sga "6 V 1.5" "more general" MvPolynomial.esymmAlgHom_surjective
add_to_sga "6 V 1.5" "partial" MvPolynomial.esymm_isSymmetric
add_to_sga "6 V 1.5" "partial" MvPolynomial.rename_esymm
add_to_sga "6 V 1.5" MvPolynomial.symmetricSubalgebra
add_to_sga "6 V 1.11" "special case" HahnSeries.orderTopSubOnePos
add_to_sga "6 V 2.5" "more general" Polynomial.preHilbertPoly
add_to_sga "6 V 2.6" BinomialRing
add_to_sga "6 V 2.6" IsAddTorsionFree
add_to_sga "6 V 2.6" PowerSeries.binomialSeries
add_to_sga "6 V 2.6" "partial" PowerSeries.binomialSeries_add
add_to_sga "6 V 2.6" "special case" PowerSeries.binomialSeries_nat
add_to_sga "6 V 2.6" "partial" Ring.add_choose_eq
add_to_sga "6 V 2.6" Ring.choose
add_to_sga "6 V 2.6" "partial" Ring.map_choose
add_to_sga "6 V 2.7" "partial" BinomialRing
add_to_sga "6 V 2.7" "partial" PowerSeries.binomialSeries
add_to_sga "6 V 2.7" "partial" Ring.choose
add_to_sga "6 V 2.9" "(2.9.1), special case" HahnSeries.binomial_power
add_to_sga "6 V 2.9" "(2.9.1) for φ=1+t" PowerSeries.binomialSeries
add_to_sga "6 V 2.9" "special case" PowerSeries.binomialSeries_add
add_to_sga "6 V 2.9" "(2.9.1) for φ=1+t" PowerSeries.binomialSeries_coeff
add_to_sga "6 V 4.10" "more general" MvPolynomial.IsWeightedHomogeneous
add_to_sga "6 V 4.10" "more general" MvPolynomial.weightedTotalDegree
add_to_sga "6 V 4.10" "more general" MvPolynomial.weightedTotalDegree'
add_to_sga "6 V 5.5" Unitization.instAdd
add_to_sga "6 V 5.5" "partial" Unitization.instAddCommGroup
add_to_sga "6 V 5.5" Unitization.instCommRing
add_to_sga "6 V 5.5" Unitization.instMul
add_to_sga "6 V 5.5" Unitization.instRing
add_to_sga "6 V 5.5" "partial" Unitization.snd_mul
add_to_sga "6 V 5.5" "partial" Unitization.toProd_add
add_to_sga "6 V 6.4" Algebra
add_to_sga "6 V 7.1" "more general" LaurentSeries.derivative
add_to_sga "6 V 7.1" "more general" MvPowerSeries.pderiv
add_to_sga "6 V 7.1" "more general" MvPowerSeries.pderivFun
add_to_sga "6 V 7.1" PowerSeries.derivative
add_to_sga "6 V 7.1" PowerSeries.derivativeFun
add_to_sga "6 VI 1.2" "partial" CategoryTheory.GradedObject.hasShift
add_to_sga "6 VI 1.2" "partial" CategoryTheory.GradedObject.shiftFunctor_obj_apply
add_to_sga "6 VI 1.5.2" "Case B = A, n = 0" Module.Flat.projective_of_finitePresentation
add_to_sga "6 VI 2.2" AlgebraicGeometry.Scheme.Modules
add_to_sga "6 VI 2.2" "𝒜 and 𝒢′ are abelian" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "6 VI 2.3.1" "more general" SheafOfModules.PullbackConstruction.adjunction
add_to_sga "6 VI 2.3.2" "partial" AlgebraicGeometry.Proj.affineOpenCover
add_to_sga "6 VI 2.3.2" "partial" AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan
add_to_sga "6 VI 2.3.2" "special case" AlgebraicGeometry.Proj.awayι
add_to_sga "6 VI 2.3.2" "(f), special case" AlgebraicGeometry.Proj.basicOpen
add_to_sga "6 VI 2.3.2" "special case" AlgebraicGeometry.Proj.basicOpenIsoAway
add_to_sga "6 VI 2.3.2" "special case" AlgebraicGeometry.Proj.instIsOpenImmersionAwayι
add_to_sga "6 VI 2.3.2" "(f), special case" AlgebraicGeometry.Proj.opensRange_awayι
add_to_sga "6 VI 2.3.2" "partial" AlgebraicGeometry.projIsoSpec
add_to_sga "6 VI 2.3.2" "special case" HomogeneousLocalization
add_to_sga "6 VI 2.3.2" "special case" HomogeneousLocalization.Away.isLocalization_mul
add_to_sga "6 VI 4.1" "special case" Module.Grassmannian.functor
add_to_sga "6 VI 4.10" "Proof step of 4.10" Polynomial.coeff_isUnit_isNilpotent_of_isUnit
add_to_sga "6 VI 4.10" "Proof step of 4.10" Polynomial.isUnit_C_add_X_mul_iff
add_to_sga "6 VI 6.1" IsNilpotent
add_to_sga "6 VII 1.1" "Rank-one case" IsSMulRegular.smulShortComplex_shortExact
add_to_sga "6 VII 1.2" Ideal.map
add_to_sga "6 VII 1.2" MvPolynomial
add_to_sga "6 VII 1.5" "special case" IsSMulRegular.of_flat
add_to_sga "6 VII 1.5" "special case" IsSMulRegular.of_flat_of_isBaseChange
add_to_sga "6 VII 1.5" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_sga "6 VII 1.5" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_sga "6 VII 1.6" Ideal.Cotangent
add_to_sga "6 VII 1.6" Ideal.cotangentIdeal
add_to_sga "6 VII 1.6" Ideal.mapCotangent
add_to_sga "6 VII 3.1" "j" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_sga "6 VII 3.1" "j" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_sga "6 VII 3.7" CategoryTheory.Limits.pullback
add_to_sga "6 VII 4.1" "special case" exteriorPower.subsingleton_of_span_eq_top_of_card_lt
add_to_sga "6 VII 4.6" "more general" TensorProduct
add_to_sga "6 VIII 1.3" "(iv), special case"
  Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
add_to_sga "6 VIII 1.3" "(iii)" AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord
add_to_sga "6 VIII 1.3" "(iv)" AlgebraicGeometry.IsImmersion.of_comp
add_to_sga "6 VIII 1.3" "more general" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_sga "6 VIII 1.3" CategoryTheory.Limits.PullbackCone.IsLimit.lift
add_to_sga "6 VIII 1.3" CategoryTheory.Limits.PullbackCone.IsWeakLimit.lift
add_to_sga "6 VIII 1.3" CategoryTheory.Limits.WidePullbackCone.IsLimit.lift
add_to_sga "6 VIII 1.3" CategoryTheory.Limits.pullback
add_to_sga "6 VIII 1.3" CategoryTheory.Limits.pullback.lift
add_to_sga "6 VIII 1.3" "VII 1.5, special case" IsSMulRegular.of_flat
add_to_sga "6 VIII 1.3" "VII 1.5, special case" IsSMulRegular.of_flat_of_isBaseChange
add_to_sga "6 VIII 1.3" MvPolynomial.eval
add_to_sga "6 VIII 1.3" MvPolynomial.eval₂Hom
add_to_sga "6 VIII 1.3" "VII 1.5, special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_sga "6 VIII 1.3" "VII 1.5, special case"
  RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_sga "6 VIII 1.3" "VII 1.5, special case" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_sga "6 VIII 1.3" "VII 1.5, special case"
  RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_sga "6 VIII 1.6" "special case" Algebra.IsStandardSmooth.baseChange
add_to_sga "6 VIII 1.6" "more general"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFinitePresentationMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "6 VIII 1.6" "special case"
  AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "6 VIII 1.8" "special case" Algebra.IsStandardSmooth.baseChange
add_to_sga "6 VIII 1.8" "special case" Algebra.IsStandardSmoothOfRelativeDimension.baseChange
add_to_sga "6 VIII 1.8" "partial" AlgebraicGeometry.IsImmersion.of_comp
add_to_sga "6 VIII 1.8" "V×_Y V′ is smooth over V" AlgebraicGeometry.instSmoothFstScheme
add_to_sga "6 VIII 1.8" "partial" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "6 VIII 1.8" "affine case" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "6 VIII 1.8" "special case"
  RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "6 VIII 1.8" "special case" RingHom.isStandardSmooth_isStableUnderBaseChange
add_to_sga "6 VIII 1.10" "special case" Algebra.IsStandardSmoothOfRelativeDimension.trans
add_to_sga "6 VIII 1.10" "special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_sga "6 VIII 1.10" "special case" RingHom.IsStandardSmoothOfRelativeDimension.comp
add_to_sga "6 VIII 2.1" "degree-1 term L_1 = J/J²" Ideal.Cotangent
add_to_sga "6 VIII 2.2" "partial" Algebra.Extension.CotangentSpace.map
add_to_sga "6 VIII 2.2" "clause (a)" Algebra.Extension.CotangentSpace.map_comp_cotangentComplex
add_to_sga "6 VIII 2.2" "clause (a)" Algebra.Extension.CotangentSpace.map_cotangentComplex
add_to_sga "6 VIII 2.2" "partial" Algebra.Generators.Cotangent.exact
add_to_sga "6 VIII 2.2" "clause (a), special case"
  Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange
add_to_sga "6 VIII 2.2" "V×_Y V′ is smooth over V" AlgebraicGeometry.instSmoothFstScheme
add_to_sga "6 VIII 2.2" "partial" AlgebraicGeometry.instSmoothSndScheme
add_to_sga "6 VIII 2.2" Ideal.mapCotangent
add_to_sga "6 VIII 2.4" Ideal.Cotangent
add_to_sga "6 VIII 2.6" "partial" Algebra.Generators.Cotangent.exact
add_to_sga "6 VIII 2.6" "partial" Algebra.Generators.CotangentSpace.exact
add_to_sga "6 VIII 2.6" "partial"
  Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange
add_to_sga "6 VIII 3.5" "special case" CommRing.Pic.inv_eq_dual
add_to_sga "6 VIII 3.5" "special case" CommRing.Pic.mk_dual
add_to_sga "6 VIII 5.2" "special case" KaehlerDifferential.mvPolynomialEquiv
add_to_sga "6 VIII 5.2" "special case" KaehlerDifferential.polynomialEquiv
add_to_sga "6 VIII 5.2" "special case" KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
add_to_sga "6 X 4.4" "special case" AlgebraicGeometry.Scheme.Hom.residueDegree
add_to_sga "6 X 5.1" "special case" CommRing.Pic
add_to_sga "6 X 5.1" "special case" CommRing.Pic.mk
add_to_sga "6 X 5.1" "special case" CommRing.Pic.mk_eq_mk_iff
add_to_sga "6 X 5.1" "special case" CommRing.Pic.mk_tensor
add_to_sga "6 X 5.1" "special case" CommRing.Pic.mul_eq_tensor
add_to_sga "6 X 6.1" "special case" ExteriorAlgebra.exteriorPower
add_to_sga "6 X 6.1" "GL(n) = Aut_O(Oⁿ)" LinearEquiv.automorphismGroup
add_to_sga "6 X 6.1" "special case" LinearMap.GeneralLinearGroup
add_to_sga "6 X 6.1" "special case" LinearMap.GeneralLinearGroup.generalLinearEquiv
add_to_sga "6 X 6.1" "special case" Matrix.GeneralLinearGroup
add_to_sga "6 X 6.1" "special case" Matrix.GeneralLinearGroup.toLin
add_to_sga "6 X 6.1" "special case" Matrix.GeneralLinearGroup.toLin'
add_to_sga "6 X 6.1" "special case" Module.Free.finsupp
add_to_sga "6 X 6.1" "special case" Module.Free.function
add_to_sga "6 X 6.1" "special case" Module.Free.pi
add_to_sga "6 X 6.1" "special case" Module.Free.prod
add_to_sga "6 X 6.1" "special case" Module.Free.tensor
add_to_sga "6 X 6.1" "special case" ModuleCat.exteriorPower
add_to_sga "6 X 6.1" "special case" ModuleCat.exteriorPower.functor
add_to_sga "6 X 6.1" "special case" TensorPower
add_to_sga "6 X 6.1" "special case" exteriorPower.instFree
add_to_sga "6 X 6.2" "special case" ExteriorAlgebra.exteriorPower
add_to_sga "6 X 6.2.2" "special case" Matrix.SpecialLinearGroup
add_to_sga "6 X 6.2.2" "special case" Matrix.SpecialLinearGroup.range_toGL
add_to_sga "6 X 6.2.2" "special case" SpecialLinearGroup
add_to_sga "6 X 6.2.2" "special case" SpecialLinearGroup.mem_range_toGeneralLinearGroup_iff
add_to_sga "6 X 6.3" "partial" Matrix.GeneralLinearGroup.det_surjective
add_to_sga "6 X 6.4" "more general" LinearEquiv.transvection
add_to_sga "6 X 6.4" "partial" LinearEquiv.transvection.apply
add_to_sga "6 X 6.4" "addition law c_(h" LinearEquiv.transvection.trans_of_right_eq
add_to_sga "6 X 6.4" Matrix.GeneralLinearGroup.transvection
add_to_sga "6 X 6.4" "special case"
  Matrix.Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow
add_to_sga "6 X 6.4" Matrix.Pivot.listTransvecRow
add_to_sga "6 X 6.4" Matrix.SpecialLinearGroup.transvection
add_to_sga "6 X 6.4" "addition law in SL(n)" Matrix.SpecialLinearGroup.transvection_add
add_to_sga "6 X 6.4" "determinant one" Matrix.TransvectionStruct.det
add_to_sga "6 X 6.4" Matrix.TransvectionStruct.toMatrix
add_to_sga "6 X 6.4" Matrix.TransvectionStruct.toSpecialLinearGroup
add_to_sga "6 X 6.4" "special case" Matrix.commutator_diag2_transvection
add_to_sga "6 X 6.4" "determinant one" Matrix.det_transvection_of_ne
add_to_sga "6 X 6.4" "partial" Matrix.mul_transvection_apply_of_ne
add_to_sga "6 X 6.4" "partial" Matrix.mul_transvection_apply_same
add_to_sga "6 X 6.4" Matrix.transvection
add_to_sga "6 X 6.4" "special case" Matrix.transvection_mem_commutator
add_to_sga "6 X 6.4" "special case" Matrix.transvection_mem_commutator₀
add_to_sga "6 X 6.4" "special case" Matrix.transvection_mem_commutator₁
add_to_sga "6 X 6.4" "partial" Matrix.transvection_mul_apply_of_ne
add_to_sga "6 X 6.4" "partial" Matrix.transvection_mul_apply_same
add_to_sga "6 X 6.4" "addition law c_{h" Matrix.transvection_mul_transvection_same
add_to_sga "6 X 6.5.2" "partial" absHom
add_to_sga "6 X 7.2" IsLocalRing.closedPoint
add_to_sga "6 X 7.5" "partial" AlgebraicGeometry.IsProper.instFstScheme
add_to_sga "6 X 7.10" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_sga "6 X 7.12" "more general" AlgebraicGeometry.IsProper.eq_valuativeCriterion
add_to_sga "6 X 7.13.3" "more general"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically
add_to_sga "6 X 7.13.3" "special case" RingHom.Smooth.isStableUnderBaseChange
add_to_sga "6 X 7.13.3" "special case"
  RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange
add_to_sga "6 X 7.13.3" "special case" RingHom.isStandardSmooth_isStableUnderBaseChange
add_to_sga "6 X 7.16" "partial" instIsAlgebraicResidueFieldOfIsIntegral
add_to_sga "6 X 7.17" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_sga "6 X 7.17.4" "partial"
  AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunctionField
add_to_sga "6 X 7.18.1" CategoryTheory.Functor.IsFinitelyAccessible
add_to_sga "6 X 7.18.1" CategoryTheory.Limits.PreservesFilteredColimits
add_to_sga "6 X 7.18.1" CategoryTheory.Limits.PreservesFilteredColimitsOfSize
add_to_sga "6 X 7.18.1" CommRingCat.flat
add_to_sga "6 X 7.18.1" IsDomain
add_to_sga "6 X 7.18.1" Module.Flat
add_to_sga "6 XII 1.6" "special case" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_sga "6 XII 1.6" AlgebraicGeometry.ValuativeCriterion
add_to_sga "6 XII 2.3" "(a)" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "6 XII 2.3" "(a)" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_sga "6 XII 2.3" "(a)" RingHom.Flat.isStableUnderBaseChange
add_to_sga "6 XII 4.1" "(1)" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "6 XII 4.1" "(1)" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "6 XII 4.2" "partial" LinearMap.tensorEqLocusEquiv
add_to_sga "6 XII 4.2" "partial" Module.Flat.eqLocus_lTensor_eq
add_to_sga "6 XIII 1.7" Polynomial.preHilbertPoly
add_to_sga "6 XIII 1.7" "partial" Polynomial.preHilbertPoly_eq_choose_sub_add
add_to_sga "6 XIII 2.2" AlgebraicGeometry.IsIntegral
add_to_sga "6 XIII 2.2" IsAlgClosed
add_to_sga "6 XIII 6.13" "more general" Ring.choose_neg
add_to_sga "6 XIII 6.13" "more general" Ring.choose_neg'
add_to_sga "6 XIII 6.13" "Q = m" Ring.multichoose_neg_self
