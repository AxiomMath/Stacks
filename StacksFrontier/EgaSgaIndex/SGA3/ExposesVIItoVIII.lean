module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.CoalgCat.Basic
import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Category.HopfAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DirectSum.Idempotents
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Conv
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Hopf_
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Subfunctor.Equalizer
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ENat.Defs
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Function.Coequalizer
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.MulOpposite
import Mathlib.RingTheory.Coalgebra.Primitive
import Mathlib.RingTheory.Coalgebra.Quotient
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Sheaves.LocallySurjective
import StacksCore.FieldTheory.ArtinSchreier
import StacksCore.RingTheory.AdjoinRoot
import StacksCore.RingTheory.Flat.TorsionFree
import StacksCore.RingTheory.Localization.Away.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 3 references registered by name: Exposés VII and VIII

The `add_to_sga` registrations of SGA 3, Exposés VII and VIII, re-exported by
`StacksFrontier.EgaSgaIndex.SGA3`.
-/

add_to_sga "3 VIIA 1.1" "more general" AlgebraicGeometry.Scheme.Modules.pushforward
add_to_sga "3 VIIA 1.1" "partial" CategoryTheory.sheafHom'
add_to_sga "3 VIIA 1.2.0" "partial" Derivation.instAddCommGroup
add_to_sga "3 VIIA 1.2.0" "special case" Derivation.instModule
add_to_sga "3 VIIA 1.2.0" "partial" Derivation.instSMul
add_to_sga "3 VIIA 1.2.0" "partial, special case" Derivation.mk'
add_to_sga "3 VIIA 1.2.0" "partial" DualNumber
add_to_sga "3 VIIA 1.2.0" "special case" ModuleCat.Derivation
add_to_sga "3 VIIA 1.2.0" "partial" ModuleCat.Derivation.d_map
add_to_sga "3 VIIA 1.2.0" "special case" derivationToSquareZeroEquivLift
add_to_sga "3 VIIA 1.2.0" "partial" derivationToSquareZeroEquivLift_symm_apply_apply_coe
add_to_sga "3 VIIA 1.2.1" "affine case" derivationToSquareZeroEquivLift
add_to_sga "3 VIIA 1.3" AlgebraicGeometry.Scheme.Hom.ker
add_to_sga "3 VIIA 1.3" AlgebraicGeometry.Scheme.kerFunctor
add_to_sga "3 VIIA 1.4" AlgebraicGeometry.Scheme.Γ
add_to_sga "3 VIIA 1.4" AlgebraicGeometry.Scheme.Γ_obj
add_to_sga "3 VIIA 1.4" AlgebraicGeometry.Scheme.Γ_obj_op
add_to_sga "3 VIIA 1.4.1" "partial" KaehlerDifferential.span_range_eq_ideal
add_to_sga "3 VIIA 2.3" CategoryTheory.AddGrpObj.addRight
add_to_sga "3 VIIA 2.3" CategoryTheory.GrpObj.mulRight
add_to_sga "3 VIIA 3.1" "more general" CategoryTheory.ComonObj.comul
add_to_sga "3 VIIA 3.1" "partial" CoalgCat
add_to_sga "3 VIIA 3.1" "special case" CoalgCat.Hom
add_to_sga "3 VIIA 3.1" "partial" CoalgCat.category
add_to_sga "3 VIIA 3.1" "special case" CoalgHom
add_to_sga "3 VIIA 3.1" "special case" CoalgHom.comp
add_to_sga "3 VIIA 3.1" "partial" Coalgebra
add_to_sga "3 VIIA 3.1" "(i), special case" Coalgebra.IsCocomm
add_to_sga "3 VIIA 3.1" Coalgebra.coassoc
add_to_sga "3 VIIA 3.1" Coalgebra.comm_comp_comul
add_to_sga "3 VIIA 3.1" Coalgebra.comm_comul
add_to_sga "3 VIIA 3.1" "(iii)" Coalgebra.lTensor_counit_comp_comul
add_to_sga "3 VIIA 3.1" "(ii), (iii)" Coalgebra.mk
add_to_sga "3 VIIA 3.1" "(iii)" Coalgebra.rTensor_counit_comp_comul
add_to_sga "3 VIIA 3.1" CoalgebraStruct.comul
add_to_sga "3 VIIA 3.1" "augmentation map" CoalgebraStruct.counit
add_to_sga "3 VIIA 3.1.0" "more general" CategoryTheory.Comon.instComonObjTensorObj
add_to_sga "3 VIIA 3.1.0" "partial" CategoryTheory.ComonObj.instTensorUnit_comul
add_to_sga "3 VIIA 3.1.0" "special case" CoalgCat.MonoidalCategoryAux.tensorObj_comul
add_to_sga "3 VIIA 3.1.0" "partial" Coalgebra.counitCoalgHom
add_to_sga "3 VIIA 3.1.0" "partial" Coalgebra.ext_to_ring_iff
add_to_sga "3 VIIA 3.1.0" "partial" CommSemiring.comul_apply
add_to_sga "3 VIIA 3.1.0" "special case" TensorProduct.comul_def
add_to_sga "3 VIIA 3.1.0" "special case" TensorProduct.comul_tmul
add_to_sga "3 VIIA 3.1.0" "special case" TensorProduct.instCoalgebra
add_to_sga "3 VIIA 3.1.0" "special case" TensorProduct.instCoalgebraStruct
add_to_sga "3 VIIA 3.1.1" "special case" Module.Dual
add_to_sga "3 VIIA 3.1.1" "affine, special case" PiTensorProduct.dualDistribEquiv
add_to_sga "3 VIIA 3.1.1" "affine, special case" PiTensorProduct.dualDistribEquivOfBasis
add_to_sga "3 VIIA 3.1.1" "affine, special case" TensorProduct.dualDistribEquiv
add_to_sga "3 VIIA 3.1.1" "affine, special case" TensorProduct.dualDistribEquivOfBasis
add_to_sga "3 VIIA 3.1.1" "affine, special case" dualTensorHomEquiv
add_to_sga "3 VIIA 3.1.1" "affine, special case" dualTensorHomEquivOfBasis
add_to_sga "3 VIIA 3.1.1" "affine, special case" dualTensorHom_bijective
add_to_sga "3 VIIA 3.1.2" "partial" GroupLike
add_to_sga "3 VIIA 3.1.2" "partial" IsGroupLikeElem
add_to_sga "3 VIIA 3.1.2" "special case" TensorProduct.instCoalgebra
add_to_sga "3 VIIA 3.1.2" "partial" TensorProduct.instCoalgebraStruct
add_to_sga "3 VIIA 3.2" Bialgebra
add_to_sga "3 VIIA 3.2" Bialgebra.mulCoalgHom
add_to_sga "3 VIIA 3.2" HopfAlgebra
add_to_sga "3 VIIA 3.2.1" "partial" CategoryTheory.HopfObj.one_antipode
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.antipodeAlgHom
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.antipodeAlgHomOp
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.antipode_mul
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.antipode_one
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.eq_antipode_of_convMul_id_eq_one
add_to_sga "3 VIIA 3.2.1" "partial" HopfAlgebra.eq_antipode_of_id_convMul_eq_one
add_to_sga "3 VIIA 3.2.1" "partial" MulOpposite.instCoalgebra
add_to_sga "3 VIIA 3.2.1" "partial" MulOpposite.instCoalgebraStruct
add_to_sga "3 VIIA 3.2.1" "partial" MulOpposite.instMul
add_to_sga "3 VIIA 3.2.2" "special case" GroupLike.instCommGroup
add_to_sga "3 VIIA 3.2.2" "special case" GroupLike.instGroup
add_to_sga "3 VIIA 3.2.2" "special case" GroupLike.toUnits
add_to_sga "3 VIIA 3.2.2.2" "enveloping algebra U(Γ(V" UniversalEnvelopingAlgebra
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.hom_ext
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.hom_ext_iff
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.lift
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.lift_unique
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.lift_ι_apply
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.ι
add_to_sga "3 VIIA 3.2.2.2" "partial" UniversalEnvelopingAlgebra.ι_comp_lift
add_to_sga "3 VIIA 3.2.3" Bialgebra.IsPrimitiveElem
add_to_sga "3 VIIA 3.2.3" "partial" Bialgebra.IsPrimitiveElem.commutator
add_to_sga "3 VIIA 3.2.3" "more general" Bialgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul
add_to_sga "3 VIIA 3.2.3" "more general" Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul
add_to_sga "3 VIIA 3.2.3" Coalgebra.IsSkewPrimitiveElem
add_to_sga "3 VIIA 3.2.3" "more general" Coalgebra.IsSkewPrimitiveElem.of_comul_eq_tmul_add_tmul
add_to_sga "3 VIIA 3.2.3" "more general" Coalgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul
add_to_sga "3 VIIA 3.2.3" "more general" Coalgebra.isSkewPrimitiveElem_iff_comul_eq_tmul_add_tmul
add_to_sga "3 VIIA 3.2.3" Coalgebra.skewPrimitive
add_to_sga "3 VIIA 3.3" "partial" AddMonoidAlgebra.comul_single
add_to_sga "3 VIIA 3.3" "special case" AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
add_to_sga "3 VIIA 3.3" "partial" AlgebraicGeometry.isCommMonObj_spec_asOver_spec
add_to_sga "3 VIIA 3.3" "partial" HopfAlgebra.antipodeAlgHom
add_to_sga "3 VIIA 3.3" IsGroupLikeElem
add_to_sga "3 VIIA 3.3" "Δ′(T) = T ⊗ T" LaurentPolynomial.comul_C_mul_T
add_to_sga "3 VIIA 3.3" "Δ′(T) = T ⊗ T" LaurentPolynomial.comul_C_mul_T_self
add_to_sga "3 VIIA 3.3" "Δ′(T) = T ⊗ T" LaurentPolynomial.comul_T
add_to_sga "3 VIIA 3.3" "special case" commHopfAlgCatEquivCogrpCommAlgCat
add_to_sga "3 VIIA 3.3.0" "partial" AlgebraicGeometry.hopfSpec
add_to_sga "3 VIIA 3.3.0" "special case" AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
add_to_sga "3 VIIA 3.3.0" "partial" AlgebraicGeometry.isCommMonObj_spec_asOver_spec
add_to_sga "3 VIIA 4.0" "partial" CategoryTheory.Over.Hom
add_to_sga "3 VIIA 4.1" "special case" RingHom.frobenius_comm
add_to_sga "3 VIIA 4.1" "special case" RingHom.map_frobenius
add_to_sga "3 VIIA 4.1" "special case" frobenius
add_to_sga "3 VIIA 4.1.3" "special case" coe_iterateFrobenius
add_to_sga "3 VIIA 4.1.3" "special case" iterateFrobenius
add_to_sga "3 VIIA 4.1.3" "special case" iterateFrobenius_eq_pow
add_to_sga "3 VIIA 4.2" "special case" AlgebraicGeometry.diagonal_SpecMap
add_to_sga "3 VIIA 4.3.3" "special case" FiniteField.coe_frobeniusAlgHom
add_to_sga "3 VIIA 4.3.3" "special case" FiniteField.frobeniusAlgHom_apply
add_to_sga "3 VIIA 4.3.3" "partial" FixedPoints.subalgebra
add_to_sga "3 VIIA 4.3.3" "partial" LinearEquiv.dualMap
add_to_sga "3 VIIA 4.3.3" LinearMap.dualMap
add_to_sga "3 VIIA 4.3.3" LinearMap.frobenius
add_to_sga "3 VIIA 4.3.3" "special case" LinearMap.frobenius_def
add_to_sga "3 VIIA 4.3.3" "dual module Hom_R(M,R)" Module.Dual
add_to_sga "3 VIIA 4.3.3" "underlying set of Σ^p A" MulAction.fixedPoints
add_to_sga "3 VIIA 4.3.3" SymmetricPower
add_to_sga "3 VIIA 4.3.3" "special case" frobenius
add_to_sga "3 VIIA 4.3.3" "special case" frobenius_def
add_to_sga "3 VIIA 4.3.3" "special case" iterateFrobenius
add_to_sga "3 VIIA 4.3.3" "special case" iterateFrobenius_def
add_to_sga "3 VIIA 4.3.3" "special case" iterateFrobenius_one_apply
add_to_sga "3 VIIA 5.1" AddMonoidHom.mul
add_to_sga "3 VIIA 5.1" Algebra.lsmul
add_to_sga "3 VIIA 5.1" "more general" LieAdmissibleAlgebra.instLieAlgebra
add_to_sga "3 VIIA 5.1" LieAlgebra.ad
add_to_sga "3 VIIA 5.1" "ad(x) = L_x − R_x" LieAlgebra.ad_eq_lmul_left_sub_lmul_right
add_to_sga "3 VIIA 5.1" LieAlgebra.ofAssociativeAlgebra
add_to_sga "3 VIIA 5.1" "partial" LieDerivation.ad
add_to_sga "3 VIIA 5.1" LieRing.ofAssociativeRing
add_to_sga "3 VIIA 5.1" "[a,b] = ab − ba" LieRing.of_associative_ring_bracket
add_to_sga "3 VIIA 5.1" LinearMap.mulLeft
add_to_sga "3 VIIA 5.1" LinearMap.mulRight
add_to_sga "3 VIIA 5.1" Ring.instBracket
add_to_sga "3 VIIA 5.1" "[a,b] = ab − ba" Ring.lie_def
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_char
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_char_of_commute
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_char_pow
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_char_pow_of_commute
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_eq_mul_pow_add_pow_div_char_of_commute
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_eq_mul_pow_add_pow_div_expChar_of_commute
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_expChar
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_expChar_of_commute
add_to_sga "3 VIIA 5.1" "(ii), special case" add_pow_expChar_pow
add_to_sga "3 VIIA 5.1" "more general" sub_one_pow_char_sub_one
add_to_sga "3 VIIA 5.2" "partial" Derivation.instBracket
add_to_sga "3 VIIA 5.2" "partial" Derivation.instLieAlgebra
add_to_sga "3 VIIA 5.2" "partial" Derivation.instLieRing
add_to_sga "3 VIIA 5.2" "special case" Differential
add_to_sga "3 VIIA 5.2" "commutator R-Lie algebra" LieAdmissibleAlgebra.instLieAlgebra
add_to_sga "3 VIIA 5.2" "partial" LieAlgebra.ofAssociativeAlgebra
add_to_sga "3 VIIA 5.2" "partial" LieRing.ofAssociativeRing
add_to_sga "3 VIIA 5.3" UniversalEnvelopingAlgebra
add_to_sga "3 VIIA 5.3" "partial" UniversalEnvelopingAlgebra.hom_ext
add_to_sga "3 VIIA 5.3" "partial" UniversalEnvelopingAlgebra.hom_ext_iff
add_to_sga "3 VIIA 5.3" "more general" UniversalEnvelopingAlgebra.lift
add_to_sga "3 VIIA 5.3" "more general" UniversalEnvelopingAlgebra.lift_unique
add_to_sga "3 VIIA 5.3" "existence" UniversalEnvelopingAlgebra.lift_ι_apply
add_to_sga "3 VIIA 5.3" "existence" UniversalEnvelopingAlgebra.lift_ι_apply'
add_to_sga "3 VIIA 5.3" UniversalEnvelopingAlgebra.ι
add_to_sga "3 VIIA 5.3" "existence" UniversalEnvelopingAlgebra.ι_comp_lift
add_to_sga "3 VIIA 5.3.2" "partial" LieAlgebra.ExtendScalars.instBracketTensorProduct
add_to_sga "3 VIIA 5.3.2" "more general" LieAlgebra.ExtendScalars.instLieAlgebra
add_to_sga "3 VIIA 5.3.2" "more general" LieAlgebra.ExtendScalars.instLieRing
add_to_sga "3 VIIA 5.3.3bis" "bracket formula [λ⊗x" LieAlgebra.ExtendScalars.bracket_tmul
add_to_sga "3 VIIA 5.3.3bis" "partial" LieAlgebra.ExtendScalars.instLieAlgebra
add_to_sga "3 VIIA 5.4" "partial" LieAlgebra.Prod.bracket_apply
add_to_sga "3 VIIA 5.4" "partial" LieAlgebra.Prod.instLieAlgebra
add_to_sga "3 VIIA 5.4" "partial" LieAlgebra.Prod.instLieRing
add_to_sga "3 VIIA 5.4" "partial" LieHom.prod_ext
add_to_sga "3 VIIA 5.5.3" Ideal.Cotangent
add_to_sga "3 VIIA 7.2.3" "special case" LieAlgebra.derivedSeries
add_to_sga "3 VIIA 7.2.3" "special case" LieAlgebra.derivedSeriesOfIdeal
add_to_sga "3 VIIA 7.4" "special case" Ideal.Cotangent
add_to_sga "3 VIIA 7.4" Ideal.instModuleCotangentOfAlgebra
add_to_sga "3 VIIA 7.4.3" "after localizing" Module.freeLocus_eq_univ
add_to_sga "3 VIIA 7.4.3" "partial" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIIA 8.1.4" "Converse clause"
  AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage
add_to_sga "3 VIIA 8.1.4" "Parenthetical clause"
  AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage
add_to_sga "3 VIIA 8.1.4" "partial" CategoryTheory.Sheaf.epi_of_isLocallySurjective
add_to_sga "3 VIIA 8.1.4" "partial" CategoryTheory.Sheaf.epi_of_isLocallySurjective'
add_to_sga "3 VIIA 8.1.4" "more general" CategoryTheory.Sheaf.isLocallySurjective_iff_epi
add_to_sga "3 VIIA 8.1.4" "more general" CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
add_to_sga "3 VIIA 8.1.4" "special case" TopCat.Sheaf.isLocallySurjective_iff_epi
add_to_sga "3 VIIA 8.3" "Smoothness clause" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "3 VIIA 8.3.1" "special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_sga "3 VIIA 8.4" "partial" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIIA 8.5.1" Submodule.dualAnnihilator
add_to_sga "3 VIIA 8.5.1" Submodule.dualCoannihilator
add_to_sga "3 VIIA 8.5.1" "vanishing of binomial(p" WittVector.map_frobeniusPoly.key₁
add_to_sga "3 VIIA 8.5.2" "Proof step, special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isDominant
add_to_sga "3 VIIA 8.5.2" "Proof step, special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_sga "3 VIIA 8.5.2" "Proof step, special case"
  AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd
add_to_sga "3 VIIA 8.5.2" "affine implies separated" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_sga "3 VIIA 8.5.2" "special case"
  AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_sga "3 VIIA 8.5.2" "special case" AlgebraicGeometry.ext_of_isDominant
add_to_sga "3 VIIA 8.5.2" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated
add_to_sga "3 VIIA 8.5.2" "special case" AlgebraicGeometry.ext_of_isDominant_of_isSeparated'
add_to_sga "3 VIIA 8.5.2" "Proof step, special case"
  AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant
add_to_sga "3 VIIB 0.1" CommRing
add_to_sga "3 VIIB 0.1.1" "special case"
  AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing
add_to_sga "3 VIIB 0.1.1" "partial" DirectSum.isIdempotentElem_idempotent
add_to_sga "3 VIIB 0.1.1" "special case" Ideal.isOpen_of_isMaximal
add_to_sga "3 VIIB 0.1.1" "more general" Ideal.isOpen_of_isOpen_subideal
add_to_sga "3 VIIB 0.1.1" "special case" Ideal.isOpen_pow_of_isMaximal
add_to_sga "3 VIIB 0.1.1" "special case" IsArtinianRing.equivPi
add_to_sga "3 VIIB 0.1.1" "partial" IsArtinianRing.instLocalization
add_to_sga "3 VIIB 0.1.1" "partial" IsArtinianRing.localization_artinian
add_to_sga "3 VIIB 0.1.1" "special case" IsArtinianRing.quotNilradicalEquivPi
add_to_sga "3 VIIB 0.1.1" "partial, special case" IsArtinianRing.quotNilradicalPowEquivPi
add_to_sga "3 VIIB 0.1.1" "special case" IsLocalRing.isOpen_maximalIdeal
add_to_sga "3 VIIB 0.1.1" "special case" IsLocalRing.isOpen_maximalIdeal_pow
add_to_sga "3 VIIB 0.1.1" "more general" IsLocalization.AtPrime.under_maximalIdeal
add_to_sga "3 VIIB 0.1.1" "partial" IsLocalization.Away.quotient_of_isIdempotentElem
add_to_sga "3 VIIB 0.1.1" "partial" IsLocalization.Away.quotient_span_singleton_of_isIdempotentElem
add_to_sga "3 VIIB 0.1.1" "partial" IsLocalization.away_of_isIdempotentElem
add_to_sga "3 VIIB 0.1.1" "partial" IsLocalization.away_of_isIdempotentElem_of_mul
add_to_sga "3 VIIB 0.1.1" "more general" Localization.AtPrime.eq_maximalIdeal_iff_comap_eq
add_to_sga "3 VIIB 0.1.1" "more general" Localization.AtPrime.eq_maximalIdeal_iff_under_eq
add_to_sga "3 VIIB 0.1.1" "partial" Localization.AtPrime.isLocalRing
add_to_sga "3 VIIB 0.1.1" "special case" MaximalSpectrum
add_to_sga "3 VIIB 0.1.2" "partial" Ideal.isOpen_of_isMaximal
add_to_sga "3 VIIB 0.1.2" "partial" Ideal.isOpen_pow_of_isMaximal
add_to_sga "3 VIIB 0.1.2" Ideal.jacobson
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.isMaximal_of_isPrime
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.isPrime_iff_isMaximal
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.jacobson_eq_radical
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.nilradical_eq_iInf
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.primeSpectrumEquivMaximalSpectrum
add_to_sga "3 VIIB 0.1.2" "special case" IsArtinianRing.primeSpectrum_asIdeal_range_eq
add_to_sga "3 VIIB 0.1.2" "partial"
  IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
add_to_sga "3 VIIB 0.1.2" "openness of mA_m" IsLocalRing.isOpen_maximalIdeal
add_to_sga "3 VIIB 0.1.2" "openness of mA_m" IsLocalRing.isOpen_maximalIdeal_pow
add_to_sga "3 VIIB 0.1.2" "partial" IsNilpotent.isUnit_one_sub
add_to_sga "3 VIIB 0.1.2" "special case" isArtinianRing_iff_isNilpotent_maximalIdeal
add_to_sga "3 VIIB 0.1.2" "special case" isLocalRing_of_isAdicComplete_maximal
add_to_sga "3 VIIB 0.1.3" "more general" PowerSeries.HasEval.map
add_to_sga "3 VIIB 0.2" "partial" ContinuousLinearMapClass
add_to_sga "3 VIIB 0.2" TopModuleCat.Hom
add_to_sga "3 VIIB 0.2" TopModuleCat.ofHom
add_to_sga "3 VIIB 0.2.1" IsLocalRing.ResidueField
add_to_sga "3 VIIB 0.2.1" "special case" Module.Basis.mk
add_to_sga "3 VIIB 0.2.1" "special case" Module.Basis.ofEquivFun
add_to_sga "3 VIIB 0.2.1" "special case" Module.Basis.ofRepr
add_to_sga "3 VIIB 0.2.2" "partial" Module.Dual
add_to_sga "3 VIIB 0.2.2" "projective implies flat" Module.Flat.of_projective
add_to_sga "3 VIIB 0.2.2" "partial" Module.Flat.projective_of_finitePresentation
add_to_sga "3 VIIB 0.2.2" StrongDual
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.AlgebraTensorModule.rid
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.lid
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.lid'_apply_tmul
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.lidOfCompatibleSMul
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.lidOfCompatibleSMul_tmul
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.quotTensorEquivQuotSMul
add_to_sga "3 VIIB 0.3.2" "special case" TensorProduct.tensorQuotEquivQuotSMul
add_to_sga "3 VIIB 0.3.2" "Corollary, special case" lTensor_exact
add_to_sga "3 VIIB 0.3.2" "Corollary, special case" rTensor_exact
add_to_sga "3 VIIB 0.3.5" TensorProduct.lift
add_to_sga "3 VIIB 0.3.6" "special case" MaximalSpectrum.toPiLocalizationEquiv
add_to_sga "3 VIIB 0.3.6" "special case" PiTensorProduct.dualDistrib
add_to_sga "3 VIIB 0.3.6" "special case" PiTensorProduct.dualDistribEquiv
add_to_sga "3 VIIB 0.3.6" "special case" PiTensorProduct.dualDistribEquivOfBasis
add_to_sga "3 VIIB 0.3.6" "special case" PrimeSpectrum.toPiLocalizationEquiv
add_to_sga "3 VIIB 0.3.6" StrongDual
add_to_sga "3 VIIB 0.3.6" "special case" TensorProduct.AlgebraTensorModule.dualDistrib
add_to_sga "3 VIIB 0.3.6" "special case" TensorProduct.dualDistrib
add_to_sga "3 VIIB 0.3.6" "special case" TensorProduct.dualDistribEquiv
add_to_sga "3 VIIB 0.3.6" "special case" TensorProduct.dualDistribEquivOfBasis
add_to_sga "3 VIIB 0.3.6" "partial" TensorProduct.dualDistrib_apply
add_to_sga "3 VIIB 0.3.6" "special case" dualTensorHom
add_to_sga "3 VIIB 0.3.6" "special case" dualTensorHomEquiv
add_to_sga "3 VIIB 0.3.6" "special case" dualTensorHomEquivOfBasis
add_to_sga "3 VIIB 0.3.6" "partial" dualTensorHom_apply
add_to_sga "3 VIIB 0.3.6" "special case" dualTensorHom_bijective
add_to_sga "3 VIIB 0.3.6" "special case" dualTensorHom_bijective_of_finite_left_projective_right
add_to_sga "3 VIIB 0.3.6" "bijectivity for M = A" dualTensorHom_self_right
add_to_sga "3 VIIB 0.3.6.A" "special case" dualTensorHomEquiv
add_to_sga "3 VIIB 0.3.6.A" "special case" dualTensorHom_bijective
add_to_sga "3 VIIB 0.3.7" "special case" Module.IsLocalRing.linearCombination_bijective_of_flat
add_to_sga "3 VIIB 0.3.7" "special case" Module.freeLocus_eq_univ
add_to_sga "3 VIIB 0.3.7" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIIB 0.3.7" "special case"
  Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
add_to_sga "3 VIIB 0.3.8" "special case" Module.free_of_flat_of_finrank_eq
add_to_sga "3 VIIB 0.3.8" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIIB 0.4.1" ContinuousAlgHom
add_to_sga "3 VIIB 0.4.2" CategoryTheory.LeftExactFunctor
add_to_sga "3 VIIB 0.4.2" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "3 VIIB 0.4.2" CategoryTheory.ObjectProperty.preservesFiniteLimits
add_to_sga "3 VIIB 0.4.2" "more general" CategoryTheory.coyonedaCompYonedaObj
add_to_sga "3 VIIB 0.4.2" CategoryTheory.leftExactFunctor
add_to_sga "3 VIIB 0.4.2" "more general" CategoryTheory.uliftYonedaOpCompCoyoneda
add_to_sga "3 VIIB 0.4.2" "more general" CategoryTheory.yonedaLemma
add_to_sga "3 VIIB 0.4.2" IsFiniteLength
add_to_sga "3 VIIB 0.4.2" "more general" isFiniteLength_iff_isNoetherian_isArtinian
add_to_sga "3 VIIB 0.5.B" TopModuleCat.Hom
add_to_sga "3 VIIB 1.1" "special case" IsArtinianRing.isPrime_iff_isMaximal
add_to_sga "3 VIIB 1.1" "special case" IsArtinianRing.primeSpectrum_asIdeal_range_eq
add_to_sga "3 VIIB 1.2.1" "special case" Module.Flat.projective_of_finitePresentation
add_to_sga "3 VIIB 1.2.3.A" "special case" PointwiseConvergenceCLM
add_to_sga "3 VIIB 1.2.3.A" "special case" PointwiseConvergenceCLM.hasBasis_nhds_zero
add_to_sga "3 VIIB 1.2.3.A" "(2), special case" dualTensorHomEquiv
add_to_sga "3 VIIB 1.2.4" "special case" SymmetricPower
add_to_sga "3 VIIB 1.2.4" "special case" TensorPower.galgebra
add_to_sga "3 VIIB 1.2.5" "special case" MvPowerSeries
add_to_sga "3 VIIB 1.2.C" "partial" Function.Coequalizer.mk
add_to_sga "3 VIIB 1.3" "finite-length case" Algebra.isEpi_iff_surjective_algebraMap_of_finite
add_to_sga "3 VIIB 1.3" "special case" Algebra.isEpi_of_surjective_algebraMap
add_to_sga "3 VIIB 1.3" "special case" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_sga "3 VIIB 1.3" "special case"
  AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_sga "3 VIIB 1.3" "special case" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_sga "3 VIIB 1.3" "partial" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "3 VIIB 1.3" "geometric clause" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_sga "3 VIIB 1.3" "partial" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 VIIB 1.3" "finite-length case" RingHom.surjective_of_epi_of_finite
add_to_sga "3 VIIB 1.3.1" "special case" Ideal.Quotient.liftₐ_comp
add_to_sga "3 VIIB 1.3.1" "special case" Ideal.quotientKerAlgEquivOfRightInverse
add_to_sga "3 VIIB 1.3.1" "special case" Ideal.quotientKerAlgEquivOfSurjective
add_to_sga "3 VIIB 1.3.1" "special case" Ideal.quotientKerAlgEquivOfSurjective_mk
add_to_sga "3 VIIB 1.3.2" "special case"
  IsLocalRing.split_injective_iff_lTensor_residueField_injective
add_to_sga "3 VIIB 1.3.3" "(iii), special case" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIIB 1.3.3" "(i), special case" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_sga "3 VIIB 1.3.3" "(i), special case"
  AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_sga "3 VIIB 1.3.3" "(iii), special case" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIIB 1.3.3" "(iii), special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 VIIB 1.3.3" "(i), special case" RingHom.Flat.stableUnderComposition
add_to_sga "3 VIIB 1.3.4" "more general"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfLocallyOfFinitePresentationOfSurjectiveOfFlat
add_to_sga "3 VIIB 1.3.4" "special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "3 VIIB 1.3.4" "special case"
  AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine
add_to_sga "3 VIIB 1.3.5.A" LinearMap.convRing
add_to_sga "3 VIIB 1.3.5.A" LinearMap.dualMap
add_to_sga "3 VIIB 1.3.5.A" Module.Dual
add_to_sga "3 VIIB 1.3.5.A" StrongDual
add_to_sga "3 VIIB 1.3.5.A" "special case" TensorProduct.dualDistribEquiv
add_to_sga "3 VIIB 1.3.5.C" Module.Dual
add_to_sga "3 VIIB 1.3.6" Coalgebra.IsCocomm
add_to_sga "3 VIIB 1.3.6" GroupLike
add_to_sga "3 VIIB 1.3.6" IsGroupLikeElem
add_to_sga "3 VIIB 1.3.6.B" "special case" TensorProduct.submodule_tensor_inf_tensor_submodule
add_to_sga "3 VIIB 1.4.1" TypeCat.Rel.ofPair
add_to_sga "3 VIIB 1.6" Algebra.Etale
add_to_sga "3 VIIB 1.6" "special case" Algebra.Etale.baseChange
add_to_sga "3 VIIB 1.6" "special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 1.6" Algebra.FormallyEtale
add_to_sga "3 VIIB 1.6" "partial" Algebra.FormallyEtale.comp_bijective
add_to_sga "3 VIIB 1.6" "special case" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 1.6" "special case" Algebra.FormallyEtale.iff_restrictScalars
add_to_sga "3 VIIB 1.6" "discrete topologies" Algebra.FormallyEtale.instEtaleForallOfFinite
add_to_sga "3 VIIB 1.6" "discrete topologies" Algebra.FormallyEtale.instForallOfFinite
add_to_sga "3 VIIB 1.6" "discrete base change" Algebra.FormallyEtale.instTensorProduct
add_to_sga "3 VIIB 1.6" "discrete topologies" Algebra.FormallyEtale.localization_base
add_to_sga "3 VIIB 1.6" "(F), special case" Algebra.FormallyEtale.of_isSeparable
add_to_sga "3 VIIB 1.6" "(F), special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_sga "3 VIIB 1.6" "discrete topologies" Algebra.FormallyEtale.of_restrictScalars
add_to_sga "3 VIIB 1.6" "discrete topologies" Algebra.FormallyEtale.pi_iff
add_to_sga "3 VIIB 1.6" CommAlgCat.etale
add_to_sga "3 VIIB 1.6" IsCoprime
add_to_sga "3 VIIB 1.6" "(F)" Polynomial.Monic.finrank_adjoinRoot
add_to_sga "3 VIIB 1.6" Polynomial.Separable
add_to_sga "3 VIIB 1.6" "partial" Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
add_to_sga "3 VIIB 1.6" "partial" Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
add_to_sga "3 VIIB 1.6" Polynomial.newtonMap
add_to_sga "3 VIIB 1.6" "more general"
  StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot
add_to_sga "3 VIIB 1.6" "(F), (F), special case" StandardEtalePair.instFormallyEtaleRing
add_to_sga "3 VIIB 1.6" "more general" existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
add_to_sga "3 VIIB 1.6" "partial" exists_isIdempotentElem_eq_of_ker_isNilpotent
add_to_sga "3 VIIB 1.6.1" CategoryTheory.Limits.prod.lift
add_to_sga "3 VIIB 1.6.1" "partial" CategoryTheory.Limits.pullback_fst_map_snd_isPullback
add_to_sga "3 VIIB 1.6.1" "partial" CategoryTheory.Limits.pullback_lift_diagonal_isPullback
add_to_sga "3 VIIB 1.6.B" "Clause (b), special case" Algebra.FormallyEtale.iff_restrictScalars
add_to_sga "3 VIIB 1.6.B" "(b)⇒(a), special case" Algebra.FormallyEtale.instForallOfFinite
add_to_sga "3 VIIB 1.6.B" "(a)⇒(b), special case" Algebra.FormallyEtale.instLocalization
add_to_sga "3 VIIB 1.6.B" "(a)⇒(c), discrete case" Algebra.FormallyEtale.instTensorProduct
add_to_sga "3 VIIB 1.6.B" "Clause (b), special case" Algebra.FormallyEtale.localization_base
add_to_sga "3 VIIB 1.6.B" "(a)⇔(b), special case" Algebra.FormallyEtale.pi_iff
add_to_sga "3 VIIB 1.6.B" "(a)⇔(b), special case" Algebra.basicOpen_subset_etaleLocus_iff
add_to_sga "3 VIIB 1.6.B" "(a)⇔(b), special case" Algebra.etaleLocus_eq_univ_iff
add_to_sga "3 VIIB 1.6.B" "(a)⇔(b), special case" Algebra.etaleLocus_eq_univ_iff_etale
add_to_sga "3 VIIB 1.6.C" "special case" Algebra.Etale.baseChange
add_to_sga "3 VIIB 1.6.C" "special case" Algebra.FormallyEtale.instTensorProduct
add_to_sga "3 VIIB 1.6.C" "special case" AlgebraicGeometry.Scheme.instEtaleFiberToSpecResidueField
add_to_sga "3 VIIB 1.6.D" "partial, special case" Algebra.FormallyEtale.comp_bijective
add_to_sga "3 VIIB 1.6.D" "partial" Algebra.FormallySmooth.exists_lift
add_to_sga "3 VIIB 1.6.D" "partial" Algebra.FormallyUnramified.lift_unique
add_to_sga "3 VIIB 1.6.D" "partial" IsAdicComplete.StrictMono.eq_liftRingHom
add_to_sga "3 VIIB 1.6.D" "partial" IsArtinianRing.isNilpotent_nilradical
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.FormallyEtale.of_isSeparable
add_to_sga "3 VIIB 1.6.E" "special case" Algebra.FormallyEtale.of_isSeparable_aux
add_to_sga "3 VIIB 1.6.E" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "3 VIIB 2.1" "partial" AlgHom.comp_convMul_distrib
add_to_sga "3 VIIB 2.1" "special case" AlgHom.convGroup
add_to_sga "3 VIIB 2.1" "partial" AlgHom.convInv
add_to_sga "3 VIIB 2.1" "partial" AlgHom.convMul_apply
add_to_sga "3 VIIB 2.1" "partial" AlgHom.convMul_def
add_to_sga "3 VIIB 2.1" "partial" AlgHom.convOne_apply
add_to_sga "3 VIIB 2.1" "partial" AlgHom.convOne_def
add_to_sga "3 VIIB 2.1" "special case" AlgHom.instCommGroupWithConvOfIsCocomm
add_to_sga "3 VIIB 2.1" "partial" AlgHom.instMulWithConv
add_to_sga "3 VIIB 2.1" "partial" AlgHom.instOneWithConv
add_to_sga "3 VIIB 2.1" "partial" AlgHom.toLinearMap_convMul
add_to_sga "3 VIIB 2.1" "partial" AlgHom.toLinearMap_convOne
add_to_sga "3 VIIB 2.1" "ω_{G/k} = I_A / I_A²" Algebra.Extension.Cotangent
add_to_sga "3 VIIB 2.1" "special case" Algebra.Extension.Cotangent.module
add_to_sga "3 VIIB 2.1" "special case" Algebra.Extension.instModuleCotangent
add_to_sga "3 VIIB 2.1" "special case" Algebra.algebraMap
add_to_sga "3 VIIB 2.1" "special case" AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
add_to_sga "3 VIIB 2.1" "partial" CategoryTheory.Conv.instMul
add_to_sga "3 VIIB 2.1" "more general" CategoryTheory.Grp.homMk
add_to_sga "3 VIIB 2.1" "more general" CategoryTheory.Grp.homMk'
add_to_sga "3 VIIB 2.1" "more general" CategoryTheory.Grp.ofHom
add_to_sga "3 VIIB 2.1" "special case" CommHopfAlgCat.Hom
add_to_sga "3 VIIB 2.1" "special case" FormalGroup
add_to_sga "3 VIIB 2.1" "special case" HopfAlgCat.Hom
add_to_sga "3 VIIB 2.1" "(iii)" HopfAlgebra
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.antipodeAlgHom
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.antipode_mul
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.antipode_mul_antidistrib
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.antipode_mul_distrib
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.antipode_one
add_to_sga "3 VIIB 2.1" "(iii), special case" HopfAlgebra.eq_antipode_of_convMul_id_eq_one
add_to_sga "3 VIIB 2.1" "special case" Ideal.Cotangent
add_to_sga "3 VIIB 2.1" "special case" Ideal.instModuleCotangentOfAlgebra
add_to_sga "3 VIIB 2.1" "functoriality in B" LinearMap.algHom_comp_convMul_distrib
add_to_sga "3 VIIB 2.1" "functoriality in B" LinearMap.algHom_comp_convOne
add_to_sga "3 VIIB 2.1" "partial" LinearMap.convCommRing
add_to_sga "3 VIIB 2.1" "special case" LinearMap.convMul
add_to_sga "3 VIIB 2.1" "identity element η_B∘ε_A" LinearMap.instOneWithConvId
add_to_sga "3 VIIB 2.1" "special case" LinearMap.convOne_apply
add_to_sga "3 VIIB 2.1" "identity element η_B∘ε_A" LinearMap.convOne_def
add_to_sga "3 VIIB 2.1" "partial" LinearMap.convRing
add_to_sga "3 VIIB 2.1" LinearMap.mul'
add_to_sga "3 VIIB 2.1" "m_A(a⊗b)=ab" LinearMap.mul'_apply
add_to_sga "3 VIIB 2.1" RingHom.ker
add_to_sga "3 VIIB 2.1" "special case" commHopfAlgCatEquivCogrpCommAlgCat
add_to_sga "3 VIIB 2.2" Coalgebra.IsCocomm
add_to_sga "3 VIIB 2.2" "partial" GroupLike.instGroup
add_to_sga "3 VIIB 2.2" HopfAlgebra
add_to_sga "3 VIIB 2.2.1" "Essential-image clause" AlgebraicGeometry.essImage_hopfSpec
add_to_sga "3 VIIB 2.2.1" "partial" AlgebraicGeometry.hopfSpec
add_to_sga "3 VIIB 2.2.1" "partial" AlgebraicGeometry.hopfSpec.fullyFaithful
-- The target is Mathlib's anonymous instance `HopfAlgebra R Γ(G, ⊤)` of
-- `Mathlib.AlgebraicGeometry.Group.Affine`, whose auto-generated name (119 characters
-- without its namespace) does not fit on one line; it is assembled from pieces here.
run_cmd do
  let decl := Lean.Name.mkStr `AlgebraicGeometry <|
    "instHopfAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpens" ++
      "TopOfGrpObjOverSchemeSpecAsOverOfIsAffine"
  Lean.Elab.Command.elabCommand
    (← `(add_to_sga "3 VIIB 2.2.1" "object part of T ↦ O(T)" $(Lean.mkIdent decl)))
add_to_sga "3 VIIB 2.2.1" "partial" CommHopfAlgCat
add_to_sga "3 VIIB 2.2.1" "partial" CommHopfAlgCat.Hom
add_to_sga "3 VIIB 2.2.1" "special case" CommHopfAlgCat.instCategory
add_to_sga "3 VIIB 2.2.1" "Objects of H_k" HopfAlgCat
add_to_sga "3 VIIB 2.2.1" "Morphisms of H_k" HopfAlgCat.Hom
add_to_sga "3 VIIB 2.2.1" "Ambient category H_k" HopfAlgCat.category
add_to_sga "3 VIIB 2.2.1" "partial" HopfAlgebra
add_to_sga "3 VIIB 2.2.1" "special case" Module.Flat
add_to_sga "3 VIIB 2.2.1" "special case" PiTensorProduct.dualDistribEquiv
add_to_sga "3 VIIB 2.2.1" "special case" TensorProduct.dualDistribEquiv
add_to_sga "3 VIIB 2.2.1" "special case" TensorProduct.dualDistribEquivOfBasis
add_to_sga "3 VIIB 2.2.1" "partial" commHopfAlgCatEquivCogrpCommAlgCat
add_to_sga "3 VIIB 2.2.1" "special case" dualTensorHomEquiv
add_to_sga "3 VIIB 2.2.1" "special case" dualTensorHomEquivOfBasis
add_to_sga "3 VIIB 2.2.1" "special case" dualTensorHom_bijective
add_to_sga "3 VIIB 2.2.2" "(G)" AlgebraicGeometry.hopfSpec
add_to_sga "3 VIIB 2.2.2" "(G)" AlgebraicGeometry.hopfSpec.fullyFaithful
add_to_sga "3 VIIB 2.2.2" "Clause of 2.2.2" AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
add_to_sga "3 VIIB 2.3.1" "partial" GroupLike.instCommGroup
add_to_sga "3 VIIB 2.3.1" "partial" GroupLike.instGroup
add_to_sga "3 VIIB 2.3.1" "special case" GroupLike.toUnits
add_to_sga "3 VIIB 2.3.1" "Left inverse" IsGroupLikeElem.antipode_mul_cancel
add_to_sga "3 VIIB 2.3.1" "partial" IsGroupLikeElem.isUnit
add_to_sga "3 VIIB 2.3.1" "Right inverse" IsGroupLikeElem.mul_antipode_cancel
add_to_sga "3 VIIB 2.3.2" "partial" AddMonoidHom.toHomAddUnits
add_to_sga "3 VIIB 2.3.2" "more general" CategoryTheory.Functor
add_to_sga "3 VIIB 2.3.2" "partial" IsUnit.map
add_to_sga "3 VIIB 2.3.2" "special case" LinearMap.mul'_tensor
add_to_sga "3 VIIB 2.3.2" "special case" Module.instIsReflexiveOfFiniteOfProjective
add_to_sga "3 VIIB 2.3.2" "partial" MonoidHom.coe_toHomUnits
add_to_sga "3 VIIB 2.3.2" "partial" MonoidHom.toHomUnits
add_to_sga "3 VIIB 2.3.2" "special case" MonoidHom.toHomUnitsMulEquiv
add_to_sga "3 VIIB 2.3.2" "special case" PiTensorProduct.instMul
add_to_sga "3 VIIB 2.3.2" "special case" PiTensorProduct.mul
add_to_sga "3 VIIB 2.3.2" "special case" PiTensorProduct.mul_tprod_tprod
add_to_sga "3 VIIB 2.3.2" "partial" TensorProduct
add_to_sga "3 VIIB 2.3.2" "partial" Units
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHom
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHomEquiv
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHomEquivOfBasis
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHom_apply
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHom_bijective
add_to_sga "3 VIIB 2.3.2" "special case" dualTensorHom_bijective_of_finite_left_projective_right
add_to_sga "3 VIIB 2.4.1" "pr₁ is an epimorphism" AlgebraicGeometry.Flat.epi_of_flat_of_surjective
add_to_sga "3 VIIB 2.4.1" "flatness of pr₁ : X → T" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 VIIB 2.4.1" "special case" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 VIIB 2.4.1" "pr₁ is an epimorphism"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "3 VIIB 2.4.1" "special case" AlgebraicGeometry.Surjective.instFstScheme
add_to_sga "3 VIIB 2.4.1" "special case" AlgebraicGeometry.Surjective.instSndScheme
add_to_sga "3 VIIB 2.4.1" "special case"
  AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfLocallyOfFinitePresentation
add_to_sga "3 VIIB 2.4.1" CategoryTheory.Abelian.factorThruCoimage
add_to_sga "3 VIIB 2.4.1" CategoryTheory.Epi
add_to_sga "3 VIIB 2.4.1" CategoryTheory.Limits.pullback
add_to_sga "3 VIIB 2.4.1" RingHom.range
add_to_sga "3 VIIB 2.4.A" "partial" GroupExtension.Splitting.conjAct
add_to_sga "3 VIIB 2.4.A" "partial" GroupExtension.Splitting.semidirectProductMulEquiv
add_to_sga "3 VIIB 2.4.A" "partial" GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv
add_to_sga "3 VIIB 2.5" Action.IsContinuous
add_to_sga "3 VIIB 2.5" "special case" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 2.5" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_sga "3 VIIB 2.5" "special case" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "3 VIIB 2.5" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "3 VIIB 2.5" AlgebraicGeometry.Scheme.Etale
add_to_sga "3 VIIB 2.5" "more general" CategoryTheory.Equivalence.mapAddGrp
add_to_sga "3 VIIB 2.5" "more general" CategoryTheory.Equivalence.mapGrp
add_to_sga "3 VIIB 2.5" "special case"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiberOfIsSepClosed
add_to_sga "3 VIIB 2.5" ContinuousSMul
add_to_sga "3 VIIB 2.5" DiscreteContAction
add_to_sga "3 VIIB 2.5" "more general" continuousSMul_iff_stabilizer_isOpen
add_to_sga "3 VIIB 2.5" "partial" stabilizer_isOpen
add_to_sga "3 VIIB 2.5.A" IntermediateField.fixedField
add_to_sga "3 VIIB 2.6" "special case" Algebra.Extension.Cotangent
add_to_sga "3 VIIB 2.6" "special case" Bialgebra.IsPrimitiveElem
add_to_sga "3 VIIB 2.6" "special case" Bialgebra.IsPrimitiveElem.commutator
add_to_sga "3 VIIB 2.6" "more general" Coalgebra.IsSkewPrimitiveElem
add_to_sga "3 VIIB 2.6" "partial" Coalgebra.skewPrimitive
add_to_sga "3 VIIB 2.6" DualNumber
add_to_sga "3 VIIB 2.6" "special case" Ideal.Cotangent
add_to_sga "3 VIIB 2.6" "more general" TrivSqZeroExt
add_to_sga "3 VIIB 2.6.2" Coalgebra.IsSkewPrimitiveElem
add_to_sga "3 VIIB 2.6.2" Coalgebra.skewPrimitive
add_to_sga "3 VIIB 2.6.2" GroupLike
add_to_sga "3 VIIB 2.6.2" "(C), special case" GroupLike.instCommGroup
add_to_sga "3 VIIB 2.6.2" "(C)" GroupLike.instGroup
add_to_sga "3 VIIB 2.6.2" IsGroupLikeElem
add_to_sga "3 VIIB 2.7" "more general" CategoryTheory.MonObj
add_to_sga "3 VIIB 2.7" "more general" CategoryTheory.MonObj.one
add_to_sga "3 VIIB 2.8" ContinuousSMul
add_to_sga "3 VIIB 2.8" "partial" IsSimpleModule.annihilator_isMaximal
add_to_sga "3 VIIB 2.8" "partial" LinearMap.convAlgebra
add_to_sga "3 VIIB 2.8" "partial" LinearMap.convCommRing
add_to_sga "3 VIIB 2.8" "partial" Module.Dual
add_to_sga "3 VIIB 2.9" "partial" LinearMap.convAlgebra
add_to_sga "3 VIIB 2.9" "If C is cocommutative" LinearMap.convCommRing
add_to_sga "3 VIIB 2.9" "If C is cocommutative" LinearMap.convCommSemiring
add_to_sga "3 VIIB 2.9" "partial" Module.Dual
add_to_sga "3 VIIB 2.9" "partial" StrongDual
add_to_sga "3 VIIB 2.9" "partial" Submodule.dualAnnihilator
add_to_sga "3 VIIB 2.9" "partial" Submodule.dualCoannihilator
add_to_sga "3 VIIB 2.9" "partial" Subspace.dualAnnihilatorGci
add_to_sga "3 VIIB 2.9" "partial" Subspace.dualAnnihilator_dualCoannihilator_eq
add_to_sga "3 VIIB 2.9.1" GroupLike
add_to_sga "3 VIIB 2.9.1" GroupLike.instGroup
add_to_sga "3 VIIB 2.9.1" IsGroupLikeElem
add_to_sga "3 VIIB 3.2" Bialgebra.IsPrimitiveElem
add_to_sga "3 VIIB 3.2" Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul
add_to_sga "3 VIIB 3.2" "more general" Coalgebra.IsSkewPrimitiveElem
add_to_sga "3 VIIB 3.2" "more general" Coalgebra.isSkewPrimitiveElem_iff_comul_eq_tmul_add_tmul
add_to_sga "3 VIIB 3.2" "more general" Coalgebra.skewPrimitive
add_to_sga "3 VIIB 3.2" "partial" IsArtinianRing.instIsSemiprimaryRing
add_to_sga "3 VIIB 3.2" "partial" IsArtinianRing.isNilpotent_jacobson_bot
add_to_sga "3 VIIB 3.2" "partial" IsArtinianRing.isNilpotent_nilradical
add_to_sga "3 VIIB 3.2" IsNilpotent.exp
add_to_sga "3 VIIB 3.2" "more general" IsNilpotent.exp_add_of_commute
add_to_sga "3 VIIB 3.2" "partial" IsNilpotent.exp_eq_sum
add_to_sga "3 VIIB 3.2" "more general" IsNilpotent.map_exp
add_to_sga "3 VIIB 3.2" "U = C with C local" isArtinianRing_iff_isNilpotent_maximalIdeal
add_to_sga "3 VIIB 3.3.3" AlgebraicClosure
add_to_sga "3 VIIB 3.3.3" Field.absoluteGaloisGroup
add_to_sga "3 VIIB 3.3.3" Field.instGroupAbsoluteGaloisGroup
add_to_sga "3 VIIB 3.3.3" "partial" Field.instIsTopologicalGroupAbsoluteGaloisGroup
add_to_sga "3 VIIB 3.3.3" Field.instTopologicalSpaceAbsoluteGaloisGroup
add_to_sga "3 VIIB 3.3.3" "more general" InfiniteGalois.profiniteGalGrp
add_to_sga "3 VIIB 3.3.3" "partial" LieAlgebra.ExtendScalars.map
add_to_sga "3 VIIB 3.3.3" "partial" LieAlgebra.ExtendScalars.map_apply_tmul
add_to_sga "3 VIIB 3.3.3" "partial" Module.Flat.iff_preservesFiniteLimits_tensorLeft
add_to_sga "3 VIIB 3.3.3" "partial" Module.Flat.iff_preservesFiniteLimits_tensorRight
add_to_sga "3 VIIB 3.3.3" "partial"
  Module.Flat.instPreservesFiniteLimitsModuleCatTensorLeftOfCarrier
add_to_sga "3 VIIB 3.3.3" "partial" MulActionHom
add_to_sga "3 VIIB 3.3.3" krullTopology
add_to_sga "3 VIIB 4.1.1" "partial" AdicCompletion
add_to_sga "3 VIIB 4.2.1" GroupLike
add_to_sga "3 VIIB 4.2.1" "partial" GroupLike.instGroup
add_to_sga "3 VIIB 4.2.1" IsGroupLikeElem
add_to_sga "3 VIIB 4.3.1" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIIB 4.4.A" "partial" Ideal.Cotangent
add_to_sga "3 VIIB 5.1.1" "(1)" HopfAlgebra.Quotient.instQuotientIdeal
add_to_sga "3 VIIB 5.1.1" "conditions (1)" Ideal.IsHopfIdeal
add_to_sga "3 VIIB 5.1.1" "conditions (1)" Submodule.IsCoideal
add_to_sga "3 VIIB 5.2" "partial" CharP
add_to_sga "3 VIIB 5.2" "partial" ENat
add_to_sga "3 VIIB 5.2" PerfectField
add_to_sga "3 VIIB 5.2" PerfectRing
add_to_sga "3 VIIB 5.2.1" Algebra.Extension.Cotangent
add_to_sga "3 VIIB 5.2.1" Algebra.Extension.Cotangent.mk
add_to_sga "3 VIIB 5.2.1" Ideal.Cotangent
add_to_sga "3 VIIB 5.2.1" Ideal.comap
add_to_sga "3 VIIB 5.2.1" Ideal.cotangentIdeal
add_to_sga "3 VIIB 5.2.1.C" Filter.eventuallyConst_atTop
add_to_sga "3 VIIB 5.2.1.C" "(ii)"
  IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing
add_to_sga "3 VIIB 5.2.3" "partial" LinearMap.frobenius
add_to_sga "3 VIIB 5.2.3" "formula of the map" LinearMap.frobenius_def
add_to_sga "3 VIIB 5.2.3" "partial" LinearMap.iterateFrobenius
add_to_sga "3 VIIB 5.2.3" "partial" frobenius
add_to_sga "3 VIIB 5.2.3" "partial" frobeniusEquiv
add_to_sga "3 VIIB 5.2.3" "partial" instAlgebraAdjoinPthRoots
add_to_sga "3 VIIB 5.2.3" "more general" iterateFrobeniusEquiv
add_to_sga "3 VIIB 5.2.4" "lower-row exactness at J" Algebra.Extension.Cotangent.ker_mk
add_to_sga "3 VIIB 5.2.4" Algebra.Extension.Cotangent.mk
add_to_sga "3 VIIB 5.2.4" "lower-row exactness at J" Algebra.Extension.Cotangent.mk_eq_zero_iff
add_to_sga "3 VIIB 5.2.4" "special case" Algebra.Extension.Cotangent.mk_surjective
add_to_sga "3 VIIB 5.2.4" Ideal.Cotangent
add_to_sga "3 VIIB 5.2.4" "special case" Ideal.mapCotangent_ker_of_surjective
add_to_sga "3 VIIB 5.2.4" "special case" Ideal.mapCotangent_toCotangent
add_to_sga "3 VIIB 5.2.4" "lower-row exactness at J" Ideal.map_toCotangent_ker
add_to_sga "3 VIIB 5.2.4" Ideal.toCotangent
add_to_sga "3 VIIB 5.2.4" "special case" Ideal.toCotangent_range
add_to_sga "3 VIIB 5.2.4" "special case" Ideal.toCotangent_surjective
add_to_sga "3 VIIB 5.2.5" Algebra.Extension.Cotangent
add_to_sga "3 VIIB 5.2.5" Algebra.Extension.Cotangent.mk
add_to_sga "3 VIIB 5.2.5" Ideal.Cotangent
add_to_sga "3 VIIB 5.2.5" "partial" Ideal.mapCotangent_surjective_of_comap_eq
add_to_sga "3 VIIB 5.2.5" Ideal.toCotangent
add_to_sga "3 VIIB 5.2.5" IsLocalRing.CotangentSpace
add_to_sga "3 VIIB 5.5.2" AdicCompletion
add_to_sga "3 VIIB 5.5.2" "special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_sga "3 VIIB 5.5.2" "special case"
  RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_sga "3 VIIB 5.5.2" "partial" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_sga "3 VIIB 5.5.2" "partial" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_sga "3 VIII 1.7.1" "special case" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "3 VIII 1.7.2" "more general"
  AlgebraicGeometry.Scheme.LocalRepresentability.instIsIsoSheafZariskiTopologyTypeYonedaGluedToSheaf
add_to_sga "3 VIII 1.7.2" "more general"
  AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable
add_to_sga "3 VIII 1.7.2" "more general"
  AlgebraicGeometry.Scheme.LocalRepresentability.representableBy
add_to_sga "3 VIII 2.1" "partial" Algebra.Smooth.of_formallySmooth_fiber
add_to_sga "3 VIII 3.4" CategoryTheory.Limits.kernel
add_to_sga "3 VIII 3.4" Module.Finite
add_to_sga "3 VIII 3.4" MonoidHom.ker
add_to_sga "3 VIII 4.2" "special case" Module.Invertible.algEquivOfRing
add_to_sga "3 VIII 6.2" "(c), special case" IsBaseChange.free
add_to_sga "3 VIII 6.2" "(a), special case" Module.FaithfullyFlat.instOfNontrivialOfFree
add_to_sga "3 VIII 6.2" "(a), special case" Module.Flat.of_free
add_to_sga "3 VIII 6.2" "special case" Module.IsLocalRing.linearCombination_bijective_of_flat
add_to_sga "3 VIII 6.2" "special case" Module.free_of_flat_of_finrank_eq
add_to_sga "3 VIII 6.2" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "3 VIII 6.5" "special case" AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
add_to_sga "3 VIII 6.5" "more general" CategoryTheory.Subfunctor.equalizer
add_to_sga "3 VIII 6.8" Module.Dual
add_to_sga "3 VIII 7.1" "equivalence" AlgebraicGeometry.IsImmersion.comp_iff
add_to_sga "3 VIII 7.1" "partial" AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective
