module  -- shake: keep-all

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 2 references registered by name

Declarations realizing numbered items of SGA 2, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "2 III 1.1" CommRing
add_to_sga "2 III 1.1" "more general" Ideal.mem_radical_iff
add_to_sga "2 III 1.1" Ideal.radical
add_to_sga "2 III 1.1" Module
add_to_sga "2 III 1.1" Module.annihilator
add_to_sga "2 III 1.1" "more general" Module.mem_annihilator
add_to_sga "2 III 1.1" Module.mem_support_iff
add_to_sga "2 III 1.1" "special case" Submodule.annihilator
add_to_sga "2 III 1.1" "special case" Submodule.mem_annihilator
add_to_sga "2 III 1.1" "special case" nilradical
add_to_sga "2 III 1.2" "(i) ⇒ (iii)" Module.annihilator_le_of_mem_support
add_to_sga "2 III 1.2" "(i) ⇔ (iii)" Module.mem_support_iff_of_finite
add_to_sga "2 III 1.2" "(i) ⇔ (iii)" Module.support_eq_zeroLocus
add_to_sga "2 III 2.1" "(iii) ⇒ (iv)" Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors
add_to_sga "2 III 2.1" "(iii) ⇒ (iv) for M = A" Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul
add_to_sga "2 III 2.1" "special case" IsLeftRegular
add_to_sga "2 III 2.1" "special case" IsRegular
add_to_sga "2 III 2.1" "special case" IsRightRegular
add_to_sga "2 III 2.1" IsSMulRegular
add_to_sga "2 III 2.1" "(i) ⇔ (iv)" ModuleCat.exists_isRegular_tfae
add_to_sga "2 III 2.1" "(iv) ⇒ (i)" ModuleCat.subsingleton_ext_of_exists_isRegular
add_to_sga "2 III 2.2" "Clause (b) under IM ≠ M"
  ModuleCat.exists_isRegular_of_exists_subsingleton_ext
add_to_sga "2 III 2.2" "special case" ModuleCat.exists_isRegular_tfae
add_to_sga "2 III 2.2" "Clause (a), special case" ModuleCat.subsingleton_ext_of_exists_isRegular
add_to_sga "2 III 2.2" RingTheory.Sequence.IsWeaklyRegular.mk
add_to_sga "2 III 2.4" "(3)⇒(4)" ModuleCat.exists_isRegular_of_exists_subsingleton_ext
add_to_sga "2 III 2.4" "partial" ModuleCat.exists_isRegular_tfae
add_to_sga "2 III 2.4" "partial" ModuleCat.subsingleton_ext_of_exists_isRegular
add_to_sga "2 III 2.8" Ideal.jacobson
add_to_sga "2 III 2.8" "special case" IsLocalRing.ResidueField
add_to_sga "2 III 2.8" Ring.jacobson
add_to_sga "2 III 2.11" Ideal.map
add_to_sga "2 III 2.11" TensorProduct
add_to_sga "2 III 3.3" "special case" ModuleCat.exists_isRegular_tfae
add_to_sga "2 III 3.4" AlgebraicGeometry.Spec
add_to_sga "2 III 3.4" AlgebraicGeometry.Spec.locallyRingedSpaceObj
add_to_sga "2 III 3.4" AlgebraicGeometry.Spec.sheafedSpaceObj
add_to_sga "2 III 3.4" "F for M = A" AlgebraicGeometry.Spec.structureSheaf
add_to_sga "2 III 3.4" AlgebraicGeometry.structureSheafInType
add_to_sga "2 III 3.4" IsLocalRing.closedPoint
add_to_sga "2 III 3.4" "(1)⇔(3), special case" ModuleCat.exists_isRegular_tfae
add_to_sga "2 IV 4.6" TensorProduct
add_to_sga "2 IV 5.2" Ideal.adicModuleTopology
add_to_sga "2 IV 5.2" Ideal.adicTopology
add_to_sga "2 IV 5.2" "partial" Module.Dual
add_to_sga "2 IV 5.2" "Case A = k = k₀ (d = 1)" Module.length_eq_finrank
add_to_sga "2 IV 5.2" "Case A = k = k₀ (d = 1)" Module.length_eq_rank
add_to_sga "2 IV 5.2" "partial" StrongDual
add_to_sga "2 IV 5.2" WithIdeal.instTopologicalSpace
add_to_sga "2 IV 5.2" WithIdeal.topologicalSpaceModule
add_to_sga "2 IV 5.3" Ext
add_to_sga "2 IV 5.3" IsRegularLocalRing
add_to_sga "2 IV 5.3" "Ext^i_A(k, special case" ModuleCat.exists_isRegular_tfae
add_to_sga "2 IV 5.3" "Ext^i_A(k, special case" ModuleCat.subsingleton_ext_of_exists_isRegular
add_to_sga "2 IV 5.4" "more general" localCohomology
add_to_sga "2 IV 5.4" "more general" localCohomology.ofDiagram
add_to_sga "2 IX 1.2" "special case" IsRegular
add_to_sga "2 IX 1.2" "partial" IsRegular.pow
add_to_sga "2 IX 1.2" "partial" IsRegular.pow_iff
add_to_sga "2 IX 1.2" IsSMulRegular
add_to_sga "2 IX 1.2" "partial" IsSMulRegular.pow
add_to_sga "2 IX 1.2" "partial" IsSMulRegular.pow_iff
add_to_sga "2 V 1.1" CochainComplex.HomComplex
add_to_sga "2 V 1.1" CochainComplex.HomComplex.CohomologyClass
add_to_sga "2 V 1.1" CochainComplex.HomComplex.homologyAddEquiv
add_to_sga "2 V 1.1" CochainComplex.HomComplex.leftHomologyData
add_to_sga "2 V 1.1" CochainComplex.HomComplex.leftHomologyData'
add_to_sga "2 V 1.1" "more general" CochainComplex.HomComplex.δ_δ
add_to_sga "2 VI 2.2" "special case" AdicCompletion.transitionMap
add_to_sga "2 VIII 1.2" ComplexShape.up
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.descHomotopy
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι_assoc
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.homotopyEquiv_inv_ι
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.homotopyEquiv_inv_ι_assoc
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.instHasInjectiveResolution
add_to_sga "2 VIII 1.4" "special case" CategoryTheory.InjectiveResolution.iso_inv_naturality
add_to_sga "2 VIII 1.4" CochainComplex.HomComplex
add_to_sga "2 VIII 1.4" CochainComplex.HomComplex.δ
add_to_sga "2 VIII 1.4" "more general" CochainComplex.Plus.exists_quasiIso_injective
add_to_sga "2 VIII 1.4" "more general"
  CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective
add_to_sga "2 VIII 1.4" "more general"
  CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
add_to_sga "2 VIII 1.4" CochainComplex.plus
add_to_sga "2 VIII 1.4" "special case" Module.instIsReflexiveOfFiniteOfProjective
add_to_sga "2 VIII 2.1" localCohomology
add_to_sga "2 VIII 2.1" localCohomology.ofSelfLERadical
add_to_sga "2 X 2.1" IsAdicComplete
add_to_sga "2 X 2.1" IsLocalRing.closedPoint
add_to_sga "2 X 2.1" "partial" IsLocalRing.isClosed_singleton_closedPoint
add_to_sga "2 XI 3.7.1" FilterBasis
add_to_sga "2 XI 3.16" "partial" IsLocalRing.closedPoint
add_to_sga "2 XII 1.2" FGModuleCat.rightDual
add_to_sga "2 XII 1.2" Module.Dual
add_to_sga "2 XII 4.1" "i" AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι
add_to_sga "2 XII 4.1" AlgebraicGeometry.Scheme.ofRestrict
add_to_sga "2 XII 4.1" "Gloss in hypothesis a)" Module.freeLocus_eq_univ
add_to_sga "2 XII 4.1" "Gloss in hypothesis a)" Module.free_of_flat_of_isLocalRing
add_to_sga "2 XIII 4.2" AlgebraicGeometry.RingedSpace.zeroLocus
add_to_sga "2 XIII 4.2" IsRegular
add_to_sga "2 XIII 4.2" nonZeroDivisors
add_to_sga "2 XIV 1.0" AlgebraicGeometry.Scheme
add_to_sga "2 XIV 1.0" AlgebraicGeometry.Scheme.IsSeparated
add_to_sga "2 XIV 1.8.2.1" "more general" CategoryTheory.Subfunctor.isSheaf_iff
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Presheaf.IsSheaf.section_ext
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Presheaf.germ_eq
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Presheaf.germ_eq_of_isBasis
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Sheaf.eq_of_locally_eq
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Sheaf.eq_of_locally_eq'
add_to_sga "2 XIV 1.8.2.1" "Zariski case" TopCat.Sheaf.eq_of_locally_eq_iff
add_to_sga "2 XIV 2.3" CategoryTheory.shiftFunctor
add_to_sga "2 XIV 2.3" CochainComplex.instHasShiftInt
add_to_sga "2 XIV 2.3" CochainComplex.shiftFunctor
