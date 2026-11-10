module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Defs
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Basic.Finite.Defs
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Condensed.AB
import Mathlib.Condensed.Discrete.Characterization
import Mathlib.Condensed.Limits
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Trace.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import StacksCore.Algebra.Algebra.Subalgebra.Centralizer
import StacksCore.Algebra.Module.Projective
import StacksCore.CategoryTheory.Localization.CalculusOfFraction.Abelian
import StacksCore.RingTheory.NormTrace
import StacksCore.RingTheory.SkolemNoether
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 5 references registered by name

Declarations realizing numbered items of SGA 5, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "5 I 5.1.9" Module.Dual
add_to_sga "5 I 5.1.9" Representation.dual
add_to_sga "5 I App.1.2" CategoryTheory.ObjectProperty.FullSubcategory
add_to_sga "5 III 1.1" IsNoetherianRing
add_to_sga "5 III 1.1" IsUnit
add_to_sga "5 III 3.1" "Case X_1=X_2=S of 3.1.1" dualTensorHomEquiv
add_to_sga "5 III 3.1" "Case X_1=X_2=S of 3.1.1" dualTensorHomEquivOfBasis
add_to_sga "5 III 3.1" "special case" rTensorHomEquivHomRTensor
add_to_sga "5 III 3.2" "more general" AlgebraicGeometry.Scheme.CanonicallyOver
add_to_sga "5 III 3.2" "more general" AlgebraicGeometry.Scheme.Over
add_to_sga "5 III 3.2" "more general" AlgebraicGeometry.Scheme.asOver
add_to_sga "5 III 4.1" "4.1.5, special case" LinearMap.trace_comp_comm
add_to_sga "5 III 4.1" "4.1.5, special case" LinearMap.trace_comp_comm'
add_to_sga "5 III 4.1" "4.1.5, special case" LinearMap.trace_mul_comm
add_to_sga "5 III 6.3" "special case" TensorProduct.dualDistribEquiv
add_to_sga "5 III 6.3" "special case" homTensorHomEquiv
add_to_sga "5 III 6.3" "special case" rTensorHomEquivHomRTensor
add_to_sga "5 III 6.4" "special case" coe_dualTensorHomEquivOfBasis
add_to_sga "5 III 6.4" "special case" dualTensorHomEquivOfBasis_apply
add_to_sga "5 III 6.4" "special case" dualTensorHomEquivOfBasis_symm_cancel_left
add_to_sga "5 III 6.4" "special case" dualTensorHomEquivOfBasis_symm_cancel_right
add_to_sga "5 III 6.8" "partial" Algebra.trace
add_to_sga "5 III 6.8" Ideal.Cotangent
add_to_sga "5 III 6.8" Ideal.cotangentIdeal
add_to_sga "5 III 6.9" "special case" LinearMap.trace_comp_comm'
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_comp_comm
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_comp_comm'
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_comp_cycle
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_comp_cycle'
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_mul_comm
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_mul_cycle
add_to_sga "5 IIIB 1.1" "special case" LinearMap.trace_mul_cycle'
add_to_sga "5 IIIB 2.1" "(1)" AlgebraicGeometry.Scheme.Hom.isPullback_resLE
add_to_sga "5 IIIB 2.1" "(1)" AlgebraicGeometry.Scheme.Hom.resLE_comp_ι
add_to_sga "5 IIIB 2.1" "(1)" AlgebraicGeometry.isPullback_morphismRestrict
add_to_sga "5 IIIB 2.1" "(1)" AlgebraicGeometry.morphismRestrict_ι
add_to_sga "5 IIIB 3.1" "special case" ZMod.chineseRemainder
add_to_sga "5 IIIB 5.0" "special case" FDRep.dualTensorIsoLinHom_hom_hom
add_to_sga "5 IIIB 5.0" "special case" FGModuleCat.FGModuleCatEvaluation
add_to_sga "5 IIIB 5.0" "special case" FGModuleCat.FGModuleCatEvaluation_apply
add_to_sga "5 IIIB 5.0" "special case" FGModuleCat.FGModuleCatEvaluation_apply'
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace_eq_contract
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace_eq_contract'
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace_eq_contract_apply
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace_eq_contract_of_basis
add_to_sga "5 IIIB 5.0" "special case" LinearMap.trace_eq_contract_of_basis'
add_to_sga "5 IIIB 5.0" "special case" Module.Dual.eval
add_to_sga "5 IIIB 5.0" "special case" coe_dualTensorHomEquivOfBasis
add_to_sga "5 IIIB 5.0" "5.0.2, special case" contractLeft_apply
add_to_sga "5 IIIB 5.0" "5.0.3" dualTensorHom
add_to_sga "5 IIIB 5.0" "special case" dualTensorHomEquiv
add_to_sga "5 IIIB 5.0" "special case" dualTensorHomEquivOfBasis_apply
add_to_sga "5 IIIB 5.0" "5.0.10, 5.0.3" dualTensorHomEquivOfBasis_symm_cancel_left
add_to_sga "5 IIIB 5.0" "5.0.10, 5.0.3" dualTensorHomEquivOfBasis_symm_cancel_right
add_to_sga "5 IIIB 5.0" "special case" dualTensorHomEquivOfBasis_toLinearMap
add_to_sga "5 IIIB 5.0" "5.0.3" dualTensorHom_apply
add_to_sga "5 IIIB 5.0" "special case" dualTensorHom_bijective
add_to_sga "5 IIIB 5.1" Bimod
add_to_sga "5 IIIB 5.1" Bimod.regular
add_to_sga "5 IIIB 5.1" "left A-module" Module
add_to_sga "5 IIIB 5.1" "partial" ModuleCat
add_to_sga "5 IIIB 5.1" "partial" MulOpposite
add_to_sga "5 IIIB 5.1" MulOpposite.instAlgebra
add_to_sga "5 IIIB 5.1" "A as a left Aᵉ-module" instModuleTensorProductMop
add_to_sga "5 IIIB 5.2" "special case" TensorProduct.AlgebraTensorModule.lift.equiv
add_to_sga "5 IIIB 5.4" "special case" LinearMap.tensorProduct
add_to_sga "5 IIIB 5.4" "special case" LinearMap.tensorProductEnd
add_to_sga "5 IIIB 5.4" "5.4(a), special case" SkolemNoether.Algebra.tensorMopToEnd
add_to_sga "5 IIIB 5.4" "more general" TensorProduct.AlgebraTensorModule.homTensorHomMap
add_to_sga "5 IIIB 5.4" "5.4.1" TensorProduct.lTensorHomToHomLTensor_apply
add_to_sga "5 IIIB 5.4" "5.4.1" TensorProduct.rTensorHomToHomRTensor_apply
add_to_sga "5 IIIB 5.4" "special case" lTensorHomEquivHomLTensor_apply
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace_eq_contract'
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace_eq_contract_of_basis'
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace_eq_sum_trace_restrict
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace_eq_sum_trace_restrict'
add_to_sga "5 IIIB 5.6" "special case" LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup
add_to_sga "5 IIIB 5.7" AlgEquiv.moduleEndSelf
add_to_sga "5 IIIB 5.7" "inverse map a ↦ (x ↦ xa)" AlgEquiv.moduleEndSelf_apply_apply
add_to_sga "5 IIIB 5.7" "partial" AlgEquiv.moduleEndSelf_symm_apply
add_to_sga "5 IIIB 5.7" "For A = K and F = K" LinearMap.trace_eq_contract
add_to_sga "5 IIIB 5.7" "For A = K and F = K" LinearMap.trace_eq_contract'
add_to_sga "5 IIIB 5.7" "For A = K and F = K" LinearMap.trace_eq_contract_apply
add_to_sga "5 IIIB 5.7" "For A = K and F = K" LinearMap.trace_eq_contract_of_basis
add_to_sga "5 IIIB 5.7" "For A = K and F = K" LinearMap.trace_eq_contract_of_basis'
add_to_sga "5 IIIB 5.7" "partial" RingEquiv.moduleEndSelf
add_to_sga "5 IIIB 5.7" "partial" RingEquiv.moduleEndSelf_symm_apply
add_to_sga "5 IIIB 5.7" "partial" Subalgebra.centralizer_range_lmul
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_comp_comm
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_comp_comm'
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_comp_cycle
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_comp_cycle'
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_conj
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_conj'
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_mul_comm
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_mul_cycle
add_to_sga "5 IIIB 5.8" "special case" LinearMap.trace_mul_cycle'
add_to_sga "5 IIIB 5.8" "special case" Matrix.trace_mul_cycle
add_to_sga "5 IIIB 5.8" "special case" Matrix.trace_mul_cycle'
add_to_sga "5 IIIB 5.10" "special case" Algebra.trace'
add_to_sga "5 IIIB 5.10" Module.FinitePresentation
add_to_sga "5 IIIB 5.10" Module.Flat
add_to_sga "5 IIIB 5.10" "partial" Module.Flat.projective_of_finitePresentation
add_to_sga "5 IIIB 5.10.11" "special case" Algebra.trace_comp_trace
add_to_sga "5 IIIB 5.10.11" "special case" Algebra.trace_comp_trace_of_basis
add_to_sga "5 IIIB 5.10.11" "special case" Algebra.trace_trace
add_to_sga "5 IIIB 5.10.11" "special case" Algebra.trace_trace_of_basis
add_to_sga "5 IIIB 5.10.11" "special case" trace_restrictScalars
add_to_sga "5 IIIB 5.10.11" "special case" trace_trace
add_to_sga "5 IIIB 5.11" ConjClasses
add_to_sga "5 IIIB 5.11" "finiteness of G" Finite
add_to_sga "5 IIIB 5.11" FiniteGrp.of
add_to_sga "5 IIIB 5.11" "partial" Group
add_to_sga "5 IIIB 5.11" MonoidAlgebra
add_to_sga "5 IIIB 5.11.1" Cardinal.mk
add_to_sga "5 IIIB 5.11.1" "finite sets" Finset.card
add_to_sga "5 IIIB 5.11.1" "finite sets" Fintype.card
add_to_sga "5 IIIB 5.11.1" "finite sets" Set.ncard
add_to_sga "5 IIIB 5.11.1" ZFSet.card
add_to_sga "5 IIIB 5.11.3" "A = K[Z_g]" MonoidAlgebra
add_to_sga "5 IIIB 5.11.3" Subgroup.centralizer
add_to_sga "5 IIIB 5.12" "special case" LinearMap.trace_tensorProduct
add_to_sga "5 IIIB 5.12" "special case" LinearMap.trace_tensorProduct'
add_to_sga "5 IIIB 5.12" "special case" Module.endTensorEndAlgHom
add_to_sga "5 IIIB 5.12" "special case" TensorProduct.AlgebraTensorModule.homTensorHomMap
add_to_sga "5 IIIB 5.12" "(3), special case"
  TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
add_to_sga "5 IIIB 5.12" "special case" TensorProduct.homTensorHomMap
add_to_sga "5 IIIB 5.12" "special case" homTensorHomEquiv
add_to_sga "5 IIIB 5.13" CategoryTheory.AddMod.scalarRestriction
add_to_sga "5 IIIB 5.13" CategoryTheory.Mod.scalarRestriction
add_to_sga "5 IIIB 5.13" CategoryTheory.Mod_.scalarRestriction
add_to_sga "5 IIIB 5.13" "special case" ConjAct.instSMul
add_to_sga "5 IIIB 5.13" "G_{♮, special case" ConjClasses
add_to_sga "5 IIIB 5.13" LinearMap
add_to_sga "5 IIIB 5.13" LinearMap.mk
add_to_sga "5 IIIB 5.13" Module.compHom
add_to_sga "5 IIIB 5.13" "special case" Module.restrictScalars
add_to_sga "5 IIIB 5.13" "more general" ModuleCat.semilinearMapAddEquiv
add_to_sga "5 IIIB 5.13" "more general" MulAction.orbitRel.Quotient
add_to_sga "5 IIIB 5.13" "more general" MulAction.orbitRel.Quotient.orbit
add_to_sga "5 IIIB 5.13" "special case" RestrictScalars.module
add_to_sga "5 IIIB 5.13" SemilinearMapClass
add_to_sga "5 IIIB 5.13" "special case" Subgroup.centralizer_eq_comap_stabilizer
add_to_sga "5 IIIB 5.13" "special case" Subgroup.mem_centralizer_iff
add_to_sga "5 IIIB 5.13" "special case" Subgroup.mem_centralizer_singleton_iff
add_to_sga "5 IIIB 5.13" "special case" conjugatesOf
add_to_sga "5 IIIB 6.1" "partial" Algebra.FiniteType
add_to_sga "5 IIIB 6.1" HasDerivedCategory.standard
add_to_sga "5 IIIB 6.1" "partial" IsNoetherianRing
add_to_sga "5 IIIB 6.1" "partial" Module.Flat
add_to_sga "5 IIIB 6.1" MulOpposite
add_to_sga "5 IIIB 6.1" MulOpposite.instAlgebra
add_to_sga "5 IIIB 6.5" CategoryTheory.Limits.pullback
add_to_sga "5 IIIB 6.7" "special case" trace_restrictScalars
add_to_sga "5 IIIB 6.7" "special case" trace_trace
add_to_sga "5 IIIB 6.9" "more general" Action
add_to_sga "5 IIIB 6.9" "Point case" Rep.equivalenceModuleMonoidAlgebra
add_to_sga "5 IIIB 6.9" "Point case"
  Rep.instIsEquivalenceModuleCatMonoidAlgebraOfModuleMonoidAlgebra
add_to_sga "5 IIIB 6.9" "Point case"
  Rep.instIsEquivalenceModuleCatMonoidAlgebraToModuleMonoidAlgebra
add_to_sga "5 IIIB 6.18" "more general" Representation.trivial
add_to_sga "5 V 1.1" "scalar-action datum ρ" CategoryTheory.Linear
add_to_sga "5 V 1.1" "the ring homomorphism ρ" CategoryTheory.Linear.toCatCenter
add_to_sga "5 V 1.1.1" "(i), special case" CategoryTheory.Mod
add_to_sga "5 V 1.1.1" "(ii), special case" CategoryTheory.Mod.Hom
add_to_sga "5 V 1.1.1" "special case" CategoryTheory.Mod.instCategory
add_to_sga "5 V 1.1.1" "(i), special case" CategoryTheory.Mod.mk
add_to_sga "5 V 1.1.1" "(i), special case" CategoryTheory.ModObj.mk
add_to_sga "5 V 1.1.1" "(i), special case" CategoryTheory.Mod_
add_to_sga "5 V 1.1.1" "(ii), special case" CategoryTheory.Mod_.Hom
add_to_sga "5 V 1.1.1" "(b), special case" Condensed.instHasLimitsOfSizeModuleCat
add_to_sga "5 V 1.1.1" "(b), special case" CondensedMod.instHasLimitsOfSizeModuleCat
add_to_sga "5 V 1.1.1" "(a), special case"
  ModuleCat.FilteredColimits.forget₂AddCommGroup_preservesFilteredColimits
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.HasColimit.instHasColimit
add_to_sga "5 V 1.1.1" "(a), special case"
  ModuleCat.HasColimit.instPreservesColimitAddCommGrpCatForget₂LinearMapIdCarrierAddMonoidHomCarrier
add_to_sga "5 V 1.1.1" "C = Ab" ModuleCat.abelian
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂AddCommGroup_preservesLimit
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂AddCommGroup_preservesLimits
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂AddCommGroup_preservesLimitsAux
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂PreservesColimitsOfShape
add_to_sga "5 V 1.1.1" "(a), special case" ModuleCat.forget₂PreservesColimitsOfSize
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasColimitsOfShape
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasColimitsOfSize
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasLimit
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasLimits
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasLimits'
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.hasLimitsOfShape
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.instHasFiniteColimits
add_to_sga "5 V 1.1.1" "(b), special case" ModuleCat.instHasLimitsOfSize
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_sga`.
run_cmd do
  let decl := Lean.mkIdent <| .str `ModuleCat <|
    "instPreservesColimitsOfSizeAddCommGrpCatForget₂LinearMapIdCarrierAddMonoidHomCarrier" ++
      "OfHasColimitsOfSizeAddCommGrpMax"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_sga "5 V 1.1.1" "(a), special case" $decl:ident))
add_to_sga "5 V 1.1.1" "(b), special case" PresheafOfModules.hasLimit
add_to_sga "5 V 1.1.1" "(a), special case" Rep.preservesColimits_forget
add_to_sga "5 V 1.1.1" "(a), projective limits" Rep.preservesLimits_forget
add_to_sga "5 V 1.1.1" "(b), inductive limits" instHasColimitsCondensedMod
add_to_sga "5 V 1.2" "partial" CategoryTheory.End.mulActionLeft
add_to_sga "5 V 1.2" "precomposition formula" CategoryTheory.End.smul_left
add_to_sga "5 V 1.2" "more general" CategoryTheory.Functor.IsCorepresentable
add_to_sga "5 V 1.2" "more general" CategoryTheory.Functor.coreprX
add_to_sga "5 V 1.2" "more general" CategoryTheory.Functor.corepresentableBy
add_to_sga "5 V 1.2" "more general" CategoryTheory.Linear.homModuleOfRingMorphism
add_to_sga "5 V 1.2" "more general" CategoryTheory.Linear.ofRingMorphism
add_to_sga "5 V 1.2" "partial" CategoryTheory.Linear.smulOfRingMorphism
add_to_sga "5 V 1.2" "precomposition formula" CategoryTheory.Linear.smulOfRingMorphism_smul_eq
add_to_sga "5 V 1.2" "more general" CategoryTheory.moduleEndLeft
add_to_sga "5 V 1.2" "special case" TensorProduct
add_to_sga "5 V 1.2" "special case" TensorProduct.map
add_to_sga "5 V 1.2.1" "special case" TensorProduct.directLimitLeft
add_to_sga "5 V 1.2.1" "Classical module case" TensorProduct.directLimitRight
add_to_sga "5 V 1.2.3" "special case" lTensor.equiv
add_to_sga "5 V 1.2.4" "special case" Submodule.comap_smul_top_of_surjective
add_to_sga "5 V 2.3" CategoryTheory.Localization.StrictUniversalPropertyFixedTarget
add_to_sga "5 V 2.3" "partial"
  CategoryTheory.Localization.instInhabitedStrictUniversalPropertyFixedTargetLocalizationQ
add_to_sga "5 V 2.3" CategoryTheory.MorphismProperty.IsInvertedBy
add_to_sga "5 V 2.3" "special case"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.strictUniversalPropertyFixedTarget
add_to_sga "5 V 2.3.1" "Clause (c), special case"
  CategoryTheory.GrothendieckTopology.RightOreCondition
add_to_sga "5 V 2.3.1" CategoryTheory.MorphismProperty.HasRightCalculusOfFractions
add_to_sga "5 V 2.3.2" CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions
add_to_sga "5 V 2.3.2"
  CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction
add_to_sga "5 V 2.3.2" CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.ext
add_to_sga "5 V 2.3.3" "Hom sets of E_S"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom
add_to_sga "5 V 2.3.4" CategoryTheory.Functor.Additive
add_to_sga "5 V 2.3.4" CategoryTheory.Limits.PreservesFiniteColimits
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.Preadditive.map_add
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.functor_additive
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.instAdditiveLocalization'Q'
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.instAdditiveLocalizationQ
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.instPreadditiveLocalization
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.instPreadditiveLocalization'
add_to_sga "5 V 2.3.4" "partial" CategoryTheory.Localization.preadditive
add_to_sga "5 V 2.3.4" "special case" CategoryTheory.Localization.preservesFiniteColimits
add_to_sga "5 V 2.3.4" "special case"
  CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteColimits
add_to_sga "5 V 2.3.5" CategoryTheory.Localization.abelian
add_to_sga "5 V 2.3.5" "right exactness of P_S" CategoryTheory.Localization.preservesFiniteColimits
add_to_sga "5 V 2.3.5" "left exactness of P_S" CategoryTheory.Localization.preservesFiniteLimits
add_to_sga "5 V 2.3.5" "special case" CategoryTheory.ObjectProperty.SerreClassLocalization.abelian
add_to_sga "5 V 2.3.5" "special case"
  CategoryTheory.ObjectProperty.SerreClassLocalization.isZero_obj_iff
add_to_sga "5 V 2.4.5" "more general"
  CategoryTheory.ObjectProperty.SerreClassLocalization.inverseImage_isomorphisms
add_to_sga "5 V 2.4.5" "more general" CategoryTheory.ObjectProperty.isoModSerre
add_to_sga "5 V 4.2" CategoryTheory.Abelian
add_to_sga "5 V 4.2" CategoryTheory.Linear
add_to_sga "5 V 4.2" CommRing
add_to_sga "5 V 4.2" CommRingCat
add_to_sga "5 V 4.2" Ideal
add_to_sga "5 V 4.2" WithIdeal
add_to_sga "5 V 5.1.4" "special case" Algebra.EssFiniteType.isNoetherianRing
add_to_sga "5 V 5.1.4" "special case" MvPolynomial.isNoetherianRing
add_to_sga "5 V 5.1.4" "special case" MvPolynomial.isNoetherianRing_fin
add_to_sga "5 V 5.1.5" "special case" instFinitePresentationTensorProduct
add_to_sga "5 V 5.3" "partial" CategoryTheory.Functor.instAdditiveObjWhiskeringRight
add_to_sga "5 V 5.3" CategoryTheory.Functor.whiskeringRight
add_to_sga "5 VI 1.2.3.1" "special case"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiberOfIsSepClosed
add_to_sga "5 VI 1.3.3" "partial" SheafOfModules.IsLocallyFree.mk
add_to_sga "5 VI 1.4.7" "Finiteness of A over ℤℓ" IsIntegralClosure.finite
add_to_sga "5 VI 1.4.7" "A is a Dedekind ring" IsIntegralClosure.isDedekindDomain
add_to_sga "5 VI 1.4.7" "partial" IsIntegralClosure.module_free
add_to_sga "5 VI 1.4.7" "A is a Dedekind ring" integralClosure.isDedekindDomain
add_to_sga "5 VI 1.4.7" "A is a Dedekind ring" integralClosure.isDedekindDomain_fractionRing
add_to_sga "5 VI 1.4.7" "Integral closedness of A"
  integralClosure.isIntegrallyClosedOfFiniteExtension
add_to_sga "5 VI 1.4.7" "Noetherianity of A" integralClosure.isNoetherianRing
add_to_sga "5 VI 2.1" CategoryTheory.Functor.whiskeringRight
add_to_sga "5 VII 3.2" "Affine, special case" Module.isLocallyConstant_rankAtStalk_freeLocus
add_to_sga "5 VII 4.1" Ideal.cotangentIdeal
add_to_sga "5 VII 5.4.1" "partial" MvPolynomial.esymmAlgEquiv
add_to_sga "5 VII 5.4.1" "special case" MvPolynomial.esymmAlgHom
add_to_sga "5 VII 5.4.1" "partial" MvPolynomial.esymmAlgHom_fin_bijective
add_to_sga "5 VII 5.4.1" "partial" MvPolynomial.esymmAlgHom_fin_injective
add_to_sga "5 VII 5.4.1" "partial" MvPolynomial.esymmAlgHom_injective
add_to_sga "5 VII 7.2.1" CochainComplex.mappingCone
add_to_sga "5 X 3.1" "Centrality clause" FDRep.char_conj
add_to_sga "5 X 3.1" "partial" FDRep.char_mul_comm
add_to_sga "5 X 3.1" "special case" FDRep.character
add_to_sga "5 X 3.1" "partial" Module.Finite
add_to_sga "5 X 3.1" "partial" Module.Projective
add_to_sga "5 X 3.1" "special case" Representation.char_conj
add_to_sga "5 X 3.1" "special case" Representation.char_mul_comm
add_to_sga "5 X 3.1" "special case" Representation.character
add_to_sga "5 X 3.3" Action.res
add_to_sga "5 X 3.3" Rep.ind
add_to_sga "5 X 3.3" Rep.indResAdjunction
add_to_sga "5 X 3.3" "left exactness of J" Rep.instPreservesLimitsResFunctor
add_to_sga "5 X 3.3" Rep.res
add_to_sga "5 X 3.3" Rep.resFunctor
add_to_sga "5 X 3.3" Rep.resMap
add_to_sga "5 X 3.3" "more general" Rep.res_map_exact
add_to_sga "5 X 3.3" "more general" Rep.shortExact_res
add_to_sga "5 X 3.3" Representation.ind
add_to_sga "5 X 3.3" TopRep.res
add_to_sga "5 X 3.3" TopRep.resFunctor
add_to_sga "5 X 3.5" Algebra.TensorProduct.instAlgebra
add_to_sga "5 X 3.5" "more general" Algebra.TensorProduct.leftAlgebra
add_to_sga "5 X 3.5" "more general" Algebra.TensorProduct.lift
add_to_sga "5 X 3.5" "more general" Algebra.TensorProduct.liftEquiv
add_to_sga "5 X 3.5" "partial" TensorProduct.Algebra.module
add_to_sga "5 X 3.7" "(g), special case" FDRep.char_dual
add_to_sga "5 X 3.7" "(3.7.2), special case" FDRep.char_linHom
add_to_sga "5 X 3.7" "special case" LinearMap.trace_transpose
add_to_sga "5 X 3.7" "special case" LinearMap.trace_transpose'
add_to_sga "5 X 3.7" "partial" Module.Dual
add_to_sga "5 X 3.7" Module.Dual.eval
add_to_sga "5 X 3.7" "partial" Module.IsReflexive.of_finite_of_free
add_to_sga "5 X 3.7" "partial" Module.instIsReflexiveOfFiniteOfProjective
add_to_sga "5 X 3.7" "(3.7.2) over a field" Representation.char_dual
add_to_sga "5 X 3.7" "special case" Representation.char_linHom
add_to_sga "5 X 3.7" Representation.dual
add_to_sga "5 X 3.7" "more general" Representation.dual_apply
add_to_sga "5 X 3.7" "partial" Representation.invariants
add_to_sga "5 X 3.8" "special case" FDRep.dualTensorIsoLinHom
add_to_sga "5 X 3.8" "special case" Representation.Equiv.dualTensorHom
add_to_sga "5 X 3.8" "special case" Representation.linHom.invariantsEquivFDRepHom
add_to_sga "5 X 3.8" "special case" Representation.linHom.invariantsEquivRepHom
add_to_sga "5 X 3.8" "special case" dualTensorHomEquiv
add_to_sga "5 X 3.8" "special case" dualTensorHom_bijective
add_to_sga "5 X 4.2" Rep.ind
add_to_sga "5 X 4.2" Representation.ind
add_to_sga "5 X 4.3" "special case" Ideal.exists_comap_galRestrict_eq
add_to_sga "5 X 4.3" MulAut.conj
add_to_sga "5 X 4.5" "partial" MulAction.orbitEquivQuotientStabilizer
add_to_sga "5 X 4.5" "orbitwise coset indexing" MulAction.selfEquivSigmaOrbitsQuotientStabilizer
add_to_sga "5 X 4.5" "partial" MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
add_to_sga "5 X 5.0" "partial" IsAlgClosed
add_to_sga "5 X 5.0" ZMod
add_to_sga "5 XII 6.2" "partial" LinearMap.dualMap
add_to_sga "5 XII 6.2" "special case" LinearMap.trace
add_to_sga "5 XII 6.2" "special case" LinearMap.traceAux
add_to_sga "5 XII 6.2" "partial" Representation.dual
add_to_sga "5 XV 1.Definition2" "affine case" frobenius
add_to_sga "5 XV 1.Definition2" "affine case at n = 1" iterateFrobenius
add_to_sga "5 XV 3.Lemma3" "more general" Module.projective_iff_lift_map_range_le
add_to_sga "5 XV 3.Lemma3" "more general" Module.projective_lifting_property
add_to_sga "5 XV 4.Definition4" "spectra of fields" PerfectField
add_to_sga "5 XV 4.Definition4" "affine schemes" PerfectRing
