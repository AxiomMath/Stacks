module  -- shake: keep-all

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Module.Presentation.Finite
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
import Mathlib.AlgebraicTopology.SimplicialObject.Split
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Bicategory.Yoneda
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Galois.EssSurj
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Subfunctor.Finite
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Subterminal
import Mathlib.Condensed.Module
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Points
import StacksCore.Algebra.Homology.HomologicalBicomplex
import StacksCore.CategoryTheory.Filtration.Preadditive
import StacksCore.CategoryTheory.Monoidal.Rigid.Retract
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4, Exposés V to VIII and V bis: references registered by name

The `add_to_sga` registrations of `StacksFrontier.EgaSgaIndex.SGA4` for Exposés V to VIII and V bis
of SGA 4, in the order of that file. See its module docstring.
-/

add_to_sga "4 V 0.1.1" "abelian groups" AddCommGrpCat.enoughInjectives
add_to_sga "4 V 0.1.1" "commutative groups" CommGrpCat.enoughInjectives
add_to_sga "4 V 0.1.1" "modules over a ring" ModuleCat.enoughInjectives
add_to_sga "4 V 0.1.1" "integer modules" instEnoughInjectivesModuleCatInt
add_to_sga "4 V 0.2" "more general" CategoryTheory.Adjunction.map_injective
add_to_sga "4 V 0.2" "more general"
  CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
add_to_sga "4 V 0.2" "more general" CategoryTheory.Injective.injective_of_adjoint
add_to_sga "4 V 0.2.1" AddCommGrpCat.enoughInjectives
add_to_sga "4 V 0.2.1" CommGrpCat.enoughInjectives
add_to_sga "4 V 0.2.1" ModuleCat.enoughInjectives
add_to_sga "4 V 0.2.1" instEnoughInjectivesModuleCatInt
add_to_sga "4 V 0.2.1" instEnoughInjectivesModuleCatOfSmall
add_to_sga "4 V 0.5.2" CategoryTheory.Functor.PreservesInjectiveObjects
add_to_sga "4 V 0.5.2" CategoryTheory.Limits.PreservesColimitsOfShape
add_to_sga "4 V 0.5.2" CategoryTheory.ObjectProperty.IsClosedUnderSubobjects
add_to_sga "4 V 0.5.2" "special case" Module.Baer.injective
add_to_sga "4 V 1.1" "special case" Module.Flat
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_lTensor_exact'
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_lTensor_preserves_shortComplex_exact
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_preservesFiniteLimits_tensorLeft
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_preservesFiniteLimits_tensorRight
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_rTensor_exact
add_to_sga "4 V 1.1" "special case" Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_sga "4 V 1.1" "partial" Module.Flat.lTensor_exact
add_to_sga "4 V 1.1" "partial" Module.Flat.lTensor_shortComplex_exact
add_to_sga "4 V 1.1" "partial" Module.Flat.rTensor_exact
add_to_sga "4 V 1.1" "partial" Module.Flat.rTensor_shortComplex_exact
add_to_sga "4 V 1.2" "(ii) ⇒ (i)" Module.Flat.iff_characterModule_baer
add_to_sga "4 V 1.2" "(ii) ⇒ (i)" Module.Flat.iff_characterModule_injective
add_to_sga "4 V 1.3.1" "special case" Module.Flat.finsupp
add_to_sga "4 V 1.3.1" "special case" Module.Flat.of_free
add_to_sga "4 V 1.6.2" "special case" Module.Flat.iff_preservesFiniteLimits_tensorLeft
add_to_sga "4 V 1.6.2" "special case" Module.Flat.iff_preservesFiniteLimits_tensorRight
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case" Module.Flat.iff_lTensor_exact'
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case"
  Module.Flat.iff_lTensor_preserves_shortComplex_exact
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case" Module.Flat.iff_rTensor_exact
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case" Module.Flat.iff_rTensor_exact'
add_to_sga "4 V 1.7.2" "(i) ⇔ (ii), special case"
  Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_sga "4 V 1.7.2" "(i) ⇒ (ii), special case" Module.Flat.lTensor_exact
add_to_sga "4 V 1.7.2" "(i) ⇒ (ii), special case" Module.Flat.lTensor_shortComplex_exact
add_to_sga "4 V 1.9" "clause 1, special case" AddCommGrpCat.instCreatesColimitsOfSizeUliftFunctor
add_to_sga "4 V 1.9" "clause 1, special case" AddCommGrpCat.instPreservesColimitsOfSizeUliftFunctor
add_to_sga "4 V 1.9" "Clause 1), special case" FGModuleCat.fullyFaithfulULift
add_to_sga "4 V 1.9" "Clause 1)" FGModuleCat.instFaithfulUlift
add_to_sga "4 V 1.9" "Clause 1)" FGModuleCat.instFullUlift
add_to_sga "4 V 1.9" "special case" FGModuleCat.ulift
add_to_sga "4 V 1.9" "Clause 4), special case" Module.Flat.ulift
add_to_sga "4 V 1.9" "Clause 4), special case" Module.Flat.ulift_right_iff
add_to_sga "4 V 1.9" "Clause 3), special case" Module.injective_iff_ulift_injective
add_to_sga "4 V 1.9" "Clause 3), special case" Module.ulift_injective_of_injective
add_to_sga "4 V 1.9" "Clause 1), special case" ModuleCat.fullyFaithfulUliftFunctor
add_to_sga "4 V 1.9" "Clause 1)" ModuleCat.instFaithfulUliftFunctor
add_to_sga "4 V 1.9" "Clause 1)" ModuleCat.instFullUliftFunctor
add_to_sga "4 V 1.9" "Clause 1)" ModuleCat.instPreservesFiniteColimitsUliftFunctor
add_to_sga "4 V 1.9" "Clause 3), special case"
  ModuleCat.instPreservesInjectiveObjectsUliftFunctorOfSmall
add_to_sga "4 V 1.9" "Clause 1), special case" ModuleCat.instPreservesLimitsOfSizeUliftFunctor
add_to_sga "4 V 1.9" "special case" ModuleCat.uliftFunctor
add_to_sga "4 V 1.9" "Clause 3), special case" ModuleCat.ulift_injective_of_injective
add_to_sga "4 V 1.10" "1.10.4" AlgebraicTopology.AlternatingFaceMapComplex.d_squared
add_to_sga "4 V 1.10" "partial" AlgebraicTopology.AlternatingFaceMapComplex.obj
add_to_sga "4 V 1.10" "1.10.5: d = Σ(-1)^i s_i" AlgebraicTopology.AlternatingFaceMapComplex.objD
add_to_sga "4 V 1.10" "1.10.5" AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
add_to_sga "4 V 1.10" "1.10.4" AlgebraicTopology.AlternatingFaceMapComplex.ε
add_to_sga "4 V 1.10" "partial" AlgebraicTopology.alternatingFaceMapComplex
add_to_sga "4 V 1.10" "1.10.5" AlgebraicTopology.alternatingFaceMapComplex_obj_d
add_to_sga "4 V 1.10" "partial" CategoryTheory.Arrow.augmentedCechNerve
add_to_sga "4 V 1.10" "more general" CategoryTheory.Limits.FormalCoproduct.cech
add_to_sga "4 V 1.10" "more general" CategoryTheory.Limits.FormalCoproduct.cechFunctor
add_to_sga "4 V 1.10" "partial" CategoryTheory.SimplicialObject.Augmented.whiskering
add_to_sga "4 V 1.10" "partial" CategoryTheory.SimplicialObject.Augmented.whiskeringObj
add_to_sga "4 V 1.10" "partial" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "4 V 1.10" "partial" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "4 V 1.10" "partial" SimplexCategory.coe_δ
add_to_sga "4 V 1.10" SimplexCategory.δ
add_to_sga "4 V 2.1.1" CategoryTheory.Abelian.Ext
add_to_sga "4 V 2.1.1" "more general" CategoryTheory.Abelian.Ext.addEquiv₀
add_to_sga "4 V 2.1.1" "partial" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "4 V 2.1.1" "At Ext^n(X1" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
add_to_sga "4 V 2.1.1" "Exactness Ext^n(X2"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_sga "4 V 2.1.1" "Exactness Ext^n(X3"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_sga "4 V 2.1.1" "more general" CategoryTheory.Abelian.Ext.homEquiv₀
add_to_sga "4 V 2.1.1" "more general" CategoryTheory.Abelian.Ext.linearEquiv₀
add_to_sga "4 V 2.1.1" "more general" CategoryTheory.Abelian.Ext.mk₀_bijective
add_to_sga "4 V 2.1.2" "H^q(E, special case" CategoryTheory.Sheaf.H
add_to_sga "4 V 2.1.2" "H^q(X, special case" CategoryTheory.Sheaf.H'
add_to_sga "4 V 2.2" "more general" CategoryTheory.Adjunction.map_injective
add_to_sga "4 V 2.2" "more general"
  CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
add_to_sga "4 V 2.2" "more general" CategoryTheory.Injective.injective_of_adjoint
add_to_sga "4 V 2.3.1" PresheafOfModules.evaluation
add_to_sga "4 V 2.3.1" "special case" Rep.free_projective
add_to_sga "4 V 2.3.1" "special case" Rep.standardComplex.x_projective
add_to_sga "4 V 2.3.2" "special case" CategoryTheory.Sheaf.ΓNatIsoLim
add_to_sga "4 V 2.3.3" "more general" CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
add_to_sga "4 V 2.3.3" "partial" CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
add_to_sga "4 V 2.3.6" CategoryTheory.ComposableArrows
add_to_sga "4 V 2.3.6" CategoryTheory.ComposableArrows.mkOfObjOfMapSucc
add_to_sga "4 V 2.3.6" "n = 2" CategoryTheory.ComposableArrows.mk₂
add_to_sga "4 V 2.3.6" "n = 3" CategoryTheory.ComposableArrows.mk₃
add_to_sga "4 V 2.3.6" "n = 4" CategoryTheory.ComposableArrows.mk₄
add_to_sga "4 V 2.3.6" "n = 5" CategoryTheory.ComposableArrows.mk₅
add_to_sga "4 V 2.3.6" "more general" CategoryTheory.Functor.leftDerived
add_to_sga "4 V 2.3.6" "more general" CategoryTheory.Limits.colim
add_to_sga "4 V 2.3.6" "more general" CategoryTheory.Limits.colimConstAdj
add_to_sga "4 V 2.3.6" "partial" CategoryTheory.Limits.colimit
add_to_sga "4 V 2.3.6" CategoryTheory.nerve
add_to_sga "4 V 2.3.6" "degree 1" CategoryTheory.nerve.homEquiv
add_to_sga "4 V 2.3.6" "face formula s_0(u_1" CategoryTheory.nerve.δ₀_eq
add_to_sga "4 V 2.3.6" "(g), special case" CategoryTheory.nerve.δ₀_mk₂_eq
add_to_sga "4 V 2.3.6" "s_2(u_1, special case" CategoryTheory.nerve.δ₂_two
add_to_sga "4 V 2.3.6" "s_0(u_1, special case" CategoryTheory.nerve.δ₂_zero
add_to_sga "4 V 2.3.6" "degree 0: ES(C)_0 = ob C" CategoryTheory.nerveEquiv
add_to_sga "4 V 2.3.6" "more general" CategoryTheory.nerveFunctor
add_to_sga "4 V 2.3.6" "partial" CategoryTheory.nerve_obj
add_to_sga "4 V 2.3.6" "Item (c), special case" Rep.barResolution
add_to_sga "4 V 2.3.6" "Item (c), special case" Rep.standardComplex.instQuasiIsoNatεToSingle₀
add_to_sga "4 V 2.3.6" "Item (c), special case" Rep.standardComplex.x_projective
add_to_sga "4 V 2.3.6" "Item (c), special case" Rep.standardComplex.εToSingle₀
add_to_sga "4 V 2.3.6" "Item (c), special case" Rep.standardResolution
add_to_sga "4 V 2.3.6" "Item (d), special case" Rep.standardResolution.extIso
add_to_sga "4 V 2.4.1" "partial"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeUliftYoneda
add_to_sga "4 V 2.4.1" "partial" CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeYoneda
add_to_sga "4 V 2.4.1" "H^q(X, special case" CategoryTheory.Sheaf.H'
add_to_sga "4 V 2.4.2" "special case" CategoryTheory.sheafToPresheaf
add_to_sga "4 V 2.4.2" "partial" TopCat.Sheaf.sections_exact_of_left_exact
add_to_sga "4 V 2.4.3" "more general" CategoryTheory.cechComplexFunctor
add_to_sga "4 V 2.4.5" "special case" CategoryTheory.GrothendieckTopology.plusFunctor
add_to_sga "4 V 2.4.5" "special case" CategoryTheory.GrothendieckTopology.plusObj
add_to_sga "4 V 2.4.5" "special case"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor
add_to_sga "4 V 2.4.5" "special case"
  CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_plusFunctor
add_to_sga "4 V 2.5.1" "special case" Module.injective_iff_ulift_injective
add_to_sga "4 V 2.5.1" "special case" Module.ulift_injective_of_injective
add_to_sga "4 V 2.5.1" "special case" ModuleCat.instPreservesInjectiveObjectsUliftFunctorOfSmall
add_to_sga "4 V 2.5.1" "special case" ModuleCat.ulift_injective_of_injective
add_to_sga "4 V 2.5.2" "q = 0" CategoryTheory.instIsIsoFunctorToRightDerivedZero
add_to_sga "4 V 3.5" SheafOfModules.toSheaf
add_to_sga "4 V 4.3" "special case" AlgebraicGeometry.Scheme.Modules.toPresheafOfModules
add_to_sga "4 V 4.3" "morphism action of ℋ⁰" SheafOfModules.Hom.val
add_to_sga "4 V 4.3" SheafOfModules.forget
add_to_sga "4 V 4.3" "object action of ℋ⁰" SheafOfModules.val
add_to_sga "4 V 4.9" "special case" TopCat.Presheaf.IsFlasque.pushforward_isFlasque
add_to_sga "4 V 4.9" "special case" TopCat.Sheaf.IsFlasque.pushforward_isFlasque
add_to_sga "4 V 4.15" Action.leftRegular
add_to_sga "4 V 4.15" "partial" Monoid.toMulAction
add_to_sga "4 V 4.15" "partial" MulAction.Regular.isPretransitive
add_to_sga "4 V 4.16" CategoryTheory.Subobject
add_to_sga "4 V 4.16" CategoryTheory.Subterminals
add_to_sga "4 V 4.16" "more general" CategoryTheory.subterminalsEquivMonoOverTerminal
add_to_sga "4 V 4.16" "partial" Opens.instHasEnoughPointsOpensGrothendieckTopology
add_to_sga "4 V 6.0" "6.0.3, 6.0.4" CategoryTheory.Abelian.Ext.addEquiv₀
add_to_sga "4 V 6.0" "6.0.3, 6.0.4" CategoryTheory.Abelian.Ext.homEquiv₀
add_to_sga "4 V 6.0" "6.0.3, 6.0.4" CategoryTheory.Abelian.Ext.linearEquiv₀
add_to_sga "4 V 6.0" "6.0.3, 6.0.4" CategoryTheory.Abelian.Ext.mk₀_bijective
add_to_sga "4 V 6.2" CategoryTheory.Abelian.Ext.contravariantSequence
add_to_sga "4 V 6.2" "Exactness of (6.2.2)" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'
add_to_sga "4 V 6.2" CategoryTheory.Abelian.Ext.covariantSequence
add_to_sga "4 V 6.2" "Exactness of (6.2.1)" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_sga "4 V 6.2" "partial" CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
add_to_sga "4 V 6.3" "(6.3.1)" CategoryTheory.Abelian.Ext.addEquiv₀
add_to_sga "4 V 7.1.0" CategoryTheory.SimplicialObject.Truncated
add_to_sga "4 V 7.1.0" CategoryTheory.SimplicialObject.Truncated.cosk
add_to_sga "4 V 7.1.0" "partial" CategoryTheory.SimplicialObject.Truncated.coskAdj.reflective
add_to_sga "4 V 7.1.0" "partial" CategoryTheory.SimplicialObject.Truncated.cosk_reflective
add_to_sga "4 V 7.1.0" CategoryTheory.SimplicialObject.Truncated.sk
add_to_sga "4 V 7.1.0" CategoryTheory.SimplicialObject.truncation
add_to_sga "4 V 7.1.0" "special case" SSet.Truncated
add_to_sga "4 V 7.1.0" "embedding clause" SSet.Truncated.cosk_reflective
add_to_sga "4 V 7.1.0" "special case" SSet.coskAdj
add_to_sga "4 V 7.1.0" "special case" SSet.skAdj
add_to_sga "4 V 7.1.0" SimplexCategory
add_to_sga "4 V 7.1.0" SimplexCategory.Hom
add_to_sga "4 V 7.1.0" SimplexCategory.Truncated
add_to_sga "4 V 7.1.0" SimplexCategory.Truncated.inclusion
add_to_sga "4 V 7.1.0" SimplexCategory.smallCategory
add_to_sga "4 V 7.1.1" CategoryTheory.SimplicialObject.cosk
add_to_sga "4 V 7.1.1" CategoryTheory.SimplicialObject.sk
add_to_sga "4 V 7.1.1" "special case" SSet.cosk
add_to_sga "4 V 7.1.1" "special case" SSet.sk
add_to_sga "4 V 7.2.0" "partial" AddCommGrpCat.free
add_to_sga "4 V 7.2.0" "partial" AlgebraicTopology.AlternatingFaceMapComplex.obj
add_to_sga "4 V 7.2.0" "partial" AlgebraicTopology.AlternatingFaceMapComplex.objD
add_to_sga "4 V 7.2.0" "partial" AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
add_to_sga "4 V 7.2.0" "special case" AlgebraicTopology.SSet.singularChainComplexFunctor
add_to_sga "4 V 7.2.0" "partial" AlgebraicTopology.alternatingFaceMapComplex
add_to_sga "4 V 7.2.0" "partial" AlgebraicTopology.alternatingFaceMapComplex_obj_d
add_to_sga "4 V 7.2.0" "partial" Condensed.freeAb
add_to_sga "4 V 7.2.0" "partial" FreeAbelianGroup.uniqueEquiv
add_to_sga "4 V 7.2.0" "special case" SSet.chainComplex
add_to_sga "4 V 7.2.0" "special case" SSet.chainComplexFunctor
add_to_sga "4 V 7.2.0" "special case" SSet.homology
add_to_sga "4 V 7.2.0" "special case" SSet.homologyFunctor
add_to_sga "4 V 7.2.0" "partial" SSet.isColimitChainComplexXCofan
add_to_sga "4 V 7.3.0" CategoryTheory.Limits.HasBinaryProducts
add_to_sga "4 V 7.3.0" CategoryTheory.Limits.HasPullbacks
add_to_sga "4 V 7.3.0" "partial" CategoryTheory.Sheaf
add_to_sga "4 V 7.3.1.6" "special case" AlgebraicGeometry.PresheafedSpace.const
add_to_sga "4 V 7.3.1.6" CategoryTheory.Functor.const
add_to_sga "4 V 7.3.1.6" "more general" CategoryTheory.Quotient
add_to_sga "4 V 7.3.1.6" "more general" CategoryTheory.yoneda
add_to_sga "4 V 7.3.1.6" "special case" SSet.Homotopy
add_to_sga "4 V 7.3.1.6" "special case" SSet.RelativeMorphism.Homotopy
add_to_sga "4 V 7.3.1.6" "partial" SSet.RelativeMorphism.HomotopyClass
add_to_sga "4 V 7.3.1.6" "partial" SSet.RelativeMorphism.homotopyClass
add_to_sga "4 V 7.3.1.6" SSet.stdSimplex
add_to_sga "4 V 7.3.1.6" "partial" SSet.stdSimplex.objEquiv
add_to_sga "4 V 7.3.1.6" "special case" SSet.ι₀
add_to_sga "4 V 7.3.1.6" "special case" SSet.ι₁
add_to_sga "4 V 7.3.6.0" CategoryTheory.MonoidalClosed.internalHom
add_to_sga "4 V 7.3.6.0" CategoryTheory.ihom
add_to_sga "4 V 8.1.0" "partial" CategoryTheory.Functor.Fiber
add_to_sga "4 V 8.1.0" CategoryTheory.Functor.Fiber.fiberCategory
add_to_sga "4 V 8.1.1.1" "more general" CategoryTheory.Functor.IsPreFibered.exists_isCartesian'
add_to_sga "4 V 8.1.1.1" "more general" CategoryTheory.IsPreFibered.exists_isCartesian
add_to_sga "4 V 8.1.2" "special case" CategoryTheory.Sheaf.ΓNatIsoSheafSections
add_to_sga "4 V 8.1.2" "Γe = Hom_cart(S" CategoryTheory.Sheaf.ΓObjEquivSections
add_to_sga "4 V 8.1.3" "special case" CategoryTheory.Limits.constLimAdj
add_to_sga "4 V 8.1.3" "special case" CategoryTheory.Limits.limit
add_to_sga "4 V 8.1.4" "special case" CategoryTheory.Functor.initial_iff_of_isCofiltered
add_to_sga "4 V 8.1.4" "partial" CategoryTheory.Functor.initial_of_exists_of_isCofiltered
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.comp_hasLimit
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.hasLimit_comp_iff
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.hasLimit_of_comp
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.hasLimitsOfShape_of_initial
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.isLimitExtendConeEquiv
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.isLimitWhiskerEquiv
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.limitConeComp
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.limitConeOfComp
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Functor.Initial.limitIso
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Limits.hasLimit_inverse_equivalence_comp_iff
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Limits.limitOfDiagramInitial
add_to_sga "4 V 8.1.5" "special case" CategoryTheory.Limits.limitOfInitial
add_to_sga "4 V 8.1.6" "special case"
  CategoryTheory.Functor.initial_iff_isCofiltered_costructuredArrow
add_to_sga "4 V 8.1.9.0" CategoryTheory.IsCofiltered
add_to_sga "4 V 8.1.9.0" "partial" CategoryTheory.isCofiltered_of_isFiltered_op
add_to_sga "4 V 8.1.9.0" CategoryTheory.isFiltered_op_iff_isCofiltered
add_to_sga "4 V 8.1.9.0" "partial" CategoryTheory.isFiltered_op_of_isCofiltered
add_to_sga "4 V 8.1.10" "more general" CategoryTheory.Comma
add_to_sga "4 V 8.1.10" "more general" CategoryTheory.Comma.fst
add_to_sga "4 V 8.1.12" "more general" CategoryTheory.Functor.inducedTopology
add_to_sga "4 V 8.1.12" "more general"
  CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense
add_to_sga "4 V 8.2.2" "special case" CategoryTheory.Limits.instIsLeftAdjointFunctorColim
add_to_sga "4 V 8.2.2" "special case" CategoryTheory.Sheaf.instHasColimitsOfShape
open CategoryTheory.Sheaf in
add_to_sga "4 V 8.2.2" "special case"
instHasExactColimitsOfShapeOfHasFiniteLimitsOfPreservesColimitsOfShapeFunctorOppositeSheafToPresheaf
add_to_sga "4 V 8.2.4" "special case" TensorProduct.directLimitLeft
add_to_sga "4 V 8.2.4" "special case" TensorProduct.directLimitRight
add_to_sga "4 V 8.2.11" "special case" Module.Flat.exists_factorization_of_finitePresentation
add_to_sga "4 V 8.2.11" "special case" Module.Flat.exists_factorization_of_isFinitelyPresented
add_to_sga "4 V 8.2.11" "(f), special case" Module.Flat.iff_forall_exists_factorization
add_to_sga "4 VI 1.3" "Zariski case" AlgebraicGeometry.Scheme.OpenCover.compactSpace
add_to_sga "4 VI 1.8" "(ii), special case"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatFiberOfQuasiCompact
add_to_sga "4 VI 1.8" "(iv), special case"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_sga "4 VI 1.8" "(iii), for schemes"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiSeparatedTopMorphismProperty
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiCompact
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiSeparated
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedFstScheme
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedMorphismRestrict
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedResLE
add_to_sga "4 VI 1.8" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedSndScheme
add_to_sga "4 VI 1.8" "(iv), special case" AlgebraicGeometry.quasiCompact_iff_compactSpace
add_to_sga "4 VI 1.8" "(i)" AlgebraicGeometry.quasiCompact_of_isIso
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_sga "4 VI 1.9.1" "special case" AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_sga "4 VI 1.9.1" "(iv), special case" AlgebraicGeometry.QuasiCompact.of_comp
add_to_sga "4 VI 1.9.1" "special case" AlgebraicGeometry.QuasiSeparated
add_to_sga "4 VI 1.9.1" "1.8 (iii) for schemes" AlgebraicGeometry.QuasiSeparated.of_comp
add_to_sga "4 VI 1.9.1" "(iv), special case"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_sga "4 VI 1.9.1" "1.8 (iii) for schemes"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiSeparatedTopMorphismProperty
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiCompact
add_to_sga "4 VI 1.9.1" "(i), special case"
  AlgebraicGeometry.instIsMultiplicativeSchemeQuasiSeparated
add_to_sga "4 VI 1.9.1" "(ii), special case" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_sga "4 VI 1.9.1" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedMorphismRestrict
add_to_sga "4 VI 1.9.1" "special case" AlgebraicGeometry.instQuasiSeparatedOfMonoScheme
add_to_sga "4 VI 1.9.1" "(ii), special case" AlgebraicGeometry.instQuasiSeparatedSndScheme
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.quasiCompact_of_isIso
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_sga "4 VI 1.9.1" "special case" AlgebraicGeometry.quasiSeparated_eq_diagonal_is_quasiCompact
add_to_sga "4 VI 1.9.1" "special case" AlgebraicGeometry.quasiSeparated_iff
add_to_sga "4 VI 1.9.1" "more general"
  CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange
add_to_sga "4 VI 1.9.1" CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
add_to_sga "4 VI 1.14" "(ii), special case" AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage
add_to_sga "4 VI 1.14" "(i), special case" AlgebraicGeometry.quasiCompact_iff_compactSpace
add_to_sga "4 VI 1.14" "(ii), special case" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_sga "4 VI 1.17" "special case" AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens
add_to_sga "4 VI 1.17" "partial" QuasiSeparatedSpace.of_isOpenCover
add_to_sga "4 VI 1.17" "partial" QuasiSeparatedSpace.of_isTopologicalBasis
add_to_sga "4 VI 1.17.1" "more general" CategoryTheory.Limits.coequalizer
add_to_sga "4 VI 1.19" "special case" QuasiSeparatedSpace.of_isOpenCover
add_to_sga "4 VI 1.22.1" "partial"
  AlgebraicGeometry.Scheme.AffineEtale.instIsCoverDenseEtaleSpecSmallEtaleTopology
add_to_sga "4 VI 1.22.1" "partial"
  AlgebraicGeometry.Scheme.AffineEtale.instIsDenseSubsiteEtaleTopologySmallEtaleTopologySpec
add_to_sga "4 VI 1.22.1" "partial" AlgebraicGeometry.Scheme.Etale
add_to_sga "4 VI 1.22.1" "partial" AlgebraicGeometry.Scheme.smallEtalePretopology
add_to_sga "4 VI 1.22.1" "small étale site X_et" AlgebraicGeometry.Scheme.smallEtaleTopology
add_to_sga "4 VI 1.24.2" CategoryTheory.IsFinitelyPresentable
add_to_sga "4 VI 1.24.2" CategoryTheory.ObjectProperty.isFinitelyPresentable
add_to_sga "4 VI 1.24.2" CategoryTheory.Retract
add_to_sga "4 VI 1.24.2" "partial" CategoryTheory.Retract.idem
add_to_sga "4 VI 1.24.2" CategoryTheory.isCardinalPresentable
add_to_sga "4 VI 1.24.2" CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimitsOfSize
add_to_sga "4 VI 1.30" CategoryTheory.IsNoetherianObject
add_to_sga "4 VI 1.30" CategoryTheory.isNoetherianObject
add_to_sga "4 VI 1.30.1" "more general" CategoryTheory.instIsClosedUnderSubobjectsIsNoetherianObject
add_to_sga "4 VI 1.30.1" "more general" CategoryTheory.isNoetherianObject_of_mono
add_to_sga "4 VI 1.33" Action
add_to_sga "4 VI 1.33" "special case" CategoryTheory.FintypeCat.Action.isConnected_iff_transitive
add_to_sga "4 VI 1.33" "partial" CategoryTheory.FintypeCat.Action.isConnected_of_transitive
add_to_sga "4 VI 1.33" "partial" CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected
add_to_sga "4 VI 1.33" "partial" CategoryTheory.PreGaloisCategory.has_decomp_connected_components
add_to_sga "4 VI 1.33" "partial" CategoryTheory.PreGaloisCategory.has_decomp_connected_components'
add_to_sga "4 VI 1.33" "partial" CategoryTheory.PreGaloisCategory.has_decomp_quotients
add_to_sga "4 VI 1.33" "the orbits partition E" MulAction.IsPartition.of_orbits
add_to_sga "4 VI 1.33" "partial" MulAction.Regular.isPretransitive
add_to_sga "4 VI 1.33" "partial" MulAction.instIsPretransitiveElemOrbit
add_to_sga "4 VI 1.33" "partial" MulAction.instIsPretransitiveElemOrbit_1
add_to_sga "4 VI 1.33" MulAction.orbit
add_to_sga "4 VI 1.33" "partial" MulAction.orbit.eq_or_disjoint
add_to_sga "4 VI 1.33" "partial" MulAction.orbit.pairwiseDisjoint
add_to_sga "4 VI 1.33" MulAction.orbitRel.Quotient
add_to_sga "4 VI 1.33" "partial" MulAction.orbitRel.Quotient.nonempty_orbit
add_to_sga "4 VI 1.33" MulAction.orbitRel.Quotient.orbit
add_to_sga "4 VI 1.33" "partial" MulAction.selfEquivSigmaOrbits
add_to_sga "4 VI 1.33" "partial" MulAction.selfEquivSigmaOrbits'
add_to_sga "4 VI 1.33" "the orbits cover E" MulAction.univ_eq_iUnion_orbit
add_to_sga "4 VI 2.4.7" "partial" AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat
add_to_sga "4 VI 2.15" "partial" TopologicalSpace.NoetherianSpace.isCompact
add_to_sga "4 VI 2.15" "more general" TopologicalSpace.noetherianSpace_TFAE
add_to_sga "4 VI 2.15" TopologicalSpace.noetherianSpace_iff_opens
add_to_sga "4 VI 2.16" "more general" IsQuasiSeparated
add_to_sga "4 VI 2.16" QuasiSeparatedSpace
add_to_sga "4 VI 2.16" "partial" quasiSeparatedSpace_iff
add_to_sga "4 VI 2.17" CategoryTheory.EssentiallySmall
add_to_sga "4 VI 2.17" "partial" CategoryTheory.Presheaf.isStrongGenerator
add_to_sga "4 VI 2.17" "I(X)" CategoryTheory.Subobject
add_to_sga "4 VI 2.17" CategoryTheory.instPartialOrderSubobject
add_to_sga "4 VI 2.17" "clause of a)"
  CategoryTheory.instPresheafIsFiniteObjFunctorOppositeTypeYoneda
add_to_sga "4 VI 2.17" CategoryTheory.yoneda
add_to_sga "4 VI 2.17" IsLowerSet
add_to_sga "4 VI 2.17" LowerSet
add_to_sga "4 VI 3.10" "Site part of 3.10" AlgebraicGeometry.Scheme.overGrothendieckTopology
add_to_sga "4 VI 3.10" "partial" AlgebraicGeometry.Scheme.smallEtaleTopology
add_to_sga "4 VI 3.10" "partial" AlgebraicGeometry.Scheme.smallGrothendieckTopology
add_to_sga "4 VI 3.10" "partial" AlgebraicGeometry.Scheme.smallGrothendieckTopologyOfLE
add_to_sga "4 VI 3.11" "b)" CategoryTheory.GrothendieckTopology.fullyFaithfulUliftYoneda
add_to_sga "4 VI 3.11" "a)(1)" CategoryTheory.Limits.HasFiniteLimits
add_to_sga "4 VI 3.11" "more general" CategoryTheory.Regular.hasStrongEpiMonoFactorisations
add_to_sga "4 VI 3.11" "more general" CategoryTheory.Regular.strongEpiMonoFactorisation
add_to_sga "4 VI 4.1" "more general" CategoryTheory.Subobject
add_to_sga "4 VI 4.1" CategoryTheory.Subterminals
add_to_sga "4 VI 4.9.3" "more general" CategoryTheory.Comma
add_to_sga "4 VI 4.9.10" "partial"
  CategoryTheory.Presheaf.instPreservesFiniteProductsOppositeObjFunctorIsSheafCoherentTopology
add_to_sga "4 VI 4.9.10" "more general"
  CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition
add_to_sga "4 VI 4.10" CategoryTheory.IsFinitelyPresentable
add_to_sga "4 VI 4.10" CategoryTheory.ObjectProperty.isFinitelyPresentable
add_to_sga "4 VI 4.10" "more general" CategoryTheory.isCardinalPresentable
add_to_sga "4 VI 4.10" CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimitsOfSize
add_to_sga "4 VI 4.13" "coherent topology"
  CategoryTheory.Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
add_to_sga "4 VI 4.13" "special case" CategoryTheory.Presheaf.isSheaf_coherent_of_projective_of_comp
add_to_sga "4 VI 4.13" "more general" CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp
add_to_sga "4 VI 5.6" "special case" Module.Finite
add_to_sga "4 VI 5.6" "special case" Module.FinitePresentation
add_to_sga "4 VI 5.6" "special case" Module.finitePresentation_iff_exists_presentation
add_to_sga "4 VI 5.6" "special case" SheafOfModules.isFinitePresentation
add_to_sga "4 VI 6.0" CategoryTheory.BasedNatTrans.homCategory
add_to_sga "4 VI 6.0" CategoryTheory.BasedNatTrans.mk
add_to_sga "4 VI 6.0" CategoryTheory.SmallCategory
add_to_sga "4 VI 6.1" CategoryTheory.Functor.IsCartesian
add_to_sga "4 VI 6.1" CategoryTheory.Functor.IsFibered
add_to_sga "4 VI 6.1" CategoryTheory.Functor.IsPreFibered
add_to_sga "4 VI 6.1.1" CategoryTheory.Functor.Fiber
add_to_sga "4 VI 6.1.1" CategoryTheory.Functor.Fiber.fiberCategory
add_to_sga "4 VI 6.1.2" "partial" CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso
add_to_sga "4 VI 6.1.2" "partial" CategoryTheory.Functor.IsPreFibered.pullbackObj
add_to_sga "4 VI 6.1.2" "partial" CategoryTheory.Limits.pullbackRightPullbackFstIso
add_to_sga "4 VI 6.1.4" CategoryTheory.Cat
add_to_sga "4 VI 6.1.4" CategoryTheory.Cat.Hom
add_to_sga "4 VI 6.1.4" CategoryTheory.Cat.category
add_to_sga "4 VI 6.1.4" CategoryTheory.MorphismProperty.FunctorsInverting
add_to_sga "4 VI 6.1.4" CategoryTheory.MorphismProperty.IsInvertedBy
add_to_sga "4 VI 6.2" "partial"
  CategoryTheory.Localization.instInhabitedStrictUniversalPropertyFixedTargetLocalizationQ
add_to_sga "4 VI 6.5" "Clause a)" CategoryTheory.Localization.Construction.objEquiv
add_to_sga "4 VI 6.5" "Clause b" CategoryTheory.Localization.exists_rightFraction
add_to_sga "4 VI 6.5" "Clause d" CategoryTheory.Localization.faithful_whiskeringLeft
add_to_sga "4 VI 6.5" "Clause d)" CategoryTheory.Localization.full_whiskeringLeft
add_to_sga "4 VI 6.5" "Clause d)" CategoryTheory.Localization.fullyFaithfulWhiskeringLeft
add_to_sga "4 VI 6.5" "Clause d)"
  CategoryTheory.Localization.instFaithfulFunctorWhiskeringLeftFunctor'
add_to_sga "4 VI 6.5" CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom
add_to_sga "4 VI 6.5" CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.comp
add_to_sga "4 VI 6.5" CategoryTheory.MorphismProperty.LeftFraction.Localization.Q
add_to_sga "4 VI 6.5" "Clause a" CategoryTheory.MorphismProperty.LeftFraction.Localization.Q_obj
add_to_sga "4 VI 6.5" "Clauses a)"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocalizationQ
add_to_sga "4 VI 6.5" CategoryTheory.MorphismProperty.LeftFraction.comp
add_to_sga "4 VI 6.5" "more general" CategoryTheory.MorphismProperty.LeftFraction.comp_eq
add_to_sga "4 VI 6.5" "Clause e), special case"
  CategoryTheory.ObjectProperty.SerreClassLocalization.preservesFiniteLimits
add_to_sga "4 VI 6.6" "clause (a), special case" CategoryTheory.IsCofiltered.over
add_to_sga "4 VI 7.1.3" "partial" CategoryTheory.Functor.IsFibered.pullbackPullbackIso
add_to_sga "4 VI 7.1.7" "special case" CategoryTheory.conjugateEquiv
add_to_sga "4 VI 7.3.2" "partial" CategoryTheory.Arrow
open CategoryTheory.Functor.sheafPullbackConstruction in
add_to_sga "4 VI 7.4.13.4" "more general"
  instIsRightAdjointSheafSheafPushforwardContinuousOfHasWeakSheafify
add_to_sga "4 VI 7.4.13.4"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
add_to_sga "4 VI 7.4.13.5" "special case" CategoryTheory.Functor.isTerminal
add_to_sga "4 VI 7.4.13.5" "special case" CategoryTheory.Sheaf.isTerminalTerminal
add_to_sga "4 VI 7.4.13.6" CategoryTheory.Over.forget
add_to_sga "4 VI 8.3.1" "partial" CategoryTheory.IsCofiltered
add_to_sga "4 VI 8.3.1" "partial" CategoryTheory.Limits.PreservesLimitsOfShape
add_to_sga "4 VI 8.3.7" CategoryTheory.Precoverage.IsStableUnderComposition
add_to_sga "4 VI 8.4.6" CategoryTheory.GrothendieckTopology.IsLocalSite.point
add_to_sga "4 VI 8.4.6" CategoryTheory.GrothendieckTopology.IsLocalSite.pointSheafFiberIso
add_to_sga "4 VI 8.6.2" "special case" RingCat.Colimits.colimitIsColimit
add_to_sga "4 VI 8.6.2" "special case" RingCat.Colimits.hasColimits_ringCat
add_to_sga "4 VI 8.6.2" "special case" RingCat.FilteredColimits.colimitCoconeIsColimit
add_to_sga "4 VI 8.7.1" "partial" CategoryTheory.Limits.PreservesFilteredColimits
add_to_sga "4 VI 9.0" "special case"
  AlgebraicGeometry.Scheme.instHasEnoughPointsEtaleSmallEtaleTopology
add_to_sga "4 VII 1.1" AlgebraicGeometry.Scheme
add_to_sga "4 VII 1.1" AlgebraicGeometry.Scheme.instCategory
add_to_sga "4 VII 1.2" "more general" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
open AlgebraicGeometry.Etale in
add_to_sga "4 VII 1.2" "more general"
  instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_sga "4 VII 1.2" "more general" AlgebraicGeometry.Etale.of_comp
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.Cover.mkOfCovers
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.Etale
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.Etale.forget
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.Etale.mk
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.etalePrecoverage
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.etalePretopology
add_to_sga "4 VII 1.2" "more general" AlgebraicGeometry.Scheme.grothendieckTopology
add_to_sga "4 VII 1.2" "more general" AlgebraicGeometry.Scheme.grothendieckTopology_eq_inf
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.smallEtalePretopology
add_to_sga "4 VII 1.2" AlgebraicGeometry.Scheme.smallEtaleTopology
add_to_sga "4 VII 1.3" AlgebraicGeometry.Scheme.Etale
add_to_sga "4 VII 1.3" AlgebraicGeometry.Scheme.etalePretopology
add_to_sga "4 VII 1.3" AlgebraicGeometry.Scheme.instCategoryEtale
add_to_sga "4 VII 1.3" AlgebraicGeometry.Scheme.smallEtalePretopology
add_to_sga "4 VII 1.3" AlgebraicGeometry.Scheme.smallEtaleTopology
add_to_sga "4 VII 1.3" CategoryTheory.Sheaf
add_to_sga "4 VII 1.3" CategoryTheory.Sheaf.H
add_to_sga "4 VII 1.3" "more general" CategoryTheory.Sheaf.H'
add_to_sga "4 VII 1.4" "special case" Algebra.Etale.baseChange
add_to_sga "4 VII 1.4" "partial" AlgebraicGeometry.Etale.instFstScheme
add_to_sga "4 VII 1.4" "special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "4 VII 1.4" "special case" AlgebraicGeometry.Etale.instResLE
open AlgebraicGeometry.Scheme in
add_to_sga "4 VII 1.4" "partial"
  instIsStableUnderBaseChangePrecoverageOfIsJointlySurjectivePreservingOfIsStableUnderBaseChange
add_to_sga "4 VII 1.6" AlgebraicGeometry.Scheme.Etale.mk
add_to_sga "4 VII 1.7" "partial" AlgebraicGeometry.Scheme.AffineEtale.instEssentiallySmall
add_to_sga "4 VII 1.7" "partial"
  AlgebraicGeometry.Scheme.AffineEtale.instIsOneHypercoverDenseEtaleSpecTopologySmallEtaleTopology
add_to_sga "4 VII 1.7" "partial" AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv
add_to_sga "4 VII 1.7" AlgebraicGeometry.Scheme.AffineEtale.topology
add_to_sga "4 VII 2.1" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "4 VII 3.1" "special case"
  AlgebraicGeometry.Scheme.AffineEtale.instIsCoverDenseEtaleSpecSmallEtaleTopology
add_to_sga "4 VII 3.1" "special case"
  AlgebraicGeometry.Scheme.AffineEtale.instIsDenseSubsiteEtaleTopologySmallEtaleTopologySpec
add_to_sga "4 VII 3.1" "special case"
  AlgebraicGeometry.Scheme.AffineEtale.instIsOneHypercoverDenseEtaleSpecTopologySmallEtaleTopology
add_to_sga "4 VII 3.1" "special case" AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv
open AlgebraicGeometry.Scheme in
add_to_sga "4 VII 3.1" "special case"
  instIsEquivalenceSheafEtaleSmallEtaleTopologyAffineEtaleTopologySheafPushforwardContinuousSpec
open AlgebraicGeometry.Scheme in
add_to_sga "4 VII 3.1" "special case"
  instIsEquivalenceSheafEtaleSmallEtaleTopologyAffineEtaleTopologySheafPushforwardContinuousSpec_1
add_to_sga "4 VII 4.0" "partial" AlgebraicGeometry.Scheme.instPreservesFiniteLimitsEtaleOverForget
add_to_sga "4 VII 4.2" AlgebraicGeometry.Scheme.fpqcPrecoverage
add_to_sga "4 VII 4.2" AlgebraicGeometry.Scheme.fpqcTopology
add_to_sga "4 VII 4.2" "more general" AlgebraicGeometry.Scheme.grothendieckTopology
add_to_sga "4 VII 4.2" "special case" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "4 VII 4.2" "more general"
  AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology
add_to_sga "4 VII 4.2" "more general" AlgebraicGeometry.Scheme.propQCTopology
add_to_sga "4 VII 4.2" AlgebraicGeometry.Scheme.zariskiPrecoverage
add_to_sga "4 VII 4.2" AlgebraicGeometry.Scheme.zariskiPretopology
add_to_sga "4 VII 4.2" AlgebraicGeometry.Scheme.zariskiTopology
add_to_sga "4 VII 4.2" "partial" AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology
add_to_sga "4 VII 4.2" "special case" AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf
add_to_sga "4 VII 4.2" "special case" AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb
add_to_sga "4 VII 4.2.2" Opens.grothendieckTopology
add_to_sga "4 VII 5.1" "more general" AlgebraicGeometry.LocallyRingedSpace.toTopCat
add_to_sga "4 VII 5.1" AlgebraicGeometry.Scheme.hasCoeToTopCat
add_to_sga "4 VII 5.1" "special case" AlgebraicGeometry.preservesLimitsOfSize_algSpec
add_to_sga "4 VII 5.2" "a" AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_sga "4 VII 5.2" "a: injectivity"
  AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_sga "4 VII 5.2" "a: surjectivity"
  AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
add_to_sga "4 VII 5.2" "more general" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_sga "4 VII 5.4" "partial" AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit
add_to_sga "4 VII 5.4" "partial" AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit
add_to_sga "4 VIII 2.1" Field.absoluteGaloisGroup
add_to_sga "4 VIII 2.1" Field.instGroupAbsoluteGaloisGroup
add_to_sga "4 VIII 2.1" "π is a topological group" Field.instIsTopologicalGroupAbsoluteGaloisGroup
add_to_sga "4 VIII 2.1" Field.instTopologicalSpaceAbsoluteGaloisGroup
add_to_sga "4 VIII 2.1" InfiniteGalois.profiniteGalGrp
add_to_sga "4 VIII 2.1" SeparableClosure
add_to_sga "4 VIII 2.1" "partial" instIsTopologicalGroupAlgEquiv
add_to_sga "4 VIII 2.1" "partial" krullTopology
add_to_sga "4 VIII 3.1" "(x)" IsSepClosure.equiv
add_to_sga "4 VIII 3.2" "partial"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "4 VIII 3.2" "partial" AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed
add_to_sga "4 VIII 3.2" AlgebraicGeometry.Scheme.pointSmallEtale
add_to_sga "4 VIII 3.2" "partial"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiberOfIsSepClosed
add_to_sga "4 VIII 3.2" "partial"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiniteSpecOfIsSepClosed
add_to_sga "4 VIII 3.2" IsSepClosed
add_to_sga "4 VIII 3.3" AlgebraicGeometry.Scheme.pointSmallEtale
add_to_sga "4 VIII 3.3" "more general" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4 VIII 3.4" "more general" AlgebraicGeometry.Scheme.pointSmallEtale
add_to_sga "4 VIII 3.5" AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
add_to_sga "4 VIII 3.5" "more general" AlgebraicGeometry.Scheme.isConservative_pointSmallEtale
add_to_sga "4 VIII 3.5" CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints
open AlgebraicGeometry.Scheme in
add_to_sga "4 VIII 3.9" "more general"
  instIsCofilteredElementsEtaleCompOverForgetObjOppositeFunctorTypeCoyonedaOpMk
add_to_sga "4 VIII 3.9" "more general"
  CategoryTheory.GrothendieckTopology.Point.instIsIsoMapFunctorOppositePresheafFiberToSheafify
open CategoryTheory.GrothendieckTopology.Point in
add_to_sga "4 VIII 3.9" "more general"
  instLiftingFunctorOppositeSheafPresheafToSheafWPresheafFiberSheafFiber
add_to_sga "4 VIII 3.9" "more general"
  CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso
add_to_sga "4 VIII 3.11" AlgebraicGeometry.Scheme.fromSpecResidueField
add_to_sga "4 VIII 3.11" AlgebraicGeometry.Scheme.instCanonicallyOverSpecResidueField
add_to_sga "4 VIII 3.11" AlgebraicGeometry.Scheme.instOverSpecResidueField
add_to_sga "4 VIII 3.13" "E = X"
  AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
add_to_sga "4 VIII 3.13" "E = X" AlgebraicGeometry.Scheme.isConservative_pointSmallEtale
add_to_sga "4 VIII 4.1" HenselianLocalRing
add_to_sga "4 VIII 4.1" HenselianRing
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.instQuasiSeparatedFstScheme
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.quasiCompact_iff_compactSpace
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_sga "4 VIII 5.4" "special case" RingHom.finite_isStableUnderBaseChange
add_to_sga "4 VIII 7.9" AlgebraicGeometry.Scheme.pointSmallEtale
add_to_sga "4 VIII 7.9.1" CategoryTheory.Functor.Elements
add_to_sga "4 VIII 7.9.1" "partial" CategoryTheory.Functor.isCofiltered_elements
add_to_sga "4 VIII 7.9.1" CategoryTheory.Functor.Elements.instCategory
add_to_sga "4 VIII 7.9.3" "partial" AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat
add_to_sga "4 VIII 7.9.3" CategoryTheory.GrothendieckTopology.Point.presheafFiber
add_to_sga "4 VIII 7.9.3" "more general"
  CategoryTheory.GrothendieckTopology.Point.subsingleton_fiber_obj
add_to_sga "4 VIII 7.9.3" "φ₀(X) = 1" CategoryTheory.GrothendieckTopology.Point.uniqueFiberObj
add_to_sga "4 VIII 7.9.3" CategoryTheory.IsCofiltered
add_to_sga "4 VIII 7.9.3" CategoryTheory.IsConnected
add_to_sga "4 VIII 7.9.3" FrameHom
add_to_sga "4 VIII 7.9.3" IsGenericPoint
add_to_sga "4 VIII 7.9.3" QuasiSober
add_to_sga "4 VIII 9.3" "more general" CategoryTheory.Subobject
add_to_sga "4 VIII 9.4.4" "more general"
  AlgebraicGeometry.instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCarrierCommRingCat
add_to_sga "4 Vbis 1.1.2" "more general" CategoryTheory.Functor.Fiber.inducedFunctor
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory.Hom
add_to_sga "4 Vbis 1.1.3" "partial" SemiSimplexCategory.homEquiv
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory.homOfMono
add_to_sga "4 Vbis 1.1.3" "partial" SemiSimplexCategory.instMonoSimplexCategoryMapToSimplexCategory
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory.mk
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory.smallCategory
add_to_sga "4 Vbis 1.1.3" SemiSimplexCategory.toSimplexCategory
add_to_sga "4 Vbis 1.1.3" "same objects" SemiSimplexCategory.toSimplexCategory_obj
add_to_sga "4 Vbis 1.1.3" SimplexCategory
add_to_sga "4 Vbis 1.1.3" SimplexCategory.Hom
add_to_sga "4 Vbis 1.1.3" SimplexCategory.Hom.id
add_to_sga "4 Vbis 1.1.3" SimplexCategory.Hom.mk
add_to_sga "4 Vbis 1.1.3" "partial" SimplexCategory.homEquivOrderHom
add_to_sga "4 Vbis 1.1.3" SimplexCategory.mk
add_to_sga "4 Vbis 1.1.3" SimplexCategory.mkHom
add_to_sga "4 Vbis 1.1.3" SimplexCategory.skeletalFunctor
add_to_sga "4 Vbis 1.1.3" SimplexCategory.smallCategory
add_to_sga "4 Vbis 1.1.3" SimplexCategory.toPartOrd
add_to_sga "4 Vbis 1.1.3" "ordered sets of objects" SimplexCategory.toPartOrd_obj
add_to_sga "4 Vbis 1.1.3" "partial" SimplexCategory.toType_apply
add_to_sga "4 Vbis 1.2.6" CategoryTheory.Functor
add_to_sga "4 Vbis 1.2.6" CategoryTheory.Functor.const
add_to_sga "4 Vbis 1.2.6" CategoryTheory.SimplicialObject.Augmented
add_to_sga "4 Vbis 1.2.6" CategoryTheory.SimplicialObject.const
add_to_sga "4 Vbis 1.2.6" "special case" SSet.Augmented
add_to_sga "4 Vbis 1.2.7" CategoryTheory.Arrow.augmentedCechNerve
add_to_sga "4 Vbis 1.2.7" CategoryTheory.Arrow.cechNerve
add_to_sga "4 Vbis 1.2.7" "special case" CategoryTheory.CechNerveTerminalFrom.iso
add_to_sga "4 Vbis 1.2.7" "partial" CategoryTheory.Functor.currying
add_to_sga "4 Vbis 1.2.7" "special case" CategoryTheory.Limits.FormalCoproduct.cech
add_to_sga "4 Vbis 1.2.7" "special case" CategoryTheory.Limits.FormalCoproduct.cechFunctor
add_to_sga "4 Vbis 1.2.7" "special case" CategoryTheory.Limits.FormalCoproduct.cechIsoCechNerve
add_to_sga "4 Vbis 1.2.7" "case S terminal"
  CategoryTheory.Limits.FormalCoproduct.cechIsoCechNerveApp
add_to_sga "4 Vbis 1.2.7" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "4 Vbis 1.2.7" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "4 Vbis 1.2.10" "more general" CategoryTheory.Bicategory.precomp
add_to_sga "4 Vbis 1.2.10" "more general" CategoryTheory.Bicategory.precomposing
add_to_sga "4 Vbis 1.2.10" "more general" CategoryTheory.Bicategory.precomposingCat
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.Cocone.isColimitYonedaEquiv
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.Cone.isLimitCoyonedaEquiv
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.IsColimit.homIso
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.coyonedaOpColimitIsoLimitCoyoneda
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.coyonedaOpColimitIsoLimitCoyoneda'
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.limit.homIso
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.Limits.limit.homIso'
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.coyonedaFunctor_preservesLimits
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.coyonedaPreservesLimitsOfShape
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.coyoneda_preservesLimit
add_to_sga "4 Vbis 1.2.10.1" "special case" CategoryTheory.coyoneda_preservesLimits
add_to_sga "4 Vbis 1.2.10.1" "special case"
  CategoryTheory.instPreservesLimitsOfSizeOppositeFunctorTypeUliftCoyoneda
add_to_sga "4 Vbis 1.2.11" "special case" CategoryTheory.constantPresheafAdj
add_to_sga "4 Vbis 1.2.11" "special case" CategoryTheory.evaluationAdjunctionLeft
add_to_sga "4 Vbis 1.2.11" "special case" CategoryTheory.evaluationAdjunctionRight
add_to_sga "4 Vbis 1.2.11" "partial" CategoryTheory.evaluationIsLeftAdjoint
add_to_sga "4 Vbis 1.2.11" "partial" CategoryTheory.evaluationIsRightAdjoint
add_to_sga "4 Vbis 1.2.11" "special case" CategoryTheory.evaluationLeftAdjoint
add_to_sga "4 Vbis 1.2.11" "partial" CategoryTheory.evaluationLeftAdjoint_obj_obj
add_to_sga "4 Vbis 1.2.11" "special case" CategoryTheory.evaluationRightAdjoint
add_to_sga "4 Vbis 1.2.11" "partial" CategoryTheory.evaluationRightAdjoint_obj_obj
add_to_sga "4 Vbis 1.3.6" "special case"
  AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "4 Vbis 1.3.6" "special case" PresheafOfModules.pushforward_obj_obj
add_to_sga "4 Vbis 1.3.6" "φ* left adjoint to φ_*" SheafOfModules.PullbackConstruction.adjunction
add_to_sga "4 Vbis 1.3.7" "special case" Rep.instIsLeftAdjointResFunctor
add_to_sga "4 Vbis 1.3.7" "special case" Rep.resCoindAdjunction
add_to_sga "4 Vbis 1.3.7" "special case" Rep.resIndAdjunction
add_to_sga "4 Vbis 1.3.7" "special case" SheafOfModules.Hom.over
add_to_sga "4 Vbis 2.1.1" "special case" CategoryTheory.CosimplicialObject.const
add_to_sga "4 Vbis 2.1.1" "partial" CategoryTheory.Functor.const
add_to_sga "4 Vbis 2.1.1" "partial" CategoryTheory.Functor.instFaithfulConstOfNonempty
add_to_sga "4 Vbis 2.1.1" CategoryTheory.Limits.constLimAdj
add_to_sga "4 Vbis 2.1.1" "partial" CategoryTheory.Limits.hasLimitsOfShape_iff_isLeftAdjoint_const
add_to_sga "4 Vbis 2.1.1" "partial" CategoryTheory.Limits.lim
add_to_sga "4 Vbis 2.1.1" "left exactness of ε*" CategoryTheory.Limits.preservesLimits_const
add_to_sga "4 Vbis 2.1.1" "partial" CategoryTheory.instFullFunctorConstOfIsConnected
add_to_sga "4 Vbis 2.2.5" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfCompIsoId
add_to_sga "4 Vbis 2.2.5" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_sga "4 Vbis 2.2.5" "partial" CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful
add_to_sga "4 Vbis 2.2.5" "partial" CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful
add_to_sga "4 Vbis 2.3.2" "more general" HomologicalComplex₂.DoubleComplex.toHomologicalComplex₂
add_to_sga "4 Vbis 2.3.3" DerivedCategory.Plus.Qh
add_to_sga "4 Vbis 2.3.3" "(A)" DerivedCategory.Plus.instIsLocalizationPlusQhQuasiIso
add_to_sga "4 Vbis 2.3.3" "more general" HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
add_to_sga "4 Vbis 2.3.3" "(A)" HomotopyCategory.plus
add_to_sga "4 Vbis 2.3.9" "partial" AlgebraicTopology.AlternatingCofaceMapComplex.obj
add_to_sga "4 Vbis 2.3.9" "2.3.9.1" AlgebraicTopology.AlternatingCofaceMapComplex.objD
add_to_sga "4 Vbis 2.3.9" "partial" AlgebraicTopology.alternatingCofaceMapComplex
add_to_sga "4 Vbis 2.3.10" "partial" AlgebraicTopology.AlternatingCofaceMapComplex.obj
add_to_sga "4 Vbis 2.3.10" "partial" AlgebraicTopology.AlternatingCofaceMapComplex.objD
add_to_sga "4 Vbis 2.4.0" "Abelianness of fibers" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "4 Vbis 2.4.0" "partial" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "4 Vbis 2.4.4" "more general" CategoryTheory.Functor.mapHomotopyCategoryPlus
add_to_sga "4 Vbis 2.4.9" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfCompIsoId
add_to_sga "4 Vbis 2.4.9" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_sga "4 Vbis 2.4.9" "partial" CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful
add_to_sga "4 Vbis 2.4.9" "partial" CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful
add_to_sga "4 Vbis 2.5.1" "more general" CategoryTheory.FilteredObject
add_to_sga "4 Vbis 2.5.1" "more general" CategoryTheory.FilteredObject.Hom
add_to_sga "4 Vbis 2.5.1" "partial" CategoryTheory.FilteredObject.preadditive
add_to_sga "4 Vbis 2.5.1" "more general" HomotopyCategory.instIsTriangulatedIntUp
add_to_sga "4 Vbis 2.5.1" "partial" HomotopyCategory.instPretriangulatedIntUp
add_to_sga "4 Vbis 2.5.1" "partial" HomotopyCategory.plus
add_to_sga "4 Vbis 3.0" CategoryTheory.Limits.HasFiniteWidePullbacks
add_to_sga "4 Vbis 3.0" CategoryTheory.Limits.HasPullbacks
add_to_sga "4 Vbis 3.0.0" "partial" CategoryTheory.Limits.BinaryCoproductDisjoint
add_to_sga "4 Vbis 3.0.0" "partial" CategoryTheory.Limits.BinaryCoproductsDisjoint
add_to_sga "4 Vbis 3.0.0" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 Vbis 3.0.0" CategoryTheory.Limits.CoproductsOfShapeDisjoint
add_to_sga "4 Vbis 3.0.0" "partial" CategoryTheory.Limits.HasBinaryCoproduct
add_to_sga "4 Vbis 3.0.0" "partial" CategoryTheory.Limits.HasBinaryCoproducts
add_to_sga "4 Vbis 3.0.0" CategoryTheory.Limits.HasCoproduct
add_to_sga "4 Vbis 3.0.0" CategoryTheory.Limits.HasCoproducts
add_to_sga "4 Vbis 3.0.0" "partial" CategoryTheory.Limits.HasCountableCoproducts
add_to_sga "4 Vbis 3.0.1" CategoryTheory.SimplicialObject.Truncated.cosk
add_to_sga "4 Vbis 3.0.1" CategoryTheory.SimplicialObject.cosk
add_to_sga "4 Vbis 3.0.1" CategoryTheory.SimplicialObject.truncation
add_to_sga "4 Vbis 3.0.1" "special case" SSet
add_to_sga "4 Vbis 3.0.1" "special case" SSet.Truncated.cosk
add_to_sga "4 Vbis 3.0.1" "special case" SSet.cosk
add_to_sga "4 Vbis 3.0.1" "special case" SSet.coskAdj
add_to_sga "4 Vbis 3.0.1" "special case" SSet.truncation
add_to_sga "4 Vbis 3.0.1" SimplexCategory.Truncated
add_to_sga "4 Vbis 3.0.2" CategoryTheory.SimplicialObject.Homotopy
add_to_sga "4 Vbis 3.0.2" "special case" SSet.Homotopy
add_to_sga "4 Vbis 3.0.2.2" "E = simplicial sets" SSet.Homotopy
add_to_sga "4 Vbis 3.0.2.2" "special case" SSet.RelativeMorphism.Homotopy
add_to_sga "4 Vbis 3.0.2.3" "E = simplicial sets"
  CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap
add_to_sga "4 Vbis 3.0.2.3" "E = simplicial sets"
  CategoryTheory.SimplicialObject.Homotopy.singularChainComplexFunctorObjMap
add_to_sga "4 Vbis 3.0.2.3" "Case E = C" CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy
add_to_sga "4 Vbis 3.0.2.3" "E = simplicial sets" SSet.Homotopy.chainComplexMap
add_to_sga "4 Vbis 3.0.2.3" "E = simplicial sets" SSet.Homotopy.singularChainComplexFunctorObjMap
add_to_sga "4 Vbis 3.2.3" CategoryTheory.Functor.const
add_to_sga "4 Vbis 3.2.3" CategoryTheory.SimplicialObject.const
add_to_sga "4 Vbis 3.3" "special case" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_sga "4 Vbis 3.3" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "4 Vbis 4.1.0" "partial" AlgebraicGeometry.SheafedSpace.instCategory
add_to_sga "4 Vbis 4.1.0" "objects (X,F) of E" AlgebraicGeometry.SheafedSpace.mk
add_to_sga "4 Vbis 4.1.0" IsSeparatedMap
add_to_sga "4 Vbis 4.1.0" "partial" SheafOfModules.mk
add_to_sga "4 Vbis 4.1.0" TopCat
add_to_sga "4 Vbis 4.1.0" TopCat.instCategory
add_to_sga "4 Vbis 4.1.0" isSeparatedMap_iff_isClosedEmbedding
add_to_sga "4 Vbis 4.1.0" isSeparatedMap_iff_isClosedMap
add_to_sga "4 Vbis 4.1.0" isSeparatedMap_iff_isClosed_diagonal
add_to_sga "4 Vbis 4.1.4" "special case" IsCompact.nhdsSet_inter_eq
add_to_sga "4 Vbis 4.1.4" "partial" SeparatedNhds.of_isCompact_isCompact_isClosed
add_to_sga "4 Vbis 4.2.0" "partial" AlgebraicGeometry.LocallyRingedSpace.𝒪
add_to_sga "4 Vbis 4.2.0" "partial" AlgebraicGeometry.QuasiSeparated
add_to_sga "4 Vbis 4.2.0" "partial" AlgebraicGeometry.Scheme.sheaf
add_to_sga "4 Vbis 4.2.0" "Fiber G_X" SheafOfModules.isQuasicoherent
add_to_sga "4 Vbis 5.1.0" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 Vbis 5.1.0" CategoryTheory.Limits.CoproductsOfShapeDisjoint
add_to_sga "4 Vbis 5.1.0" CategoryTheory.Limits.HasFiniteCoproducts
add_to_sga "4 Vbis 5.1.0" CategoryTheory.SimplicialObject.δ_def
add_to_sga "4 Vbis 5.1.0" CategoryTheory.SimplicialObject.σ_def
add_to_sga "4 Vbis 5.1.0" SimplexCategory.δ
add_to_sga "4 Vbis 5.1.1" "more general" CategoryTheory.SimplicialObject.Split
add_to_sga "4 Vbis 5.1.1" "more general" CategoryTheory.SimplicialObject.Splitting
add_to_sga "4 Vbis 5.1.8" CategoryTheory.Codiscrete.instCategory
add_to_sga "4 Vbis 5.2" CharZero
add_to_sga "4 Vbis 5.2" Field
add_to_sga "4 Vbis 5.3" CharZero
add_to_sga "4 Vbis 5.3" Field
