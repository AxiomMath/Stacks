module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Central.Defs
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Analysis.BoxIntegral.Partition.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Resolution
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.Order.SetNotation
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Teichmuller
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sober
import StacksCore.Algebra.BrauerGroup.AlgClosed
import StacksCore.Algebra.Split.Basic
import StacksCore.Algebra.Split.CentralSimple
import StacksCore.Algebra.Split.DivisionRing
import StacksCore.RingTheory.SkolemNoether
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4½ references registered by name

Declarations realizing numbered items of SGA 4½, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "4½ Arcata 1.1" CategoryTheory.Sieve.generateFamily
add_to_sga "4½ Arcata 1.1" CategoryTheory.Sieve.ofObjects
add_to_sga "4½ Arcata 1.1" Opens.grothendieckTopology
add_to_sga "4½ Arcata 1.1" Opens.mem_grothendieckTopology
add_to_sga "4½ Arcata 1.1" "more general" TopCat.LocalPredicate
add_to_sga "4½ Arcata 1.1" TopCat.Presheaf.SheafCondition.OpensLeCover
add_to_sga "4½ Arcata 1.1" "special case"
  TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology
add_to_sga "4½ Arcata 1.1" "more general" TopCat.continuousLocal
add_to_sga "4½ Arcata 1.1" "restriction direction" TopCat.continuousPrelocal
add_to_sga "4½ Arcata 1.1" "partial" continuousOn_of_locally_continuousOn
add_to_sga "4½ Arcata 1.2.1" "more general" CategoryTheory.Presieve.FamilyOfElements.SieveCompatible
add_to_sga "4½ Arcata 1.2.3" CategoryTheory.Presieve.IsSheaf
add_to_sga "4½ Arcata 1.2.3" CategoryTheory.Presieve.IsSheafFor
add_to_sga "4½ Arcata 1.2.3" "partial" ContinuousMap.liftCover'
add_to_sga "4½ Arcata 1.2.3" "partial" TopCat.Presheaf.IsGluing
add_to_sga "4½ Arcata 1.2.3" "more general" TopCat.Presheaf.IsSheaf
add_to_sga "4½ Arcata 1.3.2" "partial"
  CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence
add_to_sga "4½ Arcata 1.4.1" "Affine schemes"
  AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
add_to_sga "4½ Arcata 1.4.1" "special case" AlgebraicGeometry.flat_and_surjective_SpecMap_iff
add_to_sga "4½ Arcata 1.4.1" "Affine ring criterion" RingHom.FaithfullyFlat.eq_and
add_to_sga "4½ Arcata 1.4.1" "Affine ring criterion"
  RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_sga "4½ Arcata 1.4.2" "(ii), special case" Ideal.FG.of_FG_map_of_faithfullyFlat
add_to_sga "4½ Arcata 1.4.2" "Clause (i), special case"
  Module.FaithfullyFlat.iff_exact_iff_rTensor_exact
add_to_sga "4½ Arcata 1.4.2" "more general" Module.FaithfullyFlat.lTensor_exact_iff_exact
add_to_sga "4½ Arcata 1.4.2" "more general" Module.FaithfullyFlat.lTensor_reflects_exact
add_to_sga "4½ Arcata 1.4.2" "more general" Module.FaithfullyFlat.rTensor_exact_iff_exact
add_to_sga "4½ Arcata 1.4.2" "more general" Module.FaithfullyFlat.rTensor_reflects_exact
add_to_sga "4½ Arcata 1.4.2" Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
add_to_sga "4½ Arcata 1.4.2" Module.Flat.of_flat_tensorProduct
add_to_sga "4½ Arcata 1.4.2" "special case" RingHom.Finite.codescendsAlong_faithfullyFlat
add_to_sga "4½ Arcata 1.4.3" CategoryTheory.Sieve.generateFamily
add_to_sga "4½ Arcata 1.4.3" "singleton family" CategoryTheory.Sieve.generateSingleton
add_to_sga "4½ Arcata 1.4.3" CategoryTheory.Sieve.ofObjects
add_to_sga "4½ Arcata 1.5.1" "special case" AlgEquiv.applyMulSemiringAction
add_to_sga "4½ Arcata 1.5.1" ContRepresentation.invariants
add_to_sga "4½ Arcata 1.5.1" "special case" FixedPoints.subalgebra
add_to_sga "4½ Arcata 1.5.1" "partial" FixedPoints.subfield
add_to_sga "4½ Arcata 1.5.1" "b" LinearMap
add_to_sga "4½ Arcata 1.5.1" "c" MulAction
add_to_sga "4½ Arcata 1.5.1" "partial" MulAction.fixedPoints
add_to_sga "4½ Arcata 1.5.1" Representation.invariants
add_to_sga "4½ Arcata 1.5.3" "more general" groupCohomology.H1ofAutOnUnitsUnique
add_to_sga "4½ Arcata 1.5.3" "more general"
  groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
add_to_sga "4½ Arcata 1.6.1" CategoryTheory.Sieve.generateFamily
add_to_sga "4½ Arcata 1.6.1" CategoryTheory.Sieve.generateFamily_eq
add_to_sga "4½ Arcata 1.6.1" "singleton family" CategoryTheory.Sieve.generateSingleton
add_to_sga "4½ Arcata 1.6.1" "singleton family" CategoryTheory.Sieve.generateSingleton_eq
add_to_sga "4½ Arcata 1.6.1" "more general" CategoryTheory.Sieve.generate_apply
add_to_sga "4½ Arcata 1.6.1" CategoryTheory.Sieve.mem_ofArrows_iff
add_to_sga "4½ Arcata 1.6.1" CategoryTheory.Sieve.mk
add_to_sga "4½ Arcata 1.6.1" "partial" CategoryTheory.Sieve.ofArrows.exists
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.Cover
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.arrow_stable
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.covering_of_eq_top
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.mk
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.pullback_stable
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.pullback_stable'
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.sieves
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.top_mem
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.top_mem'
add_to_sga "4½ Arcata 1.6.2" CategoryTheory.GrothendieckTopology.transitive
add_to_sga "4½ Arcata 1.6.3" "special case"
  AlgebraicGeometry.Scheme.instAbelianSheafAffineEtaleTopology
add_to_sga "4½ Arcata 1.6.3" "special case"
  AlgebraicGeometry.Scheme.instAbelianSheafEtaleSmallEtaleTopology
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Functor
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Functor.map
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Functor.obj
add_to_sga "4½ Arcata 1.6.3" "special case" CategoryTheory.Presheaf.IsSheaf'
add_to_sga "4½ Arcata 1.6.3" "partial" CategoryTheory.Presieve.FamilyOfElements
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Presieve.FamilyOfElements.Compatible
add_to_sga "4½ Arcata 1.6.3" "special case"
  CategoryTheory.Presieve.FamilyOfElements.PullbackCompatible
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Presieve.FamilyOfElements.SieveCompatible
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Presieve.IsSheaf
add_to_sga "4½ Arcata 1.6.3" "partial" CategoryTheory.Presieve.IsSheafFor
add_to_sga "4½ Arcata 1.6.3" CategoryTheory.Sheaf
add_to_sga "4½ Arcata 1.6.3" "special case" TopCat.Presheaf.IsCompatible
add_to_sga "4½ Arcata 1.6.3" "special case" TopCat.Presheaf.IsSheaf
add_to_sga "4½ Arcata 1.6.3" "special case" TopCat.Presheaf.restrict
add_to_sga "4½ Arcata 1.6.3" "special case" TopCat.Presheaf.restrictOpen
add_to_sga "4½ Arcata 1.6.3" "open-set sites" TopCat.Sheaf.instAbelian
add_to_sga "4½ Arcata 1.6.4" Opens.grothendieckTopology
add_to_sga "4½ Arcata 1.6.4" Opens.mem_grothendieckTopology
add_to_sga "4½ Arcata 1.6.4" "partial" TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology
add_to_sga "4½ Arcata 1.6.4" "partial" TopologicalSpace.Opens
add_to_sga "4½ Arcata 1.6.5" CategoryTheory.Limits.IsTerminal
add_to_sga "4½ Arcata 1.6.5" CategoryTheory.Sheaf.Γ
add_to_sga "4½ Arcata 1.6.5" "more general" CategoryTheory.Sheaf.ΓNatIsoSheafSections
add_to_sga "4½ Arcata 1.6.5" "partial" TopCat.Sheaf.sections_exact_of_left_exact
add_to_sga "4½ Arcata 2.1.1" Algebra.Etale
add_to_sga "4½ Arcata 2.1.1" "étale implies Ω = 0" Algebra.Etale.instUnramified
add_to_sga "4½ Arcata 2.1.1" "finitely presented" Algebra.Etale.of_formallyUnramified_of_flat
add_to_sga "4½ Arcata 2.1.1" "partial" Algebra.FormallyEtale.comp_bijective
add_to_sga "4½ Arcata 2.1.1" "more general" Algebra.FormallyEtale.iff_comp_bijective
add_to_sga "4½ Arcata 2.1.1" "étale implies flat" Algebra.WeaklyEtale.instOfEtale
add_to_sga "4½ Arcata 2.1.1" "more general" AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified
add_to_sga "4½ Arcata 2.1.1" "partial" AlgebraicGeometry.Etale.of_formallyUnramified_of_flat
add_to_sga "4½ Arcata 2.1.1" CommAlgCat.etale
add_to_sga "4½ Arcata 2.1.1" RingHom.Etale
add_to_sga "4½ Arcata 2.1.1" RingHom.Etale.iff_flat_and_formallyUnramified
add_to_sga "4½ Arcata 2.1.1" "special case" StandardEtalePair.instEtaleRing
add_to_sga "4½ Arcata 2.1.2" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "4½ Arcata 2.1.2" "more general" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "4½ Arcata 2.1.2" "special case" Algebra.FormallyEtale.iff_isSeparable
add_to_sga "4½ Arcata 2.1.2" "special case" Algebra.IsFiniteSplit.instEtale
add_to_sga "4½ Arcata 2.1.3" "special case" Algebra.Etale.baseChange
add_to_sga "4½ Arcata 2.1.3" "special case" Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat
add_to_sga "4½ Arcata 2.1.3" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
add_to_sga "4½ Arcata 2.1.3" "more general"
  AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismPropertyLocallyOfFiniteTypeFormallyUnramified
add_to_sga "4½ Arcata 2.1.3" "special case" AlgebraicGeometry.Etale.instMorphismRestrict
add_to_sga "4½ Arcata 2.1.3" "special case" AlgebraicGeometry.Etale.instResLE
add_to_sga "4½ Arcata 2.1.3" "Sorite 1.3 d) (descent)"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "4½ Arcata 2.1.3" "special case" RingHom.Etale.codescendsAlong_faithfullyFlat
add_to_sga "4½ Arcata 2.1.3" "special case" RingHom.Etale.isStableUnderBaseChange
add_to_sga "4½ Arcata 2.1.4" "more general" AlgebraicGeometry.Etale.instHasOfPostcompPropertyScheme
add_to_sga "4½ Arcata 2.1.4" AlgebraicGeometry.Scheme.Etale
add_to_sga "4½ Arcata 2.1.4" "partial" AlgebraicGeometry.Scheme.Etale.forgetFullyFaithful
add_to_sga "4½ Arcata 2.1.4" AlgebraicGeometry.Scheme.Etale.mk
add_to_sga "4½ Arcata 2.1.4" AlgebraicGeometry.Scheme.instCategoryEtale
add_to_sga "4½ Arcata 2.1.4" "partial" AlgebraicGeometry.Scheme.instFaithfulEtaleOverForget
add_to_sga "4½ Arcata 2.1.4" "partial" AlgebraicGeometry.Scheme.instFullEtaleOverForget
add_to_sga "4½ Arcata 2.1.4" "partial" AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff
add_to_sga "4½ Arcata 2.2.3" "special case" CommRing.Pic
add_to_sga "4½ Arcata 2.2.3" "special case" CommRing.Pic.mk
add_to_sga "4½ Arcata 2.2.3" instCommGroupPic
add_to_sga "4½ Arcata 2.3.2" "more general" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4½ Arcata 2.3.3" "more general" CategoryTheory.Adjunction.map_injective
add_to_sga "4½ Arcata 2.3.3" "more general"
  CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
add_to_sga "4½ Arcata 2.3.3" "more general" CategoryTheory.Injective.injective_of_adjoint
add_to_sga "4½ Arcata 2.4.2" "more general" AdjoinRoot.equiv
add_to_sga "4½ Arcata 2.4.2" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "4½ Arcata 2.4.2" "more general" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "4½ Arcata 2.4.2" "special case" Algebra.IsFiniteSplit.instEtale
add_to_sga "4½ Arcata 2.4.2" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "4½ Arcata 2.4.2" "finite set Hom_K(A" CommAlgCat.FiniteEtale.fiber
add_to_sga "4½ Arcata 2.4.2" Field.absoluteGaloisGroup
add_to_sga "4½ Arcata 2.4.2" Field.instTopologicalSpaceAbsoluteGaloisGroup
add_to_sga "4½ Arcata 2.4.2" InfiniteGalois.profiniteGalGrp
add_to_sga "4½ Arcata 2.4.2" "special case" IntermediateField.algHomAdjoinIntegralEquiv
add_to_sga "4½ Arcata 2.4.2" IsSepClosure
add_to_sga "4½ Arcata 2.4.2" SeparableClosure
add_to_sga "4½ Arcata 2.4.2" krullTopology
add_to_sga "4½ Arcata 2.4.3" "special case"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiberOfIsSepClosed
add_to_sga "4½ Arcata 2.4.3" "special case"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiniteSpecOfIsSepClosed
add_to_sga "4½ Arcata 3.1.1" Algebra.IsCentral
add_to_sga "4½ Arcata 3.1.1" "(a) ⇒ (b)" Algebra.IsCentralSimple.exists_finite_galois_split
add_to_sga "4½ Arcata 3.1.1" "(b) ⇒ (a)" Algebra.IsSplit.finite_central_simple
add_to_sga "4½ Arcata 3.1.1" "special case" Algebra.IsSplit.of_isAlgClosed
add_to_sga "4½ Arcata 3.1.1" CSA
add_to_sga "4½ Arcata 3.1.1" IsSimpleRing
add_to_sga "4½ Arcata 3.1.2" Matrix.GeneralLinearGroup
add_to_sga "4½ Arcata 3.1.2" "the image of K̄× in GL(n"
  Matrix.GeneralLinearGroup.center_eq_range_scalar
add_to_sga "4½ Arcata 3.1.2" Matrix.ProjGenLinGroup
add_to_sga "4½ Arcata 3.1.2" Matrix.ProjGenLinGroup.mk
add_to_sga "4½ Arcata 3.1.2" "exactness of (*) at GL(n" Matrix.ProjGenLinGroup.mk_eq_mk_iff
add_to_sga "4½ Arcata 3.1.2" "composite K̄× → GL(n" Matrix.ProjGenLinGroup.mk_scalar
add_to_sga "4½ Arcata 3.1.2" "partial" Matrix.ProjGenLinGroup.mk_surjective
add_to_sga "4½ Arcata 3.1.2" "partial" Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective
add_to_sga "4½ Arcata 3.1.2" "more general" skolemNoether
add_to_sga "4½ Arcata 3.1.2" "more general" skolemNoether'
add_to_sga "4½ Arcata 3.2.2" "special case" BrauerGroup.eq_one_of_isAlgClosed
add_to_sga "4½ Arcata 3.2.2" "special case" BrauerGroup.instUniqueOfIsAlgClosed
add_to_sga "4½ Arcata 3.4.1" "partial" Algebra.adjoin
add_to_sga "4½ Arcata 3.4.1" "partial" AlgebraicGeometry.specOverSpec
add_to_sga "4½ Arcata 4.3" AlgebraicGeometry.IsNoetherian
add_to_sga "4½ Arcata 5.2.5" AdjoinRoot
add_to_sga "4½ Cycle 1.1.4" "more general" CategoryTheory.Subobject
add_to_sga "4½ Cycle 1.3" "Clause b), special case" GradedTensorProduct.comm
add_to_sga "4½ Cycle 1.3" "special case" GradedTensorProduct.comm_coe_tmul_coe
add_to_sga "4½ Cycle 1.3" "Clause a)" PiTensorProduct
add_to_sga "4½ Cycle 1.3" "Clause a)" TensorProduct
add_to_sga "4½ Cycle 1.3" "partial" TensorProduct.gradedComm
add_to_sga "4½ Cycle 1.3" "Clause b), special case" TensorProduct.gradedComm_of_tmul_of
add_to_sga "4½ Cycle 1.3" "Clause b), special case" TensorProduct.gradedComm_tmul_of_zero
add_to_sga "4½ Dualite 2.1" Module.Dual
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Functor.CommShift
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Pretriangulated.Triangle
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Pretriangulated.Triangle.homMk
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Pretriangulated.Triangle.mk
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Pretriangulated.TriangleMorphism
add_to_sga "4½ Etat_0 1.1.0" CategoryTheory.Pretriangulated.TriangleMorphism.mk
add_to_sga "4½ Etat_0 1.1.0" "more general" CategoryTheory.ShiftedHom
add_to_sga "4½ Etat_0 1.1.0" "more general" CategoryTheory.ShiftedHom.comp
add_to_sga "4½ Etat_0 1.1.0" "partial" CategoryTheory.ShiftedHom.comp_assoc
add_to_sga "4½ Etat_0 1.1.1" CategoryTheory.HasShift
add_to_sga "4½ Etat_0 1.1.1" CategoryTheory.IsTriangulated
add_to_sga "4½ Etat_0 1.1.1" "partial" CategoryTheory.Pretriangulated
add_to_sga "4½ Etat_0 1.1.1" CategoryTheory.Pretriangulated.distinguishedTriangles
add_to_sga "4½ Etat_0 1.1.2" "special case" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "4½ Etat_0 1.1.2" "special case"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_sga "4½ Etat_0 1.1.2" "special case"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_sga "4½ Etat_0 1.1.2" "special case" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "4½ Etat_0 1.1.2" "special case" CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_sga "4½ Etat_0 1.1.2" "special case" CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
add_to_sga "4½ Etat_0 1.1.2"
  CategoryTheory.Pretriangulated.instIsHomologicalAddCommGrpCatObjOppositeFunctorPreadditiveCoyoneda
add_to_sga "4½ Etat_0 1.1.2"
  CategoryTheory.Pretriangulated.instIsHomologicalOppositeAddCommGrpCatObjFunctorPreadditiveYoneda
add_to_sga "4½ Etat_0 1.1.2" CategoryTheory.Pretriangulated.preadditiveYoneda_map_distinguished
add_to_sga "4½ Etat_0 1.2.1" "more general" CochainComplex.HomComplex.Cocycle.rightShiftAddEquiv
add_to_sga "4½ Etat_0 1.2.1" "partial" CochainComplex.HomComplex.Cocycle.rightUnshift
add_to_sga "4½ Etat_0 1.2.1" "additivity of T"
  CochainComplex.instAdditiveHomologicalComplexIntUpShiftFunctor
add_to_sga "4½ Etat_0 1.2.1" "additivity of T" CochainComplex.instAdditiveIntShiftFunctor
add_to_sga "4½ Etat_0 1.2.1" CochainComplex.mappingCone
add_to_sga "4½ Etat_0 1.2.1" CochainComplex.mappingCone.triangle
add_to_sga "4½ Etat_0 1.2.1" CochainComplex.of
add_to_sga "4½ Etat_0 1.2.1" CochainComplex.shiftFunctor
add_to_sga "4½ Etat_0 1.2.1" HomologicalComplex.Hom
add_to_sga "4½ Etat_0 1.2.1" "partial" HomologicalComplex.double
add_to_sga "4½ Etat_0 1.2.1" HomologicalComplex.instCategory
add_to_sga "4½ Etat_0 1.2.2" "partial" Homotopy.comp_nullHomotopicMap
add_to_sga "4½ Etat_0 1.2.2" "Htp(X" Homotopy.nullHomotopicMap_add
add_to_sga "4½ Etat_0 1.2.2" "partial" Homotopy.nullHomotopicMap_comp
add_to_sga "4½ Etat_0 1.2.2" "Htp(X" Homotopy.nullHomotopicMap_sub
add_to_sga "4½ Etat_0 1.2.2" "partial"
  HomotopyCategory.Pretriangulated.complete_distinguished_triangle_morphism
add_to_sga "4½ Etat_0 1.2.2" "TR1" HomotopyCategory.Pretriangulated.contractible_distinguished
add_to_sga "4½ Etat_0 1.2.2" "TR1" HomotopyCategory.Pretriangulated.distinguished_cocone_triangle
add_to_sga "4½ Etat_0 1.2.2" "TR1" HomotopyCategory.Pretriangulated.isomorphic_distinguished
add_to_sga "4½ Etat_0 1.2.2" "TR2" HomotopyCategory.Pretriangulated.rotate_distinguished_triangle
add_to_sga "4½ Etat_0 1.2.2" "TR2" HomotopyCategory.Pretriangulated.rotate_distinguished_triangle'
add_to_sga "4½ Etat_0 1.2.2" "partial" HomotopyCategory.instAdditiveHomologicalComplexQuotient
add_to_sga "4½ Etat_0 1.2.2" "partial"
  HomotopyCategory.instAdditiveHomologicalComplexQuotientHomotopicFunctor
add_to_sga "4½ Etat_0 1.2.2" "zero object of K(A)" HomotopyCategory.instHasZeroObject
add_to_sga "4½ Etat_0 1.2.2" "partial" HomotopyCategory.instIsTriangulatedIntUp
add_to_sga "4½ Etat_0 1.2.2" "partial" HomotopyCategory.instPreadditive
add_to_sga "4½ Etat_0 1.2.2" "partial"
  HomotopyCategory.instPreadditiveQuotientHomologicalComplexHomotopic
add_to_sga "4½ Etat_0 1.2.2" "partial" HomotopyCategory.instPretriangulatedIntUp
add_to_sga "4½ Etat_0 1.2.2" HomotopyCategory.quotient
add_to_sga "4½ Etat_0 1.2.2" instCategoryHomotopyCategory
add_to_sga "4½ Etat_0 1.2.3" "partial" CategoryTheory.ObjectProperty.IsTriangulated
add_to_sga "4½ Etat_0 1.2.3" "Clause"
  CategoryTheory.ObjectProperty.instIsTriangulatedClosed₁OfIsTriangulated
add_to_sga "4½ Etat_0 1.2.3" "Clause"
  CategoryTheory.ObjectProperty.instIsTriangulatedClosed₃OfIsTriangulated
add_to_sga "4½ Etat_0 1.2.3" CochainComplex.plus
add_to_sga "4½ Etat_0 1.2.3" "more general" HomologicalComplex.Acyclic
add_to_sga "4½ Etat_0 1.2.3" HomotopyCategory.Plus.subcategoryAcyclic
add_to_sga "4½ Etat_0 1.2.3" "(A)" HomotopyCategory.instIsTriangulatedIntUpPlus
add_to_sga "4½ Etat_0 1.2.3" "(A)" HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic
add_to_sga "4½ Etat_0 1.2.3" HomotopyCategory.plus
add_to_sga "4½ Etat_0 1.2.3" HomotopyCategory.subcategoryAcyclic
add_to_sga "4½ Etat_0 1.2.4" CochainComplex.trianglehOfDegreewiseSplit_distinguished
add_to_sga "4½ Etat_0 1.3" CategoryTheory.Functor.IsHomological
add_to_sga "4½ Etat_0 1.3" "partial" CategoryTheory.Functor.homologySequence_exact₁
add_to_sga "4½ Etat_0 1.3" "partial" CategoryTheory.Functor.homologySequence_exact₃
add_to_sga "4½ Etat_0 1.3" CategoryTheory.Functor.shift
add_to_sga "4½ Etat_0 1.3.2" "more general"
  CategoryTheory.Pretriangulated.instIsHomologicalAddCommGrpCatObjOppositeFunctorPreadditiveCoyoneda
add_to_sga "4½ Etat_0 1.3.2" "more general"
  CategoryTheory.Pretriangulated.instIsHomologicalOppositeAddCommGrpCatObjFunctorPreadditiveYoneda
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.homologyMap'_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.homologyMap_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.leftHomologyMap_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.rightHomologyMap'_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" "Clause of Example 3.2(2)"
  CategoryTheory.ShortComplex.rightHomologyMap_nullHomotopic
add_to_sga "4½ Etat_0 1.3.2" HomologicalComplex.homologyFunctor
add_to_sga "4½ Etat_0 1.3.2" "partial" Homotopy.homologyMap_eq
add_to_sga "4½ Etat_0 1.3.2" HomotopyCategory.homologyFunctor
add_to_sga "4½ Etat_0 1.3.3" "partial" CategoryTheory.Functor.Additive
add_to_sga "4½ Etat_0 1.3.3" "double complex P(X"
  CategoryTheory.Functor.mapBifunctorHomologicalComplexObj
add_to_sga "4½ Etat_0 1.3.3" CategoryTheory.Functor.map₂HomologicalComplex
add_to_sga "4½ Etat_0 1.3.3" "special case" CategoryTheory.MonoidalPreadditive
add_to_sga "4½ Etat_0 1.3.3" "Object part of Hom•(X" CochainComplex.HomComplex
add_to_sga "4½ Etat_0 1.3.3" CochainComplex.mapBifunctor
add_to_sga "4½ Etat_0 1.3.3" "more general" HomologicalComplex.mapBifunctor
add_to_sga "4½ Etat_0 2.2" CategoryTheory.Functor.kernel
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.Functor.IsLocalization
add_to_sga "4½ Etat_0 2.3.1" "partial" CategoryTheory.Localization.Construction.uniq
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.Localization.StrictUniversalPropertyFixedTarget
add_to_sga "4½ Etat_0 2.3.1"
  CategoryTheory.Localization.instInhabitedStrictUniversalPropertyFixedTargetLocalizationQ
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.HasLocalization.standard
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.HasRightCalculusOfFractions
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.LeftFraction.Localization.Q
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.inverts
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.StrictUniversalPropertyFixedTarget.uniq
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocalizationQ
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.Q
add_to_sga "4½ Etat_0 2.3.1" "partial" CategoryTheory.MorphismProperty.Q_inverts
add_to_sga "4½ Etat_0 2.3.1" CategoryTheory.MorphismProperty.instCategoryLocalization
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsOppositeOpOfHasRightCalculusOfFractions
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.instHasLeftCalculusOfFractionsUnopOfHasRightCalculusOfFractionsOpposite
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.instHasRightCalculusOfFractionsOppositeOpOfHasLeftCalculusOfFractions
add_to_sga "4½ Etat_0 2.3.1" "partial"
  CategoryTheory.MorphismProperty.instHasRightCalculusOfFractionsUnopOfHasLeftCalculusOfFractionsOpposite
add_to_sga "4½ Etat_0 2.3.1" "special case"
  CategoryTheory.ObjectProperty.instHasLeftCalculusOfFractionsTrWOfIsTriangulatedOfIsTriangulated
add_to_sga "4½ Etat_0 2.3.1" "special case"
  CategoryTheory.ObjectProperty.instHasRightCalculusOfFractionsTrWOfIsTriangulatedOfIsTriangulated
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.HasShift.localization
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.HasShift.localization'
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.HasShift.localized
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.Construction.fac
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.Construction.objEquiv
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.Construction.uniq
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.exists_rightFraction
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.functor_additive_iff
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.instPreadditiveLocalization
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.instPreadditiveLocalization'
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Localization.preadditive
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ
add_to_sga "4½ Etat_0 2.3.2" CategoryTheory.MorphismProperty.LeftFraction.rightFraction
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.MorphismProperty.LeftFraction.rightFraction_fac
add_to_sga "4½ Etat_0 2.3.2" CategoryTheory.MorphismProperty.RightFraction
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization'
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization
add_to_sga "4½ Etat_0 2.3.2" "partial"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization'
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Triangulated.Localization.isTriangulated
add_to_sga "4½ Etat_0 2.3.2" "partial" CategoryTheory.Triangulated.Localization.pretriangulated
add_to_sga "4½ Etat_0 2.3.2" "D(A) is triangulated" DerivedCategory.instIsTriangulated
add_to_sga "4½ Etat_0 2.3.2" "special case"
  DerivedCategory.instIsTriangulatedHomotopyCategoryIntUpQh
add_to_sga "4½ Etat_0 2.3.2" "special case" DerivedCategory.instPretriangulated
add_to_sga "4½ Etat_0 2.4.1" CategoryTheory.Functor.homologicalKernel
add_to_sga "4½ Etat_0 2.4.1" "partial" CategoryTheory.Functor.instIsTriangulatedHomologicalKernel
add_to_sga "4½ Etat_0 2.4.1" "equality S_H = φ(B_H)"
  CategoryTheory.Functor.mem_homologicalKernel_trW_iff
add_to_sga "4½ Etat_0 2.4.1" "special case" HomotopyCategory.subcategoryAcyclic
add_to_sga "4½ Etat_0 2.4.2" "(a)"
  CategoryTheory.ObjectProperty.instIsTriangulatedMinOfIsClosedUnderIsomorphisms
add_to_sga "4½ Etat_0 2.4.2" "(a)"
  CategoryTheory.ObjectProperty.instIsTriangulatedMinOfIsClosedUnderIsomorphisms_1
add_to_sga "4½ Etat_0 2.5.4" CategoryTheory.ObjectProperty.leftOrthogonal
add_to_sga "4½ Etat_0 2.5.4" CategoryTheory.ObjectProperty.rightOrthogonal
add_to_sga "4½ Etat_0 2.6.1" CategoryTheory.ObjectProperty.leftOrthogonal
add_to_sga "4½ Etat_0 2.6.1" CategoryTheory.ObjectProperty.rightOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instContainsZeroLeftOrthogonalOfHasZeroObject
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instContainsZeroRightOrthogonalOfHasZeroObject
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsLeftOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsRightOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsStableUnderShiftLeftOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsStableUnderShiftRightOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsTriangulatedClosed₂LeftOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsTriangulatedClosed₂RightOrthogonal
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsTriangulatedLeftOrthogonalOfIsStableUnderShiftInt
add_to_sga "4½ Etat_0 2.6.2" "partial"
  CategoryTheory.ObjectProperty.instIsTriangulatedRightOrthogonalOfIsStableUnderShiftInt
add_to_sga "4½ Etat_0 2.6.2" CategoryTheory.ObjectProperty.leftOrthogonal
add_to_sga "4½ Etat_0 2.6.2" CategoryTheory.ObjectProperty.rightOrthogonal
add_to_sga "4½ Etat_0 2.6.4" CategoryTheory.CostructuredArrow
add_to_sga "4½ Etat_0 2.6.4" CategoryTheory.StructuredArrow
add_to_sga "4½ Etat_0 2.6.7" "more general" CategoryTheory.Adjunction.IsTriangulated.mk'
add_to_sga "4½ Etat_0 2.6.7" "more general" CategoryTheory.Adjunction.IsTriangulated.mk''
add_to_sga "4½ Etat_0 2.6.7" "more general" CategoryTheory.Adjunction.isTriangulated_leftAdjoint
add_to_sga "4½ Etat_0 3.1.1" "(A)" DerivedCategory.Plus.Qh
add_to_sga "4½ Etat_0 3.1.1" DerivedCategory.Plus.instIsLocalizationPlusQhQuasiIso
add_to_sga "4½ Etat_0 3.1.1" DerivedCategory.Plus.instIsLocalizationPlusQhTrWSubcategoryAcyclic
add_to_sga "4½ Etat_0 3.1.1" "partial" DerivedCategory.Qh
add_to_sga "4½ Etat_0 3.1.1" "partial" HasDerivedCategory.standard
add_to_sga "4½ Etat_0 3.1.2" DerivedCategory.Bounded.ι
add_to_sga "4½ Etat_0 3.1.2" DerivedCategory.Minus.ι
add_to_sga "4½ Etat_0 3.1.2" DerivedCategory.Plus.ι
add_to_sga "4½ Etat_0 3.1.3" DerivedCategory.Qh
add_to_sga "4½ Etat_0 3.1.3" HasDerivedCategory.standard
add_to_sga "4½ Etat_0 3.1.3" instCategoryDerivedCategory
add_to_sga "4½ Etat_0 3.1.4" "(A)" DerivedCategory.Plus.exists_injective_nonempty_iso
add_to_sga "4½ Etat_0 3.1.4" "(A)"
  HomotopyCategory.Plus.instEssSurjInjectiveObjectPlusCompMapHomotopyCategoryPlusιQh
add_to_sga "4½ Etat_0 3.1.5" "Object part of Π" DerivedCategory.triangleOfSES
add_to_sga "4½ Etat_0 3.1.5" "partial" DerivedCategory.triangleOfSES_distinguished
add_to_sga "4½ Etat_0 3.1.6" "partial" DerivedCategory.homologyFunctorFactors
add_to_sga "4½ Etat_0 3.1.6" "partial" DerivedCategory.homologyFunctorFactorsh
add_to_sga "4½ Etat_0 3.1.6" DerivedCategory.isIso_iff
add_to_sga "4½ Etat_0 3.1.7" HomologicalComplex.quasiIso
add_to_sga "4½ Etat_0 3.1.7" "(A), special case" HomotopyCategory.Plus.quasiIso
add_to_sga "4½ Etat_0 3.1.7" HomotopyCategory.quasiIso
add_to_sga "4½ Etat_0 3.1.7" QuasiIso
add_to_sga "4½ Etat_0 3.1.8" "special case" CategoryTheory.InjectiveResolution
add_to_sga "4½ Etat_0 3.1.8" "more general" CategoryTheory.LocalizerMorphism.LeftResolution
add_to_sga "4½ Etat_0 3.1.8" "more general" CategoryTheory.LocalizerMorphism.RightResolution
add_to_sga "4½ Etat_0 3.1.8" "special case" CategoryTheory.ProjectiveResolution
add_to_sga "4½ Etat_0 3.1.9" "Part 1, special case"
  CategoryTheory.InjectiveResolution.instHasInjectiveResolution
add_to_sga "4½ Etat_0 3.1.9" "Part 1, special case"
  CategoryTheory.ProjectiveResolution.instHasProjectiveResolution
add_to_sga "4½ Etat_0 3.1.9" "Part 1, special case"
  CategoryTheory.ProjectiveResolution.instHasProjectiveResolutions
add_to_sga "4½ Etat_0 3.1.9" "Part 1, special case" CochainComplex.Plus.exists_quasiIso_injective
add_to_sga "4½ Etat_0 3.2" DerivedCategory.Q
add_to_sga "4½ Etat_0 3.2" DerivedCategory.Qh
add_to_sga "4½ Etat_0 3.2.1" "special case" CategoryTheory.Abelian.Ext
add_to_sga "4½ Etat_0 3.2.1" "special case" CategoryTheory.Abelian.extFunctor
add_to_sga "4½ Etat_0 3.2.2" "special case" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "4½ Etat_0 3.2.2" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
add_to_sga "4½ Etat_0 3.2.2" "Exactness at Ext^n(X"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_sga "4½ Etat_0 3.2.2" "special case" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "4½ Etat_0 3.2.2" "Exactness at Ext^{n+1}(V"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_sga "4½ Etat_0 3.2.3" "Part 4, special case"
  CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass
add_to_sga "4½ Etat_0 3.2.3" "Part 4, special case" CategoryTheory.InjectiveResolution.homotopyEquiv
add_to_sga "4½ Etat_0 3.2.3" "Part 4, special case"
  CategoryTheory.InjectiveResolution.instHasInjectiveResolution
add_to_sga "4½ Etat_0 3.2.3" "Part 4, special case"
  CategoryTheory.InjectiveResolution.instHasInjectiveResolutions
add_to_sga "4½ Etat_0 3.2.3" "Part 4, special case" CategoryTheory.InjectiveResolution.iso
add_to_sga "4½ Etat_0 3.2.3" "special case"
  CategoryTheory.ProjectiveResolution.instHasProjectiveResolution
add_to_sga "4½ Etat_0 3.2.3" "special case"
  CategoryTheory.ProjectiveResolution.instHasProjectiveResolutions
add_to_sga "4½ Etat_0 3.2.3" "special case" CategoryTheory.ProjectiveResolution.iso
add_to_sga "4½ Etat_0 4.1.1" CategoryTheory.NatTrans.CommShift
add_to_sga "4½ Etat_0 4.1.4" "more general" CategoryTheory.Functor.partialLeftAdjointObj
add_to_sga "4½ Etat_0 4.1.5" "special case" CategoryTheory.Functor.leftDerived
add_to_sga "4½ Etat_0 4.1.6" "partial"
  HomotopyCategory.Plus.instIsIsoAppOfInjectiveXIntAsHomologicalComplexUpHomotopicObjPlus
add_to_sga "4½ Etat_0 4.2.3" "clause a), special case"
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
add_to_sga "4½ Etat_0 4.2.3" "(A), special case" HomotopyCategory.Plus.subcategoryAcyclic
add_to_sga "4½ Etat_0 4.2.3" "partial" HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic
add_to_sga "4½ Etat_0 4.2.3" "N in the case C = K(A)" HomotopyCategory.subcategoryAcyclic
add_to_sga "4½ Etat_0 4.2.3.1" "Corollary 1" CochainComplex.Plus.exists_quasiIso_injective
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.bilinearComp
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.bilinearCompOfLinear
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.comp
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.postcomp
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.precomp
add_to_sga "4½ Etat_0 4.3" "special case" CategoryTheory.Abelian.Ext.precompOfLinear
add_to_sga "4½ Etat_0 4.3" "partial, special case" CategoryTheory.Abelian.extFunctorObj
add_to_sga "4½ Etat_0 6.2" "special case" AddCommGrpCat.enoughInjectives
add_to_sga "4½ Etat_0 6.2" "special case" CommGrpCat.enoughInjectives
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat.iff_lTensor_exact'
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat.iff_lTensor_preserves_shortComplex_exact
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat.iff_rTensor_exact
add_to_sga "4½ Etat_0 6.2" "special case" Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_sga "4½ Etat_0 6.2" "special case" ModuleCat.enoughInjectives
add_to_sga "4½ Etat_0 6.2" "special case" instEnoughInjectivesModuleCatInt
add_to_sga "4½ Etat_0 6.2" "special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "4½ Etat_0 Problem1" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization
add_to_sga "4½ Etat_0 Problem1" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization'
add_to_sga "4½ Etat_0 Problem1"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization
add_to_sga "4½ Etat_0 Problem1"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization'
add_to_sga "4½ Etat_0 Problem2" "partial" CategoryTheory.Localization.Construction.uniq
add_to_sga "4½ Etat_0 Problem2" "partial"
  CategoryTheory.Localization.instInhabitedStrictUniversalPropertyFixedTargetLocalizationQ
add_to_sga "4½ Etat_0 Problem2" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization
add_to_sga "4½ Etat_0 Problem2" "partial"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization'
add_to_sga "4½ Etat_0 Problem2"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization
add_to_sga "4½ Etat_0 Problem2"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization'
add_to_sga "4½ Etat_0 Problem2" "partial" CategoryTheory.Triangulated.Localization.isTriangulated
add_to_sga "4½ Fonctions_L 1.7.2" "partial" CochainComplex.shiftFunctorObjXIso
add_to_sga "4½ Fonctions_L 1.14" "special case" LinearEquiv.det
add_to_sga "4½ Fonctions_L 1.14" "special case" LinearEquiv.isUnit_det'
add_to_sga "4½ Fonctions_L 1.14" "special case" LinearMap.isUnit_det
add_to_sga "4½ Fonctions_L 1.14" "special case" LinearMap.isUnit_iff_isUnit_det
add_to_sga "4½ Fonctions_L 3.8" LinearMap
add_to_sga "4½ Fonctions_L 3.8" LinearMap.baseChange
add_to_sga "4½ Fonctions_L 3.8" LinearMap.fixedSubmodule
add_to_sga "4½ Fonctions_L 3.8" LinearMap.trace
add_to_sga "4½ Fonctions_L 3.8" "equality Tr(F" LinearMap.trace_baseChange
add_to_sga "4½ Fonctions_L 3.8" TensorProduct
add_to_sga "4½ Fonctions_L 4.5" DualNumber
add_to_sga "4½ Fonctions_L 4.5" MonoidAlgebra
add_to_sga "4½ Fonctions_L 4.5" "Y₀ is an elliptic curve" WeierstrassCurve.instIsEllipticOfJ
add_to_sga "4½ Fonctions_L 4.5" "Y₀ is an elliptic curve"
  WeierstrassCurve.instIsEllipticOfJ0OfFactIsUnitOfNat
add_to_sga "4½ Fonctions_L 4.5" "partial" WeierstrassCurve.ofJ
add_to_sga "4½ Rapport 1.1" AlgebraicClosure
add_to_sga "4½ Rapport 1.1" "special case" FiniteField.Extension.frob
add_to_sga "4½ Rapport 1.1" "special case" FiniteField.Extension.frob_apply
add_to_sga "4½ Rapport 1.1" "Spec L case: F^*x = x^q" FiniteField.coe_frobeniusAlgEquivOfAlgebraic
add_to_sga "4½ Rapport 1.1" "affine case" FiniteField.coe_frobeniusAlgHom
add_to_sga "4½ Rapport 1.1" "perfect affine case" FiniteField.frobeniusAlgEquiv
add_to_sga "4½ Rapport 1.1" "special case" FiniteField.frobeniusAlgEquivOfAlgebraic
add_to_sga "4½ Rapport 1.1" "Spec L case: F^*x = x^q" FiniteField.frobeniusAlgEquivOfAlgebraic_apply
add_to_sga "4½ Rapport 1.1" "perfect affine case" FiniteField.frobeniusAlgEquiv_apply
add_to_sga "4½ Rapport 1.1" "affine case" FiniteField.frobeniusAlgHom
add_to_sga "4½ Rapport 1.1" "affine case" FiniteField.frobeniusAlgHom_apply
add_to_sga "4½ Rapport 1.1" "special case" Subfield.mem_bot_iff_pow_eq_self
add_to_sga "4½ Rapport 1.1" "affine case" frobenius
add_to_sga "4½ Rapport 1.1" "special case" frobenius_def
add_to_sga "4½ Rapport 1.3" "special case" RingHom.frobenius_comm
add_to_sga "4½ Rapport 1.3" "special case" RingHom.iterateFrobenius_comm
add_to_sga "4½ Rapport 1.3" "special case" RingHom.map_frobenius
add_to_sga "4½ Rapport 1.6" "more general" AlgebraicGeometry.Scheme.Hom.residueDegree
add_to_sga "4½ Rapport 1.6" closedPoints
add_to_sga "4½ Rapport 2.9" "more general"
  CategoryTheory.ObjectProperty.SerreClassLocalization.abelian
add_to_sga "4½ Rapport 4.1" "partial" CategoryTheory.Functor.HasLeftDerivedFunctor
add_to_sga "4½ Rapport 4.1" "partial" CategoryTheory.Functor.HasRightDerivedFunctor
add_to_sga "4½ Rapport 4.1" CategoryTheory.Functor.IsRightDerivedFunctor
add_to_sga "4½ Rapport 4.1" CategoryTheory.Functor.rightDerivedFunctorPlus
add_to_sga "4½ Rapport 4.1" HasDerivedCategory.standard
add_to_sga "4½ Rapport 4.1" "partial" MulOpposite
add_to_sga "4½ Rapport 4.1" MulOpposite.instRing
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.traceAux
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_comp_comm
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_comp_comm'
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_comp_cycle
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_comp_cycle'
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_eq_matrix_trace
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_eq_matrix_trace_of_finset
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_mul_comm
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_mul_cycle
add_to_sga "4½ Rapport 4.2" "special case" LinearMap.trace_mul_cycle'
add_to_sga "4½ Rapport 4.2" "special case" Matrix.trace
add_to_sga "4½ Rapport 4.2" "special case" Matrix.traceLinearMap
add_to_sga "4½ Rapport 4.2" "special case" Matrix.trace_mul_comm
add_to_sga "4½ Rapport 4.2" "special case" Matrix.trace_mul_cycle
add_to_sga "4½ Rapport 4.2" "special case" Matrix.trace_mul_cycle'
add_to_sga "4½ Rapport 4.2" "special case" Matrix.trace_toLin'_eq
add_to_sga "4½ Rapport 4.3" "partial" instCategoryHomotopyCategory
add_to_sga "4½ Rapport 4.11" FiniteDimensional
add_to_sga "4½ Rapport 4.11" Module.Finite
add_to_sga "4½ Rapport 5.7" Representation.tprod
add_to_sga "4½ Rapport 5.9" AddSubmonoid.comap
add_to_sga "4½ Rapport 5.9" "more general" Submonoid.comap
add_to_sga "4½ Rapport 5.10" Rep.coinvariantsFunctor
add_to_sga "4½ Rapport 5.10" "special case" Rep.quotientToCoinvariants
add_to_sga "4½ Rapport 5.10" "special case" Rep.quotientToCoinvariantsFunctor
add_to_sga "4½ Rapport 5.10" "special case" Rep.toCoinvariants
add_to_sga "4½ Rapport 5.10" "special case" Rep.toCoinvariantsMkQ
add_to_sga "4½ Rapport 5.10" Representation.Coinvariants
add_to_sga "4½ Rapport 5.10" Representation.Coinvariants.instModule
add_to_sga "4½ Rapport 5.10" Representation.Coinvariants.mk
add_to_sga "4½ Rapport 5.10" "special case"
  Representation.instIsTrivialSubtypeMemSubgroupCoinvariantsCompLinearMapIdSubtypeToCoinvariants
add_to_sga "4½ Rapport 5.10" "special case" Representation.quotientToCoinvariants
add_to_sga "4½ Rapport 5.10" "special case" Representation.toCoinvariantsMkQ
add_to_sga "4½ Rapport 5.10" "special case" Representation.toCoinvariants_mk
add_to_sga "4½ Sommes_trig 1.6" "G_0 = G_m" Algebra.algebraMap_intNorm_of_isGalois
add_to_sga "4½ Sommes_trig 1.6" "G_0 = G_m" Algebra.norm_eq_prod_automorphisms
add_to_sga "4½ Sommes_trig 1.6" "G_0 = G_m" FiniteField.algebraMap_norm_eq_pow_sum
add_to_sga "4½ Sommes_trig 1.6" "G_0 = G_m" FiniteField.algebraMap_norm_eq_prod_pow
add_to_sga "4½ Sommes_trig 1.6" "G_0 = G_m" groupCohomology.norm_ofAlgebraAutOnUnits_eq
add_to_sga "4½ Sommes_trig 2.1" "binary sums" IsIntegral.add
add_to_sga "4½ Sommes_trig 2.1" "more general" IsIntegral.multiset_sum
add_to_sga "4½ Sommes_trig 2.1" "more general" IsIntegral.sum
add_to_sga "4½ Sommes_trig 2.1" "binary sums" RingHom.IsIntegralElem.add
add_to_sga "4½ Sommes_trig 2.3" "special case" BoxIntegral.Prepartition.sum_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "special case" ENNReal.tsum_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "Counting measure" Finset.card_eq_sum_card_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "Counting measure" Finset.card_preimage_eq_sum_card_image_eq
add_to_sga "4½ Sommes_trig 2.3" "special case" Finset.dens_eq_sum_dens_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "Counting measure" Finset.sum_card_fiberwise_eq_card_filter
add_to_sga "4½ Sommes_trig 2.3" Finset.sum_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "special case" Finset.sum_fiberwise'
add_to_sga "4½ Sommes_trig 2.3" "more general" Finset.sum_fiberwise_eq_sum_filter
add_to_sga "4½ Sommes_trig 2.3" "special case" Finset.sum_fiberwise_eq_sum_filter'
add_to_sga "4½ Sommes_trig 2.3" Finset.sum_fiberwise_of_maps_to
add_to_sga "4½ Sommes_trig 2.3" "special case" Finset.sum_fiberwise_of_maps_to'
add_to_sga "4½ Sommes_trig 2.3" "special case" Finset.sum_image'
add_to_sga "4½ Sommes_trig 2.3" Fintype.sum_fiberwise
add_to_sga "4½ Sommes_trig 2.3" "special case" Fintype.sum_fiberwise'
add_to_sga "4½ Sommes_trig 2.3" "special case" HasSum.tsum_fiberwise
add_to_sga "4½ Sommes_trig 2.4" "special case" Finset.prod_add
add_to_sga "4½ Sommes_trig 2.4" "special case" Finset.prod_add_one
add_to_sga "4½ Sommes_trig 2.4" "special case" Finset.prod_one_add
add_to_sga "4½ Sommes_trig 2.4" "more general" Finset.prod_sum
add_to_sga "4½ Sommes_trig 2.4" "more general" Finset.prod_univ_sum
add_to_sga "4½ Sommes_trig 2.4" "special case" Finset.sum_prod_piFinset
add_to_sga "4½ Sommes_trig 2.4" "special case" Fintype.prod_add
add_to_sga "4½ Sommes_trig 2.4" "more general" Fintype.prod_sum
add_to_sga "4½ Sommes_trig 2.5" "Counting: ε constantly 1" Finset.card_add_card_compl
add_to_sga "4½ Sommes_trig 2.5" "Counting: ε constantly 1" Finset.card_compl
add_to_sga "4½ Sommes_trig 2.5" "Counting: ε constantly 1" Finset.card_compl_add_card
add_to_sga "4½ Sommes_trig 2.5" "Counting: ε constantly 1" Finset.card_sdiff_add_card_eq_card
add_to_sga "4½ Sommes_trig 2.5" Finset.sum_add_sum_compl
add_to_sga "4½ Sommes_trig 2.5" Finset.sum_compl_add_sum
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Finset.sum_eq_add_sum_sdiff_singleton
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Finset.sum_eq_add_sum_sdiff_singleton_of_mem
add_to_sga "4½ Sommes_trig 2.5" "more general" Finset.sum_eq_sum_range_sdiff
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Finset.sum_eq_sum_sdiff_singleton_add
add_to_sga "4½ Sommes_trig 2.5" "more general" Finset.sum_inter_add_sum_sdiff
add_to_sga "4½ Sommes_trig 2.5" Finset.sum_sdiff
add_to_sga "4½ Sommes_trig 2.5" "special case" Finset.sum_sdiff_eq_sub
add_to_sga "4½ Sommes_trig 2.5" "special case" Finset.sum_sdiff_sub_sum_sdiff
add_to_sga "4½ Sommes_trig 2.5" "more general" Finset.sum_union
add_to_sga "4½ Sommes_trig 2.5" "special case" Finset.weightedVSub_sdiff
add_to_sga "4½ Sommes_trig 2.5" "Counting: ε constantly 1" Fintype.card_compl_set
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Fintype.sum_eq_add_sum_compl
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Fintype.sum_eq_add_sum_subtype_ne
add_to_sga "4½ Sommes_trig 2.5" "B is a singleton" Fintype.sum_eq_sum_compl_add
add_to_sga "4½ Sommes_trig 2.5" IsCompl.sum_add_sum
add_to_sga "4½ Sommes_trig 2.5" "special case" Summable.sum_add_tsum_subtype_compl
add_to_sga "4½ Sommes_trig 2.5" "special case" Summable.tsum_subtype_add_tsum_subtype_compl
add_to_sga "4½ Sommes_trig 2.5" finsum_mem_add_sdiff
add_to_sga "4½ Sommes_trig 2.6" "constant weight 1" Finset.inclusion_exclusion_card_biUnion
add_to_sga "4½ Sommes_trig 2.6" "constant weight 1" Finset.inclusion_exclusion_card_inf_compl
add_to_sga "4½ Sommes_trig 2.6" "more general" Finset.inclusion_exclusion_sum_biUnion
add_to_sga "4½ Sommes_trig 2.6" "more general" Finset.inclusion_exclusion_sum_inf_compl
add_to_sga "4½ Sommes_trig 2.6" Set.iInter
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.expect_eq_zero_iff_ne_zero
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.expect_ne_zero_iff_eq_zero
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.sum_eq_ite
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.sum_eq_zero_iff_ne_zero
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.sum_eq_zero_of_ne_one
add_to_sga "4½ Sommes_trig 2.7" "special case" AddChar.sum_mulShift
add_to_sga "4½ Sommes_trig 2.7" "more general" AddChar.sum_ne_zero_iff_eq_zero
add_to_sga "4½ Sommes_trig 2.7" "special case" FiniteField.sum_subgroup_units_eq_zero
add_to_sga "4½ Sommes_trig 2.7" "more general" MulChar.sum_eq_zero_of_ne_one
add_to_sga "4½ Sommes_trig 2.7" "(2.7.1)" gaussSum_one_left
add_to_sga "4½ Sommes_trig 2.7" "(2.7.1)" gaussSum_one_right
add_to_sga "4½ Sommes_trig 2.7" "more general" sum_hom_units_eq_zero
add_to_sga "4½ Sommes_trig 2.7" "partial" sum_translate
add_to_sga "4½ Sommes_trig 3.2" "more general" GradedObject.eulerChar
add_to_sga "4½ Sommes_trig 3.2" "more general" HomologicalComplex.homologyEulerChar
add_to_sga "4½ Sommes_trig 3.8" "special case" AddChar.zmodChar
add_to_sga "4½ Sommes_trig 3.8" "special case" ZMod.stdAddChar
add_to_sga "4½ Sommes_trig 3.8" "special case" ZMod.toCircle
add_to_sga "4½ Sommes_trig 4.4" "more general" gaussSum_mul_gaussSum_eq_card
add_to_sga "4½ Sommes_trig 4.5" "partial" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "4½ Sommes_trig 4.5" "partial" Algebra.FormallyEtale.iff_exists_algEquiv_prod
add_to_sga "4½ Sommes_trig 4.6" "special case" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_sga "4½ Sommes_trig 4.6" "partial" Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
add_to_sga "4½ Sommes_trig 4.6" "special case"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_sga "4½ Sommes_trig 4.6" "partial" Algebra.norm_eq_prod_embeddings
add_to_sga "4½ Sommes_trig 4.12" "Final clause of 4.12" Equiv.Perm.sign_of_cycleType
add_to_sga "4½ Sommes_trig 4.12" "Final clause of 4.12" Equiv.Perm.sign_of_cycleType'
add_to_sga "4½ Sommes_trig 4.12" "Final clause of 4.12" Fin.sign_cycleRange
add_to_sga "4½ Sommes_trig 4.15" "special case" gaussSum_mul_gaussSum_pow_orderOf_sub_one
add_to_sga "4½ Sommes_trig 4.15" "special case" gaussSum_sq
add_to_sga "4½ Sommes_trig 6.1" "partial" Algebra.Etale.iff_exists_algEquiv_prod
add_to_sga "4½ Sommes_trig 6.7" "more general" FiniteField.sum_pow_lt_card_sub_one
add_to_sga "4½ Sommes_trig 6.7" "more general" FiniteField.sum_subgroup_pow_eq_zero
add_to_sga "4½ Sommes_trig 6.7" "more general" MulChar.sum_eq_zero_of_ne_one
add_to_sga "4½ Sommes_trig 6.7" "(x)" Perfection.mk_teichmuller
add_to_sga "4½ Sommes_trig 6.7" "more general" Perfection.teichmuller
add_to_sga "4½ Sommes_trig 6.7" "more general" WittVector.teichmuller
add_to_sga "4½ Sommes_trig 6.7" "partial" gaussSum
add_to_sga "4½ Sommes_trig 6.8" CyclotomicField
add_to_sga "4½ Sommes_trig 6.8" Int.fract
add_to_sga "4½ Sommes_trig 6.8" IsCyclotomicExtension.Rat.galEquivZMod
add_to_sga "4½ Sommes_trig 6.8" "partial" IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
add_to_sga "4½ Sommes_trig 6.8" "partial" IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq
add_to_sga "4½ Sommes_trig 6.8" IsCyclotomicExtension.autEquivPow
add_to_sga "4½ Sommes_trig 6.8" IsCyclotomicExtension.fromZetaAut
add_to_sga "4½ Sommes_trig 6.8" "partial" IsCyclotomicExtension.fromZetaAut_spec
add_to_sga "4½ Sommes_trig 6.8" galCyclotomicEquivUnitsZMod
add_to_sga "4½ Sommes_trig 6.8" galXPowEquivUnitsZMod
add_to_sga "4½ Sommes_trig 7.13" "partial" AlgebraicGeometry.AffineSpace.coord
add_to_sga "4½ Sommes_trig 7.17" "more general" AddChar.FiniteField.primitiveChar
add_to_sga "4½ Th_finitude 2.1" "special case" Module.injective_of_isSemisimpleRing
add_to_sga "4½ Th_finitude 2.7" "special case"
  AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
add_to_sga "4½ Th_finitude 3.1" IsGenericPoint
add_to_sga "4½ Th_finitude 3.1" IsIrreducible.genericPoint
add_to_sga "4½ Th_finitude 3.1" SeparableClosure
add_to_sga "4½ Th_finitude 3.1" genericPoint
add_to_sga "4½ Th_finitude 3.1" genericPoints.ofComponent
