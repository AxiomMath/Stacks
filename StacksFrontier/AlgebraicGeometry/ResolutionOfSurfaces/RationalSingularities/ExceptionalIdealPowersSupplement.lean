module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.IdealSheafQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Generators.KernelTensorInvertible
public import StacksFrontier.Topology.Sheaves.Modules.Generators.TensorGloballyGenerated
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.QuasicoherentCohomologyExtra
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra

/-!
# Setup for further results on the powers of the ideal sheaf of the special fibre

This file contains no declarations. It imports
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowers`
together with further dependencies, and opens the namespace
`AlgebraicGeometry.RationalSingularitySituation` with a variable
`S : RationalSingularitySituation`, as a place for results about the objects of that module that
need imports beyond its own.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}}

namespace RationalSingularitySituation

open Stacks.Cohomology.AffineBase

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : RationalSingularitySituation.{u})

end RationalSingularitySituation

end

end AlgebraicGeometry

end
