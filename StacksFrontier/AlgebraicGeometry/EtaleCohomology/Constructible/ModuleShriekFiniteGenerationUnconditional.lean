module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafGenerationByQCQS
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ModuleCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# ModuleShriekFiniteGenerationUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration`, stated
as separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CoproductsFromFiniteFiltered
open Opposite

universe u r

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local implicit_reducible] CoproductsFromFiniteFiltered.liftToFinsetObj
  CoproductsFromFiniteFiltered.finiteSubcoproductsCocone

namespace AlgebraicGeometry

section GeneralRing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

attribute [local instance] smallEtaleHasColimitsOfSizeModuleMax
  SmallEtale.isRightAdjointPushforward_moduleCat SmallEtale.hasWeakSheafifyOver_moduleCat

attribute [local instance 2000] wEqualsLocallyBijectiveModuleMax

attribute [local instance] hasProductsModuleMax hasLimitsOfSizeModuleMax

variable [IsNoetherianRing Λ]

variable [CompactSpace X.1] [QuasiSeparatedSpace X.1]

attribute [local instance] smallEtaleHasSheafifyModuleMax

end GeneralRing

section SelfRing

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ] [CompactSpace X.1] [QuasiSeparatedSpace X.1]

attribute [local instance] smallEtaleHasSheafifyModuleMax

end SelfRing


end AlgebraicGeometry

end
