module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoreticCoherent
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.FiniteFibres
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Unconditional

/-!
# Further results on `Basic`

Results about the objects of `StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic` that need
imports beyond those of that module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Reduction

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

end Reduction

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
