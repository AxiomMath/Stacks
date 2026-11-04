module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationVariants

/-!
# Variants of the adic finite-type characterization

This module declares nothing of its own: it combines
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization` with
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationVariants`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

end AlgebraicGeometry.FormalSpace

end
