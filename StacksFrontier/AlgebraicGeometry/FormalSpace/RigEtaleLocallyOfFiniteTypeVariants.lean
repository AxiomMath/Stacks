module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteType

/-!
# Variants of the results on rig-étale morphisms of formal algebraic spaces

The declarations below extend those of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteType`. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `isCountablyIndexed_of_isNoetherian'`
* `isLocallyCountablyIndexed_of_isLocallyNoetherian'`
* `isLocallyOfFiniteType_of_isRigEtale'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- **A Noetherian affine formal algebraic space over `S` is countably indexed**, the affine
implication of the list of **Stacks 0AKY**. A Noetherian affine formal algebraic space is
adic\* by the implication (1) ⇒ (3) of Stacks 0AKM, and the powers of an ideal of definition
of an adic ring are a countable fundamental system of open ideals.

Untagged: Stacks 0AKY is a list of definitions, whose covering set is the five predicates of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Types.lean`; this is the implication between two of
them that the source records in passing. -/
theorem isCountablyIndexed_of_isNoetherian' {U : FppfSheaf B S hS}
    (hU : IsNoetherian B S hS U) : IsCountablyIndexed B S hS U :=
  isCountablyIndexedOfIsAdicStar' B S hS U
    (isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS hU).1

end AlgebraicGeometry.FormalSpace

end
