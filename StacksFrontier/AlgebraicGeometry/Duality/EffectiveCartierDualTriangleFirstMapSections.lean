module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleFirstMapCochain
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportCochainCoreSections

/-!
# The remaining obligation of Tag 0B4B as one identity of sections

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDualTriangleFirstMapCochain.lean` reduces
the isomorphism assertion of [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) to the
cochain-level identity `Stacks.Divisors.DualTriangleFirstMapCochainCore`.

**This file reduces that identity to one identity of sections of sheaves**, through
`…ClosedQuotientMorphismOfRingedSpaces.cochainCore_of_sectionsCore`: nothing about cochain
complexes, and nothing about the adjunction of [Stacks, Tag 0A75] lifted to complexes, is left in
the hypothesis.  What remains is the underived core
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_comp_unitIso_comp_counit`, which
is proved, read on sections with both trivialisations of `ℰom(𝒪, -)` spelled as evaluation at the
unit section.

## Main results

* `Stacks.Divisors.dualTriangleFirstMapCochainCore_of_sectionsCore`: **the identity of sections
  gives `Stacks.Divisors.DualTriangleFirstMapCochainCore`.**
* `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_sectionsCore`: **the
  identity of sections gives the isomorphism assertion of [Stacks, Tag 0B4B]**, through
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore`.

## Implementation notes

The only divisor-specific input is that the degree-zero component of
`Stacks.Divisors.pushforwardStructureSheafUnitCochain` is the unit
`RingedSpaceModuleAdjunction.structureSheafModuleHom` of the closed immersion, and that holds by
`rfl`: the second morphism of the ideal sequence of [Stacks, Tag 0C6K] is
`Stacks.IdealSheafSequence.divisorQuotientMap`, which is
`SheafOfModules.unitToPushforwardObjUnit` of the structure-sheaf map, and so is the generic unit;
the comparison of the degree-zero single functor with pushforward contributes the identity in
degree zero.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (derivedSheafHom ringedSite StructureSheafModules)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

omit [IsEffectiveCartierDivisor D] in
/-- **The degree-zero component of the unit as a morphism of complexes is the unit.** The second
morphism of the ideal sequence of [Stacks, Tag 0C6K] is
`SheafOfModules.unitToPushforwardObjUnit` of the structure-sheaf map of the closed immersion, so
it is `RingedSpaceModuleAdjunction.structureSheafModuleHom` of that morphism; the comparison of
the degree-zero single functor with pushforward is the identity in degree zero. -/
theorem pushforwardStructureSheafUnitCochain_f_zero :
    (pushforwardStructureSheafUnitCochain D).f 0 =
      structureSheafModuleHom (closedQuotient D).i :=
  rfl

omit [IsEffectiveCartierDivisor D] in
/-- **The identity of sections gives the cochain-level core of [Stacks, Tag 0B4B].** This is
`…ClosedQuotientMorphismOfRingedSpaces.cochainCore_of_sectionsCore` at the closed quotient
morphism of the divisor, with the unit supplied as a morphism of complexes by
`Stacks.Divisors.pushforwardStructureSheafUnitCochain`. -/
theorem dualTriangleFirstMapCochainCore_of_sectionsCore
    (hs : (closedQuotient D).SheafHomPushforwardSectionsCore) :
    DualTriangleFirstMapCochainCore D := fun I =>
  (closedQuotient D).cochainCore_of_sectionsCore hs
    (pushforwardStructureSheafUnitCochain D)
    (pushforwardStructureSheafUnitCochain_f_zero D) I

/-- **The identity of sections gives the isomorphism assertion of [Stacks, Tag 0B4B]:** the
canonical comparison morphism `𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)` of an effective
Cartier divisor is an isomorphism. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_sectionsCore
    (hs : (closedQuotient D).SheafHomPushforwardSectionsCore) :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) :=
  isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_cochainCore D
    (dualTriangleFirstMapCochainCore_of_sectionsCore D hs)

end Stacks.Divisors

end
