module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSectionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FormallyEtaleOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverseSupplement
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.InductionSupplement
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStepSupplement
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Full faithfulness of spaces-étale base change along a thickening

For the inclusion `f : X ⟶ Y` of a thickening of algebraic spaces, base change `V ↦ X ×_Y V` is
fully faithful from the spaces-étale site of `Y` to that of `X` (Stacks 05ZH for thickenings),
with no hypothesis on the order of the thickening.

## Main definitions

* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsThickeningRange`: base change along
  the inclusion of a thickening is fully faithful.
* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsNthOrderThickening`: the same for a
  thickening of order `n`.

## Main results

* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isNthOrderThickening` and
  `AlgebraicGeometry.Space.full_spacesBaseChange_of_isNthOrderThickening`: base change along the
  inclusion of an `n`th-order thickening is faithful and full.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Base change `V ↦ X ×_Y V` is fully faithful from the spaces-étale site of `Y` to that of `X`,
for the inclusion `f` of a thickening of algebraic spaces — a monomorphism whose range is a
closed subspace with the same points, with no hypothesis on its defining ideal. -/
@[stacks 05ZH "full faithfulness at a thickening of unbounded order, not the integral \
  universally injective case"]
noncomputable def fullyFaithfulSpacesBaseChangeOfIsThickeningRange [Mono f.hom]
    (hT : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  letI := full_spacesBaseChange_of_mono_of_isThickening B S hS f hT
  letI := faithful_spacesBaseChange_of_mono_of_isThickening B S hS f hT
  Functor.FullyFaithful.ofFullyFaithful _

/-- Base change along the inclusion of an `n`th-order thickening is faithful on spaces-étale
sites. -/
theorem faithful_spacesBaseChange_of_isNthOrderThickening {n : ℕ} [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Faithful :=
  faithful_spacesBaseChange_of_mono_of_isThickening B S hS f hT.1

/-- Base change along the inclusion of an `n`th-order thickening is full on spaces-étale
sites. -/
theorem full_spacesBaseChange_of_isNthOrderThickening {n : ℕ} [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.Full :=
  full_spacesBaseChange_of_mono_of_isThickening B S hS f hT.1

/-- Base change `V ↦ X ×_Y V` is fully faithful from the spaces-étale site of `Y` to that of `X`,
for the inclusion `f` of a thickening of order `n`, whose defining ideal has vanishing `(n+1)`st
power. -/
@[stacks 05ZH "full faithfulness at a thickening of finite order"]
noncomputable def fullyFaithfulSpacesBaseChangeOfIsNthOrderThickening {n : ℕ} [Mono f.hom]
    (hT : IsNthOrderThickening B S hS n Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.FullyFaithful :=
  fullyFaithfulSpacesBaseChangeOfIsThickeningRange B S hS f hT.1

end AlgebraicGeometry.Space

end
