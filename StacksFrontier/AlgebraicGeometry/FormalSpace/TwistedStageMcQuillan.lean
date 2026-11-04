module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanSectionProjections
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSpaces

/-!
# The target is McQuillan and the source is not

This is the point of the construction of Stacks 0CBE — the second sense of the warning of
Stacks 0AN7. Of the two affine formal algebraic spaces built in
`StacksFrontier.AlgebraicGeometry.FormalSpace.TwistedStageSpaces`, the **target** satisfies
McQuillan's criterion, condition (4) of Stacks 0AIC, because a single fixed ring `Lam I`
surjects compatibly onto every one of its stage rings, by `Stacks.Coherent.lamProj_surjective`
and `Stacks.Coherent.stageRingMap_comp_lamProj`; and the **source** does not, because its stage
rings are the dual numbers over those, whose twisted transition maps have no surjective limit
projection.

Refuting McQuillan's criterion looks as though it needs a statement about every presentation,
since the criterion asks only that *some* presentation have surjective section projections. It
does not: condition (4) implies condition (5) of Stacks 0AIC
(`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation.hasAllSurjectivePresentations`),
so exhibiting *one* presentation whose projections fail suffices. That is the economy which
makes the whole counterexample affordable.

## Main results

* `Stacks.Coherent.hasSomeSurjectivePresentation_targetSpace`: **the target is McQuillan.**
* `Stacks.Coherent.not_hasSomeSurjectivePresentation_sourceSpace`: **the source is not
  McQuillan.**

## Implementation notes

The only geometric input is `AlgebraicGeometry.Scheme.ΓSpecIso`, the identification of the ring
of global sections of `Spec R` with `R`, used in its `inv` direction so that the compatible
family of surjections out of `Lam I` lands in the section rings; its naturality in that
direction, `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`, is what makes the family
compatible.

Neither half builds a functor out of the system of rings.
`AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_surjective_family` takes a
bare *type* for the surjecting object — nothing in its argument uses the ring structure — and
`AlgebraicGeometry.FormalSpace.HasSurjectiveSectionProjections` already quantifies over the
sections of the section diagram. Repackaging the system as a diagram would require its identity
and composition laws to hold definitionally, which for a twisted system they do not: the
cocycle is the content, so `Stacks.Coherent.stageRingMap_comp` and its relatives are theorems.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.FormalSpace

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]
variable (B : BigFppfSite.{u}) (hcard : Cardinal.mk (Lam I) < B.cutoff)

include hcard in
/-- The section projections of the target's presentation are surjective: the one fixed ring
`Lam I` surjects compatibly onto every stage ring, and the ring of global sections of the
spectrum of a ring is that ring. -/
theorem hasSurjectiveSectionProjections_targetBigAffineDiagram :
    HasSurjectiveSectionProjections B (baseScheme I) (contains_baseScheme B hcard)
      (targetBigAffineDiagram B hcard) := by
  refine hasSurjectiveSectionProjections_of_surjective_family B (baseScheme I)
    (contains_baseScheme B hcard) (Λ := Lam I)
    (π := fun j x ↦ (Scheme.ΓSpecIso (CommRingCat.of (StageRing j.unop.down))).inv
      (lamProj j.unop.down x))
    (fun {j k} g x ↦ ?_) (fun j y ↦ ?_)
  · have hle : k.unop ≤ j.unop := leOfHom g.unop
    have hnat := congrArg (fun m ↦ (CommRingCat.Hom.hom m) (lamProj j.unop.down x))
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (stageRingMap (show k.unop.down ≤ j.unop.down from hle))))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, stageRingMap_comp_lamProj] at hnat
    exact hnat.symm
  · exact Function.Surjective.comp
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (StageRing j.unop.down))).inv).surjective
      (lamProj_surjective j.unop.down) y

include hcard in
/-- **The target is McQuillan**: condition (4) of Stacks 0AIC holds for it, witnessed by its own
presentation. -/
theorem hasSomeSurjectivePresentation_targetSpace [Nonempty I] :
    HasSomeSurjectivePresentation B (baseScheme I) (contains_baseScheme B hcard)
      (targetSpace B hcard) :=
  ⟨isAffineFormalAlgebraicSpace_targetSpace B hcard, Index I, inferInstance, inferInstance,
    inferInstance, targetBigAffineDiagram B hcard,
    fun {_ _} f ↦ targetBigAffineDiagram_isThickening B hcard f, ⟨Iso.refl _⟩,
    hasSurjectiveSectionProjections_targetBigAffineDiagram B hcard⟩

/-! ### The source is not McQuillan -/

include hcard in
/-- The section projections of the source's presentation are **not** surjective. A compatible
family of sections would, read through the identification of each section ring with its stage
ring, be a compatible family for the twisted system hitting a prescribed element — and
`Stacks.Coherent.not_surjective_dualSection` forbids that.

No functor and no natural transformation is built: the compatible family is transported by hand
along `AlgebraicGeometry.Scheme.ΓSpecIso` and its naturality. -/
theorem not_hasSurjectiveSectionProjections_sourceBigAffineDiagram [Uncountable I] [Nonempty I]
    (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    ¬ HasSurjectiveSectionProjections B (baseScheme I) (contains_baseScheme B hcard)
      (sourceBigAffineDiagram B hcard hcnt) := by
  intro hsurj
  refine not_surjective_dualSection hcnt (Classical.arbitrary I) fun y ↦ ?_
  -- a preimage of `y` under the identification, so that no cancellation law is needed
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (DualStage (Classical.arbitrary I)))).hom).surjective y
  obtain ⟨s, hs⟩ := hsurj (ULift.up (Classical.arbitrary I)) z
  refine ⟨⟨fun b ↦ (Scheme.ΓSpecIso (CommRingCat.of (DualStage b))).hom
      (s.1 (op (ULift.up b))), fun a b h ↦ ?_⟩, ?_⟩
  · have hnat := congrArg (fun m ↦ (CommRingCat.Hom.hom m) (s.1 (op (ULift.up a))))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap hcnt h)))
    simp only at hnat
    exact hnat.symm.trans (congrArg (ConcreteCategory.hom
      (Scheme.ΓSpecIso (CommRingCat.of (DualStage b))).hom)
      (s.2 (homOfLE (show (ULift.up b : Index I) ≤ ULift.up a from h)).op))
  · exact (congrArg (ConcreteCategory.hom
      (Scheme.ΓSpecIso (CommRingCat.of (DualStage (Classical.arbitrary I)))).hom) hs).trans hz

include hcard in
/-- **The source is not McQuillan.** Were it, condition (4) of Stacks 0AIC would give condition
(5) — surjective section projections for *every* presentation by affine thickenings — and in
particular for the presentation the source is built from, whose projections fail. This is the
economy that makes the counterexample affordable: refuting a condition on *some* presentation
needs only *one* presentation exhibited. -/
theorem not_hasSomeSurjectivePresentation_sourceSpace [Uncountable I] [Nonempty I]
    (hcnt : ∀ a : I, (Set.Iio a).Countable) :
    ¬ HasSomeSurjectivePresentation B (baseScheme I) (contains_baseScheme B hcard)
      (sourceSpace B hcard hcnt) := by
  intro h
  obtain ⟨-, hall⟩ := HasSomeSurjectivePresentation.hasAllSurjectivePresentations
    B (baseScheme I) (contains_baseScheme B hcard) h
  exact not_hasSurjectiveSectionProjections_sourceBigAffineDiagram B hcard hcnt
    (hall (Index I) inferInstance (sourceBigAffineDiagram B hcard hcnt)
      (fun {_ _} f ↦ sourceBigAffineDiagram_isThickening B hcard hcnt f) ⟨Iso.refl _⟩)

end Stacks.Coherent

end
