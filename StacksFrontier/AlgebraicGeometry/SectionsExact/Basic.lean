module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Taking sections of a sheaf over an object is left exact

Limits in a category of sheaves are created by the forgetful functor to presheaves, and limits of
presheaves are computed objectwise. So for any site `(C, J)` and any target category `A` with
finite limits, the sections functor `Γ(K, -) : Sheaf J A ⥤ A` at an object `K : Cᵒᵖ` preserves
finite limits.

This file records that fact and the one instance the repository's sheaf cohomology needs from it:
the global-sections functor `secF R U : Mod(𝒪_X) ⥤ Ab` underlying the cohomology of
[Stacks, Tag 01E3] is left exact. That is the side condition of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, hence
of the degree-zero clause of a cohomological δ-functor over an open `U`.

## Main results

* `Stacks.SectionsExact.preservesFiniteLimits_evaluation_obj`: evaluation at an object,
  `(evaluation D A).obj K : (D ⥤ A) ⥤ A`, preserves finite limits as soon as `A` has them.
* `Stacks.SectionsExact.preservesFiniteLimits_sheafSections_obj`: sections over an object,
  `(sheafSections J A).obj K`, preserve finite limits.
* `Stacks.SectionsExact.preservesFiniteLimits_secF`: `Γ(U, -)` on sheaves of `𝒪_X`-modules is
  left exact.

No tag attribute is attached: this is general sites infrastructure belonging to another chapter.

## Implementation notes

**Why the two Mathlib halves do not compose by instance search.** Both factors of
`sheafSectionsNatIsoEvaluation` are available at this pin — `PreservesFiniteLimits
(sheafToPresheaf J A)` from `HasFiniteLimits A`, and the evaluation half from
`CategoryTheory.Limits.evaluation_preservesLimitsOfShape` once the shape is finite — but
`CategoryTheory.Limits.comp_preservesFiniteLimits` is a `lemma` here, not an `instance`
(`Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:87`). An instance trace on the composite
offers only `PreservesLimits.preservesFiniteLimits` and
`PreservesLimitsOfSize0.preservesFiniteLimits`, which demand *all* limits of the relevant size
and are not available for `sheafToPresheaf` without `HasSheafify`. So the composite is supplied
positionally at each of the two steps, as a local instance for the transport along
`sheafSectionsNatIsoEvaluation` and directly for `secF`.

**Why `secF` needs no unfolding.** `secF` is a `noncomputable abbrev`, so it is reducible and
unifies with `F ⋙ G` during elaboration of `comp_preservesFiniteLimits`; no `change`,
`inferInstanceAs` or transparency adjustment is required. Had it been a semireducible `def`, one
of those would have been.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v₁ u₁ v₂ u₂ v₃ u₃ u

namespace Stacks.SectionsExact

section Evaluation

variable {D : Type u₃} [Category.{v₃} D] (A : Type u₂) [Category.{v₂} A] [HasFiniteLimits A]

/-- **Evaluation at an object is left exact.** Limits of functors into `A` are computed
objectwise, so `(evaluation D A).obj K` preserves every finite limit as soon as `A` has finite
limits. Mathlib's `CategoryTheory.Limits.evaluationPreservesLimits` asks for all limits of `A`;
this is the finite-limit form. -/
instance preservesFiniteLimits_evaluation_obj (K : D) :
    PreservesFiniteLimits ((evaluation D A).obj K) :=
  ⟨fun _ _ _ => inferInstance⟩

end Evaluation

section SheafSections

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasFiniteLimits A]

/-- **Taking sections over an object is left exact.** The functor
`(sheafSections J A).obj K : Sheaf J A ⥤ A` preserves finite limits: it is `sheafToPresheaf J A`,
which creates them, followed by evaluation at `K`, which computes them objectwise. -/
@[sga "4 II 4.1" "Clause 3"]
instance preservesFiniteLimits_sheafSections_obj (K : Cᵒᵖ) :
    PreservesFiniteLimits ((sheafSections J A).obj K) := by
  have : PreservesFiniteLimits (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op K.unop)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J A (X := K.unop)).symm

end SheafSections

section Sections

variable {X : Type u₁} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u₂})

/-- **The global-sections functor `Γ(U, -)` on sheaves of `𝒪_X`-modules is left exact.** It is
the forgetful functor to sheaves of abelian groups, which preserves finite limits, followed by
sections over `U`, which preserve them by
`Stacks.SectionsExact.preservesFiniteLimits_sheafSections_obj`.

This is the hypothesis of `CategoryTheory.Functor.rightDerivedZeroIsoSelf` at `secF R U`, hence
what identifies the degree-zero part of the right derived δ-functor of `Γ(U, -)` with `Γ(U, -)`
itself. -/
@[sga "4½ Arcata 1.6.5" "special case"]
instance preservesFiniteLimits_secF (U : Opens X) :
    PreservesFiniteLimits (secF.{u₁, u₂, u₃} R U) :=
  comp_preservesFiniteLimits _ _

end Sections

end Stacks.SectionsExact
