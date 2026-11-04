module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FormalFunctionsNoHypotheses

/-!
# Full faithfulness of the completion functor over a complete base, with nothing assumed

**Stacks 0883.** Let `A` be a Noetherian ring complete with respect to an ideal `J`, let
`f : X ⟶ Spec A` be proper and put `𝓘 = J · 𝒪_X`. Then completion

  `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`

is fully faithful.

`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithful.lean` proves this
from the theorem on formal functions in degree zero, carried there as the hypothesis `hFF`:
`H⁰(X, H) ⟶ limₙ H⁰(X, H / 𝓘ⁿ H)` is an isomorphism for every coherent `H`. That is now a
theorem of this library,
`Stacks.Algebraization.isIso_cohomologyToLimit_unconditional` ([Stacks, Tag 087U]) read in
degree zero, so this file discharges it.

## Main results

* `Stacks.Algebraization.isIso_globalSectionsToLimit_unconditional` — the theorem on formal
  functions in degree zero, with no hypothesis.
* `Stacks.Algebraization.forall_isIso_globalSectionsToLimit` — the same, quantified over every
  coherent module: this is the hypothesis `hFF` of
  `Stacks.Algebraization.fullyFaithful_completionFunctor`.
* `Stacks.Algebraization.fullyFaithful_completionFunctor_unconditional` — **Stacks 0883**, with
  no hypothesis.

## Implementation notes

`AlgebraicGeometry.IsLocallyNoetherian` is a `Prop`, so the instance obtained from properness
over the Noetherian base and any other instance of it are definitionally equal; the statements
below therefore introduce it with `letI`, exactly as
`Stacks.Algebraization.fullyFaithful_completionFunctor` does, and no transport is needed.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions

section DegreeZero

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **The theorem on formal functions in degree zero, with no hypothesis**, stated with local
Noetherianity of `X` as an instance: for `A` Noetherian and `J`-adically complete,
`f : X ⟶ Spec A` proper and `H` coherent, the canonical map

  `H⁰(X, H) ⟶ limₙ H⁰(X, H / 𝓘ⁿ H)`

is an isomorphism.

This is `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit` applied
to [Stacks, Tag 087U] in degree zero. -/
public theorem isIso_globalSectionsToLimit_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    IsIso (globalSectionsToLimit (baseIdealSheaf A J f) H) :=
  isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit (baseIdealSheaf A J f) H
    (isIso_cohomologyToLimit_of_isLocallyNoetherian A J f H 0)

/-- **The theorem on formal functions in degree zero, with no hypothesis.** Local Noetherianity
of `X` is not assumed: it follows from properness over the Noetherian base. -/
public theorem isIso_globalSectionsToLimit_unconditional
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (globalSectionsToLimit (baseIdealSheaf A J f) H) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isIso_globalSectionsToLimit_of_isLocallyNoetherian A J f H

/-- **The hypothesis `hFF` of `Stacks.Algebraization.fullyFaithful_completionFunctor`, proved.**
The theorem on formal functions in degree zero holds for every coherent module on a scheme
proper over the spectrum of a Noetherian `J`-adically complete ring. -/
public theorem forall_isIso_globalSectionsToLimit :
    ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      IsIso (globalSectionsToLimit (baseIdealSheaf A J f) H) :=
  fun H => isIso_globalSectionsToLimit_unconditional A J f H

end DegreeZero

/-! ### Stacks 0883 with no hypothesis -/

section FullyFaithful

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A]
  {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]

/-- **Stacks 0883, with no hypothesis.** Let `A` be a Noetherian ring complete with respect to an
ideal `J` and let `f : Y ⟶ Spec A` be proper. Then completion along `𝓘 = J · 𝒪_Y` is a fully
faithful functor `Coh(𝒪_Y) ⥤ Coh(Y, 𝓘)`.

This is `Stacks.Algebraization.fullyFaithful_completionFunctor` with its hypothesis `hFF` — the
theorem on formal functions in degree zero — discharged by
`Stacks.Algebraization.forall_isIso_globalSectionsToLimit`. -/
public theorem fullyFaithful_completionFunctor_unconditional :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    Nonempty (completionFunctor Y (baseIdealSheaf A J f)).FullyFaithful :=
  fullyFaithful_completionFunctor A J f (forall_isIso_globalSectionsToLimit A J f)

end FullyFaithful

end Stacks.Algebraization

end
