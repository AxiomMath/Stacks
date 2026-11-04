module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionGeneration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjective

/-!
# Grothendieck existence for an H-projective morphism, with the generation statement discharged

`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjective.lean`) is the projective case
of Grothendieck's existence theorem read at clause (2) of Tag 01W8 — H-projectivity — with the
generation statement of the source's first paragraph carried as an arrow hypothesis `hGen`. This
file discharges that arrow.

## Main results

* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism_of_vanishing` —
  the completion functor of Stacks 0880 is an equivalence for every H-projective morphism to the
  spectrum of a Noetherian ring complete for `I`, with nothing assumed beyond that.

This is the H-projective analogue of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing`
(`CompletionProjectiveEquivalence.lean`), which carries Tag 0885 for clause (1) of Tag 01W8 and is
where that tag is registered. No `@[stacks]` attribute is attached here: clause (1) is the weaker
notion by Tag 01W9, so the registered statement already subsumes this one, and this one exists
because H-projectivity is the hypothesis the dévissage of Stacks 088C produces from Chow's lemma.

## Implementation notes

The generation statement is
`Stacks.Algebraization.exists_epi_completionFunctor_of_isRelativelyAmple` along the `f`-ample
invertible sheaf an H-projective morphism carries by Tag 07RL
(`AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective`). Properness comes from H-projectivity
by `AlgebraicGeometry.isProper_of_isProjectiveMorphism`, and with it the local Noetherianity of `X`
that the completion functor needs; the theorem on formal functions in degree zero (Stacks 087U) is
read off properness by `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`. All three
appear as `letI`s inside the statement rather than as hypotheses because they are consequences of
`hf`.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **Grothendieck's existence theorem for an H-projective morphism**, Stacks 0885 read at clause
(2) of Tag 01W8.

Let `A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` admit a closed
immersion over `Spec A` into some `ℙⁿ_{Spec A}` and set `𝓘 = I · 𝒪_X`. Then the completion
functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence.

This is `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism` with its
`hGen` arrow discharged, so it stands at the source's hypotheses: nothing beyond them is assumed.
It is a separate declaration rather than a strengthening of that one because the conditional form
is what the dévissage consumes internally. -/
public theorem isEquivalence_completionFunctor_of_isProjectiveMorphism_of_vanishing
    (hf : AlgebraicGeometry.IsProjectiveMorphism f) :
    letI : IsProper f := isProper_of_isProjectiveMorphism f hf
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let _ : IsProper f := isProper_of_isProjectiveMorphism f hf
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨-, L, hL, hamp⟩ := hf.isQuasiProjective
  let _ : Stacks.Ample.IsInvertibleModule X L := hL
  exact isEquivalence_completionFunctor_of_exists_epi A I f
    (fun H => isIso_globalSectionsToLimit_of_isProper A I f H)
    fun 𝓕 => exists_epi_completionFunctor_of_isRelativelyAmple A I f L hamp 𝓕

end Stacks.Algebraization

end
