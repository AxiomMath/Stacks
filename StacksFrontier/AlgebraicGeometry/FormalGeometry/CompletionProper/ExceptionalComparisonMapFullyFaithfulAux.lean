module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete

/-!
# Full faithfulness of the completion functor, with no carried hypothesis

Let `A` be a Noetherian ring complete with respect to an ideal `J`, let `f : Y ⟶ Spec A` be
proper and put `𝓙 = J · 𝒪_Y`. Completion along `𝓙` is a fully faithful functor
`Coh(𝒪_Y) ⥤ Coh(Y, 𝓙)`.

This is the form of Stacks 0883 that the comparison maps of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/` consume: the hypotheses are
exactly the source's — `A` Noetherian, `A` complete for `J`, `f` proper — and nothing about the
theorem on formal functions is carried. The two files behind it are

* `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithful.lean`, which runs
  the source's argument through Stacks 0882 for the internal hom and leaves the theorem on formal
  functions in degree zero (Stacks 087U) as the named hypothesis `hFF`; and
* `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean`,
  which discharges `hFF` by reducing Stacks 087U, in every degree, to the finiteness of
  `Hᵖ(Y, F)` over `A` ([Stacks, Tag 02O6]) and the two uniform Artin–Rees bounds of
  [Stacks, Tag 02OB] over the unconditional [Stacks, Tag 02O8].

## Main results

* `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isAdicComplete` — full faithfulness of
  the completion functor over a complete Noetherian base, with no extra hypothesis.

## Implementation notes

The statement opens with a `letI` supplying `IsLocallyNoetherian Y` from
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, because a proper morphism to a
Noetherian affine base is of finite type and the completion functor is only defined on a locally
Noetherian scheme; the instance is a consequence of the hypotheses rather than an extra one, so
it is produced in the statement instead of being assumed.

The conclusion is `Nonempty (…).FullyFaithful` rather than the pair of `Full` and `Faithful`
instances: `Functor.FullyFaithful` is data, and only its existence is available here.

No Stacks attribute is attached. The tag for this statement is registered by
`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`, of which this is a
restatement at the binders the comparison-map files use.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- Full faithfulness of the completion functor over a complete Noetherian base
(Stacks 0883), with no extra hypothesis. -/
public theorem fullyFaithful_completionFunctor_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    Nonempty (Stacks.Algebraization.completionFunctor Y
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).FullyFaithful :=
  fullyFaithful_completionFunctor_of_isProper A J f

end Stacks.Algebraization

end
