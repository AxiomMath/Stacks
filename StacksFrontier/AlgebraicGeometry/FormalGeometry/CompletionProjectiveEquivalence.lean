module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxEpiAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxGen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic

/-!
# Grothendieck's existence theorem for a projective morphism

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be
projective and put `𝓘 = I · 𝒪_X`. Then the completion functor of Stacks 0880

  `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`,  `F ↦ (F / 𝓘ⁿ F)`

is an equivalence. That is Stacks 0885, and this file assembles it from its two halves at the
source's own hypotheses.

**Projectivity is read as clause (1) of Tag 01W8**, `AlgebraicGeometry.IsProjective`: a closed
immersion over `Spec A` into the projective bundle `𝐏(ℰ)` of a quasi-coherent `𝒪_{Spec A}`-module
of finite type. That is the Stacks Project's unqualified "projective morphism", and it is the
weaker of the two clauses — an H-projective morphism is projective by Tag 01W9
(`AlgebraicGeometry.IsProjectiveMorphism.isProjective`) — so the statement below is the stronger
one and covers clause (2) as a special case. Nothing is assumed beyond it: properness comes from
`AlgebraicGeometry.IsProjective.isProper` and with it `UniversallyClosed f`,
`LocallyOfFiniteType f` and the local Noetherianity of `X`, and the `f`-ample invertible module
the proof needs is produced from the defining closed immersion by
`AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple` together with Tag 01VN.

## How it is proved

Full faithfulness is Stacks 0883,
`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`, which rests on the theorem on
formal functions in degree zero (Stacks 087U) through the uniform Artin-Rees bounds of Stacks
02OB over the unconditional Stacks 02O8.

Essential surjectivity follows the source. An `f`-ample `L` is chosen;
`H¹(X, Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ L^{⊗d})` is made to vanish for all `n` at once and all `d ≫ 0`
(Stacks 0884); the resulting surjectivity of the transition maps lifts a generating family of
`𝓕_1 ⊗ L^{⊗d}` to a compatible system, which Stacks 087Y turns into an epimorphism from the
completion of a coherent module; and the generation statement together with the exactness of the
functor (Stacks 0881) and the abelian structure of `Coh(X, 𝓘)` (Stacks 087X) gives essential
surjectivity. `Stacks.Algebraization.exists_epi_completionFunctor_of_vanishing` is the generation
statement granted the vanishing, and `Stacks.Algebraization.essSurj_of_forall_exists_epi` is the
last paragraph.

The input of Stacks 0884 is **Stacks 0897 part (2) for the associated graded algebra of `𝓘`**,
`Stacks.Coherent.HasAssociatedGradedTwistVanishing`. It is supplied unconditionally by
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper`: the dévissage of Stacks 0897
over the polynomial algebra `𝒪_X[x_i]` on a finite family of generators of `I`
(`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_forall_epi_over_polyAlgebra`), with the
degreewise epimorphic presentation `⨁_{j ∈ J} N_j ⊗ 𝒪_X[x_i](-j) ⟶ N` of
`Stacks.Coherent.exists_epi_degreePresentation_polyAlgebra`. So the statement below assumes
nothing beyond the source's hypotheses, and Tag 0885 is registered on it without qualification.
The statements in `CompletionProjective.lean` assume the generation statement itself, which is
strictly more, and carry no Stacks attribute.

## Main results

* `Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective` — a projective morphism to the
  spectrum of a ring carries an invertible module that is `f`-ample, and hence ample, the base
  being affine.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing` — Stacks
  0885 for a projective morphism in the sense of clause (1) of Tag 01W8, at the source's
  hypotheses. The name's `_of_vanishing` records the shape the statement had while Stacks 0897
  part (2) for the associated graded algebra was still a hypothesis; it is now derived.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### An ample invertible module from projectivity -/

omit [IsNoetherianRing A] in
/-- **A projective morphism to an affine base carries an ample invertible module.** The defining
closed immersion into `𝐏(ℰ)` exhibits the pullback of `𝒪_{𝐏(ℰ)}(1)` as `f`-very ample
(Tag 01VM, `AlgebraicGeometry.IsProjective.exists_isRelativelyVeryAmple`); a quasi-compact
morphism with an `f`-very ample module has it `f`-ample (Tag 01VN); and over the affine base
`Spec A` relative ampleness is ampleness (Tag 01VK). -/
public theorem exists_isRelativelyAmple_of_isProjective (hf : AlgebraicGeometry.IsProjective f) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI : Stacks.Ample.IsInvertibleModule X L := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L ∧ Stacks.Ample.IsAmple X L := by
  obtain ⟨L, hLinv, hvamp⟩ := hf.exists_isRelativelyVeryAmple
  let : Stacks.Ample.IsInvertibleModule X L := hLinv
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f L :=
    Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f L hf.quasiCompact hvamp
  exact ⟨L, hLinv, hrel,
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hrel⟩

/-! ### Grothendieck existence for a projective morphism -/

variable [IsAdicComplete I A]

/-- **Grothendieck's existence theorem for a projective morphism**, [Stacks, Tag 0885], read at
clause (1) of Tag 01W8.

Let `A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be projective —
a closed immersion over `Spec A` into a projective bundle `𝐏(ℰ)` — and set `𝓘 = I · 𝒪_X`. Then
the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence.

Nothing is assumed beyond the source's hypotheses. In particular `UniversallyClosed f` and
`LocallyOfFiniteType f` are *derived* from projectivity, through
`AlgebraicGeometry.IsProjective.isProper`, rather than assumed; so is the local Noetherianity of
`X` that the completion functor of Stacks 0880 needs, and so is the `f`-ample invertible module
`L` the proof chooses.

Full faithfulness is Stacks 0883
(`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`). Essential surjectivity is
`Stacks.Algebraization.essSurj_of_forall_exists_epi` fed by the generation statement
`Stacks.Algebraization.exists_epi_completionFunctor_of_vanishing`, whose own input is the uniform
`H¹`-vanishing of Stacks 0884
(`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`); and that theorem's
single hypothesis, part (2) of Stacks 0897 for the associated graded algebra of `𝓘`, is
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper`, which needs only properness and
the invertibility of `L`.

The name's `_of_vanishing` records the shape the statement had while that hypothesis was still
carried; it is kept because the statement itself did not change. -/
@[stacks 0885]
public theorem isEquivalence_completionFunctor_of_isProjective_of_vanishing
    (hf : AlgebraicGeometry.IsProjective f) :
    letI : IsProper f := hf.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let : IsProper f := hf.isProper
  obtain ⟨L, hLinv, hrel, -⟩ := exists_isRelativelyAmple_of_isProjective A f hf
  let : Stacks.Ample.IsInvertibleModule X L := hLinv
  refine isEquivalence_completionFunctor_of_exists_epi A I f
    (fun H => isIso_globalSectionsToLimit_of_isProper A I f H) fun 𝓕 => ?_
  exact exists_epi_completionFunctor_of_vanishing A I f L hrel 𝓕
    (Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule A I f L hrel 𝓕
      (Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper A I f L))

end Stacks.Algebraization

end
