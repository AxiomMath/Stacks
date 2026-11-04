module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProjectiveMorphismEquivalence
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.ChowConsumption
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Chow step of the dévissage of Stacks 088C

Stacks 088C is proved by a Noetherian induction over the quasi-coherent ideal sheaves of `X`,
carried in `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/Devissage.lean`, whose
single inductive step enters there as the hypothesis `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`. The source discharges that
step by applying **Chow's lemma** (Stacks 0200) to the closed subscheme cut out by the ideal
sheaf under consideration, algebraizing upstairs by the **projective case** (Stacks 0885) and
comparing the result with the original system by Stacks 088A and 088B.

This file carries the Chow half of that step, and carries it as far as the projective case
allows. Two things are proved with no hypothesis at all:

* Chow's lemma for a proper morphism produces a modification which is **H-projective over the
  base**, not merely immersed in a projective space over it
  (`AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification`); and
* the completion functor of the closed subscheme cut out by *any* quasi-coherent ideal sheaf is
  **fully faithful**, which is one of the two halves of hypothesis (1) of Stacks 088A
  (`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_subschemeι`).

The projective case is itself unconditional: both of its carriers,
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective` and
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism`, assume only that
`A` is Noetherian and `I`-adically complete and that the morphism is projective. It enters here
through the named predicate
`Stacks.Algebraization.IsEquivalenceCompletionFunctorOfIsProjectiveMorphism`, which is **exactly**
the statement the second of those two carriers has, universally quantified over the scheme and
the H-projective morphism. That this is so is not a remark but a theorem:
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds` proves it
outright, by one application of the carrier. Stacks 0885 stands at the source's hypotheses, so the
predicate below is a parameterisation rather than an obligation.

The carrier targeted is the **H-projective** one, clause (2) of Tag 01W8, because that is the
notion Chow's lemma delivers: a modification immersed in a projective space over the base, proper
over it, is a *closed* immersion into that projective space, which is H-projectivity on the nose.
Clause (1), `AlgebraicGeometry.IsProjective`, asks for a closed immersion into the projective
bundle of a module, and reaching it from Chow's lemma would route through
`AlgebraicGeometry.IsProjectiveMorphism.isProjective` for no gain.

## Main results

* `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification` — **Chow's lemma for a
  proper morphism, with the modification H-projective over the base.** Unconditional.
* `Stacks.Algebraization.IsEquivalenceCompletionFunctorOfIsProjectiveMorphism` — the projective
  case of Grothendieck existence, as a hypothesis.
* `Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds` — that
  hypothesis **is** Stacks 0885 at clause (2) of Tag 01W8, and holds outright.
* `Stacks.Algebraization.exists_chowModification_isEquivalence_completionFunctor` — **the Chow
  step**: a proper morphism to the spectrum of a complete Noetherian ring admits a proper
  surjective modification, an isomorphism over a dense open and H-projective over the base, along
  which the completion functor of Stacks 0880 is an equivalence. From the projective case alone.
* `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper` — the completion
  functor of a scheme above `X` whose composite to `Spec A` is proper, along the inverse image of
  `𝓘`, is fully faithful. Unconditional.
* `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_subschemeι` — the completion
  functor of the closed subscheme cut out by a quasi-coherent ideal sheaf is fully faithful.
  Unconditional; the previous result at `π = J.subschemeι`.
* `Stacks.Algebraization.IsSystemAnnihilatedBy.mono` — being killed by an ideal sheaf is
  inherited by smaller ideal sheaves.

## Implementation notes

Chow's lemma is `AlgebraicGeometry.hasDenseChowModification`, whose hypotheses are
`[IsNoetherian S]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]` and `[QuasiCompact f]` and which
carries no hypothesis term; a proper `f` supplies the last three by instance search. Its
conclusion gives only an *immersion* `i : X' ⟶ 𝐏ⁿ_S`. The upgrade to a closed immersion is the
one of Stacks 0201: `π ≫ f` is proper, so `i` is proper because `𝐏ⁿ_S` is separated over `S`, and
a proper immersion is closed, `AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper`.
The two spellings of projective space meet here — `AlgebraicGeometry.ProjectiveSpace`, in which
Chow's lemma states its conclusion, and the definitionally equal
`AlgebraicGeometry.projectiveSpaceOver`, in which `AlgebraicGeometry.IsProjectiveMorphism` is
stated — exactly as they do in
`AlgebraicGeometry.isProjectiveMorphism_chowModification`: the closed immersion and the
commutation are handed to the definition of H-projectivity directly, and no `rw` is performed
across the two.

Full faithfulness over a scheme above `X` is Stacks 0883 on that scheme: if `π : X' ⟶ X` is such
that `π ≫ f` is proper, then
`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper` applies to `π ≫ f`, and
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` identifies the ideal sheaf it is stated for
with the inverse image `(𝓘).comap π`. That is
`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper`, and the closed subscheme
case `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_subschemeι` is its instance at
`π = J.subschemeι`, the composite being proper because a closed immersion is. The subscheme case is
the half of hypothesis (1) of Stacks 088A which the Noetherian induction of Stacks 088C gets for
free; the other half, essential surjectivity on the subschemes `V(𝒦 ᵉ)`, is what the induction
hypothesis is for, and converting it needs the *ascent* of membership in `Coh(-, -)` along the
direct image of a closed immersion — the converse of
`Stacks.Coherent.isCoherentAdicSystem_of_pushforward` — which is
`Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/ClosedImmersionAscent.lean`, so
that conversion is carried: it is
`Stacks.Algebraization.essSurj_completionFunctor_comap_subschemeι_of_essImage`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for a category of sheaves of modules which agrees
with it only at default transparency, so the submodule lattice used to state annihilation is
introduced as a local instance, as in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/Devissage.lean`.

**No Stacks tag attribute is attached to anything here.** Tag 0200 sits on
`AlgebraicGeometry.hasDenseChowModification` and tag 0201 on the refinements of
`StacksFrontier/AlgebraicGeometry/ChowNoetherian/Refinements.lean`; tag 0885 sits on the two
carriers of the projective case, and the statements below that depend on it carry it as a
hypothesis rather than proving it.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0201](https://stacks.math.columbia.edu/tag/0201)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! ### Chow's lemma for a proper morphism, with an H-projective modification -/

namespace AlgebraicGeometry

/-- **Chow's lemma for a proper morphism over a Noetherian base, with the modification
H-projective over the base.** Let `f : X ⟶ S` be proper with `S` Noetherian. Then there are a
scheme `X'`, a proper surjective `π : X' ⟶ X` and a dense open `U ⊆ X` such that `π` is an
isomorphism over `U` and `π ≫ f` is H-projective.

Chow's lemma, `AlgebraicGeometry.hasDenseChowModification`, provides all of this except that it
gives only an *immersion* `i : X' ⟶ 𝐏ⁿ_S` over `S`. Since `π ≫ f = i ≫ (𝐏ⁿ_S ↘ S)` is proper and
`𝐏ⁿ_S` is separated over `S`, the immersion `i` is itself proper, hence a closed immersion by
`AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper`; a closed immersion into a
projective space over `S`, over `S`, is exactly H-projectivity of `π ≫ f`. -/
@[ega "II 5.6.1" "(i), special case, (ii)",
  ega "II 5.6.2" "partial",
  sga "4½ Arcata 3.4.3" "partial"]
public theorem exists_isProjectiveMorphism_denseChowModification {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [IsProper f] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (U : X.Opens),
      IsProper π ∧ Surjective π ∧ IsProjectiveMorphism (π ≫ f) ∧
        Dense (U : Set X) ∧ IsIso (π ∣_ U) := by
  obtain ⟨n, X', π, i, U, hπ, hsurj, himm, hcomm, hU, hiso⟩ := hasDenseChowModification f
  have hπ' : IsProper π := hπ
  have himm' : IsImmersion i := himm
  have hcomp : IsProper (i ≫ (ProjectiveSpace n S ↘ S)) := by
    rw [← hcomm]; infer_instance
  have hi : IsProper i := IsProper.of_comp i (ProjectiveSpace n S ↘ S)
  exact ⟨X', π, U, hπ, hsurj,
    ⟨n, i, isClosedImmersion_of_isImmersion_of_isProper i, hcomm.symm⟩, hU, hiso⟩

end AlgebraicGeometry

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-! ### The projective case of Stacks 0885 as a hypothesis -/

/-- **The projective case of Grothendieck's existence theorem, Stacks 0885, as a hypothesis.**
Let `A` be a Noetherian ring complete with respect to `I`. The statement asserts that for every
H-projective `g : X' ⟶ Spec A` — clause (2) of Tag 01W8 — the completion functor
`Coh(𝒪_{X'}) ⥤ Coh(X', 𝓘 𝒪_{X'})` of Stacks 0880 is an equivalence.

This is the statement
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism` will have once its
generation hypothesis `hGen` is discharged, universally quantified over `X'` and `g`; it holds
outright by
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`. Properness,
and with it the local Noetherianity of `X'` that the completion functor needs, is introduced from
H-projectivity by `AlgebraicGeometry.isProper_of_isProjectiveMorphism` rather than assumed, which
is why the two instances appear as `letI`s inside the statement — the same shape the carrier
has. -/
public def IsEquivalenceCompletionFunctorOfIsProjectiveMorphism
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] : Prop :=
  ∀ {X' : Scheme.{u}} (g : X' ⟶ Spec (.of A)) (hg : AlgebraicGeometry.IsProjectiveMorphism g),
    letI : IsProper g := isProper_of_isProjectiveMorphism g hg
    letI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian g
    (completionFunctor X' (baseIdealSheaf A I g)).IsEquivalence

/-- **The hypothesis above is Stacks 0885 at clause (2) of Tag 01W8 with `hGen` discharged, and
nothing more.** Granted the generation statement of the source's first paragraph for every
H-projective morphism to `Spec A`, the projective case holds for every such morphism.

The proof is one application of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism`, the carrier of
Stacks 0885 for clause (2), which stands at the source's hypotheses: `A` Noetherian and
`I`-adically complete and `g` H-projective, and nothing further. So every statement below taking
`Stacks.Algebraization.IsEquivalenceCompletionFunctorOfIsProjectiveMorphism` as a hypothesis is
discharged by this theorem, with no obligation left over.

This predicate was introduced when that carrier still took the generation statement of the
source's first paragraph as a named hypothesis `hGen`, so that the Chow step below could be
written against it before the generation statement was proved. It is now a theorem rather than a
reduction. -/
public theorem isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] :
    IsEquivalenceCompletionFunctorOfIsProjectiveMorphism A I :=
  fun g hg => isEquivalence_completionFunctor_of_isProjectiveMorphism_of_vanishing A I g hg

/-! ### The Chow step -/

/-- **The Chow step of the dévissage of Stacks 088C.** Let `A` be a Noetherian ring complete with
respect to an ideal `I` and let `f : X ⟶ Spec A` be proper. Granted the projective case of
Grothendieck existence — and granted nothing else — there are a scheme `X'`, a proper surjective
`π : X' ⟶ X` which is H-projective over `Spec A` and an isomorphism over a dense open `U ⊆ X`,
such that the completion functor

  `Coh(𝒪_{X'}) ⥤ Coh(X', 𝓘 𝒪_{X'})`,   `𝓘 = I · 𝒪_{X'}`,

of Stacks 0880 along the base ideal sheaf of `π ≫ f` is an equivalence.

This is the move the source makes at the start of the inductive step of its Noetherian induction:
Chow's lemma over the Noetherian base `Spec A`, applied to the proper morphism at hand, produces
a modification which is projective over the base, and the projective case algebraizes every
coherent adic system on it. Everything here beyond the projective case is proved:
`AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification` is unconditional, and
H-projectivity of `π ≫ f` is precisely what the projective case consumes. What the source does
*next* — descending the algebraization along `π` by Stacks 02O5 and comparing it with the
original system by Stacks 088B and 088A — is not here; see the module docstring. -/
public theorem exists_chowModification_isEquivalence_completionFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (h0885 : IsEquivalenceCompletionFunctorOfIsProjectiveMorphism A I) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (U : X.Opens) (_ : IsProper π)
      (hproj : AlgebraicGeometry.IsProjectiveMorphism (π ≫ f)),
      Surjective π ∧ Dense (U : Set X) ∧ IsIso (π ∣_ U) ∧
        letI : IsProper (π ≫ f) := isProper_of_isProjectiveMorphism (π ≫ f) hproj
        letI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ f)
        (completionFunctor X' (baseIdealSheaf A I (π ≫ f))).IsEquivalence := by
  obtain ⟨X', π, U, hπ, hsurj, hproj, hU, hiso⟩ :=
    AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification f
  exact ⟨X', π, U, hπ, hproj, hsurj, hU, hiso, h0885 (π ≫ f) hproj⟩

/-! ### Dévissage bookkeeping -/

/-- **Being killed by an ideal sheaf is inherited by smaller ideal sheaves.** If `𝒦 · F_n = 0` for
every `n` and `𝒦' ⊆ 𝒦`, then `𝒦' · F_n = 0` for every `n`.

The family `Ξ` of the proof of Stacks 088C is therefore an up-set in the quasi-coherent ideal
sheaves, which is what makes the Noetherian induction of
`Stacks.Algebraization.essImage_completionFunctor_of_devissage` the right one: the objects granted
at an ideal sheaf strictly larger than `𝒦` are *fewer*, not more. -/
public theorem IsSystemAnnihilatedBy.mono {X : Scheme.{u}} {K K' : X.IdealSheafData} (h : K' ≤ K)
    {F : ℕᵒᵖ ⥤ X.Modules} (hF : IsSystemAnnihilatedBy K F) :
    IsSystemAnnihilatedBy K' F := fun n =>
  le_bot_iff.mp
    ((idealPowerMultiple_le_of_pow_le (by simpa using h) (F.obj (op n))).trans (hF n).le)

/-- **Completion is fully faithful on any scheme above `X` which is proper over the base, along
the inverse image of `𝓘`.** Let `A` be a Noetherian ring complete with respect to `I`, let
`f : X ⟶ Spec A` be any morphism and let `π : X' ⟶ X` be such that `π ≫ f` is proper. Then
completion along `(𝓘).comap π`, `𝓘 = I · 𝒪_X`, is fully faithful on `Coh(𝒪_{X'})`. **No
hypothesis.**

This is Stacks 0883 on `X'`, applied to `π ≫ f`, read through
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`: the base ideal sheaf of the composite is
the inverse image along `π` of the base ideal sheaf of `f`. Properness of `f` itself is not
needed — only of the composite, which is what the completion functor on `X'` consumes.

This is the whole content of the binder

`hff : Nonempty (completionFunctor X (𝒥.comap f)).FullyFaithful`

of `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`
(Stacks 088B at a general base) when `𝒥` is a base ideal sheaf: the module docstring there records
that discharging it needs only the identification of `baseIdealSheaf A I g` with `𝒥.comap f`, and
that identification is `baseIdealSheaf_comap`. The discharge is carried out in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/DevissageComparison.lean`. -/
public theorem fullyFaithful_completionFunctor_comap_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper (π ≫ f)] :
    letI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ f)
    Nonempty (completionFunctor X' ((baseIdealSheaf A I f).comap π)).FullyFaithful := by
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f π]
  exact fullyFaithful_completionFunctor_of_isProper A I (π ≫ f)

/-- **The completion functor of the closed subscheme cut out by a quasi-coherent ideal sheaf is
fully faithful.** Let `A` be a Noetherian ring complete with respect to `I`, let
`f : X ⟶ Spec A` be proper and let `J ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. Then completion
along the inverse image of `𝓘 = I · 𝒪_X` is fully faithful on `Coh(𝒪_{V(J)})`. **No
hypothesis.**

This is `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper` at
`π = J.subschemeι`, the composite `V(J) ⟶ X ⟶ Spec A` being proper because a closed immersion is.

It is one of the two halves of hypothesis (1) of Stacks 088A, which asks for the completion
functors of the subschemes `V(𝒦 ᵉ)` to be *equivalences*. Full faithfulness is thus free in the
situation of Stacks 088C; only essential surjectivity on those subschemes has to come from the
induction hypothesis. -/
public theorem fullyFaithful_completionFunctor_comap_subschemeι
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (J : X.IdealSheafData) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (J.subschemeι ≫ f)
    Nonempty (completionFunctor J.subscheme
      ((baseIdealSheaf A I f).comap J.subschemeι)).FullyFaithful :=
  fullyFaithful_completionFunctor_comap_of_isProper A I f J.subschemeι

end Stacks.Algebraization

end
