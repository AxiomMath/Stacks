module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ClosedImmersionEssSurj
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.PullbackCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckExistenceII

/-!
# The comparison half of the dévissage of Stacks 088C

Stacks 088C is proved by a Noetherian induction over the quasi-coherent ideal sheaves of `X`,
carried in `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/Devissage.lean`, whose
single inductive step enters there as the hypothesis `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`. The Chow half of that step —
Chow's lemma with an H-projective modification, and the projective case of Grothendieck existence
on it — is in `CompletionProper/DevissageChow.lean`. This file carries the *comparison* half: what
the source does with the modification once it has it, namely Stacks 088B to produce a map
`α : (𝓕_n) ⟶ 𝓗 ^∧` and Stacks 088A to conclude from it.

## Main results

* `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper` —
  **Stacks 088B at a base ideal sheaf, with full faithfulness no longer a binder.** One binder
  remains, `halg`; see the residuals below.
* `Stacks.Algebraization.essImage_completionFunctor_of_devissageComparison` — **Stacks 088A fed by
  the dévissage's induction hypothesis.** Granted the comparison data `(𝒦, 𝓗, α)` that Stacks 088B
  produces, and granted that every power of `𝒦` is *strictly larger* than the ideal sheaf `K` being
  inducted on, a coherent `𝓘`-adic system killed by `K` is in the essential image. Hypothesis (1)
  of Stacks 088A is assembled here from the induction hypothesis and costs nothing further: its
  full-faithfulness half is
  `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_subschemeι` and its
  essential-surjectivity half
  `Stacks.Algebraization.essSurj_completionFunctor_comap_subschemeι_of_essImage`.

## What the dévissage still needs, and what it does not

Everything the source's inductive step does *before* the comparison is unconditional in this
library, and nothing below has to assume any of it:

* Chow's lemma with the modification H-projective over the base,
  `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification`;
* the projective case, Stacks 0885, at the source's hypotheses — both carriers
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective` and
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism` assume only `A`
  Noetherian and `I`-adically complete and the morphism projective, so the Chow step
  `Stacks.Algebraization.exists_chowModification_isEquivalence_completionFunctor` is available with
  its hypothesis discharged by
  `Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`;
* hence the source's `β`: the termwise pullback `π^*(𝓕_n)` of the system along the modification is
  a coherent adic system along `(𝓘).comap π`
  (`Stacks.Coherent.coherentAdicPullback`), and that ideal sheaf *is* the base ideal sheaf of
  `π ≫ f` by `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`, so the equivalence upstairs
  algebraizes it;
* coherence of the proper direct image `𝓗 = π_*𝓕'`, Stacks 02O5, through
  `Stacks.Coherent.properPushforwardCoherent`;
* full faithfulness, Stacks 0883, at every ideal sheaf in sight — on `X`
  (`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`), on the modification and on
  the subschemes (`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper`);
* Stacks 087T in both directions, which is what turns the induction hypothesis into hypothesis (1)
  of Stacks 088A;
* Stacks 088A itself,
  `Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower`, at
  hypotheses (1) and (2) only;
* and the induction itself, `Stacks.Algebraization.essImage_completionFunctor_of_devissage`, with
  the ascending chain condition on quasi-coherent ideal sheaves of a Noetherian scheme.

Two things are **not** available, and both are recorded here rather than papered over.

### Residual 1: Stacks 088B at a base which is not affine

`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage` carries
two binders beyond the source's. One of them, `hff`, is discharged below. The other,

`halg : (completionFunctor Y 𝒥).essImage G`,

is Grothendieck existence over the *base* `Y` at the one system `G`, and it stands — as the module
docstring of `CompletionProper/PullbackCompletion.lean` records — for the first two paragraphs of
the source's proof of Stacks 088B: the uniqueness of `α`, which makes its construction local on `Y`
so that `Y` may be taken affine, and the flat base change along `B ⟶ B ^∧`. Over an affine base
complete along `𝒥` the binder is a theorem
(`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`, Stacks 087W); the reduction to
such a base is not formalized.

In the dévissage that binder is asked at `Y = X` and `G = (𝓕_n)`, the system being algebraized. So
it is the conclusion of Stacks 088C itself, and the route through
`exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage` **cannot** discharge
`hDev`: not because the dévissage is circular — it is not; the source's 088B is a theorem — but
because the one input of 088B that this library replaces by a binder is exactly the one the
dévissage cannot supply. Formalizing the source's reduction of 088B to an affine base is therefore
the prerequisite for 088C, and nothing weaker will do.

### Residual 2: the order of the ideal sheaves at which hypothesis (1) is consumed

This is the sharper finding, and it is about the shape of the induction rather than about a missing
lemma.

Hypothesis (1) of Stacks 088A, as the tag states it and as
`Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower` takes it, is
about the subschemes `V(𝒦 ᵉ⁺¹)` cut out by the **powers** of the single ideal sheaf `𝒦` that the
comparison `α` is annihilated along. On `X`, the only route from the dévissage's induction
hypothesis to that hypothesis is
`Stacks.Algebraization.isEquivalence_completionFunctor_comap_subschemeι_of_essImage`, which
consumes the statement at `𝒦 ᵉ⁺¹`. The antecedent of `hDev` supplies it only at ideal sheaves
**strictly larger** than `K`. So the side condition is

`∀ e : ℕ, K < 𝒦 ^ (e + 1)`,

which appears as `hpow` below. It cannot be arranged. Powers decrease — `𝒦 ᵉ⁺¹ ≤ 𝒦` — so the whole
family sits below `𝒦`, and the condition asks `K` to lie strictly below a descending chain, whereas
the Chow step's `𝒦` is the ideal sheaf cutting out the complement of the dense open on which the
modification is an isomorphism and bears no relation to `K` at all. At `K = ⊤` the condition is
unsatisfiable outright: there is no ideal sheaf above `⊤`, let alone a power of one, and `hDev`
quantifies over `⊤` like any other ideal sheaf.

The source does not run into this, because it does not run the comparison on `X`. Its inductive
step begins *"after replacing `X` by the closed subscheme of `X` corresponding to `𝒦` we may assume
that every nonzero `𝒦` is in `Ξ`"*, and only then applies Chow's lemma. Its `𝒦` is thus an ideal
sheaf of `V(K)`, not of `X`, and the ideal sheaves at which hypothesis (1) is consumed are the
**inverse images in `X` of the powers `𝒦 ᵉ⁺¹ ⊆ 𝒪_{V(K)}`** — equivalently the joins `K ⊔ 𝒦₀ ᵉ⁺¹`
for a lift `𝒦₀`, and *not* the powers `(K ⊔ 𝒦₀) ᵉ⁺¹` of any ideal sheaf of `X`. That family lies
above `K` by construction (`le_sup_left`) and strictly above it exactly when the member is not
already below `K` (`left_lt_sup`), which on `V(K)` is the nonvanishing of `𝒦 ᵉ⁺¹` — and that is
where the density of the open and the reducedness of its complement enter the source's argument.

So the orders do line up, on the join family, and they do not line up on the family of powers. The
consequence for the formalization is structural: `hDev` cannot be discharged by applying Stacks
088A on `X`. It has to be discharged by applying Stacks 088A **on `V(K)`**, with the morphism
`K.subschemeι ≫ f`, and transporting the conclusion back along Stacks 087T — the same reduction
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver` already performs for Stacks 088E,
whose own `hDev` is asked on `K.subscheme` rather than at an ideal sheaf of `X`. The theorem below
is the step in the position the source occupies *after* its replacement, where the ideal sheaf
being inducted on is `⊥` and `hpow` reads `∀ e, ⊥ < 𝒦 ᵉ⁺¹`, i.e. that no power of `𝒦` vanishes.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### Stacks 088B at a base ideal sheaf -/

/-- **Stacks 088B at a base ideal sheaf, with full faithfulness discharged.** Let `A` be a
Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper, set `𝓘 = I · 𝒪_X`,
let `π : X' ⟶ X` be proper and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. Given a coherent
`𝒪_{X'}`-module `𝓕`, an object `G` of `Coh(X, 𝓘)`, the source's isomorphism

`β : π^*G ≅ 𝓕 ^∧`

in `Coh(X', (𝓘).comap π)` and the condition `hc` in which the source uses that `π` is an
isomorphism away from `V(𝒦)`, there is a morphism

`α : G ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦` — the pair of hypotheses
`α` and `hα` that Stacks 088A consumes.

This is `Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`
with its binder `hff` discharged. That binder asks for full faithfulness of completion on `X'`
along `(𝓘).comap π`, and
`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper` proves it: the
identification of `(𝓘).comap π` with the base ideal sheaf of `π ≫ f` is
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`, after which Stacks 0883 for the proper
morphism `π ≫ f` applies.

The remaining binder `halg` — essential surjectivity of completion over the base `X` at `G`,
standing for the source's reduction of Stacks 088B to an affine base — is discussed in the module
docstring. It is the reason this statement does not discharge the `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`: in the dévissage it is asked
at the system being algebraized, and is then the conclusion of Stacks 088C itself. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f]
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (baseIdealSheaf A I f))
    (halg : (completionFunctor X (baseIdealSheaf A I f)).essImage G)
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj G ≅
      (completionFunctor X' ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (G ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower 𝒦 α :=
  exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage π
    (baseIdealSheaf A I f) 𝒦 𝓕 G halg
    (fullyFaithful_completionFunctor_comap_of_isProper A I f π) β hc

/-! ### Stacks 088A fed by the dévissage's induction hypothesis -/

/-- **The comparison step of the dévissage of Stacks 088C.** Let `A` be a Noetherian ring complete
with respect to `I`, let `f : X ⟶ Spec A` be proper and set `𝓘 = I · 𝒪_X`. Let `K` be the
quasi-coherent ideal sheaf being inducted on and `𝒦` the one along which the comparison of the
Chow step is annihilated, and suppose

* `hpow`, that every power `𝒦 ᵉ⁺¹` is **strictly larger** than `K`, and
* `hInd`, the antecedent of `hDev`: every coherent `𝓘`-adic system killed by an ideal sheaf
  strictly larger than `K` is in the essential image of the completion functor.

Then any object `(𝓕_n)` of `Coh(X, 𝓘)` admitting the comparison data of Stacks 088A — a coherent
`𝒪_X`-module `𝓗` and a map `α : (𝓕_n) ⟶ 𝓗 ^∧` whose levelwise kernels and cokernels are
annihilated by a power of `𝒦` — is in the essential image.

Everything beyond the two hypotheses is proved. Hypothesis (1) of Stacks 088A is assembled from
`hInd` by `Stacks.Algebraization.isEquivalence_completionFunctor_comap_subschemeι_of_essImage`,
whose full-faithfulness half is unconditional (Stacks 0883 on the subscheme) and whose essential
surjectivity is the induction hypothesis read through Stacks 087T; `hpow` is what lets `hInd` be
applied at `𝒦 ᵉ⁺¹`. Noetherianity of `X` is not assumed: local Noetherianity comes from
`LocallyOfFiniteType f` over the Noetherian base and quasi-compactness from the universal
closedness of `f`.

**`hpow` is a condition on the data, and it is where the dévissage parts company with the source.**
Powers decrease, so the family `𝒦 ᵉ⁺¹` lies below `𝒦` while `hInd` lives strictly above `K`; the
Chow step's `𝒦` cuts out the complement of a dense open and bears no relation to `K`. The source
avoids this by replacing `X` by `V(K)` before applying Chow's lemma, so that its `𝒦` is an ideal
sheaf of `V(K)` and the ideal sheaves at which hypothesis (1) is consumed are the inverse images in
`X` of the powers of that `𝒦` — the joins `K ⊔ 𝒦₀ ᵉ⁺¹`, which lie above `K` by construction, and
not the powers of any ideal sheaf of `X`. This statement is therefore the step in the position the
source occupies after that replacement, where `K = ⊥` and `hpow` reads `∀ e, ⊥ < 𝒦 ᵉ⁺¹`, i.e. that
no power of `𝒦` vanishes. See the module docstring. -/
public theorem essImage_completionFunctor_of_devissageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (K 𝒦 : X.IdealSheafData) (hpow : ∀ e : ℕ, K < 𝒦 ^ (e + 1))
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f))
      (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (α : 𝓕.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj H).obj),
      IsKernelCokernelAnnihilatedByPower 𝒦 α →
        (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  intro 𝓕 H α hα
  refine essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower
    (baseIdealSheaf A I f) 𝒦 𝓕 (fun e => ?_) H (ObjectProperty.homMk α) hα
  exact isEquivalence_completionFunctor_comap_subschemeι_of_essImage A I f 𝒦 e
    (hInd (𝒦 ^ (e + 1)) (hpow e))

end Stacks.Algebraization

end
