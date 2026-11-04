module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicFibreSectionsSurjective
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.FibreLayerVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# Assertion (B) of [Stacks, Tag 0D2M] over a local base: sections restrict onto the fibre

[Stacks, Tag 0D2M] is Lemma 30.21.3, and its statement is **not** split into numbered parts.
Under the hypotheses that `f : X ⟶ Y` is proper with `Y` Noetherian, `ℒ` is an invertible
`𝒪_X`-module, `ℱ` is a coherent `𝒪_X`-module and `y ∈ Y` is a point at which `ℒ_y` is ample on
the fibre `X_y`, it asserts that there is a `d₀` such that for every `d ≥ d₀` **both** of

* **(A)** `R ᵖ f_*(ℱ ⊗_{𝒪_X} ℒ ^⊗ d)_y = 0` for `p > 0`, and
* **(B)** `f_*(ℱ ⊗_{𝒪_X} ℒ ^⊗ d)_y ⟶ H⁰(X_y, ℱ_y ⊗_{𝒪_{X_y}} ℒ_y ^⊗ d)` is surjective

hold. The items numbered (1) and (2) *inside* the source's proof are different statements — the
vanishing of `H ᵖ(X, ℱ / 𝔪 ⁿ ℱ ⊗ ℒ ^⊗ d)`, and the surjectivity of
`H⁰(X, ℱ / 𝔪 ⁿ ℱ ⊗ ℒ ^⊗ d) ⟶ H⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` for `n ≥ 1` — and are not clauses of the
tag; nothing below is stated in terms of them.

**This file proves assertion (B)**, in the situation the source's first paragraph reduces to:
`Y = Spec A` for a Noetherian local ring `(A, 𝔪, κ)` and `y` the closed point, so that
`f_*(ℱ ⊗ ℒ ^⊗ d)_y = H⁰(X, ℱ ⊗ ℒ ^⊗ d)` and the fibre `X_y` is the closed subscheme cut out by
`𝔪 𝒪_X`. Both assertions at a point of an arbitrary Noetherian base are
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist`
(`AmpleFibreTwistStalkSurjective.lean`, which carries the project's `@[stacks 0D2M]`). Assertion
(A) is not proved here: [Stacks, Tag 0D2N] does not use it.

The two rest on **one common input**: the vanishing of `H ᵖ` on the graded layers
`𝔪 ⁿ ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d)` with one exponent serving every `n` — there for every `p > 0`, here at
`p = 1`, which that one implies. It is now proved, from ampleness of `ℒ` on the fibre, by
`Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`
(`../GradedProperCohomology/FibreLayerVanishing.lean`), so neither carries any hypothesis beyond
the source's.

## Main results

* `Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` — assertion
  (B) over a local base, at the source's own hypotheses: `A` Noetherian local, `f` proper, `ℱ`
  coherent and `ℒ` ample on the fibre. One `d₀` serves every `d ≥ d₀` and

  `H⁰(X, ℱ(d)) ⟶ H⁰(X_y, ℱ(d)|_{X_y})`

  is surjective, the map being `H⁰` of the unit of `v^* ⊣ v_*` followed by the identification of
  the cohomology of a direct image along a closed immersion.

## How the fibre enters

The input from this tree is
`Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_one_of_isZero_kernel`: the
quotient projection induces a surjection `H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝓘 ℱ)`. Two
identifications turn that into assertion (B).

* `ℱ / 𝓘 ℱ ≅ v_* v^* ℱ` for a closed immersion `v` with ideal sheaf `𝓘` —
  `Stacks.Algebraization.idealQuotientPushforwardIso`, a corollary of [Stacks, Tag 08M3] (see the
  implementation notes on its citation) — together with its normalization
  `Stacks.Algebraization.idealQuotientPushforwardMap_π`, which says that the comparison composed
  after the quotient projection is exactly the unit of `v^* ⊣ v_*`. So the surjection above *is*
  `H⁰` of that unit.
* `H ᵖ(X, v_* 𝒢) ≅ H ᵖ(V, 𝒢)` for a closed immersion, which is
  `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`. It carries **no**
  quasi-coherence hypothesis, being the collapse of the derived composition against the
  exactness of `v_*`, so it is strictly stronger than the three `@[stacks 089W]` sites in the
  tree (all of which ask `[IsAffineHom]` and `[IsQuasicoherent]`) and is used in preference to
  them.

The closed immersion is left general — any `v : V ⟶ X` with `v.ker = 𝔪 𝒪_X` — rather than fixed
to one presentation of the fibre, so that a caller may supply whichever it has. The canonical
choice `v := (𝔪 𝒪_X).subschemeι` satisfies the hypothesis on the nose, by
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`. That its source is the fibre is
`Stacks.Cohomology.FormalFunctions.idealPowerSubschemeIsoPullback` at `I = 𝔪` and `n = 1`, which
identifies `(𝔪 𝒪_X ^ 1).subscheme` — the same subscheme, by `pow_one` — with
`X ×_{Spec A} Spec (A / 𝔪 ^ 1)`; `A / 𝔪` is the residue field at the closed point, so that fibre
product is `X_y`. The pullback `v^* (ℱ ⊗ ℒ ^⊗ d)` is then `ℱ_y ⊗_{𝒪_{X_y}} ℒ_y ^⊗ d`, the
pullback of modules being monoidal.

## Where the graded-layer vanishing comes from

The vanishing of `H¹` on the graded layers is the whole mathematical content of the source's
second paragraph: the uniformity of the exponent in `n` is what makes the dévissage run, and it
is where ampleness of `ℒ` on the fibre and the choice of `d₀` live. It is part (2) of
[Stacks, Tag 0897] on the fibre, applied to `⨁ₙ 𝔪 ⁿ ℱ / 𝔪 ⁿ⁺¹ ℱ` over the associated graded
algebra `Gr_𝔪(A)`, and it is proved as
`Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`
(`../GradedProperCohomology/FibreLayerVanishing.lean`). It takes the fibre as the closed
immersion `v : V ⟶ X` with ideal sheaf `𝔪 𝒪_X` lying properly over `Spec(A ⧸ 𝔪)` — the same `v`
this statement already carries — together with ampleness of `v ^* ℒ`, which is exactly the
source's hypothesis on the fibre; those are the data `g`, `hg`, `hsq` and `hL` below.

The dévissage consumes the layer vanishing on `X`, for `𝒪_X`-modules, while the engine concludes
on the fibre. `Stacks.Algebraization.kernelIdealPowerQuotientDropTwistReesIso` identifies the
transition kernel upstairs with the direct image of the twisted layer on the fibre — the layers
are killed by `𝔪 𝒪_X`, so each is such a direct image — and
`Stacks.Cohomology.FormalFunctions.isZero_rightDerived_pushforward_iff_isZero_hgroup` moves the
cohomology across; both steps are performed in the file named above and not here.

What separates the statement below from assertion (B) at the source's own hypotheses is the
source's first paragraph alone: the reduction of a general Noetherian base to `Spec 𝒪_{Y, y}` by
flat base change for the higher direct images ([Stacks, Tag 02KH]). It is not carried out here.
Accordingly **no `@[stacks 0D2M]` attribute is attached** — the tag's statement is the
conjunction of (A) and (B) at the source's hypotheses, and this is (B) over a local base.

## Implementation notes

**The citation of `Stacks.Algebraization.idealQuotientPushforwardIso` is corrected here and not
where it is declared.** Its own docstring and the module docs of
`../FormalGeometry/CompletionFullyFaithful/SectionsComplete.lean` and
`../FormalGeometry/QuotientComparison/Basic.lean` call it [Stacks, Tag 0EL1]. Tag 0EL1 is
Proposition 52.28.1, a Lefschetz statement: under a depth bound off a closed subscheme `Q`,
`H ⁱ(P, ℱ) ⟶ lim H ⁱ(Q_n, ℱ_n)` is an isomorphism for `i < σ`. That is not what the declaration
says. What it says is a corollary of [Stacks, Tag 08M3], Lemma 18.25.1: for a closed immersion of
ringed topoi with surjective `i ^♯` and `𝓘 = Ker(i ^♯)`, the functor `i_*` is exact and fully
faithful with essential image the `𝒪'`-modules killed by `𝓘` — which is exactly what the proof
there invokes, through `Stacks.ClosedImmersion.pushforward_essImage_iff` and
`fullyFaithfulPushforward`. Both tags were read at the source. The declaration is not touched,
since nothing about this file's statement needs it changed; the mis-citation is recorded for
adjudication.

**Why the hypotheses are the local-base ones rather than the general ones the proof needs.**
Nothing in the argument uses locality of `A` or maximality of `𝔪`: the statement below holds
verbatim for an arbitrary Noetherian `A` and an arbitrary ideal `I`, as its two inputs do
(`surjective_adicCohomologyProj_one_of_isZero_kernel` and
`Stacks.Algebraization.idealQuotientPushforwardIso` are both stated at that generality). It is
written with `[IsLocalRing A]` and `𝔪` so that it stands at exactly the hypotheses assertion (A)
stands at over a local base in `AmpleFibreTwistLocalBase.lean`, which is what a whole-tag reading of
[Stacks, Tag 0D2M] would need; locality is what makes `H⁰(X, −)` the stalk at `y` and `V` the
fibre, so dropping it would also drop the reading.

Cohomology is the degree-zero right derived functor of global sections, in the shape
`Stacks.Cohomology.FormalFunctions.adicCohomologyProj` produces it; the whole argument is
carried as `Epi` in `ModuleCat Γ(X, ⊤)` and converted to `Function.Surjective` only at the ends,
since `Epi` composes and an isomorphism is an `Epi` with no further argument. Restriction of
scalars along `A ⟶ Γ(X, ⊤)` changes neither carriers nor maps, so the surjectivity of the
`A`-linear map that the input provides and of the underlying `Γ(X, ⊤)`-linear map are the same
statement, and the input is used in the spelling it already has.

The tree has `moduleGlobalSections` twice — `Stacks.Cohomology.AffineBase.moduleGlobalSections`
(`../AffineCohomologyVanishing/AffineBase.lean`) and `AlgebraicGeometry.moduleGlobalSections`
(`../ModuleGlobalSections.lean`) — both `abbrev`s for
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`. No third copy is introduced here, and neither
is opened: both of this file's inputs speak the `AffineBase` spelling, which is therefore the one
written out, since with both in scope the bare name is ambiguous.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Algebraization Stacks.Ample Stacks.AlgebraicGeometry.HyperplaneTwistSequence

/-- **Assertion (B) of [Stacks, Tag 0D2M] over a local base.**

Let `(A, 𝔪)` be a Noetherian local ring, `f : X ⟶ Spec A` proper, `ℒ` an invertible `𝒪_X`-module
and `ℱ` a coherent `𝒪_X`-module; write `ℱ(d) = ℱ ⊗_{𝒪_X} ℒ ^⊗ d`. Let `v : V ⟶ X` be a closed
immersion with ideal sheaf `𝔪 𝒪_X`, that is, the fibre of `f` over the closed point. If `H¹` of
the graded layers `𝔪 ⁿ ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d)` vanishes for every `n` once `d` is large, then one
`d₀` serves every `d ≥ d₀` and

`H⁰(X, ℱ(d)) ⟶ H⁰(V, v^* ℱ(d))`

is surjective: `H⁰` of the unit of `v^* ⊣ v_*`, followed by the identification of the cohomology
of a direct image along a closed immersion with the cohomology upstairs.

Over `Spec A` with `y` the closed point the source's `f_*(ℱ(d))_y` is `H⁰(X, ℱ(d))` and
`H⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` is `H⁰(V, v^* ℱ(d))`, which is the reduction the source's first
paragraph makes.

Noetherianness of `A`, properness of `f` and coherence of `ℱ` are the source's own standing
hypotheses, and so is ampleness of `ℒ` on the fibre, which is `hL`. The source uses that
ampleness exactly to make `H ¹` of the graded layers `𝔪 ⁿ ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d)` vanish for large
`d`, with one exponent serving every `n`; that is part (2) of [Stacks, Tag 0897] at the fibre,
`Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist`,
and the choice of `d₀` lives there. -/
public theorem exists_surjective_fibreCohomology_twistModule
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : AlgebraicGeometry.IsProper f)
    (F L : X.Modules) [IsInvertibleModule X L] [F.IsCoherent]
    {V : Scheme.{u}} (v : V ⟶ X) [IsClosedImmersion v]
    (hv : v.ker = baseIdealSheaf A (IsLocalRing.maximalIdeal A) f)
    (g : V ⟶ Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A)))
    (hg : AlgebraicGeometry.IsProper g)
    (hsq : v ≫ f = g ≫ Stacks.ClosedImmersion.AffineConormal.quotImmersion
      (CommRingCat.of A) (IsLocalRing.maximalIdeal A))
    (hL : Stacks.Ample.IsAmple V ((Scheme.Modules.pullback v).obj L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Function.Surjective
        ((((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
            ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app
              (twistModule X L F d)) ≫
          (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward v
            ((Scheme.Modules.pullback v).obj (twistModule X L F d)) 0).hom).hom) := by
  have := hf
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have : PresheafOfModules.IsFiniteType (Opens.grothendieckTopology (X : TopCat)) F.val :=
    Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType F
      ‹_root_.SheafOfModules.IsCoherent F›.isFiniteType
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.GradedProperCohomology.exists_isZero_rightDerived_kernelIdealPowerQuotientDropTwist
      f F L v hv g hg hsq hL
  refine ⟨d₀, fun d hd => ?_⟩
  have hv' : v.ker = baseIdealSheaf A (IsLocalRing.maximalIdeal A) f ^ 1 := by
    rw [pow_one]; exact hv
  have hcoh : (twistModule X L F d).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
      (tensorPowModule X L d)
  have : (twistModule X L F d).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  -- The quotient projection `ℱ(d) ⟶ ℱ(d) / 𝔪 ℱ(d)` is surjective on `H⁰`.
  have : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
      (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) 1
          (twistModule X L F d)).ι)) :=
    (ModuleCat.epi_iff_surjective _).2
      (surjective_adicCohomologyProj_one_of_isZero_kernel A f hf
        (IsLocalRing.maximalIdeal A) (twistModule X L F d)
        ((Stacks.SheafOfModules.TensorOver.isCoherent_iff _).1 hcoh)
        (hd₀ d hd 1 Nat.one_pos))
  -- [Stacks, Tag 08M3] identifies that projection with the unit of `v^* ⊣ v_*`.
  have : IsIso (idealQuotientPushforwardMap
      (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) 1 (twistModule X L F d) v hv') :=
    isIso_idealQuotientPushforwardMap _ 1 _ v hv'
  have : Epi (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
      ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app (twistModule X L F d))) := by
    rw [← idealQuotientPushforwardMap_π
      (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) 1 (twistModule X L F d) v hv',
      Functor.map_comp]
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).1 (epi_comp _ _)

end Stacks.Cohomology.FormalFunctions

end
