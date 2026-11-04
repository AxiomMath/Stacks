module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffinePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ClauseThree.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.NoetherianDevissage
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic
public import StacksFrontier.AlgebraicGeometry.HighTwistVanishing.Devissage
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Stacks Tag 0B5V: ampleness and a finite surjective morphism

For a finite surjective morphism `f : Y ⟶ X` of schemes proper over a Noetherian ring `R` and an
invertible `𝒪_X`-module `L`, [Stacks, Tag 0B5V] asserts

> `L` is ample if and only if `f^* L` is ample.

**Both implications are proved here**, and
`Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback` states the biconditional at the
source's own hypothesis list, carrying the bare tag. The implication `⟹` is proved
**unconditionally and with none of the hypotheses of the source statement beyond finiteness of
`f`**, and keeps its own scoped clause
`"the implication `L` ample ⟹ `f^* L` ample"`, as the four scoped implications of
[Stacks, Tag 0B5U] do beside that tag's `"the three equivalent conditions"`. The implication `⟸`
is the source's cohomological argument, and every one of its five inputs is in the library; see "The
converse" below.

## Main definitions

* `Stacks.AmpleFiniteSurjective.PreimageAffineDescent`: affineness of an open of `X` descends from
  its preimage — the relative form of [Stacks, Tag 01YQ].
* `Stacks.AmpleFiniteSurjective.HasDescendingAffineNonvanishingOpens`: the nonvanishing opens of the
  *pulled back* global sections of the positive tensor powers of `L` are affine and cover `Y`.

Both belong to the second, non-cohomological reduction described below; neither is needed for the
biconditional, which is proved outright.

## Main results

* `Stacks.AmpleFiniteSurjective.isAmple_iff_isAmple_modulePullback`: **[Stacks, Tag 0B5V]**, the
  biconditional at the source's own hypothesis list. This is the declaration carrying the bare
  tag.
* `Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite`: **the implication `⟹`**, for
  any finite morphism of schemes and any ample invertible module, with no base, no properness and no
  surjectivity. Unconditional.
* `Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite_surjective`: the same at the
  hypothesis list of the source statement, so that it is literally the forward half of the
  source statement. This is the declaration carrying the scoped forward clause.
* `Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback`: **the implication `⟸`**, by
  the source's cohomological route.
* `Stacks.AmpleFiniteSurjective.hasHighTwistVanishing_of_isCoherent`: the dévissage conclusion
  that `⟸` consumes — every coherent `𝒪_X`-module has eventually vanishing higher twisted
  cohomology, which is clause (2) of [Stacks, Tag 0B5U] for `L`.
* `Stacks.AmpleFiniteSurjective.exists_coherent_generic_highTwist`: **clause (3) of
  [Stacks, Tag 01YM] for that property**, with `𝒢 = f_* ℱ`. This is the one step of the source's
  proof that is not already in the library, and the only new mathematics in this file.
* `Stacks.AmpleFiniteSurjective.hasHighTwistVanishing_pushforward` and
  `hasHighTwistVanishing_idealSmul_pushforward`: the transport of the vanishing from `Y` to `X`
  along `f`, by the projection formula [Stacks, Tag 01E8] and [Stacks, Tag 089W].
* `Stacks.AmpleFiniteSurjective.isAmple_of_isAmple_modulePullback_of_section`: the converse,
  unconditionally, when `f` admits a section. No cohomology and no Noetherian hypothesis; a
  genuinely smaller hypothesis list than the biconditional's, which is why it is kept.
* `Stacks.AmpleFiniteSurjective.isAmple_of_hasDescendingAffineNonvanishingOpens` and
  `isAmple_iff_isAmple_modulePullback_of_hasDescendingAffineNonvanishingOpens`:
  the converse from `PreimageAffineDescent` and `HasDescendingAffineNonvanishingOpens` alone,
  the second reduction. Both are now subsumed by the unconditional results above.
* `Stacks.AmpleFiniteSurjective.hasDescendingAffineNonvanishingOpens_of_isAmple`: the second of
  those two premises follows from the conclusion. Unconditional for any affine `f`.

## The forward implication, and why it is already finished

A finite morphism is affine (`AlgebraicGeometry.IsFinite` extends `IsIntegralHom`, which extends
`IsAffineHom`), and the pullback of an ample invertible module along an **affine** morphism is
ample unconditionally: that is
`Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom`, which is [Stacks, Tag 0892]
part (2) in the one case needing no input from [Stacks, Tag 01PW]. The source quotes exactly this
(Morphisms, Lemma 29.38.7) for the easy direction, so the route here is the source's. Neither
properness, nor surjectivity of `f`, nor the Noetherian ring is used.

## The converse: the source's route, with every input in the library

The source proves `⟸` by cohomology. Write `P(F)` for "there is `n₀` with
`Hᵖ(X, F ⊗ L^⊗ n) = 0` for all `n ≥ n₀` and all `p > 0`" on coherent `𝒪_X`-modules `F`; that is
`Stacks.HighTwistVanishing.HasHighTwistVanishing L F`. Then

1. [Stacks, Tag 0B5U] turns `P` on every coherent module into ampleness of `L`, and conversely
   reads ampleness of `f^* L` as `P` on every coherent `𝒪_Y`-module;
2. [Stacks, Tag 01YM] — the cohomological dévissage — reduces `P` to the case `G = f_* F`, using
   [Stacks, Tag 01YO] to produce a coherent `F` on `Y` whose pushforward is supported on a given
   integral closed subscheme with generic stalk killed by the maximal ideal;
3. for a quasi-coherent ideal `J ⊆ 𝒪_X`, [Stacks, Tag 01YP] identifies `J · f_* F` with
   `f_*((f⁻¹ J) · F)`, and the projection formula [Stacks, Tag 01E8] together with
   [Stacks, Tag 089W] transports the vanishing from `Y` to `X`.

**All five inputs are in the library and tagged**, and `isAmple_of_isAmple_modulePullback` consumes them
as they stand:

* **[Stacks, Tag 0B5U]**, both directions the converse consumes:
  `AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple` for
  `(1) ⟹ (2)` (`../AmpleDegreeCriterion/CohomologicalCriterion.lean:145`) and
  `isAmple_of_eventualTwistVanishing` for `(2) ⟹ (1)` (`:187`).
* **[Stacks, Tag 01YM]**: `Stacks.AlgebraicGeometry.NoetherianDevissage.property_higher_rank`
  (`../CoherentDevissage/NoetherianDevissage.lean:90`).
* **[Stacks, Tag 01YO]**: `exists_isCoherent_supp_pushforward_eq_range` in
  `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport`
  (`../FiniteSurjectiveCoherentSupport/Basic.lean:352`).
* **[Stacks, Tag 01YP]**:
  `Stacks.AlgebraicGeometry.AffineIdealPushforward.ideal_smul_pushforward_sections_eq`
  (`../Cohomology/IdealPushforwardAffine.lean:157`), promoted from an equality of section
  submodules to one of subsheaves by
  `Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq`.
* **[Stacks, Tag 01E8]**: `Stacks.ProjectionFormula.pushforwardTensorRightNatIso`, the
  degree-zero clause for an invertible module
  (`../ProjectionFormula/HigherDirectImage.lean:221`).
* **[Stacks, Tag 089W]**: `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso`
  (`../AffineHigherDirectImage/Natural.lean:251`), with `cohomologyPushforwardIsoApp` (`:268`)
  the component at a single quasi-coherent module.

Of the dévissage's four hypotheses, three are discharged for `P` with no geometry by
`Stacks.HighTwistVanishing.terminal`, `of_shortExact` and `of_finiteProduct`, which
`Stacks.HighTwistVanishing.forall_of_hgeneric` feeds to the 01YM engine. **So the one step this
file adds is clause (3)** — `exists_coherent_generic_highTwist`. It is the same construction as
`Stacks.AlgebraicGeometry.Tag01YQClauseThree.exists_coherent_generic_of_isFinite_surjective`,
clause (3) for the property `H¹(X, -) = 0`, with two differences: `Y` need not be affine, only
Noetherian, which is what properness over `R` gives; and the last clause is `P(𝒥 · 𝒢)` rather
than `H¹(X, 𝒥 · 𝒢) = 0`.

That last clause is `hasHighTwistVanishing_idealSmul_pushforward`, and it is where the projection
formula enters. Only the **degree-zero** clause of [Stacks, Tag 01E8] is used, not the higher
direct images: `𝒥 · f_* ℱ` is a direct image by [Stacks, Tag 01YP], so the twist is moved inside
it by `f_*(ℳ ⊗ f^* 𝒢) ≅ (f_* ℳ) ⊗ 𝒢`, and [Stacks, Tag 089W] then reads the cohomology on `Y`,
where ampleness of `f^* L` and Serre vanishing ([Stacks, Tag 0B5T] clause (4),
`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`) make it
vanish. That transport is `hasHighTwistVanishing_pushforward`, stated for an arbitrary affine
morphism and an arbitrary quasi-coherent module.

## A second reduction, not the source's, now subsumed

Ampleness is a statement about affine nonvanishing opens, and two facts about those are available:
[Stacks, Tag 0H78] in the form `Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`
(`Y_{f^* s} = f⁻¹(X_s)` as opens), and
`Stacks.AmpleTheory.isAmple_iff_forall_affine_nonvanishingOpen` (ampleness is exactly
quasi-compactness plus an affine `X_s` through every point). Together they turn the converse into
two separate statements, `PreimageAffineDescent` and `HasDescendingAffineNonvanishingOpens`, and
`isAmple_of_hasDescendingAffineNonvanishingOpens` discharges the converse from them. This locates
the converse's difficulty sharply: the geometric half is affineness descending along a finite
surjective morphism, and the arithmetic half is that the sections realizing ampleness of `f^* L`
may be taken to be pullbacks of sections on `X`. The cohomological route of the source produces
the second of those; nothing cheaper does.

Both premises are statements the source statement does not make, so nothing in this section carries
the tag.

## What is not done

**Nothing of [Stacks, Tag 0B5V] is outstanding.** Both implications are proved at the source's
hypothesis list and `isAmple_iff_isAmple_modulePullback` carries the bare tag.

What this file does *not* settle is the geometric statement
`PreimageAffineDescent` — the relative form of [Stacks, Tag 01YQ], which is open in general
(`Stacks.AlgebraicGeometry.Tag01YQGenericStalk.isAffine_of_isFinite_surjective`,
`../ClauseThree/GenericStalkInput.lean:73`, carries the bare `@[stacks 01YQ]` under two
hypotheses). The converse above does not go through it.

**No tag is withheld on a formality.** Both halves are proved at the source's hypothesis list,
and the only substitutions are two spellings: Tag 01PS's `IsAmple X L` is
`Stacks.Ample.IsAmple X L`, and the invertibility instance, Tag 01CS's
`IsInvertible X.toRingedSpace.sheaf.obj (structureSheaf X.toRingedSpace.sheaf).property L`,
is `Stacks.Ample.IsInvertibleModule X L`. Rebuilding invertibility of the pullback through
Tag 0B8L's `Stacks.RingedSpace.modulePullback_isInvertible` with a `letI` block is
unnecessary here: `Stacks.InvertiblePullback.isInvertibleModule_pullback`
(`../InvertiblePullback/Basic.lean:196`) is a global instance, so the right-hand side elaborates
with nothing written down. No transparency option is needed either.

## Implementation notes

**Invertibility of `(f^* L)^{\otimes n}` has to be written down, and invertibility of `f^* L`
does not.** Instance search finds
`Stacks.InvertiblePullback.isInvertibleModule_pullback` for `f^* L`, and finds
`Stacks.Ample.isInvertibleModule_tensorPowModule` for `L^{\otimes n}`, but it does not chain the
two: `IsInvertibleModule Y (Stacks.Ample.tensorPowModule Y (f^* L) n)` fails to synthesize even
with the pullback's invertibility seated as a local instance, while
`Stacks.Ample.isInvertibleModule_tensorPowModule Y _ n` closes it as a term. So the instance is
seated by hand, once, at the top of `hasHighTwistVanishing_pushforward`, before the
quasi-coherence of the twist is asked for.

**The quasi-coherence instance on `f_* ℱ` is never named**, following
`../ClauseThree/Basic.lean`: `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` takes that
instance as an argument, so a local `have` for it would make the subsheaf in the goal a different
term from the one in the conclusions of
`Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq` and of
`Stacks.AlgebraicGeometry.Tag01YQClauseThree.surjective_stalk_idealPowSmul_of_notMem_support`.
For the same reason `hasHighTwistVanishing_idealSmul_pushforward` takes `[ℱ.IsQuasicoherent]` as
a binder rather than deriving it from coherence inside the proof: the statement mentions
`idealPowSmul J 1 (f_* ℱ)` and so needs the instance before the proof begins.

**No comparison morphism is built anywhere.** `Stacks.RelativeVeryAmple.tensorModules X A B` is an
`abbrev` for the tensor product `Stacks.HighTwistVanishing.HasHighTwistVanishing` and clause (4)
of [Stacks, Tag 0B5T] are both stated over, and
`(Stacks.ProjectionFormula.tensorRightInvertible X B).obj A` is that same term on the nose, so the
projection formula applies to the stated form with nothing transported; likewise
`AlgebraicGeometry.Scheme.Modules.pullback f` and
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` agree by `rfl`. The only
transports in the converse are the two genuine isomorphisms `f_*(ℳ ⊗ f^* 𝒢) ≅ (f_* ℳ) ⊗ 𝒢` and
`f^*(L^{\otimes n}) ≅ (f^* L)^{\otimes n}`.

## Remarks on the inputs

Of the tags 01CD, 01CU and 0B8M, two are attached in the library:

* **tag 01CD** is attached twice — `../PullbackTensorIso/Invertible.lean:338` and
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean:361`;
* **tag 01CU** is attached seventeen times, including `../TensorPowerAssoc/SheafOfModules.lean:109`
  and `../SelfBraidingInvertible/TensorPowerScalar.lean:90`;
* 0B8M is attached twice (`../InvertibleRankOneIff/Basic.lean:132`, `:151`).

None of the three is in fact an input here: the statement needs 01CU's tensor powers and 0B8L's
invertible pullback, both of which the ampleness theory already supplies, and 0B8M is not used
at all.

Tag 0B8L is likewise attached (`../InvertiblePullback/Basic.lean:157`), so the dependence on
Tag 0B8L is satisfied by a proved statement.

## References

* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01YO](https://stacks.math.columbia.edu/tag/01YO)
* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleFiniteSurjective

section Forward

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The implication `⟹` of [Stacks, Tag 0B5V], unconditionally.** If `L` is an ample invertible
`𝒪_X`-module and `f : Y ⟶ X` is finite, then `f^* L` is ample.

A finite morphism is affine, and [Stacks, Tag 0892] part (2) for an affine morphism is proved with
no premise as `Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom`. None of the
source's further hypotheses — the Noetherian base ring, properness over it, surjectivity of `f` —
plays any part. -/
theorem isAmple_modulePullback_of_isFinite [IsFinite f] (hL : IsAmple X L) :
    IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L) :=
  Stacks.AmpleQuasiAffinePullback.isAmple_modulePullback_of_isAffineHom f L hL

/-- **The forward half of [Stacks, Tag 0B5V]**, at the source's hypothesis list: `X` proper over a
Noetherian ring `R`, `f` finite and surjective. The hypotheses other than finiteness are inert;
`Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite` is the same statement without
them. -/
@[stacks 0B5V "the implication `L` ample ⟹ `f^* L` ample"]
theorem isAmple_modulePullback_of_isFinite_surjective (R : Type u) [CommRing R]
    [IsNoetherianRing R] (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [Surjective f]
    (hL : IsAmple X L) :
    IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L) :=
  isAmple_modulePullback_of_isFinite f L hL

end Forward

section Retract

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The converse of [Stacks, Tag 0B5V] when `f` admits a section, unconditionally.** If
`s : X ⟶ Y` satisfies `s ≫ f = 𝟙 X` and `f` is finite, then ampleness of `f^* L` gives ampleness
of `L`, with no cohomology, no Noetherian hypothesis and no properness.

`s` is finite by `AlgebraicGeometry.IsFinite.of_comp`, because `s ≫ f` is the identity and `f`,
being affine, is separated; hence `s` is affine and the forward implication applies to it, making
`s^* f^* L` ample. Pseudofunctoriality of the module pullback
(`Stacks.PullbackPseudofunctor.modulePullbackCompIso` and `modulePullbackIdIso`) identifies that
module with `L`, and ampleness is an isomorphism invariant
(`Stacks.RelativeVeryAmple.isAmple_congr`).

This is a genuine special case and not a route to the general one: a finite surjective morphism
admits no section in general, and the source's cohomological argument exists precisely because of
that. -/
theorem isAmple_of_isAmple_modulePullback_of_section [IsFinite f] (s : X ⟶ Y)
    (hs : s ≫ f = 𝟙 X)
    (h : IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L)) :
    IsAmple X L := by
  -- `s` is finite, hence affine: `s ≫ f = 𝟙 X` is finite and `f` is separated.
  have hsf : IsFinite (s ≫ f) := by rw [hs]; infer_instance
  have : IsFinite s := IsFinite.of_comp s f
  -- Invertibility of the iterated pullback, supplied in one step at a time: instance search
  -- resolves `Stacks.InvertiblePullback.isInvertibleModule_pullback` once but not twice.
  have hinvY : IsInvertibleModule Y ((modulePullback f.toLRSHom.toShHom).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback f L
  have hinvX : IsInvertibleModule X ((modulePullback s.toLRSHom.toShHom).obj
      ((modulePullback f.toLRSHom.toShHom).obj L)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback s _
  -- The forward implication, applied to `s`, makes `s^* (f^* L)` ample.
  have h' : IsAmple X ((modulePullback s.toLRSHom.toShHom).obj
      ((modulePullback f.toLRSHom.toShHom).obj L)) :=
    isAmple_modulePullback_of_isFinite s _ h
  -- Pseudofunctoriality identifies `s^* (f^* L)` with `(s ≫ f)^* L = L`.
  have hid : (s ≫ f).toLRSHom.toShHom = 𝟙 _ := by rw [hs]; rfl
  have e : (modulePullback s.toLRSHom.toShHom).obj
      ((modulePullback f.toLRSHom.toShHom).obj L) ≅ L :=
    ((Stacks.PullbackPseudofunctor.modulePullbackCompIso
          f.toLRSHom.toShHom s.toLRSHom.toShHom).app L).symm ≪≫
      (eqToIso (congrArg (fun g => (modulePullback g).obj L) hid)) ≪≫
      (Stacks.PullbackPseudofunctor.modulePullbackIdIso _).app L
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp h'

end Retract

section Reduction

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **Affineness of an open of `X` descends along `f`.** This is the relative form of
[Stacks, Tag 01YQ] — a Noetherian scheme receiving a finite surjective morphism from an affine
scheme is affine — applied to the open subschemes of `X`, which is how the converse of
[Stacks, Tag 0B5V] would consume it.

Nothing in this repository proves it: `../ChevalleyAffine/Basic.lean` reduces Tag 01YQ to
`Stacks.AlgebraicGeometry.ChevalleyAffine.isAffine_of_isQuasiAffine_of_isIntegral_appTop`, which
carries two hypotheses Tag 01YQ does not have (quasi-affineness of the target, and integrality of
the ring map on global sections). -/
def PreimageAffineDescent : Prop :=
  ∀ V : X.Opens, IsAffineOpen (f ⁻¹ᵁ V) → IsAffineOpen V

/-- **The nonvanishing opens of the pulled-back sections are affine and cover `Y`.** For every
point of `Y` there are `n ≥ 1` and a global section `s` of `L ^⊗ n` *on `X`* such that the point
lies in `Y_{f^* s}` and that open is affine.

It differs from ampleness of `f^* L` in exactly one respect, and that respect is the whole
difficulty: ampleness of `f^* L` supplies affine nonvanishing opens of *arbitrary* global sections
of `(f^* L) ^⊗ n`, whereas this asks for them at sections *pulled back from `X`*. It is implied by
ampleness of `L`, by [Stacks, Tag 0H78] together with the affineness of the preimage of an affine
open under an affine morphism. Producing it from ampleness of `f^* L` alone is what the source's
cohomological argument does. -/
def HasDescendingAffineNonvanishingOpens : Prop :=
  ∀ y : Y, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
    y ∈ powNonvanishingOpen Y ((modulePullback f.toLRSHom.toShHom).obj L) n
        (Stacks.NonvanishingPullback.pullbackPowSection f L n s) ∧
      IsAffineOpen (powNonvanishingOpen Y ((modulePullback f.toLRSHom.toShHom).obj L) n
        (Stacks.NonvanishingPullback.pullbackPowSection f L n s))

/-- **Ampleness of `L` gives `Stacks.AmpleFiniteSurjective.HasDescendingAffineNonvanishingOpens`**,
for any finite — indeed any affine — `f`. So that premise is genuinely only the converse's gap, and
not an extra assumption smuggled into the biconditional below: in the presence of the conclusion it
is automatic.

The affine `X_s` through `f y` comes from ampleness
(`Stacks.AmplePullback.exists_mem_powNonvanishingOpen_pullbackPowSection`, which already combines
that with [Stacks, Tag 0H78]), and its preimage is affine because `f` is
(`AlgebraicGeometry.IsAffineOpen.preimage`). -/
theorem hasDescendingAffineNonvanishingOpens_of_isAmple [IsAffineHom f] (hL : IsAmple X L) :
    HasDescendingAffineNonvanishingOpens f L := by
  intro y
  obtain ⟨n, hn, s, haff, hmem⟩ :=
    Stacks.AmplePullback.exists_mem_powNonvanishingOpen_pullbackPowSection f L hL y
  refine ⟨n, hn, s, hmem, ?_⟩
  rw [Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection f L n s]
  exact haff.preimage f

/-- **The converse of [Stacks, Tag 0B5V] from the two named premises.** For `f` surjective and `X`
quasi-compact, `Stacks.AmpleFiniteSurjective.PreimageAffineDescent` together with
`Stacks.AmpleFiniteSurjective.HasDescendingAffineNonvanishingOpens` gives ampleness of `L`.

Given `x : X`, surjectivity produces `y` above it; the second premise produces `n ≥ 1` and `s` with
`y ∈ Y_{f^* s}` affine; [Stacks, Tag 0H78] in the form
`Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection` identifies `Y_{f^* s}` with
`f⁻¹(X_s)`, so the first premise makes `X_s` affine, and `x = f y` lies in it. That is clause (4) of
[Stacks, Tag 01Q3] at the ambient open, which is ampleness by
`Stacks.AmpleTheory.isAmple_iff_forall_affine_nonvanishingOpen`. -/
theorem isAmple_of_hasDescendingAffineNonvanishingOpens [Surjective f] [CompactSpace X]
    (hdesc : PreimageAffineDescent f)
    (hsec : HasDescendingAffineNonvanishingOpens f L) :
    IsAmple X L := by
  refine (isAmple_iff_forall_affine_nonvanishingOpen X L).mpr ⟨inferInstance, fun x => ?_⟩
  obtain ⟨y, hy⟩ := f.surjective x
  obtain ⟨n, hn, s, hmem, haff⟩ := hsec y
  rw [Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection f L n s] at hmem haff
  exact ⟨n, hn, s, hdesc _ haff, hy ▸ hmem⟩

/-- **[Stacks, Tag 0B5V] in full, from the two named premises**, at the hypothesis list of the
source statement: `X` proper over a Noetherian ring `R`, `f` finite and surjective. The forward
implication is unconditional
(`Stacks.AmpleFiniteSurjective.isAmple_modulePullback_of_isFinite`); the converse is
`Stacks.AmpleFiniteSurjective.isAmple_of_hasDescendingAffineNonvanishingOpens`.

Quasi-compactness of `X`, which the reduction needs, is *not* an extra hypothesis: a universally
closed morphism is quasi-compact in Mathlib (`AlgebraicGeometry.UniversallyClosed` gives
`QuasiCompact`), so `IsProper p` makes `X` compact over the compact `Spec R`, by
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`. That is the only use the
properness assumption gets here. -/
theorem isAmple_iff_isAmple_modulePullback_of_hasDescendingAffineNonvanishingOpens
    (R : Type u) [CommRing R] [IsNoetherianRing R] (p : X ⟶ Spec (.of R)) [IsProper p]
    [IsFinite f] [Surjective f]
    (hdesc : PreimageAffineDescent f)
    (hsec : HasDescendingAffineNonvanishingOpens f L) :
    IsAmple X L ↔ IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨isAmple_modulePullback_of_isFinite f L,
    fun _ => isAmple_of_hasDescendingAffineNonvanishingOpens f L hdesc hsec⟩

end Reduction

section Converse

open CategoryTheory.Limits Opposite
open Stacks.HighTwistVanishing
open Stacks.AlgebraicGeometry

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **A tensor product of quasi-coherent modules is quasi-coherent**, at the spelling
`Stacks.HighTwistVanishing.HasHighTwistVanishing` is stated over.
`Stacks.RelativeVeryAmple.tensorModules Z A B` is the ringed-space tensor product on the nose, so
this is `AlgebraicGeometry.tensorSheaf_isQuasicoherent`; it is a theorem rather than an instance
because the instance of that name is keyed on the ringed-space spelling and does not fire through
the `abbrev`. -/
theorem isQuasicoherent_tensorModules {Z : Scheme.{u}} (A B : Z.Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] :
    (Stacks.RelativeVeryAmple.tensorModules Z A B).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent Z.toRingedSpace A B ‹_› ‹_›

/-- **Eventual vanishing of the higher twisted cohomology travels along an affine morphism.** For
`f : Y ⟶ X` affine and `ℳ` a quasi-coherent `𝒪_Y`-module, if the twists of `ℳ` by the powers of
`f^* L` eventually have no higher cohomology on `Y`, then the twists of `f_* ℳ` by the powers of
`L` eventually have none on `X`, with the same bound.

Three results from the library and nothing else. For each `n` and each `q > 0`:

* the degree-zero projection formula for an invertible module, [Stacks, Tag 01E8] in the form
  `Stacks.ProjectionFormula.pushforwardTensorRightNatIso`, gives
  `f_*(ℳ ⊗ f^*(L ^⊗ n)) ≅ (f_* ℳ) ⊗ L ^⊗ n`;
* [Stacks, Tag 01CU] in the form `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` rewrites
  `f^*(L ^⊗ n)` as `(f^* L) ^⊗ n` inside it;
* [Stacks, Tag 089W], `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`, identifies
  `H q(X, f_* 𝒩)` with `H q(Y, 𝒩)` for the quasi-coherent `𝒩 = ℳ ⊗ (f^* L) ^⊗ n`.

No hypothesis on `X` or `Y`, and no coherence. -/
theorem hasHighTwistVanishing_pushforward [IsAffineHom f] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : HasHighTwistVanishing ((modulePullback f.toLRSHom.toShHom).obj L) M) :
    HasHighTwistVanishing L ((Scheme.Modules.pushforward f).obj M) := by
  obtain ⟨n₀, hn₀⟩ := hM
  refine ⟨n₀, fun n q hn hq => ?_⟩
  -- Instance search finds neither this nor the quasi-coherence that follows from it; see the
  -- implementation notes.
  have hinvpow : IsInvertibleModule Y
      (tensorPowModule Y ((modulePullback f.toLRSHom.toShHom).obj L) (n : ℤ)) :=
    isInvertibleModule_tensorPowModule Y _ (n : ℤ)
  have _ : ((modulePullback f.toLRSHom.toShHom).obj L).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have _ : (tensorPowModule Y ((modulePullback f.toLRSHom.toShHom).obj L)
      (n : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have hNq : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj M).obj
        (tensorPowModule Y ((modulePullback f.toLRSHom.toShHom).obj L) (n : ℤ))) :=
    isQuasicoherent_tensorModules (Z := Y) M
      (tensorPowModule Y ((modulePullback f.toLRSHom.toShHom).obj L) (n : ℤ))
  have e1 : Stacks.RelativeVeryAmple.tensorModules X ((Scheme.Modules.pushforward f).obj M)
        (tensorPowModule X L (n : ℤ)) ≅
      (Scheme.Modules.pushforward f).obj
        (Stacks.RelativeVeryAmple.tensorModules Y M
          ((modulePullback f.toLRSHom.toShHom).obj (tensorPowModule X L (n : ℤ)))) :=
    ((Stacks.ProjectionFormula.pushforwardTensorRightNatIso f
      (tensorPowModule X L (n : ℤ))).app M).symm
  have e2 : Stacks.RelativeVeryAmple.tensorModules Y M
        ((modulePullback f.toLRSHom.toShHom).obj (tensorPowModule X L (n : ℤ))) ≅
      Stacks.RelativeVeryAmple.tensorModules Y M
        (tensorPowModule Y ((modulePullback f.toLRSHom.toShHom).obj L) (n : ℤ)) :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl M)
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f L n)
  refine ((hn₀ n q hn hq).of_iso
    (Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp f q _).symm).of_iso
      ((Hfunctor X.ringCatSheaf ⊤ q).mapIso
        (e1 ≪≫ (Scheme.Modules.pushforward f).mapIso e2))

/-- `𝒥 · f_* ℱ` is the direct image of the coherent module `(f⁻¹𝒥) · ℱ` on a Noetherian `Y`. -/
private theorem exists_idealPowSmul_pushforward_eq [IsFinite f] [IsNoetherian Y]
    (J : X.IdealSheafData) (F : Y.Modules) [F.IsQuasicoherent] [F.IsCoherent] :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧ M.IsCoherent ∧
      (IdealPowerSmul.idealPowSmul J 1
        ((Scheme.Modules.pushforward f).obj F)).toSheafOfModules =
        (Scheme.Modules.pushforward f).obj M :=
  ⟨_, IdealPowerSmul.isQuasicoherent_idealPowSmul (J.comap f) 1 F,
    IdealPowerSmul.isCoherent_idealPowSmul (J.comap f) 1 F,
    by
      rw [PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq f J F,
        PushforwardIdealSubsheaf.toSheafOfModules_pushforwardSubmodule]⟩

/-- **Clause (3)(c) of [Stacks, Tag 01YM] for the property the converse of [Stacks, Tag 0B5V]
verifies**: for `ℱ` coherent on `Y` and `𝒥` a quasi-coherent sheaf of ideals on `X`, the subsheaf
`𝒥 · f_* ℱ` has eventually vanishing higher twisted cohomology.

This is the source's computation, verbatim. [Stacks, Tag 01YP] makes `𝒥 · f_* ℱ` the direct image
of `(f⁻¹𝒥) · ℱ` — as an equality of subsheaves, by
`Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq`, whose right-hand
side is a direct image on the nose — that module is coherent on the Noetherian `Y`, so ampleness
of `f^* L` and Serre vanishing (clause (4) of [Stacks, Tag 0B5T]) give the vanishing upstairs, and
`hasHighTwistVanishing_pushforward` brings it down. -/
theorem hasHighTwistVanishing_idealSmul_pushforward {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [IsNoetherian Y]
    (hL : IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L))
    (J : X.IdealSheafData) (F : Y.Modules) [F.IsQuasicoherent] [F.IsCoherent] :
    HasHighTwistVanishing L
      (IdealPowerSmul.idealPowSmul J 1
        ((Scheme.Modules.pushforward f).obj F)).toSheafOfModules := by
  obtain ⟨M, _, _, hM⟩ := exists_idealPowSmul_pushforward_eq f J F
  rw [hM]
  exact hasHighTwistVanishing_pushforward f L _
    (ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist (f ≫ p) _ _ hL)

/-- **Clause (3) of the dévissage [Stacks, Tag 01YM] for the property the converse of
[Stacks, Tag 0B5V] verifies.** For every integral closed subscheme of `X` there is a coherent
`𝒢` with support exactly that subscheme, annihilated generic stalk, and — for every
quasi-coherent sheaf of ideals `𝒥` not vanishing at the generic point — a coherent subsheaf of
`𝒥 · 𝒢` which is generically surjective onto `𝒢` and has eventually vanishing higher twisted
cohomology.

`𝒢 = f_* ℱ` for the `ℱ` of [Stacks, Tag 01YO] and `𝒢' = 𝒥 · 𝒢`, exactly as in
`Stacks.AlgebraicGeometry.Tag01YQClauseThree.exists_coherent_generic_of_isFinite_surjective`,
which proves the same clause for the property `H¹(X, -) = 0`. The support clause is
[Stacks, Tag 01YO] together with the identification of `I.support` with the range of
`I.subschemeι`, the annihilation clause is [Stacks, Tag 01YO] character for character, the stalk
clause is `Tag01YQClauseThree.surjective_stalk_idealPowSmul_of_notMem_support`, the sections
clause is `IdealPowerSmul.obj_idealPowSmul` at `n = 1`, and the cohomological clause is
`hasHighTwistVanishing_idealSmul_pushforward`.

Coherence of `𝒢'` is reproved here rather than taken from
`PushforwardIdealSubsheaf.isCoherent_idealPowSmul_pushforward`, whose `IsAffine Y` serves only to
make `Y` Noetherian; here `Y` is Noetherian because it is proper over `R` through `f ≫ p`. -/
theorem exists_coherent_generic_highTwist {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [Surjective f] [IsNoetherian Y]
    [IsLocallyNoetherian X]
    (hL : IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L))
    (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    ∃ G : X.Modules, G.IsCoherent ∧
      (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
      Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
        (I.subschemeι (genericPoint I.subscheme)) ∧
      (∀ J : X.IdealSheafData,
        I.subschemeι (genericPoint I.subscheme) ∉ J.support →
        ∃ G' : G.Submodule,
          G'.toSheafOfModules.IsCoherent ∧
          (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
            (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
              J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
          Function.Surjective
            (((TopCat.Presheaf.stalkFunctor Ab
              (I.subschemeι (genericPoint I.subscheme))).map
                (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
          HasHighTwistVanishing L G'.toSheafOfModules) := by
  obtain ⟨F, hFcoh, hsupp, hann⟩ :=
    FiniteSurjectiveCoherentSupport.exists_isCoherent_supp_pushforward_eq_range f I.subschemeι
  have _ : F.IsCoherent := hFcoh
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine ⟨(Scheme.Modules.pushforward f).obj F,
    FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f F, fun x ↦ ?_, hann,
    fun J hJ ↦ ?_⟩
  · have hmem : x ∈ SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) ↔
        x ∈ I.support := by
      rw [hsupp]
      simp
    exact hmem.symm.trans (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x)
  · refine ⟨IdealPowerSmul.idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj F), ?_,
      fun U s ↦ ?_,
      Tag01YQClauseThree.surjective_stalk_idealPowSmul_of_notMem_support J 1 _ hJ,
      hasHighTwistVanishing_idealSmul_pushforward f L p hL J F⟩
    · obtain ⟨M, _, _, hM⟩ := exists_idealPowSmul_pushforward_eq f J F
      rw [hM]
      exact FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f M
    · have hobj := IdealPowerSmul.obj_idealPowSmul J 1 ((Scheme.Modules.pushforward f).obj F) U
      rw [pow_one] at hobj
      exact hobj.le s.2

/-- **Clause (2) of [Stacks, Tag 0B5U] for `L`, from ampleness of `f^* L`.** Every coherent
`𝒪_X`-module has eventually vanishing higher twisted cohomology.

This is the dévissage [Stacks, Tag 01YM] applied to the property, through
`Stacks.HighTwistVanishing.forall_of_hgeneric`: that result already discharges the dévissage's
clauses (1), (2) and the zero-module clause for this property, and the two inputs it still carries
— [Stacks, Tag 01YE] and [Stacks, Tag 01YL] — are available for a Noetherian scheme as
`Stacks.AlgebraicGeometry.NoetherianDevissage.hasGenericStalkIdealCoproductSub` and
`hasIrreducibleHigherRankCriterion`. So the only thing supplied here is clause (3),
`exists_coherent_generic_highTwist`. -/
theorem hasHighTwistVanishing_of_isCoherent {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [Surjective f] [IsNoetherian Y]
    [IsNoetherian X]
    (hL : IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L)) :
    ∀ F : X.Modules, F.IsCoherent → HasHighTwistVanishing L F :=
  Stacks.HighTwistVanishing.forall_of_hgeneric X L
    (NoetherianDevissage.hasGenericStalkIdealCoproductSub X)
    (NoetherianDevissage.hasIrreducibleHigherRankCriterion X)
    fun I _ ↦ exists_coherent_generic_highTwist f L p hL I

/-- **The implication `⟸` of [Stacks, Tag 0B5V].** For `f : Y ⟶ X` finite and surjective and `X`
proper over a Noetherian ring `R`, ampleness of `f^* L` gives ampleness of `L`.

The source's route, every step of it from the library. `hasHighTwistVanishing_of_isCoherent` is clause
(2) of [Stacks, Tag 0B5U] for `L`, and `(2) ⟹ (1)` of that tag is ampleness. The two spellings of
clause (2) — this file's `Stacks.HighTwistVanishing.HasHighTwistVanishing` over `Hgroup`, and
`AlgebraicGeometry.Scheme.Modules.HasEventualTwistCohomologyVanishing` over the derived functor of
the module-valued global sections — are reconciled by that tag's own
`isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup`, and the two ampleness predicates by
`Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple`, which is [Stacks, Tag 01PS] over the two
families of tensor powers.

`Y` is Noetherian for free: it is proper over `R` through `f ≫ p`, since a finite morphism is
proper and properness composes. -/
theorem isAmple_of_isAmple_modulePullback (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [Surjective f]
    (h : IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L)) :
    IsAmple X L := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have _ : IsNoetherian X := ⟨⟩
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  have _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  have _ : IsNoetherian Y := ⟨⟩
  have hall := hasHighTwistVanishing_of_isCoherent f L p h
  have hvan : AlgebraicGeometry.Scheme.Modules.HasEventualTwistCohomologyVanishing L := by
    intro F hF
    obtain ⟨n₀, hn₀⟩ := hall F hF
    exact ⟨n₀, fun n q hn hq ↦
      AlgebraicGeometry.Scheme.Modules.isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup
        L F (n : ℤ) q (hn₀ n q hn hq)⟩
  exact Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L
    (AlgebraicGeometry.Scheme.Modules.isAmple_of_eventualTwistVanishing L p hvan)

/-- **[Stacks, Tag 0B5V].** Let `R` be a Noetherian ring, let `f : Y ⟶ X` be a morphism of schemes
proper over `R` — `X` through `p` and `Y` through `f ≫ p`, which is automatic since a finite
morphism is proper and properness composes — and let `L` be an invertible `𝒪_X`-module. If `f` is
finite and surjective, then `L` is ample if and only if `f^* L` is ample.

Every binder is the source's: the Noetherian ring, properness over it, finiteness and
surjectivity of `f`, and invertibility of `L`. `⟹` is `isAmple_modulePullback_of_isFinite`, which
needs only finiteness; `⟸` is `isAmple_of_isAmple_modulePullback`, the source's cohomological
argument. -/
@[stacks 0B5V]
theorem isAmple_iff_isAmple_modulePullback (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (.of R)) [IsProper p] [IsFinite f] [Surjective f] :
    IsAmple X L ↔ IsAmple Y ((modulePullback f.toLRSHom.toShHom).obj L) :=
  ⟨isAmple_modulePullback_of_isFinite f L, isAmple_of_isAmple_modulePullback f L R p⟩

end Converse

end Stacks.AmpleFiniteSurjective

end
