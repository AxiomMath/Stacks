module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.TorDimensionOpenBase
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a perfect complex along a perfect proper morphism

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes and let
`E` be a perfect object of `D(𝒪_X)`. [Stacks, Tag 0B6G] asserts that `Rf_*E` is a perfect object
of `D(𝒪_S)`.

The source proves this by checking the hypotheses of [Stacks, Tag 08EV] and quoting that tag.
This file carries out that check: every hypothesis [Stacks, Tag 08EV] makes of the source
complex is derived here from perfectness of `E` and properness of `f`, and the conclusion of
[Stacks, Tag 0B6G] is reached from the part of [Stacks, Tag 08EV] this library has.

## Main results

* `isCoherent_homology_and_bounds_of_isPerfect`: a perfect object of `D(𝒪_X)` on a scheme
  quasi-compact and locally of finite type over a Noetherian base has coherent cohomology
  sheaves and is bounded, which is what [Stacks, Tag 08EV] asks of its source complex.
* `isPseudoCoherent_derivedPushforward_of_isPerfect`: **[Stacks, Tag 0B6G], the
  pseudo-coherence half of the conclusion, with no hypothesis.** `Rf_*E` is a pseudo-coherent
  object of `D(𝒪_S)`.
* `locallyHasFiniteTorDimension_of_forall_affineOpen`: locally finite Tor dimension is
  affine-local — it follows from finite Tor dimension of the restriction to each affine open.
  This is the first step of the route below.
* `isPerfect_derivedPushforward_of_isPerfect_of_locallyHasFiniteTorDimension`:
  **[Stacks, Tag 0B6G], granted the Tor-dimension half.** `Rf_*E` is a perfect object of
  `D(𝒪_S)` once it is of locally finite Tor dimension.
* `isPerfect_derivedPushforward_of_isPerfect_of_forall_affineOpen`: the same with the
  Tor-dimension half asked for on each affine open of the base only, which is what the reduction
  of `TorDimensionOpenBase.lean` brings it down to.

## What is proved, and what is carried

By [Stacks, Tag 08CQ] a perfect object of `D(𝒪_S)` is exactly a pseudo-coherent one of locally
finite Tor dimension, and the source's proof of [Stacks, Tag 08EV] establishes the two halves
separately. This library carries the pseudo-coherence half of [Stacks, Tag 08EV], as
`Stacks.AlgebraicGeometry.ProperSupportCoherent`'s
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp`. Accordingly:

*The hypotheses of [Stacks, Tag 08EV] on the source complex are discharged here.* `S` is
Noetherian and `f` is of finite type and quasi-compact, so `X` is Noetherian
(`AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`); a perfect object of `D(𝒪_X)` on a
Noetherian scheme then has coherent cohomology sheaves and is bounded, which is
[Stacks, Tag 0FXU]; and `f` being proper, *every* closed subset of `X` is proper over `S` — the
reduced induced closed subscheme on it maps to `X` by a closed immersion, which is proper, and a
composition of proper morphisms is proper — in particular the support of each cohomology sheaf.
So no boundedness, coherence or support hypothesis is imposed below, exactly as in
[Stacks, Tag 0B6G]: in the source these are consequences of perfectness of `E` and properness of
`f`, and they belong to the proof rather than to the statement.

*`haff` is discharged.* The pseudo-coherence half of [Stacks, Tag 08EV] takes
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5], as a hypothesis. That `Prop` is *proved*
in this tree, with no hypothesis, as
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` in
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean`, which is where
[Stacks, Tag 02O5] is registered; it is supplied from there below rather than assumed, so
neither declaration in this file has a hypothesis standing for [Stacks, Tag 02O5].

*`htor` is the Tor-dimension half of [Stacks, Tag 08EV], and it is proved — elsewhere.* The
source tensors `Rf_*E` with an arbitrary quasi-coherent `𝒪_S`-module `ℱ`, rewrites
`Rf_*E ⊗^𝐋_{𝒪_S} ℱ = Rf_*(E ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}ℱ)` by [Stacks, Tag 08EU] and
[Stacks, Tag 08DE], bounds the cohomology of the right-hand side using the finite Tor dimension of
`E` over `f^{-1}𝒪_S`, and converts the resulting vanishing on quasi-coherent test modules into
genuine Tor amplitude by [Stacks, Tag 08EA]. Two of those steps are absent from this library:
[Stacks, Tag 08EA] is carried only as its clause `(1) implies (2)`, which is the direction the
proof does not use, and [Stacks, Tag 08EU] only at `K = 𝒪_S[0]` and for a strictly perfect `K`,
neither of which covers the `ℱ` of the proof.

A route that does not pass through either is taken instead, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/MayerVietorisTorDimension.lean`:
locally finite Tor dimension is a statement about a cover of `S`, so by
`locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen` it is enough to bound the
Tor amplitude of `R(f|_V)_*(E|_{f^{-1}V})` on each affine open `V ⊆ S`, and over such a `V` the
Mayer--Vietoris induction of [Stacks, Tag 08DR] on a finite cover of `f^{-1}V` reduces the bound to
a morphism of affine schemes, where [Stacks, Tag 0A9F] turns `Rf_*` into derived restriction of
scalars and the Tor clause of perfectness of `f` ([Stacks, Tag 0687]) finishes it. That file
carries the whole Tor-dimension half, and hence [Stacks, Tag 0B6G] itself, as
`isPerfect_derivedPushforward_of_isPerfect`, where the bare `@[stacks 0B6G]` is placed.

*The localisation of the goal, joined to [Stacks, Tag 08FE].* The reduction of the whole
Tor-dimension half to the affine opens of `S` is
`locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/TorDimensionOpenBase.lean`:
`Rf_*E` is of locally finite Tor dimension as soon as `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor
dimension on `V` for every affine open `V ⊆ S`, with nothing assumed beyond what
`AlgebraicGeometry.derivedPushforwardModules` is stated under. It joins the affine-locality of the
predicate (`locallyHasFiniteTorDimension_of_forall_affineOpen` below) to [Stacks, Tag 08FE] in the
scheme spelling (`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpenIso` and
`AlgebraicGeometry.schemeDerivedPushforwardRestrictOpensIso` in
`StacksFrontier/AlgebraicGeometry/Perfect/DerivedPushforwardOpenBase.lean`). The two declarations of
this file which carry that bound as a hypothesis are therefore steps of the route and not the end
of it; the end is in the file named above.

## Implementation notes

Perfectness of an object of `D(𝒪_X)` is `Stacks.Cohomology.PerfectComplexes.IsPerfect`, the
spelling of [Stacks, Tag 08CM] that [Stacks, Tag 08CQ] is stated at, and the same predicate
appears in the hypothesis on `E` and in the conclusion about `Rf_*E`. Its other spelling
`AlgebraicGeometry.RingedSpace.IsPerfect`, which [Stacks, Tag 0FXU] is stated at, is the same
definition read at equal space and section universes, so the hypothesis is handed to
[Stacks, Tag 0FXU] directly.

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`, as in the pseudo-coherence half of
[Stacks, Tag 08EV]; pseudo-coherence is `AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the
spelling of [Stacks, Tag 08CB] part (3) that that half concludes in.

*Properness of the supports is argued inline.* This library does state it, as
`AlgebraicGeometry.isProperOver_of_isProper` in
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherent`, where it was
needed for the base change of a proper morphism; importing the Fourier-Mukai development for a
two-line `change`-and-`infer_instance` would couple this file to a development it has nothing
to do with, so the argument is made as a `have` here instead.

Properness is Mathlib's `IsProper` and perfectness of the morphism is
`AlgebraicGeometry.Perfect`, [Stacks, Tag 0687]; both extend `LocallyOfFiniteType`, and
`IsProper` gives `QuasiCompact`, so neither a finite-type nor a quasi-compactness hypothesis has
to be repeated. `IsNoetherian S` is [Stacks, Tag 01OV] part (2) — locally Noetherian together
with quasi-compactness — which is what the source assumes of the base; `IsLocallyNoetherian`
alone would be weaker.

## References

* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 069C](https://stacks.math.columbia.edu/tag/069C)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 0687](https://stacks.math.columbia.edu/tag/0687)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSupportCoherent

universe u

namespace Stacks.AlgebraicGeometry.PerfectProperDirectImage

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **What [Stacks, Tag 08EV] asks of its source complex, for a perfect complex.** Let `S` be a
Noetherian scheme, let `f : X ⟶ S` be quasi-compact and locally of finite type and let `E` be a
perfect object of `D(𝒪_X)`. Then the cohomology sheaves of `E` are coherent and `E` is bounded.

`X` is Noetherian, being quasi-compact and locally of finite type over a Noetherian scheme, so
this is [Stacks, Tag 0FXU] with its two conclusions read as a bound below and a bound above. -/
@[sga "6 0 3.1" "partial"]
theorem isCoherent_homology_and_bounds_of_isPerfect [IsNoetherian S] [LocallyOfFiniteType f]
    [QuasiCompact f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent) ∧
      ∃ a b : ℤ, E.IsGE a ∧ E.IsLE b := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨⟨⟨a, hlo⟩, ⟨b, hhi⟩⟩, hcoh⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X E hE
  exact ⟨hcoh, a, b, (DerivedCategory.isGE_iff E a).2 hlo, (DerivedCategory.isLE_iff E b).2 hhi⟩

/-- **[Stacks, Tag 0B6G], the pseudo-coherence half of the conclusion, with no hypothesis.** Let
`S` be a Noetherian scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes and let `E`
be a perfect object of `D(𝒪_X)`. Then `Rf_*E` is a pseudo-coherent object of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor
dimension; this is the first of the two. The hypotheses the pseudo-coherence half of
[Stacks, Tag 08EV] makes of `E` are supplied by `isCoherent_homology_and_bounds_of_isPerfect`,
and its support hypothesis by the fact that every closed subset of the source of a proper
morphism is proper over the target. The hypothesis that half carries for [Stacks, Tag 02O5] is
supplied by the proof of [Stacks, Tag 02O5] in this tree,
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, so it is
not assumed here. -/
@[stacks 0B6G "the pseudo-coherence half of the conclusion: Rf_*E is a pseudo-coherent object \
of D(𝒪_S), proved under the source's own hypotheses and no others",
  sga "6 0 3.1" "partial",
  sga "6 XIV 2.2" "special case"]
-- Scope of the clause above, which the registration deliberately does not carry: perfectness is
-- pseudo-coherence together with locally finite Tor dimension (Tag 08CQ), and this declaration
-- states only the first of the two. The second, and with it the whole of Tag 0B6G, is proved in
-- `StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/MayerVietorisTorDimension.lean`,
-- where the bare `@[stacks 0B6G]` sits on
-- `isPerfect_derivedPushforward_of_isPerfect`; this clause is kept because the statement under it
-- is true, unconditional, and the input that proof consumes.
theorem isPseudoCoherent_derivedPushforward_of_isPerfect [IsNoetherian S]
    [AlgebraicGeometry.Perfect f] [IsProper f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨hcoh, a, b, hGE, hLE⟩ := isCoherent_homology_and_bounds_of_isPerfect f E hE
  have hproper : ∀ T : Closeds X, IsProperOver f T := fun T => by
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
    infer_instance
  exact isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh
    (fun _ => hproper _)
    AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase a b
    hGE hLE

/-- **Locally finite Tor dimension is affine-local.** An object of `D(𝒪_Y)` on a scheme is of
locally finite Tor dimension as soon as its restriction to each affine open of `Y` has finite Tor
dimension.

The affine opens of a scheme cover it (`AlgebraicGeometry.iSup_affineOpens_eq_top`), and
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` asks for *some* cover, so this is
that cover together with the hypothesis. It is the first step of any proof that an object is
perfect: by [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor
dimension, and the second half is a statement about a cover. -/
theorem locallyHasFiniteTorDimension_of_forall_affineOpen (Y : Scheme.{u})
    (E : DerivedCategory Y.Modules)
    (h : ∀ V : Y.affineOpens,
      Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
        (Y.toRingedSpace.restrict (V : Y.Opens).isOpenEmbedding)
        ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules Y.toRingedSpace
          (V : Y.Opens)).mapDerivedCategory.obj E)) :
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension Y.toRingedSpace E :=
  ⟨Y.affineOpens, fun V => (V : Y.Opens), iSup_affineOpens_eq_top Y, h⟩

/-- **[Stacks, Tag 0B6G], granted the Tor-dimension half of [Stacks, Tag 08EV].** Let `S` be a
Noetherian scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes and let `E` be a
perfect object of `D(𝒪_X)`. If `Rf_*E` is of locally finite Tor dimension then it is a perfect
object of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the pseudo-coherence proved
above. The hypothesis `htor` is the Tor-dimension half of the source's proof of
[Stacks, Tag 08EV], discharged in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/MayerVietorisTorDimension.lean`; the
appeal to [Stacks, Tag 02O5] is discharged here, not assumed. -/
-- No `@[stacks 0B6G]` here: this declaration carries a mathematical input as a hypothesis, and a
-- tag counts only on a declaration proved under the source's own hypotheses. The unconditional
-- statement, which is where the tag is registered, is
-- `Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect`.
theorem isPerfect_derivedPushforward_of_isPerfect_of_locallyHasFiniteTorDimension
    [IsNoetherian S] [AlgebraicGeometry.Perfect f] [IsProper f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (htor : Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2
      (isPseudoCoherent_derivedPushforward_of_isPerfect f E hE))
    htor


/-- **[Stacks, Tag 0B6G], with the Tor-dimension half asked for on the affine opens of the base.**
Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a perfect proper morphism of schemes and let
`E` be a perfect object of `D(𝒪_X)`. If `R(f|_V)_*(E|_{f^{-1}V})` has finite Tor dimension on `V`
for every affine open `V ⊆ S`, then `Rf_*E` is a perfect object of `D(𝒪_S)`.

This is `isPerfect_derivedPushforward_of_isPerfect_of_locallyHasFiniteTorDimension` with `htor`
replaced by the affine-open form it is reduced to, by
`locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen`. It is the same statement
one step further along the route: what is still carried is a Tor-amplitude bound on each affine
open of the base, which is what the Mayer--Vietoris induction over a finite affine cover of
`f^{-1}V` together with the affine base case
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_specMap` is for. -/
-- No `@[stacks 0B6G]` here either: `htor'` is a mathematical input, carried as a hypothesis. It is
-- proved in
-- `StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/MayerVietorisTorDimension.lean`,
-- as `...hasFiniteTorDimension_derivedPushforward_affineOpen`, and this theorem fed with it is the
-- unconditional `...isPerfect_derivedPushforward_of_isPerfect` registered there.
theorem isPerfect_derivedPushforward_of_isPerfect_of_forall_affineOpen
    [IsNoetherian S] [AlgebraicGeometry.Perfect f] [IsProper f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (htor' : ∀ V : S.affineOpens,
      Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
        (S.toRingedSpace.restrict (V : S.Opens).isOpenEmbedding)
        ((schemeDerivedPushforward (f ∣_ (V : S.Opens))).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj E))) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPerfect_derivedPushforward_of_isPerfect_of_locallyHasFiniteTorDimension f E hE
    (locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen f E htor')

end Stacks.AlgebraicGeometry.PerfectProperDirectImage

end
