module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# A Fourier-Mukai functor and the perfect derived category

Let `S` be a scheme, let `X` and `Y` be schemes over `S` and let `K ∈ D(𝒪_{X ×_S Y})`.
[Stacks, Tag 0FYT] asserts that the Fourier-Mukai functor

`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`

of [Stacks, Tag 0FYQ] sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)` as soon as one of six alternative
conditions holds. This file carries all six clauses.

Throughout, write `T = L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K`, so that `Φ_K(M) = R pr_{2,*} T`. The
source's proof has two steps that are used in every clause and are proved here unconditionally:

* if `M` is perfect on `X` then `L pr_1^* M` is perfect on `X ×_S Y`, which is
  [Stacks, Tag 09UA] (`AlgebraicGeometry.isPerfect_fourierMukaiPullback`);
* if `X ⟶ S` is of finite type, proper, flat or of finite presentation then so is the base
  change `pr_2 : X ×_S Y ⟶ Y`, [Stacks, Tag 01T4], [Stacks, Tag 01W4], [Stacks, Tag 01U9] and
  [Stacks, Tag 01TS] — in this development these are Mathlib's base-change instances for the
  corresponding morphism properties, so they are found by instance search and never written.

After that, each clause is an application of a perfectness criterion for a derived direct image
to `T`. Perfectness of `T` itself, which clauses (3)-(6) assume of `K` and which the two steps
above turn into perfectness of `T`, is [Stacks, Tag 09J5]
(`AlgebraicGeometry.isPerfect_fourierMukaiTensor`).

## Main results

* `AlgebraicGeometry.isPerfect_fourierMukaiPullback`: [Stacks, Tag 09UA] read at `pr_1`.
* `AlgebraicGeometry.isPerfect_fourierMukaiTensor`: `T` is perfect when `M` and `K` are.
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isCoherent_kernel`: **[Stacks, Tag 0FYT],
  clause (1).**
* `AlgebraicGeometry.isPerfect_fourierMukai_of_flatProperSupportComplex`:
  **[Stacks, Tag 0FYT], clause (2).**
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel`: the common core of
  clauses (3) and (4) — `Φ_K(M)` is perfect for a perfect `K`, a proper `X ⟶ S` and a
  Noetherian `Y`.
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlat`:
  **[Stacks, Tag 0FYT], clause (3).**
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_noetherianBase`:
  **[Stacks, Tag 0FYT], clause (4).**
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel`:
  **[Stacks, Tag 0FYT], clause (5).**
* `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel_of_noetherianBase`:
  **[Stacks, Tag 0FYT], clause (6).**

## What each clause is routed through

Clause (1) is [Stacks, Tag 08EV] combined with [Stacks, Tag 0FXU], as the source says.
Clause (2) is routed through the Noetherian form [Stacks, Tag 0DJQ] of [Stacks, Tag 0A1H], whose
perfectness half this library does not carry. Clauses (3) and (4) are routed through
[Stacks, Tag 0B6F]'s reduction, the Noetherian special case of [Stacks, Tag 0B91], whose
perfectness half this library does not carry either. Clauses (5) and (6) are
[Stacks, Tag 0DJT] combined with [Stacks, Tag 0DI4], as the source says, with
[Stacks, Tag 0DJT] applied in its Noetherian-base form
`isPerfect_derivedPushforward_of_isPerfectRelativeTo` (in the namespace
`Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward`), the form stated for an
arbitrary pinned certificate family `D`; the tag over an arbitrary base,
`isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap`, is stated at the canonical
certificate family. Each of clauses (2)-(6) therefore assumes `AlgebraicGeometry.IsNoetherian Y`,
which [Stacks, Tag 0FYT] does not; the per-clause
docstrings say where that hypothesis is spent.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, which `AlgebraicGeometry.fourierMukai`,
[Stacks, Tag 09UA], [Stacks, Tag 09J5] and [Stacks, Tag 08EV] are all stated at; the priority of
the local instance selects it over the locally small model arriving with the imports.

*Perfectness.* `Stacks.Cohomology.PerfectComplexes.IsPerfect` and
`AlgebraicGeometry.RingedSpace.IsPerfect` are the library's two statements of
[Stacks, Tag 08CM]; they are the same predicate by `rfl`, as
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectKGroupRing.lean` records. The first is used below,
because it is the one `AlgebraicGeometry.perfectDerived` — the full subcategory `D_perf(𝒪_X)` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/TransformedDiagonal/Basic.lean` — reads for a
scheme. So "`Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`" is the statement that `Φ_K(M)` is
perfect for every perfect `M`, which is what is proved below; the induced functor
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is then `AlgebraicGeometry.fourierMukaiOn` at that pair of
properties and nothing new is needed for it.

*The two spellings of the derived direct image.* `AlgebraicGeometry.fourierMukaiPushforward` is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` of the morphism of ringed
spaces underlying `pr_2`, and so is
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX`, which [Stacks, Tag 08EV] is
stated with; the two are literally the same functor, so the conclusion of that tag is read
directly against `Φ_K`.

### What is carried, and why

Clauses (1)-(4) carry inputs *of [Stacks, Tag 08EV]*, not of [Stacks, Tag 0FYT]; clauses (5) and
(6) carry inputs of [Stacks, Tag 0DI4], listed in their own docstrings.
[Stacks, Tag 08EV] is proved unconditionally as
`Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp`;
this file uses its conditional form
`Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport`, stated
for an arbitrary certified derived tensor datum `D` and proved granted two residues of its own
proof, both statements about the derived direct image and neither mentioning perfectness of the
source object:

* `hpushforwardCoherence`, the quantified form
  `Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue` — [Stacks, Tag 08E2] for
  `R pr_{2,*}`, read through [Stacks, Tag 08E8]. The obstruction is coherence of the direct
  image along a proper morphism, [Stacks, Tag 02O5], which this repository proves only
  conditionally.
* `hpushforwardTorDimension`, the quantified form
  `Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue` — the closing step of
  the source's proof of [Stacks, Tag 08EV]. It needs the projection formula of
  [Stacks, Tag 08EU] at a general target complex and the clause `(2) implies (1)` of
  [Stacks, Tag 08EA]; the first is carried only at `K = 𝒪_S[0]` and the second only in the
  opposite direction.

Both are quantified over the source object, so each is strictly stronger than the instance of it
the proof consumes, and each is therefore a named citation of a step of [Stacks, Tag 08EV]
at the datum `D` rather than an assumption of the conclusion of [Stacks, Tag 0FYT].

`D` is a datum rather than an assumption: an arbitrary
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` on the inverse-image ringed space
`(X ×_S Y, pr_2^{-1}𝒪_Y)`, which is how part (3) of [Stacks, Tag 08CG] is expressed throughout
this library. The remaining carried hypothesis is `hTor`, finiteness of the Tor dimension of `T`
over `pr_2^{-1}𝒪_Y`, which is clause (3) of the hypothesis of [Stacks, Tag 08EV]; for each
clause of [Stacks, Tag 0FYT] the per-clause notes below say where the source gets it and what
this library lacks.

## References

* [Stacks Project, Tag 0FYT](https://stacks.math.columbia.edu/tag/0FYT)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
* [Stacks Project, Tag 0B6F](https://stacks.math.columbia.edu/tag/0B6F)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DI4](https://stacks.math.columbia.edu/tag/0DI4)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-! ### The kernel tensor -/

/-- `T = L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K`, the object of `D(𝒪_{X ×_S Y})` whose derived direct
image along `pr_2` is `Φ_K(M)`. -/
abbrev fourierMukaiKernelTensor (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules) : DerivedCategory (Limits.pullback f g).Modules :=
  (fourierMukaiTensor f g K).obj ((fourierMukaiPullback f g).obj M)

/-- **`Φ_K(M)` is the derived direct image of `T` along `pr_2`.** Both sides are the total right
derived functor of degreewise pushforward along the morphism of ringed spaces underlying `pr_2`,
applied to `T`; this records that the functor `Φ_K` is built from in
`AlgebraicGeometry.fourierMukai` and the one [Stacks, Tag 08EV] is stated with agree. -/
theorem fourierMukai_obj_eq_derivedPushforwardOX
    (K : DerivedCategory (Limits.pullback f g).Modules) (M : DerivedCategory X.Modules) :
    (fourierMukai f g K).obj M =
      (derivedPushforwardOX (Limits.pullback.snd f g)).obj (fourierMukaiKernelTensor f g K M) :=
  rfl

/-! ### Perfectness of the pullback and of the kernel tensor -/

/-- **The derived pullback along `pr_1` of a perfect object is perfect.** This is
[Stacks, Tag 09UA] for the morphism of ringed spaces underlying `pr_1 : X ×_S Y ⟶ X`, which is
the morphism `AlgebraicGeometry.fourierMukaiPullback` is the derived pullback along. The source
uses this step in every clause of [Stacks, Tag 0FYT] "without further mention". -/
theorem isPerfect_fourierMukaiPullback (M : DerivedCategory X.Modules)
    (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := (Limits.pullback f g).toRingedSpace)
      ((fourierMukaiPullback f g).obj M) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (Limits.pullback.fst f g).toLRSHom.toShHom M hM

/-- **`T = L pr_1^* M ⊗^𝐋 K` is perfect when `M` and `K` are.** The derived pullback of a
perfect object is perfect by [Stacks, Tag 09UA]
(`AlgebraicGeometry.isPerfect_fourierMukaiPullback`), and the derived tensor product of two
perfect objects is perfect by [Stacks, Tag 09J5]; the derived tensor product
`AlgebraicGeometry.fourierMukaiTensor` is taken at is the canonical one of
[Stacks, Tag 06YU], which is the one [Stacks, Tag 09J5] is applied at here. -/
theorem isPerfect_fourierMukaiTensor (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := (Limits.pullback f g).toRingedSpace) (fourierMukaiKernelTensor f g K M) :=
  RingedSpace.isPerfect_canonicalDerivedTensorProduct (Limits.pullback f g).toRingedSpace
    ((fourierMukaiPullback f g).obj M) K (isPerfect_fourierMukaiPullback f g M hM) hK

/-! ### Clause (1) -/

section ClauseOne

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

/-- **[Stacks, Tag 0FYT], clause (1).** Let `S` be a Noetherian scheme, let `X ⟶ S` and
`Y ⟶ S` be of finite type and let `K` be an object of `D^b_{Coh}(𝒪_{X ×_S Y})`. Then `Φ_K` sends
`D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

The proof is the source's: `M` perfect on the Noetherian scheme `X` lies in `D^b_{Coh}(𝒪_X)` by
[Stacks, Tag 0FXU], so the cohomology sheaves of `T = L pr_1^* M ⊗^𝐋 K` are coherent by the
first half of the argument of [Stacks, Tag 0FYU]
(`AlgebraicGeometry.isCoherent_homology_fourierMukaiTensor`) and `T` is bounded above by
`AlgebraicGeometry.isLE_fourierMukaiPullback` and
`AlgebraicGeometry.isLE_fourierMukaiTensor`; [Stacks, Tag 08EV] applied to
`pr_2 : X ×_S Y ⟶ Y`, which is of finite type by base change and whose target is Noetherian
because `Y ⟶ S` is of finite type, then gives the conclusion.

Three of the four hypotheses of [Stacks, Tag 08EV] are therefore discharged. What is carried,
beyond its two residues (see the implementation notes of this file), is:

* `d` and `hGE`, a bound below on `T`. The source takes `T ∈ D^b_{Coh}` for granted here:
  `L pr_1^* M` is perfect, so it has locally finite Tor amplitude, and `K` is bounded below, so
  the tensor product is bounded below on each member of a covering and hence — `X ×_S Y` being
  Noetherian — globally. The passage from locally finite Tor amplitude of one factor to a bound
  below on a derived tensor product is not in this library: it has
  `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct` for the bound above and nothing
  for the bound below.
* `hsupp`, the proper-support clause, read on the cohomology sheaves of `T` rather than on those
  of `K` as the source states it. The two are joined by the inclusion
  `supp H^i(L pr_1^* M ⊗^𝐋 K) ⊆ ⋃_j supp H^j(K)`, which this library has only for a tensor
  product with a *complex* of modules with bounded support
  (`Stacks.Cohomology.PerfectPushforward.supp_homology_derivedTensor_subset`) and not for a
  second factor given as a derived object. When `X ⟶ S` is proper the clause is free, by
  `AlgebraicGeometry.isProperOver_pullbackSnd_of_isProper`.
* `hTor`, finiteness of the Tor dimension of `T` over `pr_2^{-1}𝒪_Y`, read on `T` rather than on
  `K` as the source states it. The source's clause is on `K`, and the passage to `T` is
  "tensoring with a perfect object preserves finite Tor dimension over `pr_2^{-1}𝒪_Y`", which is
  the second assertion of [Stacks, Tag 0DI4] in the relative-perfectness form and is not
  available at the absolute Tor-dimension predicate
  `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasFiniteTorDimension` this
  clause of [Stacks, Tag 08EV] is written with. -/
@[stacks 0FYT "clause (1), with Tag 08EV's own inputs carried: its two residues, a bound below \
on L pr₁^* M ⊗ᴸ K, and the support and Tor-dimension clauses read on that tensor, not on K"]
theorem isPerfect_fourierMukai_of_isCoherent_kernel
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base))
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (d : ℤ) (hGE : (fourierMukaiKernelTensor f g K M).IsGE d)
    (hsupp : ∀ i : ℤ, ∃ Z : Closeds (Limits.pullback f g : Scheme.{u}),
      IsProperOver (Limits.pullback.snd f g) Z ∧
        SheafOfModules.supp ((DerivedCategory.homologyFunctor
            (Limits.pullback f g).Modules i).obj (fourierMukaiKernelTensor f g K M)) ⊆
          (Z : Set (Limits.pullback f g : Scheme.{u})))
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction
      (Limits.pullback.snd f g)).obj (fourierMukaiKernelTensor f g K M)))
    (hpushforwardCoherence : Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue
      (Limits.pullback.snd f g) (derivedPushforwardOX (Limits.pullback.snd f g)))
    (hpushforwardTorDimension :
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue
        (Limits.pullback.snd f g) D (derivedPushforwardOX (Limits.pullback.snd f g))) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) := by
  have hXN : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  obtain ⟨⟨-, b, hKhi⟩, hKc⟩ := hK
  obtain ⟨⟨-, c, hMhi⟩, hMc⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X M hM
  have hMLE : M.IsLE c := (DerivedCategory.isLE_iff M c).2 fun j hj => hMhi j hj
  have hKLE : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun j hj => hKhi j hj
  have hLE : (fourierMukaiKernelTensor f g K M).IsLE (c + b) :=
    isLE_fourierMukaiTensor f g K M c b (isLE_fourierMukaiPullback f g M c hMLE) hKLE
  refine Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport
    (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M) D ⟨d, c + b, ?_⟩
    (isCoherent_homology_fourierMukaiTensor f g K ⟨⟨b, hKhi⟩, hKc⟩ M ⟨⟨c, hMhi⟩, hMc⟩) hsupp hTor
    (hpushforwardCoherence _) (hpushforwardTorDimension _)
  intro i hi
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with hi | hi
  · exact (DerivedCategory.isGE_iff _ d).1 hGE i hi
  · exact (DerivedCategory.isLE_iff _ (c + b)).1 hLE i hi

end ClauseOne

/-! ### Clause (2) -/

/-- **[Stacks, Tag 0FYT], clause (2), over a Noetherian `Y`.** Let `X ⟶ S` be of finite
presentation, let `𝒦^•` be a bounded complex of coherent `𝒪_{X ×_S Y}`-modules, flat over `Y`,
with support proper over `Y`, and let `K` be an object of `D(𝒪_{X ×_S Y})` represented by `𝒦^•`.
Then `Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

The source deduces the clause from [Stacks, Tag 0A1H], whose perfectness half this library does
not carry: as the module documentation of
`StacksFrontier/AlgebraicGeometry/Perfect/TensorFinitelyPresentedPushforwardBaseChange.lean`
records, the source bridges that tag to its Noetherian form by a limit descent that is not
assembled here. The route taken instead is that Noetherian form, [Stacks, Tag 0DJQ]
(`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor`), applied to
`pr_2 : X ×_S Y ⟶ Y` — which is locally of finite presentation, hence locally of finite type, by
base change — with `E = L pr_1^* M`, perfect by [Stacks, Tag 09UA], and `𝒢 = 𝒦^•`.

Two things are therefore weaker than the source's clause, and both come from using
[Stacks, Tag 0DJQ] in place of [Stacks, Tag 0A1H]:

* `IsNoetherian Y` is assumed, where the clause assumes nothing about `Y`;
* the terms of `𝒦^•` are asked to be coherent rather than of finite presentation. Over the
  Noetherian `X ×_S Y` the two conditions agree, by [Stacks, Tag 01XZ].

Everything else is the source's, and three of the four hypotheses of [Stacks, Tag 08EV] for
`L pr_1^* M ⊗^𝐋 𝒦^•` are *proved* inside [Stacks, Tag 0DJQ] — the support clause from the
proper support of `𝒦^•`, the coherence clause, and the boundedness clause. What is carried is
`hTor`, finiteness of the Tor dimension of `L pr_1^* M ⊗^𝐋 𝒦^•` over `pr_2^{-1}𝒪_Y`, which is
the fourth clause and which [Stacks, Tag 0DJQ] carries as the `hasFiniteTorDimension` field of
`Stacks.Cohomology.PerfectPushforward.TensorPushforwardData`, together with the two residues of
[Stacks, Tag 08EV] described in the implementation notes of this file. -/
@[stacks 0FYT "clause (2), routed through the Noetherian form Tag 0DJQ of Tag 0A1H: Y is assumed \
Noetherian, the terms of the complex coherent (Tag 01XZ), and Tag 08EV's residues carried"]
theorem isPerfect_fourierMukai_of_flatProperSupportComplex [IsNoetherian Y]
    [LocallyOfFinitePresentation f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base))
    (G : CochainComplex
      (StrictlyPerfect.OXMod.{u, u} (Limits.pullback f g).toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex
      (Limits.pullback.snd f g) G)
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (e : DerivedCategory.Q.obj G ≅ K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction
      (Limits.pullback.snd f g)).obj
        (fourierMukaiKernelTensor f g (DerivedCategory.Q.obj G) M)))
    (hpushforwardCoherence : Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue
      (Limits.pullback.snd f g) (derivedPushforwardOX (Limits.pullback.snd f g)))
    (hpushforwardTorDimension :
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue
        (Limits.pullback.snd f g) D (derivedPushforwardOX (Limits.pullback.snd f g))) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) := by
  have key := Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor
    (Limits.pullback.snd f g) D
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (Stacks.Cohomology.PerfectPushforward.schemeSite (Limits.pullback f g)).O)
    hpushforwardCoherence hpushforwardTorDimension
    ((fourierMukaiPullback f g).obj M) G
    { isPerfect := isPerfect_fourierMukaiPullback f g M hM
      flatProperSupport := hG
      hasFiniteTorDimension := hTor }
  exact key.of_iso ((fourierMukaiPushforward f g).mapIso
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (Limits.pullback f g).toRingedSpace.sheaf).flip.mapIso e).app
        ((fourierMukaiPullback f g).obj M)))

/-! ### Clauses (3) and (4) -/

/-- **The common core of clauses (3) and (4) of [Stacks, Tag 0FYT].** Let `X ⟶ S` be proper, let
`Y` be Noetherian and let `K` be a perfect object of `D(𝒪_{X ×_S Y})`. Then `Φ_K` sends
`D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

`T = L pr_1^* M ⊗^𝐋 K` is perfect by `AlgebraicGeometry.isPerfect_fourierMukaiTensor`, and
`pr_2 : X ×_S Y ⟶ Y` is proper by base change, so three of the four hypotheses of
[Stacks, Tag 08EV] for `T` are discharged by
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.input`: the support clause
because every closed subset of the source of a proper morphism is proper over the target, the
coherence clause by [Stacks, Tag 0FEP], and the boundedness clause from quasi-compactness of
`X ×_S Y`. That is the reduction the proof of [Stacks, Tag 0B6F] performs, and it is reused
verbatim.

`IsNoetherian Y` is a hypothesis neither clause of [Stacks, Tag 0FYT] makes. It is what
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.input` spends, on the
boundedness and coherence clauses, and it is where this statement is weaker than the source's;
clause (3) grants nothing about `Y` at all and clause (4) only that `S` is Noetherian, which
does not make `Y` Noetherian.

Flatness of `X ⟶ S` is not used by this core statement. In the source it is used exactly once,
to produce `hTor`: `pr_2` flat makes `𝒪_{X ×_S Y}` flat over `pr_2^{-1}𝒪_Y`
([Stacks, Tag 02N3]), and a perfect object is then of finite Tor dimension over `pr_2^{-1}𝒪_Y`.
That step is the field
`Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.hasFiniteTorDimension`, which
this library carries rather than derives, and it is carried here as `hTor` for the same reason;
the two clauses below record flatness in their hypotheses, where the source has it. -/
theorem isPerfect_fourierMukai_of_isPerfect_kernel [IsNoetherian Y] [IsProper f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base))
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction
      (Limits.pullback.snd f g)).obj (fourierMukaiKernelTensor f g K M)))
    (hpushforwardCoherence : Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue
      (Limits.pullback.snd f g) (derivedPushforwardOX (Limits.pullback.snd f g)))
    (hpushforwardTorDimension :
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue
        (Limits.pullback.snd f g) D (derivedPushforwardOX (Limits.pullback.snd f g))) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) := by
  have hin := (Stacks.Cohomology.PerfectPushforward.FlatProperPushforwardData.input
    (f := Limits.pullback.snd f g) (D := D) (E := fourierMukaiKernelTensor f g K M)
    { isPerfect := isPerfect_fourierMukaiTensor f g K M hK hM
      hasFiniteTorDimension := hTor })
  exact Stacks.Cohomology.ProperSupportPerfection.isPerfect_derivedPushforward_of_properSupport
    (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M) D hin.bounded hin.isCoherent
    hin.properSupport hin.hasFiniteTorDimension
    (hpushforwardCoherence _) (hpushforwardTorDimension _)

/-- **[Stacks, Tag 0FYT], clause (3).** Let `X ⟶ S` be a proper flat morphism of finite
presentation and let `K` be a perfect object of `D(𝒪_{X ×_S Y})`. Then `Φ_K` sends
`D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

This is `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel`. The source deduces the
clause from [Stacks, Tag 0B91], whose perfectness half this library does not carry — see the
module documentation of
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean` — so the route
taken instead is the Noetherian special case [Stacks, Tag 0B6F] of that tag, which is why
`IsNoetherian Y` appears and `LocallyOfFinitePresentation f` does not enter the proof. -/
@[stacks 0FYT "clause (3), with Tag 08EV's two residues and its Tor-dimension clause for \
L pr₁^* M ⊗ᴸ K carried, and with Y assumed Noetherian"]
theorem isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlat [IsNoetherian Y] [IsProper f]
    [Flat f] [LocallyOfFinitePresentation f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base))
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction
      (Limits.pullback.snd f g)).obj (fourierMukaiKernelTensor f g K M)))
    (hpushforwardCoherence : Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue
      (Limits.pullback.snd f g) (derivedPushforwardOX (Limits.pullback.snd f g)))
    (hpushforwardTorDimension :
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue
        (Limits.pullback.snd f g) D (derivedPushforwardOX (Limits.pullback.snd f g))) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  isPerfect_fourierMukai_of_isPerfect_kernel f g D K hK M hM hTor hpushforwardCoherence
    hpushforwardTorDimension

/-- **[Stacks, Tag 0FYT], clause (4).** Let `S` be Noetherian, let `X ⟶ S` be flat and proper
and let `K` be a perfect object of `D(𝒪_{X ×_S Y})`. Then `Φ_K` sends `D_perf(𝒪_X)` into
`D_perf(𝒪_Y)`.

The source says: part (4) follows from part (3) and the fact that a finite type morphism of
Noetherian schemes is of finite presentation, [Stacks, Tag 01TX]. That is what is done here:
`X ⟶ S` is proper, hence of finite type, and `S` is Noetherian, so
`AlgebraicGeometry.finitePresentation_of_finiteType` makes it of finite presentation and
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlat` applies. -/
@[stacks 0FYT "clause (4), reduced to clause (3) by Tag 01TX; Tag 08EV's two residues and its \
Tor-dimension clause for L pr₁^* M ⊗ᴸ K are carried, and Y is assumed Noetherian"]
theorem isPerfect_fourierMukai_of_isPerfect_kernel_of_noetherianBase [IsNoetherian S]
    [IsNoetherian Y] [IsProper f] [Flat f]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base))
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (hTor : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction
      (Limits.pullback.snd f g)).obj (fourierMukaiKernelTensor f g K M)))
    (hpushforwardCoherence : Stacks.Cohomology.PerfectPushforward.PushforwardCoherenceResidue
      (Limits.pullback.snd f g) (derivedPushforwardOX (Limits.pullback.snd f g)))
    (hpushforwardTorDimension :
      Stacks.Cohomology.PerfectPushforward.PushforwardTorDimensionResidue
        (Limits.pullback.snd f g) D (derivedPushforwardOX (Limits.pullback.snd f g))) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  have hfp : FinitePresentation f := finitePresentation_of_finiteType f
  have _ : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlat f g D K hK M hM hTor
    hpushforwardCoherence hpushforwardTorDimension

/-! ### Clauses (5) and (6) -/

section RelativelyPerfect

open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward
  (TensorFamily IsGenuineTensorFamily isPerfect_derivedPushforward_of_isPerfectRelativeTo)

/-- The inverse-image ringed space `(X ×_S Y, pr_2^{-1}𝒪_Y)`, on which relative perfectness over
`Y` of an object of `D(𝒪_{X ×_S Y})` is measured, as [Stacks, Tag 0DI0] asks. This is
`AlgebraicGeometry.RingedSpace.inverseImage` at `pr_2`, named here only so that the long types
the hypotheses of [Stacks, Tag 0DI4] carry are written at one spelling. -/
abbrev fourierMukaiInverseImage : RingedSpace.{u, u} :=
  RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base

variable [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
  (D : TensorFamily (Limits.pullback.snd f g))
  (commShift : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
      (F : StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)),
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
      (F : StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)),
    have := commShift V F
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- **The common core of clauses (5) and (6) of [Stacks, Tag 0FYT].** Let `X ⟶ S` be proper,
flat and locally of finite presentation, let `Y` be Noetherian and let `K` be a `Y`-perfect
object of `D(𝒪_{X ×_S Y})` in the sense of [Stacks, Tag 0DI0]. Then `Φ_K` sends `D_perf(𝒪_X)`
into `D_perf(𝒪_Y)`.

This is the source's route. `L pr_1^* M` is perfect by [Stacks, Tag 09UA]; the second assertion
of [Stacks, Tag 0DI4] makes `T = L pr_1^* M ⊗^𝐋 K` `Y`-perfect, `pr_2 : X ×_S Y ⟶ Y` being
proper, flat and locally of finite presentation by base change; and the perfectness clause of
[Stacks, Tag 0DJT] then makes `R pr_{2,*} T` perfect.

`IsNoetherian Y` is a hypothesis neither clause makes. It is what the form of
[Stacks, Tag 0DJT] used here asks: `isPerfect_derivedPushforward_of_isPerfectRelativeTo` is the
Noetherian case, stated for an arbitrary pinned certificate family `D`, while the tag over an
arbitrary base (`isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap`) is stated at the
canonical certificate family.

Everything else carried below is a hypothesis of [Stacks, Tag 0DI4] in this library, passed
through unchanged, and each is documented at its source:

* `D` is the family of certified derived tensor products on the open subspaces of
  `(X ×_S Y, pr_2^{-1}𝒪_Y)`, which is how part (3) of [Stacks, Tag 08CG] is expressed, and `hD`
  pins its underived tensor product to the genuine one of [Stacks, Tag 06YU] — without that
  pinning the Tor clause of relative perfectness carries no information.
* `commShift` and `triangulated` are exactness of each `- ⊗^{L} ℱ[0]`, and `hrestricts` is
  locality of finite Tor dimension; these are the hypotheses [Stacks, Tag 0DI3] is stated with
  in this development.
* `hcl` is the complex level of [Stacks, Tag 09J3] — the step the source states with "details
  omitted".
* `hind` is `AlgebraicGeometry.Scheme.Hom.StrictlyPerfectInduction`, the generic triangulated
  induction peeling the top term off a bounded complex; it mentions neither `pr_2` nor `K`.
* `Θ`, `ΘcommShift`, `Θtriangulated`, `Θunit` and `Θtensor` are the interaction of the derived
  tensor product with restriction to open subspaces, as [Stacks, Tag 0DI4] asks for it here. -/
@[stacks 0FYT "clause (5): K is Y-perfect; Tag 0DI4's own hypotheses are carried and Y is \
assumed Noetherian, Tag 0DJT being applied in its Noetherian-base form"]
theorem isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel [IsNoetherian Y]
    (hD : IsGenuineTensorFamily (Limits.pullback.snd f g) D)
    (hrestricts : RingedSpace.FiniteTorDimensionRestricts (fourierMukaiInverseImage f g) D)
    (hind : Scheme.Hom.StrictlyPerfectInduction.{u + 1, u})
    (hcl : Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel.{u})
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (Θ : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
        (W : Opens (Limits.pullback f g : Scheme.{u}).toRingedSpace.carrier),
        (∀ x, x ∈ V → x ∈ W) →
      DerivedCategory (StrictlyPerfect.OXMod.{u, u}
        ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding)) ⥤
        DerivedCategory (StrictlyPerfect.OXMod.{u, u}
          ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)))
    (ΘcommShift : ∀ V W h, (Θ V W h).CommShift ℤ)
    (Θtriangulated : ∀ V W h, have := ΘcommShift V W h; (Θ V W h).IsTriangulated)
    (Θunit : ∀ V W h, (Θ V W h).obj ((DerivedCategory.singleFunctor
        (StrictlyPerfect.OXMod.{u, u}
          ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding)) 0).obj
          (StrictlyPerfect.structureModule
            ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding))) ≅
      (RingedSpace.derivedRestrictModules (fourierMukaiInverseImage f g) V).obj
        ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.snd f g)).obj K))
    (Θtensor : ∀ (V W h) (A : DerivedCategory
        (StrictlyPerfect.OXMod.{u, u} (Limits.pullback f g).toRingedSpace)),
      (Θ V W h).obj
          ((RingedSpace.derivedRestrictModules (Limits.pullback f g).toRingedSpace W).obj A) ≅
        (RingedSpace.derivedRestrictModules (fourierMukaiInverseImage f g) V).obj
          ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.snd f g)).obj
            (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
              (Limits.pullback f g).toRingedSpace).tensor.obj A).obj K)))
    (hK : (Limits.pullback.snd f g).IsPerfectRelativeTo D K) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  isPerfect_derivedPushforward_of_isPerfectRelativeTo (Limits.pullback.snd f g) D hD
    (fourierMukaiKernelTensor f g K M)
    (Scheme.Hom.isPerfectRelativeTo_derivedTensor (Limits.pullback.snd f g) D commShift
      triangulated hrestricts hind hcl ((fourierMukaiPullback f g).obj M) K Θ ΘcommShift
      Θtriangulated Θunit Θtensor (isPerfect_fourierMukaiPullback f g M hM) hK)

end RelativelyPerfect

section RelativelyPerfectNoetherianBase

open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward
  (TensorFamily IsGenuineTensorFamily)

variable [IsNoetherian S] [IsProper f] [Flat f]
  (D : TensorFamily (Limits.pullback.snd f g))
  (commShift : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
      (F : StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)),
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)) 0).obj F)).CommShift ℤ)
  (triangulated : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
      (F : StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)),
    have := commShift V F
    ((D V).derivedTensor.flip.obj ((DerivedCategory.singleFunctor
      (StrictlyPerfect.OXMod.{u, u}
        ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)) 0).obj F)).IsTriangulated)

include commShift triangulated in
/-- **[Stacks, Tag 0FYT], clause (6).** Let `S` be Noetherian, let `X ⟶ S` be flat and proper,
let `Y` be Noetherian and let `K` be a `Y`-perfect object of `D(𝒪_{X ×_S Y})`. Then `Φ_K` sends
`D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

The source says: part (6) follows from part (5) in the same way that part (4) follows from
part (3), that is through [Stacks, Tag 01TX]. That is what happens here, and it happens by
instance search: `X ⟶ S` is proper, hence locally of finite type, and `S` is Noetherian, hence
locally Noetherian, so part (1) of [Stacks, Tag 01TX] — Mathlib's
`AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`,
recorded against that tag in
`StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentation/LocallyNoetherian.lean` — supplies
the `AlgebraicGeometry.LocallyOfFinitePresentation` instance that
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel` asks for, and no other
hypothesis changes.

`IsNoetherian Y` is carried for the same reason as in clause (5): the form of
[Stacks, Tag 0DJT] used there is its Noetherian case, and `S` Noetherian says nothing about
`Y`. -/
@[stacks 0FYT "clause (6), reduced to clause (5) by Tag 01TX part (1); Tag 0DI4's own \
hypotheses are carried and Y is assumed Noetherian"]
theorem isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel_of_noetherianBase [IsNoetherian Y]
    (hD : IsGenuineTensorFamily (Limits.pullback.snd f g) D)
    (hrestricts : RingedSpace.FiniteTorDimensionRestricts (fourierMukaiInverseImage f g) D)
    (hind : Scheme.Hom.StrictlyPerfectInduction.{u + 1, u})
    (hcl : Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel.{u})
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M)
    (Θ : ∀ (V : Opens (fourierMukaiInverseImage f g).carrier)
        (W : Opens (Limits.pullback f g : Scheme.{u}).toRingedSpace.carrier),
        (∀ x, x ∈ V → x ∈ W) →
      DerivedCategory (StrictlyPerfect.OXMod.{u, u}
        ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding)) ⥤
        DerivedCategory (StrictlyPerfect.OXMod.{u, u}
          ((fourierMukaiInverseImage f g).restrict V.isOpenEmbedding)))
    (ΘcommShift : ∀ V W h, (Θ V W h).CommShift ℤ)
    (Θtriangulated : ∀ V W h, have := ΘcommShift V W h; (Θ V W h).IsTriangulated)
    (Θunit : ∀ V W h, (Θ V W h).obj ((DerivedCategory.singleFunctor
        (StrictlyPerfect.OXMod.{u, u}
          ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding)) 0).obj
          (StrictlyPerfect.structureModule
            ((Limits.pullback f g).toRingedSpace.restrict W.isOpenEmbedding))) ≅
      (RingedSpace.derivedRestrictModules (fourierMukaiInverseImage f g) V).obj
        ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.snd f g)).obj K))
    (Θtensor : ∀ (V W h) (A : DerivedCategory
        (StrictlyPerfect.OXMod.{u, u} (Limits.pullback f g).toRingedSpace)),
      (Θ V W h).obj
          ((RingedSpace.derivedRestrictModules (Limits.pullback f g).toRingedSpace W).obj A) ≅
        (RingedSpace.derivedRestrictModules (fourierMukaiInverseImage f g) V).obj
          ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.snd f g)).obj
            (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
              (Limits.pullback f g).toRingedSpace).tensor.obj A).obj K)))
    (hK : (Limits.pullback.snd f g).IsPerfectRelativeTo D K) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  isPerfect_fourierMukai_of_isPerfectRelativeTo_kernel f g D commShift triangulated hD hrestricts
    hind hcl K M hM Θ ΘcommShift Θtriangulated Θunit Θtensor hK

end RelativelyPerfectNoetherianBase

end AlgebraicGeometry

end
