module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BoundedLocalApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Summands
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfect objects are exactly the pseudo-coherent ones of locally finite Tor dimension

Tag 08CQ characterises the perfect objects of `D(O_X)` on a ringed space as those which are
pseudo-coherent and locally of finite Tor dimension. This file proves both directions, and
deduces Tag 08CS: both summands of a perfect binary biproduct are perfect.

## Main results

* `Stacks.Cohomology.TorAmplitude.exists_bounds_of_isStrictlyPerfect`: a strictly perfect complex
  vanishes outside some finite interval.
* `Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect`: a perfect object of `D(O_X)` is
  pseudo-coherent.
* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect`: a perfect object of
  `D(O_X)` locally has finite Tor dimension.
* `Stacks.Cohomology.TorAmplitude.isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect`:
  the forward implication of Tag 08CQ.
* `Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'`: the two spellings of
  pseudo-coherence on a ringed space agree.
* `Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`:
  the converse implication of Tag 08CQ.
* `Stacks.Cohomology.TorAmplitude.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`:
  **Tag 08CQ**, as an equivalence.
* `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`: **Tag 08CS.**

## Implementation notes

The pseudo-coherence half takes place at the level of complexes: a perfect complex is
`m`-pseudo-coherent for every `m`, because near every point it receives a quasi-isomorphism from a
strictly perfect complex (`AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent`). Only one
representative complex is needed for every `m` at once — the one perfectness supplies — so the
conclusion is `IsPseudoCoherent` and not merely `IsPseudoCoherentFrom` for each `m` separately,
and no derived category of an open subspace occurs.

The Tor-dimension half is Tag 08CI's easy direction. On a member of the cover the object is
isomorphic in the derived category to the localization of a strictly perfect complex: the local
model maps to the restriction of the representative by a quasi-isomorphism, and the derived
restriction of the object is identified with the localization of the restricted representative
by `Functor.mapDerivedCategoryFactors`. A strictly perfect complex has flat terms (Tag 08C4
through `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree`)
and vanishes outside a finite interval, so
`Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative` gives Tor
amplitude in that interval.

Everything is destructured with `obtain` rather than with `Exists.choose`, for a concrete reason:
here the data is *consumed*, not produced. The open `U` that
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is applied at, and the complex `P`
that `Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative` is applied
at, each occur several times, and each occurrence makes instance search resolve
`HasDerivedCategory (OXMod (X.restrict ?.isOpenEmbedding))` out of the `∀ U : Opens X.carrier`
variable. With `Exists.choose` chains those arguments are large `Classical.choose` terms and the
search has to `whnf` through them once per occurrence: the two theorems of the forward half, as
first written, did not finish elaborating in **thirty minutes**. With `obtain` the same arguments
are local hypotheses, so the search sees a free variable and the file elaborates normally. So the
hazard is not `obtain` versus `Exists.choose` as such; it is whether the subject of an instance
binder is an fvar or a term. Where instead the whole nested existential is *produced* as a term
the trade goes the other way, `obtain` being pure overhead at about 1.2 s per use.

**The reverse implication.** Beyond Tag 08BL it rests on two degreewise statements about one
complex. The first is `StrictlyPerfect.isStrictlyPerfect_stupidTrunc` — the brutal truncation
`σ^{≥a-1}P` of a strictly perfect complex is strictly perfect, which is what gives the local
approximation the shape that the flatness of the opcycles asks for, since pseudo-coherence
constrains the degrees of an approximation only from above. The second is
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictOpcyclesIso`, the comparison of the
opcycles of a restricted complex with the restriction of the opcycles, which is what turns the
local conclusion of Tag 08BL into the hypothesis of the truncation criterion. Neither needs a
comparison of the opcycles or of the canonical truncation of `σ^{≥a-1}P` with those of `P`: the
flatness is applied to the truncated complex and read off there, exactly as the ringed-site
proof of Tag 08G7 does.

With those in place the whole chain is assembled as Tag 08CP,
`Stacks.Cohomology.PerfectFromTorAmplitude.isPerfect_of_hasTorAmplitude_of_isPseudoCoherentFrom`,
and the converse below is that plus the locality of perfectness
(`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`) — which is what makes
the per-member intervals of `LocallyHasFiniteTorDimension` usable at all, Tag 08CP needing one
global interval — plus the fact that pseudo-coherence restricts to an open subspace
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules`).

**Two spellings of pseudo-coherence.** The predicate of Tag 08CB exists twice in the trees, once
written with `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex` and once with
`AlgebraicGeometry.RingedSpace.restrictComplex`. The two restriction functors are the same
pushforward, so the two predicates are the same proposition; but typeclass synthesis does not
cross between them, and the results this file composes are split across the two — the forward
half and Tag 08CK at the first, the restriction of pseudo-coherence and Tag 08CE at the second.
`isPseudoCoherent_iff_isPseudoCoherent'` is that translation, proved by destructuring and
rebuilding, which is all it is.

The universes of the space, its structure sheaf and its modules all coincide, as they already
must for `StrictlyPerfect.OXMod` and for the local-model engine of Tags 08CR/08CP. For the
forward half the derived category's own hom universes stay independent (`d` for `X`, `d'` for its
opens, which only the Tor-dimension half involves); the converse still carries
`HasDerivedCategory.standard` on the opens, which fills the family of models of the derived
categories of the opens that `isPerfect_of_local_isPerfect` takes. Everything the converse
consumes takes the corresponding instance as a parameter.

## References

* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
* [Stacks Project, Tag 08CE](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d d'

/-- **A strictly perfect complex vanishes outside a finite interval.** Only finitely many terms
are nonzero, so the set of such degrees is bounded on both sides; when it is empty the interval
`[0, 0]` will do. -/
theorem exists_bounds_of_isStrictlyPerfect {X : RingedSpace.{u, u}}
    (P : CochainComplex (OXMod.{u} X) ℤ) (hP : IsStrictlyPerfect P) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i ∉ Set.Icc a b → IsZero (P.X i) := by
  classical
  have hs : {i : ℤ | ¬ IsZero (P.X i)}.Finite := hP.bounded
  by_cases hne : {i : ℤ | ¬ IsZero (P.X i)}.Nonempty
  · obtain ⟨a, ha⟩ := hs.bddBelow
    obtain ⟨b, hb⟩ := hs.bddAbove
    refine ⟨min a b, max a b, min_le_max, ?_⟩
    intro i hi
    by_contra hzero
    exact hi ⟨(min_le_left _ _).trans (ha hzero), (hb hzero).trans (le_max_right _ _)⟩
  · refine ⟨0, 0, le_rfl, ?_⟩
    intro i _
    by_contra hzero
    exact hne ⟨i, hzero⟩

/-- **The two spellings of pseudo-coherence on a ringed space agree.** The predicate of Tag 08CB
is written twice in the trees, once with
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex` and once with
`AlgebraicGeometry.RingedSpace.restrictComplex`; the two restriction functors are the same
pushforward, so the two predicates are the same proposition and the translation is the identity.

It is stated rather than inlined because typeclass synthesis does not cross between the two
spellings, while an ordinary application -- which is all this is -- does. -/
theorem isPseudoCoherent_iff_isPseudoCoherent' {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u} X)] (E : DerivedCategory (OXMod.{u} X)) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E ↔
      AlgebraicGeometry.RingedSpace.IsPseudoCoherent E := by
  exact Iff.rfl

section Forward

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]

-- Restriction to an open is exact, so it descends to derived categories.  Tag 08C9 proves both
-- halves, but neither is registered as a global instance, so both are seated locally here.
attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

omit [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))] in
/-- **A perfect object of `D(O_X)` is pseudo-coherent.** A representative which is a perfect
complex is `m`-pseudo-coherent for every `m`: near every point it receives a quasi-isomorphism
from a strictly perfect complex, which is an isomorphism on cohomology in every degree
(`AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent`). Only the model of `D(O_X)` is
involved. -/
@[sga "6 I 5.8.1" "partial"]
theorem isPseudoCoherent_of_isPerfect (E : DerivedCategory (OXMod.{u} X))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect E) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E :=
  (isPseudoCoherent_iff_isPseudoCoherent' E).2
    (AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent hE)

/-- **A perfect object of `D(O_X)` locally has finite Tor dimension.** On a member `U` of the
cover witnessing perfectness, the derived restriction of the object is isomorphic to the
localization of a strictly perfect complex `P`: the quasi-isomorphism `P ⟶ Fc|_U` becomes an
isomorphism in `D(O_U)`, and `Functor.mapDerivedCategoryFactors` identifies the derived
restriction of `Q.obj Fc` with `Q.obj (Fc|_U)`. The terms of `P` are direct summands of finite
free modules, hence flat, and `P` vanishes outside a finite interval, so Tag 08CI's easy
direction gives Tor amplitude in that interval. -/
@[sga "6 I 5.8.1" "partial", sga "6 I 8.5" "Clause, special case"]
theorem locallyHasFiniteTorDimension_of_isPerfect (E : DerivedCategory (OXMod.{u} X))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect E) :
    LocallyHasFiniteTorDimension X E := by
  obtain ⟨Fc, hFc, ⟨eE⟩⟩ := hE
  obtain ⟨I, U, hsup, hmod⟩ := hFc
  refine ⟨I, U, hsup, fun i => ?_⟩
  obtain ⟨P, hP, f, hf⟩ := hmod i
  obtain ⟨a, b, -, hz⟩ := exists_bounds_of_isStrictlyPerfect P hP
  have hqi : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  have eU := (@asIso _ _ _ _ (DerivedCategory.Q.map f) hqi) ≪≫
    ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X (U
      i)).mapDerivedCategoryFactors.app Fc).symm ≪≫
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X (U
      i)).mapDerivedCategory.mapIso eE
  exact ⟨a, b, Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative _ a b P
    (fun j =>
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree _
        (hP.directSummand j)) hz eU⟩

/-- **Tag 08CQ, the forward implication.** A perfect object of `D(O_X)` is pseudo-coherent and
locally has finite Tor dimension. -/
@[stacks 08CQ "(1) implies (2)", sga "6 I 5.8.1" "necessity", sga "6 I 8.5" "special case"]
theorem isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
    (E : DerivedCategory (OXMod.{u} X)) (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect E) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E ∧
      LocallyHasFiniteTorDimension X E :=
  ⟨isPseudoCoherent_of_isPerfect E hE, locallyHasFiniteTorDimension_of_isPerfect E hE⟩

end Forward

section Converse

open Stacks.Cohomology.PerfectFromTorAmplitude

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

-- The derived categories of the open subspaces are the standard ones here: they fill the family
-- of models that `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`,
-- through which the converse localises, takes for the derived categories its hypothesis
-- mentions. Everything the converse consumes -- Tag 08CE, Tag 08CK, Tag 08CP -- takes the
-- corresponding instance as a parameter.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

/-- **Tag 08CQ, the converse implication.** A pseudo-coherent object of `D(O_X)` which locally has
finite Tor dimension is perfect.

Perfectness is local on the space
(`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`), which is what makes
the per-member Tor-amplitude intervals of `LocallyHasFiniteTorDimension` usable: over a member `U`
of the cover witnessing finite Tor dimension there is a *single* interval `[a, b]`, and the
restriction of `E` to `X|_U` is still pseudo-coherent, hence `(a-1)`-pseudo-coherent, so Tag 08CP
applies there. The interval is widened to `[min a b, max a b]` so that it is nonempty, which Tag
08CP requires. -/
@[stacks 08CQ "(2) implies (1)", sga "6 I 5.8.1" "sufficiency"]
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (E : DerivedCategory (OXMod.{u} X))
    (hpc : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E)
    (htor : LocallyHasFiniteTorDimension X E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect E := by
  obtain ⟨I, U, hsup, hfin⟩ := htor
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect E fun x => ?_
  obtain ⟨i, hxi⟩ : ∃ i : I, x ∈ U i := by
    refine Opens.mem_iSup.1 ?_
    rw [hsup]
    trivial
  obtain ⟨a, b, hamp⟩ := hfin i
  refine ⟨U i, hxi, ?_⟩
  -- Widen the interval so that it is nonempty, which Tag 08CP requires.
  have hampU : HasTorAmplitude (X.restrict (U i).isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} X
        (U i)).mapDerivedCategory.obj E) (min a b) (max a b) := fun F j hj =>
    hamp F j fun hmem => hj ⟨(min_le_left a b).trans hmem.1,
      hmem.2.trans (le_max_right a b)⟩
  refine isPerfect_of_hasTorAmplitude_of_isPseudoCoherentFrom
    (X := X.restrict (U i).isOpenEmbedding) _ (min a b) (max a b) min_le_max hampU ?_
  refine AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules E
    (min a b - 1) ?_ (U i)
  exact (AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall E).1
    ((isPseudoCoherent_iff_isPseudoCoherent' E).1 hpc) (min a b - 1)

/-- **Tag 08CQ.** An object of `D(O_X)` on a ringed space is perfect exactly when it is
pseudo-coherent and locally has finite Tor dimension. -/
@[sga "6 I 5.8.1" "special case", sga "6 I 8.5" "special case"]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DerivedCategory (OXMod.{u} X)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect E ↔
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E ∧
        LocallyHasFiniteTorDimension X E :=
  ⟨isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect E,
    fun h => isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension E h.1 h.2⟩

/-- **Tag 08CS.** If a binary biproduct in `D(O_X)` is perfect, then so are both of its summands.

By Tag 08CQ the biproduct is pseudo-coherent and locally of finite Tor dimension; both properties
pass to the summands, pseudo-coherence by Tag 08CE and locally finite Tor dimension by Tag 08CK;
and Tag 08CQ turns the pair back into perfectness of each summand. -/
@[stacks 08CS]
theorem isPerfect_of_biprod (K L : DerivedCategory (OXMod.{u} X))
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (K ⊞ L)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect K ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect L := by
  obtain ⟨hpc, htor⟩ := isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect (K ⊞ L) h
  obtain ⟨hpcK, hpcL⟩ := Stacks.PseudoCoherence.Summands.isPseudoCoherent_of_biprod K L
    ((isPseudoCoherent_iff_isPseudoCoherent' (K ⊞ L)).1 hpc)
  obtain ⟨htorK, htorL⟩ := locallyHasFiniteTorDimension_of_biprod K L htor
  exact ⟨isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension K
      ((isPseudoCoherent_iff_isPseudoCoherent' K).2 hpcK) htorK,
    isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension L
      ((isPseudoCoherent_iff_isPseudoCoherent' L).2 hpcL) htorL⟩

end Converse

end Stacks.Cohomology.TorAmplitude

end
