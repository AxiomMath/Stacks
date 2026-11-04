module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRingLevelZeroLocusOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The vanishing locus is a closed subspace when the support is proper

In Situation Stacks 083F — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a
map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — Stacks 083M says that if `f` is locally of
finite presentation, `𝒢` is of finite presentation and flat over `B`, and the support of `𝒢` is
proper over `B`, then `F_zero` is an algebraic space and `F_zero ⟶ B` is a closed immersion,
which is moreover of finite presentation as soon as `ℱ` is of finite type.

The source proves this by reduction to Stacks 0CWC, which is the same statement with `f` of
finite presentation and with properness of the support replaced by purity of `𝒢` relative
to `B`.  Both steps of that reduction are carried out here:

* when `f` is of finite presentation, purity of `𝒢` relative to `B` is supplied by Stacks 0CVI
  part (1) out of properness of the support, and Stacks 0CWC finishes;
* in general the source replaces `X` by the closed subspace `Z ⊆ X` cut out by the zeroth
  Fitting ideal of `𝒢` (Stacks 0CZ3), moves `u` to the adjoint map `i^*ℱ ⟶ ℋ` on `Z`
  (Stacks 0CZ6 and Stacks 0CW7) and observes that `Z ⟶ B` is proper, hence that `ℋ` is pure
  relative to `B` by Stacks 0CVI part (2) and that `Z ⟶ B` is of finite presentation.

In both cases properness of the closed subspace carrying `𝒢` is **proved** from properness of
the support, which is hypothesis (3) of Stacks 083M, by
`AlgebraicGeometry.Space.isProper_comp_of_hasProperSupport_of_range_subset`: hypothesis (3) is
properness of the support as a closed set of points, hence of the *reduced* induced closed
subspace on it (Stacks 0CZD), and Stacks 0CZE followed by Stacks 0CZC carries it to the
possibly non-reduced subspace the module lives on.  All that each theorem asks about that
subspace is the containment `|i|(|Z|) ⊆ Supp(𝒢)` — part (2) of Stacks 0CZ6 for the Fitting
subspace — so that it is no larger than the support.

Stacks 0CWC is itself conditional in this development: its closed-immersion clause is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusSubspace.lean` and its
finite-presentation clause in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`, each from inputs
it does not formalize.  So neither theorem below carries 0CWC as a black box; each carries those
two inputs — the dévissage and affine endgame of 0CWC's own proof, and the chart case at the
affine stages of the source's proof of Stacks 083J part (2) — and obtains
`AlgebraicGeometry.Space.ModuleMapSituation.Is0CWC` from them by
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus`.  The
geometric input of the second paragraph of the source's proof is carried as the data
`AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction`.  See the
implementation notes for exactly which clause each carried hypothesis stands for.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.IsTargetPureRelative` and
  `.IsTargetUniversallyPureRelative`: `𝒢` is pure, resp. universally pure, relative to `B`.
* `AlgebraicGeometry.Space.ModuleMapSituation.ZeroLocusRepresentation`: the conclusion of
  Stacks 083M and of Stacks 0CWC — a closed subspace of `B` representing `F_zero`, whose
  inclusion is of finite presentation when `ℱ` is of finite type.
* `AlgebraicGeometry.Space.ModuleMapSituation.Is0CWC`: the statement of Stacks 0CWC.
* `AlgebraicGeometry.Space.ModuleMapSituation.Is0CWCStageChartInput`: the chart input of this
  development's Stacks 0CWC.  Its geometric input is
  `AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput`, taken directly, the affine
  endgame being proved.
* `AlgebraicGeometry.Space.ModuleMapSituation.replaceSource`: the situation of Stacks 083F
  obtained by replacing the source space and both modules, keeping the target `B`.
* `AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction`: the output of the
  second paragraph of the source's proof, carried as data.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus`:
  **Stacks 0CWC** for every situation of Stacks 083F at once, from the one input this
  development does not formalize.
* `AlgebraicGeometry.Space.ModuleMapSituation.isTargetUniversallyPureRelative_of_isProper`:
  **Stacks 0CVI part (2)** read through the bridge: if `f` itself is proper then `𝒢` is
  universally pure relative to `B`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isTargetUniversallyPureRelative_of_pushforward`:
  **Stacks 0CVI part (1)** read through the bridge: if `𝒢 = i_*ℋ` for a closed immersion
  `i : Z ⟶ X` with `Z ⟶ B` proper, then `𝒢` is universally pure relative to `B`.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation_of_isFinitePresentation`:
  **Stacks 083M for `f` of finite presentation**, the first paragraph of the source's proof and
  the only case the source considers to be of interest.
* `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation`: **Stacks 083M**, with
  `f` merely locally of finite presentation.

## Implementation notes

### What is carried, and for which clause

`AlgebraicGeometry.Space.ModuleMapSituation.Is0CWC` is Stacks 0CWC verbatim, universally
quantified over situations of Stacks 083F: under `f` of finite presentation, `𝒢` of finite
presentation, flat over `B` and pure relative to `B`, the functor `F_zero` is represented by a
closed subspace of `B`, whose inclusion is of finite presentation when `ℱ` is of finite type.
Its own hypotheses are *not* carried: they are discharged at every application below, which is
the whole content of Stacks 083M.

`Is0CWC` is not a hypothesis of either theorem.  Its closed-immersion clause is proved,
conditionally, in
`StacksFrontier/AlgebraicGeometry/Spaces/ZeroLocusClosedEtaleLocalDescent.lean` and its
finite-presentation clause in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`, and
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus` assembles
them into `Is0CWC` from the one input this development does not formalize.  That one is what
the two theorems carry in place of 0CWC:

* `hdev`, `AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput`: for every situation
  satisfying 0CWC's hypotheses, a flat chart whose image carries `Ass_{X/B}(𝒢)` and along which
  the sections of `g^*𝒢` are projective over the functions on the base.  This is the first
  stage of the source's proof of 0CWC, the dévissage out of purity (Stacks 0CW5, which
  this development has only conditionally, with 0CVZ, 0CVV, 0CW3 part (2) and Morphisms 05LW).
  Neither of the other two stages is carried: the affine endgame Stacks 083L is proved, as
  `AlgebraicGeometry.Space.ModuleMapSituation.affineChartZeroLocusClosed`, and so is the descent
  step that joins them,
  `AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusClosedEtaleLocalOnBase`.  The
  dévissage is taken directly.
Nothing of Stacks 083J part (2) is carried.  The chart case of that clause at the affine stages,
`AlgebraicGeometry.Space.ModuleMapSituation.Is0CWCStageChartInput`, is proved, as
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWCStageChartInput`, out of the limit-free
ring-level reading of the vanishing locus of the chart situation.

  Nor is part (2) itself carried, that is, relative limit preservation of the inclusion of the
  vanishing subfunctor for every situation satisfying 0CWC's hypotheses with `ℱ` of finite type —
  Stacks 083J part (2) together with its transport from the subterminal presheaf `F_zero` to a
  subfunctor of `B`.  Part (2) at the source's own hypothesis and the transport are both proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`, and part (2)'s
  hypothesis that the support of `ℱ` be quasi-compact over `B` is discharged for the situations
  0CWC applies to, where `f` is of finite presentation and hence quasi-compact, by
  `AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`.

The implication (2) ⇒ (1) of Stacks 01ZC for a morphism of the site is *not* among the inputs.
This development's reading of Stacks 04AK needs it, and it is proved, as
`AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map`, so
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving` is
unconditional and nothing below carries it.

Beyond those two the two theorems carry:

* `hdec`, decency of the structure morphism.  Purity in this development is a notion attached
  to a situation of Stacks 0CV6, which requires its morphism to be of finite type *and decent*;
  so the purity hypothesis of Stacks 0CWC cannot even be stated without decency, and
  Situation 083F does not provide it.  This is a requirement inherited from the source's own
  Situation 0CV6, not an assumption introduced here.
* for the case of `f` of finite presentation, the closed-immersion presentation `𝒢 ≅ i_*ℋ`
  together with the input `hin` of this library's Stacks 0CVH.  These are exactly the inherited
  inputs of this library's Stacks 0CVI part (1): the presentation is what Stacks 07U0 produces
  at the scheme-theoretic support of `𝒢`, and `hin` is affine base change on the base changes of
  the situation.  Properness of `Z ⟶ B`, which Stacks 0CVI part (1) consumes, is *not* carried:
  it is derived from hypothesis (3) of Stacks 083M as described above.  What is asked of the
  presentation beyond the isomorphism is the containment `|i|(|Z|) ⊆ Supp(𝒢)`, the hypothesis
  `hZsupp`; it holds for the two presentations the source uses — part (4) of Stacks 07U0 for the
  scheme-theoretic support, part (2) of Stacks 0CZ6 for the Fitting subspace — and hypothesis (3)
  cannot replace it, since a presentation with `ℋ = 0` leaves `Z` entirely unconstrained.
* for the general case, `AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction`,
  whose fields are the second paragraph of the source's proof: the closed subspace `Z` cut out
  by the zeroth Fitting ideal of `𝒢` and the local finite presentation of its inclusion
  (Stacks 0CZ3, Stacks 0CZ5 and Stacks 084Q), the identification of the underlying set of `Z`
  with the support of `𝒢` (Stacks 0CZ6 part (2)), the module `ℋ` on `Z` with `i_*ℋ = 𝒢` and its
  finite type (Stacks 0CZ6 part (3)), its finite presentation (Stacks 0561), its flatness (the
  source's "check on stalks; details omitted"), the adjoint map `v : i^*ℱ ⟶ ℋ`, and the
  agreement of the two vanishing loci (Stacks 0CW7 part (1)).

### What is proved

Everything else.  From the data above, both theorems **derive** rather than assume:

* properness over `B` of the closed subspace carrying the module, from hypothesis (3) of
  Stacks 083M by Stacks 0CZE and Stacks 0CZC, in
  `AlgebraicGeometry.Space.isProper_comp_of_hasProperSupport_of_range_subset`.  This is the one
  step through which hypothesis (3) acts: everything else below consumes its conclusion and not
  the hypothesis;
* purity of the relevant module relative to `B`, from Stacks 0CVI — part (1) in the first
  theorem, part (2) in the second, the latter needing no input beyond properness;
* in the general case, finite presentation of `Z ⟶ B`: locally of finite presentation by
  composing the inclusion with `f`, which is where hypothesis (1) of Stacks 083M is used, and
  quasi-compact and quasi-separated because `Z ⟶ B` is proper;
* in the general case, finite type of `i^*ℱ` from finite type of `ℱ`, which is what carries the
  finite-presentation clause of Stacks 083M across the reduction;
* the transport of the representing closed subspace back from the situation on `Z` to the
  original situation.  The two situations have the same target `B` by construction, so they have
  the same category of test schemes and the *same* closed subspace of `B` serves; only the
  characterisation of the vanishing locus has to be moved, by the carried Stacks 0CW7.

### The shape of the conclusion

`F_zero` is a subterminal presheaf on the test schemes over `B`, so "`F_zero` is an algebraic
space and `F_zero ⟶ B` is a closed immersion" is: there is a subfunctor `Z` of `B` which is a
closed subspace, Stacks 02YU part (4), such that a test scheme lies in `F_zero` exactly when its
structure morphism factors through `Z`.  This is the form in which
`AlgebraicGeometry.Space.ModuleMapSituation.exists_isOpenSubspace_isSurjectiveAt_iff` states the
companion result Stacks 09TP for `F_surj`, with `IsOpenSubspace` in place of `IsClosedSubspace`.
"`F_zero ⟶ B` is of finite presentation" is then finite presentation of the inclusion `Z.ι`.

## References

* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
* [Stacks Project, Tag 0CVI](https://stacks.math.columbia.edu/tag/0CVI)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CW7](https://stacks.math.columbia.edu/tag/0CW7)
* [Stacks Project, Tag 0CZ6](https://stacks.math.columbia.edu/tag/0CZ6)
* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 0CW5](https://stacks.math.columbia.edu/tag/0CW5)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ModuleMapSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The purity situation of the target module

The bridge between Situation 083F and the purity notions of Stacks 0CVD — the situation of
Stacks 0CV6 carried by the structure morphism `f : X ⟶ B` and the target module `𝒢` — is
`AlgebraicGeometry.Space.ModuleMapSituation.targetPrePureSituation`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusSubspace.lean`, where it is also what
hypothesis (2) of Stacks 0CWC is stated through.  It needs two properties of `f` that
Situation 083F does not record — finite type and decency — because Situation 0CV6 requires
them: purity of `𝒢` relative to `B` is not even expressible without them.
-/

/-- **Stacks 0CVD part (5) for the target module of a situation of Stacks 083F.**  The module
`𝒢` is *pure relative to `B`*: it is pure above every point of `B`. -/
def IsTargetPureRelative (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) : Prop :=
  ∀ y : points B S hS D.Y.1, IsPureAbove (D.targetPrePureSituation hft hdec hGft y)

/-- **Stacks 0CVD part (4) for the target module of a situation of Stacks 083F.**  The module
`𝒢` is *universally pure relative to `B`*: it is universally pure above every point of `B`. -/
def IsTargetUniversallyPureRelative (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) : Prop :=
  ∀ y : points B S hS D.Y.1, IsUniversallyPureAbove (D.targetPrePureSituation hft hdec hGft y)

/-- Purity of `𝒢` relative to `B` is Stacks 0CVD part (5) for the bridged situation, at any
chosen point of `B`: the purity predicates of Stacks 0CVD quantify the chosen point away. -/
theorem isTargetPureRelative_iff_isPureRelative (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) (y : points B S hS D.Y.1) :
    D.IsTargetPureRelative hft hdec hGft ↔
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y) :=
  Iff.rfl

/-- Universal purity of `𝒢` relative to `B` is Stacks 0CVD part (4) for the bridged situation,
at any chosen point of `B`. -/
theorem isTargetUniversallyPureRelative_iff_isUniversallyPureRelative
    (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G) (y : points B S hS D.Y.1) :
    D.IsTargetUniversallyPureRelative hft hdec hGft ↔
      IsUniversallyPureRelative (D.targetPrePureSituation hft hdec hGft y) :=
  Iff.rfl

/-- Universal purity relative to `B` implies purity relative to `B`, Stacks 0CVD. -/
theorem IsTargetUniversallyPureRelative.isTargetPureRelative
    {D : ModuleMapSituation.{u, u} B S hS}
    {hft : IsFiniteType B S hS D.f.hom} {hdec : IsDecent B S hS D.f.hom}
    {hGft : SheafOfModules.IsFiniteTypeOnSite D.G}
    (h : D.IsTargetUniversallyPureRelative hft hdec hGft) :
    D.IsTargetPureRelative hft hdec hGft :=
  fun y => IsPureAbove.of_isUniversallyPureAbove (h y)

/-! ### Stacks 0CVI through the bridge -/

/-- **Stacks 0CVI part (2) for the target module of a situation of Stacks 083F.**  If the
structure morphism `f : X ⟶ B` is proper then `𝒢` is universally pure relative to `B`.

This needs no input beyond properness: a proper morphism is universally closed and a universally
closed morphism admits no impurity diagram at all.

Deliberately carries no Stacks 0CVI tag attribute. It is a pointwise lifting of
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper` into the language of a situation of
Stacks 083F — its proof is that declaration applied at each `y` — and the covering set of
Stacks 0CVI is already the four declarations of
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityProper.lean`.  Registering this adapter as well
would record the tag as carried by six declarations when four are the content. -/
theorem isTargetUniversallyPureRelative_of_isProper (D : ModuleMapSituation.{u, u} B S hS)
    (hdec : IsDecent B S hS D.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hproper : IsProper B S hS D.f.hom) :
    D.IsTargetUniversallyPureRelative (IsProper.isFiniteType B S hS hproper) hdec hGft :=
  fun _ => isUniversallyPureAbove_of_isProper _ hproper

/-- The closed-immersion presentation of `𝒢` as data for Stacks 0CVI part (1), read through
the bridge: a closed immersion `i : Z ⟶ X` and a finite type quasi-coherent `𝒪_Z`-module `ℋ`
with `𝒢 ≅ i_*ℋ`. -/
@[reducible] noncomputable def closedSubspaceModuleOfPushforward
    (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ D.X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2) (hHft : SheafOfModules.IsFiniteTypeOnSite H)
    (hHqc : H.IsQuasicoherentOnSite)
    (e : D.G ≅ (modulePushforward B S hS i).obj H) (y : points B S hS D.Y.1) :
    ClosedSubspaceModule (D.targetPrePureSituation hft hdec hGft y) where
  Z := Z
  i := i
  isClosedImmersion := hi
  G := H
  moduleFiniteType := hHft
  moduleQuasicoherent := hHqc
  iso := e

/-- **Stacks 0CVI part (1) for the target module of a situation of Stacks 083F.**  If `𝒢` is
the direct image `i_*ℋ` of a finite type quasi-coherent module along a closed immersion
`i : Z ⟶ X` whose composite `Z ⟶ B` is proper, then `𝒢` is universally pure relative to `B`.

This is part (2) applied to the situation on `Z`, transferred to `𝒢` by Stacks 0CVH.  The
hypothesis `hin`, affine base change on the base changes of the situation, is not used: the
proof is the unconditional
`AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_of_isProper_comp`.

Deliberately carries no Stacks 0CVI tag attribute, for the reason given on
`AlgebraicGeometry.Space.ModuleMapSituation.isTargetUniversallyPureRelative_of_isProper`: this
is a pointwise lifting of
`AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_of_isProper_comp` into the
language of a situation of Stacks 083F, and the covering set of Stacks 0CVI is already the four
declarations of `StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityProper.lean`. -/
theorem isTargetUniversallyPureRelative_of_pushforward
    (D : ModuleMapSituation.{u, u} B S hS)
    (hft : IsFiniteType B S hS D.f.hom) (hdec : IsDecent B S hS D.f.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ D.X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2) (hHft : SheafOfModules.IsFiniteTypeOnSite H)
    (hHqc : H.IsQuasicoherentOnSite)
    (e : D.G ≅ (modulePushforward B S hS i).obj H)
    (hin : ∀ y : points B S hS D.Y.1,
      (D.closedSubspaceModuleOfPushforward hft hdec hGft i hi H hHft hHqc e y).BaseChangeInput)
    (hZB : IsProper B S hS (i.hom ≫ D.f.hom)) :
    D.IsTargetUniversallyPureRelative hft hdec hGft :=
  fun y =>
    (D.closedSubspaceModuleOfPushforward hft hdec hGft i hi H hHft hHqc e
      y).isUniversallyPureAbove_of_isProper_comp hZB

/-! ### The conclusion of Stacks 083M -/

/-- **The conclusion of Stacks 083M and of Stacks 0CWC.**  There is a subfunctor `Z` of `B`
which is a closed subspace, Stacks 02YU part (4), whose inclusion is of finite presentation as
soon as `ℱ` is of finite type, and which represents `F_zero`: a test scheme over `B` lies in
`F_zero` exactly when its structure morphism factors through `Z`.

The first conjunct of `AlgebraicGeometry.Space.IsClosedSubspace` is that `Z` is an algebraic
space and the second is that `Z ⟶ B` is a closed immersion, so this says exactly that `F_zero`
is an algebraic space and that `F_zero ⟶ B` is a closed immersion, of finite presentation
when `ℱ` is of finite type. -/
def ZeroLocusRepresentation (D : ModuleMapSituation.{u, u} B S hS) : Prop :=
  ∃ Z : Subfunctor D.Y.1, IsClosedSubspace B S hS Z ∧
    (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) ∧
    ∀ T : D.SchemesOver, D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      ∃ k : yoneda.obj T.left ⟶ Z.toFunctor, k ≫ Z.ι = T.hom.hom

/-! ### Stacks 0CWC and the inputs it is proved from -/

/-- **Stacks 0CWC** as a statement: in Situation 083F, if `f` is of finite presentation and `𝒢`
is of finite presentation, flat over `B` and pure relative to `B`, then `F_zero` is an algebraic
space and `F_zero ⟶ B` is a closed immersion, of finite presentation when `ℱ` is of finite
type.

The decency hypothesis `hdec` and the finite type `hGft` of `𝒢` are not extra assumptions on
0CWC's content: they are what it takes to state purity of `𝒢` relative to `B` at all, purity
being a notion of Situation 0CV6.  Finite type of `𝒢` in fact follows from its finite
presentation, but this development has no such implication for modules on a site, so it is asked
for.

This is not carried as an opaque hypothesis by the two theorems below: it is **proved**,
in `AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus`, from
the geometric and chart inputs of this development's Stacks 0CWC.  The geometric input is the
dévissage alone, and it is the only one of them still unformalized. -/
def Is0CWC (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ (D : ModuleMapSituation.{u, u} B S hS) (hf : IsFinitePresentation B S hS D.f.hom)
    (_hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (_hGflat : IsFlatOver B S hS D.X.property D.f.hom D.G)
    (hdec : IsDecent B S hS D.f.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite D.G),
    D.IsTargetPureRelative (isFiniteType_of_isFinitePresentation B S hS hf) hdec hGft →
      D.ZeroLocusRepresentation

/-- **The chart input of Stacks 083J part (2)**: the chart case of that clause at the affine
stages, `AlgebraicGeometry.Space.ModuleMapSituation.HasAffineStageChartZeroDescent`, for every
situation of Stacks 083F.

The theorems below need no limit-preservation input beyond this: Stacks 083J part (2) *together
with* its transport to the inclusion of the vanishing subfunctor of the base, quantified over the
situations 0CWC applies to, are both proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`: part (2) is
`ModuleMapSituation.limitPreserving_zeroFunctor_of_hasQuasiCompactSupportOverTarget` and the
transport is `ModuleMapSituation.relativelyLimitPreserving_zeroSubfunctor_ι`.  What
remains unformalized of part (2) is the single step this hypothesis is: the affine endgame of
the source's proof, Algebra, Lemma 05LI part (1) applied to the system of charts
`W_i = W_0 ×_{T_0} T_i`, which this development cannot reach because the modules on the chart
over the limit are not identified with extensions of scalars.  See the docstring of
`AlgebraicGeometry.Space.ModuleMapSituation.HasAffineChartZeroDescent`.

Nothing restricts the quantifier: unlike the hypothesis it replaces, this one asserts no
conclusion about a vanishing locus, only that the chart case of 05LI is available, so it is
stated for every situation rather than for those satisfying 0CWC's hypotheses.  The support
hypothesis of part (2) is *not* among the inputs — for the situations 0CWC applies to it is
discharged from finite presentation of `f` by
`AlgebraicGeometry.Space.ModuleMapSituation.hasQuasiCompactSupportOverTarget_of_isQuasiCompact`. -/
def Is0CWCStageChartInput (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ D : ModuleMapSituation.{u, u} B S hS, D.HasAffineStageChartZeroDescent.{u, u, u}

/-- **The chart input of Stacks 083J part (2) is proved, not carried.**

For every situation of Stacks 083F the chart case of that clause at the affine stages holds,
because its limit-free replacement does:
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartRingLevelZeroLocus` builds the
ring-level reading of the vanishing locus of the chart situation over each affine stage — base
ring the functions on that stage, chart ring the functions on the affine chart of the source
space, modules the sections of `ℱ` and `𝒢` there — and
`AlgebraicGeometry.Space.ModuleMapSituation.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus`
supplies the limit content, which is Algebra, Lemma 05LI part (1) along the system of
base-changed algebras together with Stacks 01YW.

So `AlgebraicGeometry.Space.ModuleMapSituation.Is0CWCStageChartInput` is an input of
nothing; it is the name of a statement, and the theorems below do not carry it. -/
theorem is0CWCStageChartInput : Is0CWCStageChartInput B S hS := fun D =>
  D.hasAffineStageChartZeroDescent_of_ringLevelZeroLocus
    (hasAffineStageChartRingLevelZeroLocus B S hS D)

/-- **Stacks 0CWC from the one input this development does not prove.**  The statement
`AlgebraicGeometry.Space.ModuleMapSituation.Is0CWC` follows from `hdev`, the dévissage of the
source's proof (`AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput`), alone.

The affine endgame of that proof is not an input: it is proved, as
`AlgebraicGeometry.Space.ModuleMapSituation.affineChartZeroLocusClosed`, and both clauses of
Stacks 0CWC apply that proof rather than take it, with `DevissageInput` taken directly.

Nothing is carried of Stacks 083J part (2).  Part (2) itself and its transport to the
inclusion of the vanishing subfunctor are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`; its support
hypothesis is discharged from finite presentation of `f`; and its chart case at the affine
stages is
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWCStageChartInput`.

The scheme-level implication (2) ⇒ (1) of Stacks 01ZC for a morphism of the site, which this
development's reading of Stacks 04AK needs, is not an input: it is proved, as
`AlgebraicGeometry.locallyOfFinitePresentation_of_relativelyLimitPreserving_yoneda_map`.

The étale-local descent step of the closed-immersion clause is not an input either: it is
proved, as
`AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusClosedEtaleLocalOnBase`, and is applied
here through the registered hdesc-free form of the clause,
`AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_devissage`.

The vanishing subfunctor `AlgebraicGeometry.Space.ModuleMapSituation.zeroSubfunctor` is the
closed subspace that represents `F_zero`: its closedness is the closed-immersion clause of
Stacks 0CWC,
`AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_devissage`;
finite presentation of its inclusion is the other clause,
`AlgebraicGeometry.Space.ModuleMapSituation.isFinitePresentation_zeroSubfunctor_ι`; and that it
represents `F_zero` is
`AlgebraicGeometry.Space.ModuleMapSituation.isZeroAt_iff_exists_factor_zeroSubfunctor`.

The purity hypotheses of the two clauses are
`AlgebraicGeometry.Space.IsPureRelative` of the bridged situation at every point of the base,
which is what `AlgebraicGeometry.Space.ModuleMapSituation.IsTargetPureRelative` is by
`AlgebraicGeometry.Space.ModuleMapSituation.isTargetPureRelative_iff_isPureRelative` — the
chosen point of a situation of Stacks 0CV6 being irrelevant to purity relative to the base.  So
no purity is assumed beyond what `Is0CWC` already asks for. -/
theorem is0CWC_of_hasFlatChartWithClosedZeroLocus (hdev : DevissageInput B S hS) :
    Is0CWC B S hS := by
  intro D hf hGfp hGflat hdec hGft hpure
  have hft := isFiniteType_of_isFinitePresentation B S hS hf
  have hpure' : ∀ y : points B S hS D.Y.1,
      IsPureRelative (D.targetPrePureSituation hft hdec hGft y) :=
    fun y => (D.isTargetPureRelative_iff_isPureRelative hft hdec hGft y).1 hpure
  exact ⟨D.zeroSubfunctor,
    D.isClosedSubspace_zeroSubfunctor_of_devissage hf hGfp hGft hGflat hft hdec hpure' hdev,
    fun hFft => D.isFinitePresentation_zeroSubfunctor_ι hf hGfp hGft hGflat hft hdec hpure'
      hdev hFft (is0CWCStageChartInput D),
    D.isZeroAt_iff_exists_factor_zeroSubfunctor⟩

/-! ### Stacks 083M for a structure morphism of finite presentation -/

/-- **Stacks 083M when `f` is of finite presentation**, the first paragraph of the source's
proof and the only case the source considers to be of interest: it is Stacks 0CWC together with
Stacks 0CVI part (1).

Purity of `𝒢` relative to `B`, which is what Stacks 0CWC asks for, is produced here by
Stacks 0CVI part (1) out of the closed-immersion presentation `𝒢 ≅ i_*ℋ` together with
properness of `Z ⟶ B`, and that properness is *proved* from hypothesis (3) of Stacks 083M, the
hypothesis `hproper`.  Hypothesis (3) is properness of the support of `𝒢` as a closed set of
points, hence by Stacks 0CZD properness of the *reduced* induced closed subspace on it; Stacks
0CZE brings that down to the closed set `|i|(|Z|)` and Stacks 0CZC carries it from the reduced
induced subspace there to the possibly non-reduced `Z`.  The composite is
`AlgebraicGeometry.Space.isProper_comp_of_hasProperSupport_of_range_subset`.

What hypothesis (3) cannot supply is that `Z` is no larger than the support: a presentation
`𝒢 ≅ i_*ℋ` with `ℋ = 0` has `Supp(𝒢) = ∅` and leaves `Z` arbitrary, so properness of the support
says nothing about `Z ⟶ B`.  That is the hypothesis `hZsupp`, the containment
`|i|(|Z|) ⊆ Supp(𝒢)`.  It holds for both presentations the source uses — part (4) of Stacks 07U0
for the scheme-theoretic support, which is the one Stacks 0CVI part (1) is stated at, and part
(2) of Stacks 0CZ6 for the subspace cut out by the zeroth Fitting ideal — and by
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_eq_image_of_isFiniteTypeOnSite` it says
exactly that `ℋ` has full support on `Z`.  It is used in place of a properness hypothesis on
`Z ⟶ B` alongside hypothesis (3).

Stacks 0CWC itself is not carried: it is supplied by
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus` out of
its one geometric input, `hdev`, the dévissage of the source's proof of 0CWC.  The affine
endgame of that proof is proved, as
`AlgebraicGeometry.Space.ModuleMapSituation.affineChartZeroLocusClosed`.  Nothing of Stacks 083J
part (2) is carried: part (2) and its transport are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapZeroLocusLimitPreserving.lean`; its support
hypothesis follows from hypothesis (1); and its chart case at the affine stages is
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWCStageChartInput`.  `hin` is the input of this
library's Stacks 0CVH. -/
theorem zeroLocusRepresentation_of_isFinitePresentation
    (hdev : DevissageInput B S hS)
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGflat : IsFlatOver B S hS D.X.property D.f.hom D.G)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj D.G))
    (hdec : IsDecent B S hS D.f.hom)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ D.X) (hi : IsClosedImmersion B S hS i.hom)
    (H : Modules.{u, u} B S hS Z.1 Z.2) (hHft : SheafOfModules.IsFiniteTypeOnSite H)
    (hHqc : H.IsQuasicoherentOnSite)
    (e : D.G ≅ (modulePushforward B S hS i).obj H)
    (hin : ∀ y : points B S hS D.Y.1,
      (D.closedSubspaceModuleOfPushforward (isFiniteType_of_isFinitePresentation B S hS hf)
        hdec hGft i hi H hHft hHqc e y).BaseChangeInput)
    (hZsupp : Set.range (pointsMap B S hS Z.1 i.hom) ⊆
      supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G)) :
    D.ZeroLocusRepresentation :=
  is0CWC_of_hasFlatChartWithClosedZeroLocus hdev D hf hGfp hGflat hdec hGft
    (D.isTargetUniversallyPureRelative_of_pushforward
      (isFiniteType_of_isFinitePresentation B S hS hf) hdec hGft i hi H hHft hHqc e hin
      (isProper_comp_of_hasProperSupport_of_range_subset B S hS D.X.property D.Y.property
        D.f.hom (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1) hproper
        Z.property i.hom hi hZsupp)).isTargetPureRelative

/-! ### Changing the source of a situation -/

/-- **The situation of Stacks 083F obtained by replacing the source space and both modules**,
keeping the target `B` and hence the category of test schemes over it. -/
def replaceSource (D : ModuleMapSituation.{u, u} B S hS) (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ D.Y) (F' G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF' : F'.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) (u' : F' ⟶ G') :
    ModuleMapSituation.{u, u} B S hS where
  X := X'
  Y := D.Y
  f := f'
  F := F'
  G := G'
  quasicoherent_F := hF'
  quasicoherent_G := hG'
  u := u'

/-- Replacing the source of a situation keeps its target `D.Y`. -/
@[simp]
theorem replaceSource_Y (D : ModuleMapSituation.{u, u} B S hS) (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ D.Y) (F' G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF' : F'.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite) (u' : F' ⟶ G') :
    (D.replaceSource X' f' F' G' hF' hG' u').Y = D.Y :=
  rfl

/-! ### The reduction of the second paragraph of the proof -/

/-- **The reduction of the second paragraph of the proof of Stacks 083M**, carried as data.

The source replaces `X` by the closed subspace `Z ⊆ X` cut out by the zeroth Fitting ideal of
`𝒢` and `u` by the adjoint map `v : i^*ℱ ⟶ ℋ`, where `ℋ` is the module on `Z` with `i_*ℋ = 𝒢`.
Every field below is one assertion of that paragraph; the Stacks tag each one comes from is
named in its doc comment.  None of them is proved in this development. -/
structure FinitePresentationReduction (D : ModuleMapSituation.{u, u} B S hS) where
  /-- The closed subspace `Z ⊆ X` cut out by the zeroth Fitting ideal of `𝒢`, Stacks 0CZ3. -/
  Z : AlgebraicSpaces B S hS
  /-- Its inclusion into `X`. -/
  i : Z ⟶ D.X
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion B S hS i.hom
  /-- The inclusion is locally of finite presentation: Stacks 0CZ5 and Stacks 084Q. -/
  isLocallyOfFinitePresentation : IsLocallyOfFinitePresentation B S hS i.hom
  /-- The underlying set of `Z` is the support of `𝒢`: Stacks 0CZ6 part (2).  Only the
  containment `|i|(|Z|) ⊆ Supp(𝒢)` is recorded, which is all that is used; the reverse
  containment is automatic for a subspace with `i_*ℋ = 𝒢`.

  Properness of `Z ⟶ B` is *not* a field: it follows from this together with hypothesis (3) of
  Stacks 083M, by Stacks 0CZE and Stacks 0CZC, and that derivation is
  `AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction.isProper`. -/
  range_pointsMap_subset_support : Set.range (pointsMap B S hS Z.1 i.hom) ⊆
    supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G)
  /-- `Z ⟶ B` is decent, which purity of `ℋ` relative to `B` needs in order to be stated:
  it holds because a closed immersion is decent, Stacks 03L1, and `f` is decent whenever
  Situation 083F is read inside Situation 0CV6. -/
  isDecent : IsDecent B S hS (i.hom ≫ D.f.hom)
  /-- The module `ℋ` on `Z`, Stacks 0CZ6 part (3). -/
  H : Modules.{u, u} B S hS Z.1 Z.2
  /-- `ℋ` is quasi-coherent, Stacks 0CZ6 part (3). -/
  quasicoherent_H : H.IsQuasicoherentOnSite
  /-- `ℋ` is of finite type, Stacks 0CZ6 part (3). -/
  finiteType_H : SheafOfModules.IsFiniteTypeOnSite H
  /-- `ℋ` is of finite presentation, Stacks 0561. -/
  finitePresentation_H : SheafOfModules.IsFinitePresentationOnSite H
  /-- `ℋ` is flat over `B`, because `𝒢` is: the source's "check on stalks; details
  omitted". -/
  flat_H : IsFlatOver B S hS Z.property (i.hom ≫ D.f.hom) H
  /-- The identification `𝒢 ≅ i_*ℋ` of Stacks 0CZ6 part (3).  It is recorded so that this
  datum is the source's reduction and not an unrelated closed subspace carrying an unrelated
  module; the proof below consumes it only through `isZeroAt_iff`, which is where Stacks 0CW7
  turns it into the agreement of the two vanishing loci. -/
  iso_pushforward_H : D.G ≅ (modulePushforward B S hS i).obj H
  /-- The pullback `i^*ℱ` is quasi-coherent. -/
  quasicoherent_pullback_F : ((modulePullback B S hS i).obj D.F).IsQuasicoherentOnSite
  /-- The map `v : i^*ℱ ⟶ ℋ` adjoint to `u`. -/
  v : (modulePullback B S hS i).obj D.F ⟶ H
  /-- `F_zero` for `v` on `Z` is `F_zero` for `u` on `X`: Stacks 0CW7 part (1). -/
  isZeroAt_iff : ∀ T : D.SchemesOver,
    (D.replaceSource Z (i ≫ D.f) ((modulePullback B S hS i).obj D.F) H
      quasicoherent_pullback_F quasicoherent_H v).IsZeroAt (modulePullbackSystem B S hS) T ↔
        D.IsZeroAt (modulePullbackSystem B S hS) T

namespace FinitePresentationReduction

variable {D : ModuleMapSituation.{u, u} B S hS} (R : D.FinitePresentationReduction)

/-- The situation of Stacks 083F on the closed subspace `Z`, with the adjoint map
`v : i^*ℱ ⟶ ℋ`.  Its target is `B`, the target of the original situation. -/
noncomputable abbrev situation : ModuleMapSituation.{u, u} B S hS :=
  D.replaceSource R.Z (R.i ≫ D.f) ((modulePullback B S hS R.i).obj D.F) R.H
    R.quasicoherent_pullback_F R.quasicoherent_H R.v

/-- The map of `R.situation` is the composite `i ≫ f` of the closed immersion `i : Z ⟶ X` with
the map `f : X ⟶ Y` of `D`. -/
theorem situation_f_hom : R.situation.f.hom = R.i.hom ≫ D.f.hom := rfl

/-- **`Z ⟶ B` is proper**, from hypothesis (3) of Stacks 083M.

Hypothesis (3) is properness of the support of `𝒢` as a closed subset of `|X|`, which by
Stacks 0CZD is properness of the *reduced* induced closed subspace on it; the Fitting subspace
`Z` need not be reduced.  Stacks 0CZE brings properness down from the support to the closed
subset `|i|(|Z|)`, which is contained in it by `range_pointsMap_subset_support`, part (2) of
Stacks 0CZ6, and Stacks 0CZC carries it from the reduced induced subspace there to `Z` itself.
The composite is
`AlgebraicGeometry.Space.isProper_comp_of_hasProperSupport_of_range_subset`.

This is the step the source performs when it says that `Z ⟶ B` is proper because `|Z|` is the
support of `𝒢`; proving it, rather than carrying it as a field of
`AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction`, is what makes
hypothesis (3) of Stacks 083M used. -/
theorem isProper (hft : IsLocallyOfFiniteType B S hS D.f.hom)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom hft
      ((SheafOfModules.toSheaf _).obj D.G)) :
    IsProper B S hS (R.i.hom ≫ D.f.hom) :=
  isProper_comp_of_hasProperSupport_of_range_subset B S hS D.X.property D.Y.property D.f.hom
    hft hproper R.Z.property R.i.hom R.isClosedImmersion R.range_pointsMap_subset_support

/-- **`Z ⟶ B` is of finite presentation.**  It is locally of finite presentation by composing
the inclusion `i`, which is locally of finite presentation by Stacks 0CZ5 and Stacks 084Q, with
`f`, which is locally of finite presentation by hypothesis (1) of Stacks 083M; and it is
quasi-compact and quasi-separated because it is proper. -/
theorem isFinitePresentation (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hZB : IsProper B S hS (R.i.hom ≫ D.f.hom)) :
    IsFinitePresentation B S hS R.situation.f.hom :=
  ⟨isLocallyOfFinitePresentation_comp B S hS R.Z.property D.X.property D.Y.property
      R.i.hom D.f.hom R.isLocallyOfFinitePresentation hf,
    (IsProper.isFiniteType B S hS hZB).2,
    isQuasiSeparated_of_isSeparated B S hS (IsProper.isSeparated B S hS hZB)⟩

/-- **`ℋ` is pure relative to `B`**, by Stacks 0CVI part (2): `Z ⟶ B` is proper. -/
theorem isTargetPureRelative (hZB : IsProper B S hS (R.i.hom ≫ D.f.hom)) :
    R.situation.IsTargetPureRelative (IsProper.isFiniteType B S hS hZB) R.isDecent
      R.finiteType_H :=
  (R.situation.isTargetUniversallyPureRelative_of_isProper R.isDecent R.finiteType_H
    hZB).isTargetPureRelative

end FinitePresentationReduction

/-! ### Stacks 083M -/

/-- **Stacks 083M.**  In Situation 083F, assume that `f` is locally of finite presentation, that
`𝒢` is an `𝒪_X`-module of finite presentation flat over `B`, and that the support of `𝒢` is
proper over `B`.  Then `F_zero` is an algebraic space and `F_zero ⟶ B` is a closed immersion;
if `ℱ` is of finite type then `F_zero ⟶ B` is of finite presentation.

The proof is the second paragraph of the source's: pass to the closed subspace `Z ⊆ X` cut out
by the zeroth Fitting ideal of `𝒢`, where `u` becomes the adjoint map `v : i^*ℱ ⟶ ℋ` and the
vanishing locus is unchanged, and apply Stacks 0CWC there.  The geometric content of that
paragraph is the carried datum `R`, field by field; what is proved here is the verification of
Stacks 0CWC's hypotheses for the situation on `Z` and the transport of the answer back:

* `Z ⟶ B` is proper, by Stacks 0CZE and Stacks 0CZC out of hypothesis (3) of Stacks 083M and
  the identification of `|Z|` with the support of `𝒢`;
* `Z ⟶ B` is of finite presentation, because `i` is locally of finite presentation and `f` is
  locally of finite presentation, and because `Z ⟶ B` is proper;
* `ℋ` is pure relative to `B` by Stacks 0CVI part (2), `Z ⟶ B` being proper;
* `i^*ℱ` is of finite type when `ℱ` is, which is what carries the finite-presentation clause
  across the reduction;
* the representing closed subspace of `B` is the *same* subspace for both situations, the two
  having the same target and hence the same test schemes; only the characterisation of the
  vanishing locus moves, along the carried Stacks 0CW7.

Hypothesis (2) of Stacks 083M, finite presentation and flatness of `𝒢`, enters through the
corresponding fields of `R` for `ℋ` — the source's Stacks 0561 and its "check on stalks" — and
is carried in the statement as well, so that the hypotheses of Stacks 083M are literally
present.  Hypothesis (3), `hproper`, is consumed: properness of `Z ⟶ B`, which the source
derives from it and which `R` does not carry, is produced by
`AlgebraicGeometry.Space.ModuleMapSituation.FinitePresentationReduction.isProper` out of
`hproper` and the field `range_pointsMap_subset_support` of `R`, part (2) of Stacks 0CZ6.

Stacks 0CWC itself is not carried: it is supplied by
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWC_of_hasFlatChartWithClosedZeroLocus` out of
its one remaining geometric input `hdev`, the dévissage.  The affine endgame is proved, as
`AlgebraicGeometry.Space.ModuleMapSituation.affineChartZeroLocusClosed`.  The chart case of
Stacks 083J part (2) at the
affine stages is
`AlgebraicGeometry.Space.ModuleMapSituation.is0CWCStageChartInput`. -/
theorem zeroLocusRepresentation (hdev : DevissageInput B S hS)
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (_hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (_hGflat : IsFlatOver B S hS D.X.property D.f.hom D.G)
    (hproper : HasProperSupport B S hS D.X.property D.Y.property D.f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf)
      ((SheafOfModules.toSheaf _).obj D.G))
    (R : D.FinitePresentationReduction) :
    D.ZeroLocusRepresentation := by
  have hZB : IsProper B S hS (R.i.hom ≫ D.f.hom) :=
    R.isProper (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf) hproper
  obtain ⟨Z, hZ, hfp, hzero⟩ :=
    is0CWC_of_hasFlatChartWithClosedZeroLocus hdev R.situation
      (R.isFinitePresentation hf hZB) R.finitePresentation_H R.flat_H R.isDecent R.finiteType_H
      (R.isTargetPureRelative hZB)
  refine ⟨Z, hZ, fun hFft => hfp ?_, fun T => ?_⟩
  · exact isFiniteTypeOnSite_modulePullback B S hS R.i D.F hFft
  · exact (R.isZeroAt_iff T).symm.trans (hzero T)

end ModuleMapSituation

end AlgebraicGeometry.Space

end
