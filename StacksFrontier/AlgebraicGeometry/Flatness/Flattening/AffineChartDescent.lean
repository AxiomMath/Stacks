module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.EtaleLocalFlatteningDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover

/-!
# Flattening a module by a blowup, from the affine charts

Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be a morphism with `X`
quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open.
Suppose that for every affine open `V ⊆ S` and every affine open `W ⊆ f⁻¹(V)` there is a centre
on `V`, finitely presented and supported away from `V ∩ U`, whose blowup flattens the strict
transform of `F|_W`. Then there is a single centre `I` on `S`, finitely presented and supported
away from `U` — so the blowup of `S` in `I` is a `U`-admissible blowup — such that the strict
transform of `F` along it is flat over it.

## Main definitions

* `AlgebraicGeometry.AffineChartFlatteningCentre` is the affine case of the flatness assertion of
  [Stacks, Tag 0815], read on the affine charts of the data `F/X/S` and `U`, with the source's
  own hypotheses (2)-(5) **not** imposed. It is FALSE in general
  (`AlgebraicGeometry.affineChartFlatteningCentre_top_iff` of
  `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/AffineChartDescentTop.lean`), and it is the
  predicate `AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre` of
  `StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatteningBlowupFromAffineCase` is stated
  with — for the structure sheaf, where that wrapper's own hypotheses discharge (2)-(5), it is
  proved outright as
  `AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre`. So this name is not free
  to be rebound.
* `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` is the same statement
  guarded by those four hypotheses, hence weaker. **This is the predicate to carry** for an
  arbitrary quasi-coherent module: it is what the affine case of the source actually asserts,
  and `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`
  proves it from [Stacks, Tag 0811] with nothing granted.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCase`:
  the flatness assertion of **[Stacks, Tag 0815]** under exactly the source's hypotheses, with
  the affine case — stated under those same hypotheses — carried.
* `AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`:
  the descent step alone, carrying the hypothesis-free form. No tag.
* `AlgebraicGeometry.AffineChartFlatteningCentre.of_centre`: a global flattening centre restricts
  to one on every pair of charts.
* `AlgebraicGeometry.affineChartFlatteningCentre_iff`: the two previous results combined — the
  hypothesis-free form is *equivalent* to the flatness assertion of the tag with the source's
  hypotheses (2)-(5) deleted, which is why deleting them is what made it false.

## Implementation notes

The source reduces the flatness assertion to `S = Spec(R)` and `X = Spec(A)` in one step, by
étale locality on source and target ([Stacks, Tag 0814]), and the whole induction on the maximum
fibre-support dimension takes place over affines. That reduction is what is proved here: `X` is
quasi-compact, so finitely many affine opens `W` cover it, each inside the preimage of an affine
open `V` of `S`; the inclusions `V ⟶ S` are étale and, `S` being quasi-separated and `V` affine,
quasi-compact; the inclusions `W ⟶ X` are étale and jointly surjective; and `W ⟶ V` is the
restriction of `f`. Those are exactly the data [Stacks, Tag 0814] consumes.

Hypotheses (2)-(5) of the source — `f` locally of finite presentation, `F` of finite type, and
`F` of finite presentation and flat over `U` — are not assumed, because they enter only through
`AlgebraicGeometry.AffineChartFlatteningCentre`: they are hypotheses of the affine case, where
every one of them restricts to an affine chart. The same is true of the surjectivity half of
condition (1) of [Stacks, Tag 0814], which the library's form of that tag already drops.

**What the carried hypothesis costs.** It is a proper special case of the conclusion — the
conclusion restricted to affine `S` and affine `X` — so it is not a restatement of it; but like
every reduction to a special case it is *inter-derivable* with the conclusion, and
`AlgebraicGeometry.affineChartFlatteningCentre_iff` proves that: a global centre `I` restricts
to the centre `I·𝒪_V` on a chart
(`AlgebraicGeometry.AffineChartFlatteningCentre.of_centre`, which is
`AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale` along the
étale `V ⟶ S` and the flat `W ⟶ X`), while the converse is the whole of the source's first
reduction and consumes [Stacks, Tag 0814]. So the hypothesis assumes nothing beyond the
conclusion.

What it still is, is **unproved**. The only producer of it that does not assume the conclusion is
`AlgebraicGeometry.AffineChartFlatteningCentre.of_isFlatOver`, which exhibits it on the region
where no blowup is needed — `F` already flat over the base. The source's own proof of the affine
case is an induction on `d = max_s dim Supp(F_s)` whose step needs, besides [Stacks, Tag 057S]
(`AlgebraicGeometry.exists_elementaryDevissage`), [Stacks, Tag 080G], [Stacks, Tag 080W],
[Stacks, Tag 05I3] and [Stacks, Tag 05CL] — all of which this development has — the blowup
produced by [Stacks, Tag 0811], which it does not: that is
`AlgebraicGeometry.exists_isAdmissibleBlowup_opens_free_surjective`, itself carrying the
unproved `AlgebraicGeometry.GenericFibreFlatteningBlowup`.

**The predicate is stated in a generality in which it is false, and that has to be repaired
before any producer can exist.** `AlgebraicGeometry.AffineChartFlatteningCentre f F U` imposes
*no* hypothesis on `f`, `F` or `U`; it is asked below of a merely quasi-coherent `F` and an
arbitrary `f`, because in
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`
hypotheses (2)-(5) of the source are not assumed separately, on the ground that they
enter only through it. They do enter only through it, but the predicate does not re-impose them,
and without hypothesis (5) — `F_U` flat over `U` — it fails.
`AlgebraicGeometry.affineChartFlatteningCentre_top_iff` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/AffineChartDescentTop.lean` proves that at
`U = ⊤` the predicate is *equivalent* to `F` being flat over the base, with no hypothesis on
`f`, on `S`, or on `F` beyond quasi-coherence. So it is false for every quasi-coherent `F` that
is not flat over its base — `S = X = Spec k[x, y]`, `f = 𝟙` and `F = 𝒪_S/(x)`, for instance,
which is of finite type over a quasi-compact and quasi-separated base.

So a proof of the affine case of [Stacks, Tag 0815] will not discharge the hypothesis as the
predicate now stands: the predicate has to carry the chart-level forms of hypotheses (2)-(5)
first — `f` locally of finite presentation, `F` of finite type, and `F` of finite presentation
and flat over `U` — and the declarations that consume it have to assume those hypotheses in turn,
which are the source's own. The declarations that consumed it for
[Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0EVC, 0F3W, 0F3Z] have each been restated that way,
with the source hypothesis restored; this form is kept because those restated statements are
proved from it.

**What the repair still owes.**
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCase`
carries `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` under the
source's hypotheses, so [Stacks, Tag 0815] is now stated faithfully. The declarations above it
in the development still consume `AlgebraicGeometry.AffineChartFlatteningCentre`, and they divide
in two:

* The library's forms of [Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0F3W, 0F3Z] assume their
  morphism only of finite **type**, while hypothesis (2) of [Stacks, Tag 0815] asks for finite
  **presentation**. The source does not apply the affine case to such a morphism either: by
  [Stacks, Tag 04II] (`AlgebraicGeometry.exists_immersion_affineSpace`) it immerses the chart
  `W` over `V` into `𝔸ⁿ_V` and applies the affine case to `𝔸ⁿ_V ⟶ V` and the pushforward
  `i_*𝒪_W`, transporting the result back by [Stacks, Tag 080G]
  (`AlgebraicGeometry.strictTransformSheafPushforwardIso` of
  `StacksFrontier/AlgebraicGeometry/Blowup/Transform/AffinePushforward.lean`). That route is taken
  in `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/AffineChartDescentFiniteType.lean`:
  `AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase` produces the predicate for a
  morphism locally of finite type out of
  `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, the
  affine case under the source's hypotheses for an arbitrary quasi-coherent module, proved from
  [Stacks, Tag 0811] with nothing granted. What it needs besides is hypothesis (2) of
  [Stacks, Tag 081R] — that the morphism be flat and locally of finite presentation over `U`.
  Each of those tags now has a declaration with that hypothesis present, carrying nothing, and
  the tag registered there:
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
  for 081R, `AlgebraicGeometry.strictTransformOpenImmersion_of_isIso_morphismRestrict` for 081S,
  `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_affineCase` for 081T,
  `AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper`
  for 0B49, `AlgebraicGeometry.exists_isAdmissibleBlowup_extending_section_of_qcqs` for
  0CP1 and `AlgebraicGeometry.exists_isAdmissibleBlowup_properExtension` for 0F3Z. For 081S,
  081T, 0CP1 and 0B49 hypothesis (2) is not even an addition: their own source hypotheses — an
  isomorphism over the open, or a finite locally free base change — imply it.
  [Stacks, Tag 0F3W] is
  `AlgebraicGeometry.exists_isAdmissibleBlowup_strictTransform_isIso_near_closure`.
* The library's forms of [Stacks, Tags 0EVC, 0EVF, 0EVI, 0EX9, 0ETR, 0ETT] do assume finite
  presentation, so they reach the affine case under its own hypotheses as soon as their own
  flatness hypothesis over the open is restored. For 0EVC that is
  `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_affineCase`, where the tag now sits.

The remaining assertion of [Stacks, Tag 0815], that the strict transform is of finite
presentation, is recovered from flatness by [Stacks, Tag 081N] once `U` is scheme-theoretically
dense in `S`; it is not treated here. Both assertions of [Stacks, Tag 0815] together, with
nothing carried, are
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts` in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup`, which runs the
Raynaud–Gruson induction itself rather than through the reduction proved here.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 081N](https://stacks.math.columbia.edu/tag/081N)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815]**, for the data `F/X/S` and
the open `U ⊆ S`: for every affine open `V` of `S` and every affine open `W` of `X` inside
`f⁻¹(V)` there is a centre `I` on `V`, finitely presented as a closed subscheme and supported
away from `V ∩ U`, such that the strict transform of `F|_W` along the blowup of `V` in `I` is flat
over that blowup.

Each chart `W ⟶ V` inherits the five hypotheses of the source from those on `f`, `F` and `U`:
`V` and `W` are affine, hence quasi-compact and quasi-separated; the restriction of a morphism
locally of finite presentation is locally of finite presentation; and `F|_W` is of finite type,
and of finite presentation and flat over `V ∩ U`, wherever `F` is over `U`. -/
def AffineChartFlatteningCentre {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (U : S.Opens) : Prop :=
  ∀ (V : S.affineOpens) (W : X.affineOpens) (hVW : (W.1 : X.Opens) ≤ f ⁻¹ᵁ V.1),
    ∃ I : (V.1.toScheme).IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (V.1.ι ⁻¹ᵁ U : Set V.1.toScheme) (I.support : Set V.1.toScheme) ∧
      IsFlatOver (pullback.snd (f.resLE V.1 W.1 hVW) (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf (f.resLE V.1 W.1 hVW) (blowUpToBase I)
          (exceptionalIdeal I) ((Scheme.Modules.pullback W.1.ι).obj F))

/-- A module that is already flat over the base satisfies
`AlgebraicGeometry.AffineChartFlatteningCentre`, with the unit ideal sheaf as the centre on every
chart: that centre is empty, hence of finite presentation and supported away from every open, and
the strict transform of a module flat over the base is flat over the blowup for any centre at all.

So the hypothesis of
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`
holds on the whole region where no blowup is needed. -/
theorem AffineChartFlatteningCentre.of_isFlatOver {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (U : S.Opens) (hF : IsFlatOver f.toLRSHom.toShHom F) :
    AffineChartFlatteningCentre f F U := by
  intro V W hVW
  have _ : ((Scheme.Modules.pullback W.1.ι).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback W.1.ι F ‹_›
  have hres : IsFlatOver (f.resLE V.1 W.1 hVW).toLRSHom.toShHom
      ((Scheme.Modules.pullback W.1.ι).obj F) := fun x ↦
    (isFlatOverAt_iff_of_moduleIso (f.resLE V.1 W.1 hVW).toLRSHom.toShHom
      ((Scheme.Modules.restrictFunctorIsoPullback W.1.ι).app F) x).mp
        (isFlatOver_resLE F hF W.1 V.1 hVW x)
  exact ⟨⊤, Stacks.Blowup.finitePresentation_subschemeι_top, by simp,
    isFlatOver_strictTransformSheaf_of_isFlatOver (f.resLE V.1 W.1 hVW) ⊤ _ hres⟩

/-- **A global flattening centre restricts to the affine charts.** If `I` is a centre on `S`
which is finitely presented, supported away from `U` and such that the strict transform of `F`
along the blowup of `S` in `I` is flat over that blowup, then `I·𝒪_V` is such a centre on every
affine open `V ⊆ S`, for the restriction of `F` to every affine open `W ⊆ f⁻¹(V)`.

This is the converse of
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`,
and together with it makes `AlgebraicGeometry.AffineChartFlatteningCentre f F U` *equivalent* to
the flatness assertion of [Stacks, Tag 0815] for `f`, `F` and `U` under that tag's
quasi-compactness and quasi-separatedness hypotheses
(`AlgebraicGeometry.affineChartFlatteningCentre_iff`). So the hypothesis carried there is
exactly the conclusion read on the affine charts: it is a genuine special case of the
conclusion, and it assumes nothing beyond it.

The centre restricts because finite presentation of a closed subscheme is stable under base
change (`AlgebraicGeometry.finitePresentation_comap_subschemeι`) and the support of an inverse
image is the inverse image of the support
(`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`). Flatness restricts because `V.ι` is
étale and `W.ι` is flat, so
`AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale` —
[Stacks, Tag 0805] with [Stacks, Tag 05B9] and [Stacks, Tag 02JZ] — identifies the strict
transform on the chart with the pullback of the strict transform downstairs. -/
theorem AffineChartFlatteningCentre.of_centre {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (U : S.Opens) (I : S.IdealSheafData)
    (hIfp : FinitePresentation I.subschemeι)
    (hIdisj : Disjoint (U : Set S) (I.support : Set S))
    (hIflat : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    AffineChartFlatteningCentre f F U := by
  intro V W hVW
  refine ⟨I.comap V.1.ι, finitePresentation_comap_subschemeι I V.1.ι hIfp, ?_, ?_⟩
  · simp only [Scheme.IdealSheafData.support_comap]
    rw [Set.disjoint_left]
    intro y hy hy'
    exact Set.disjoint_left.mp hIdisj hy hy'
  · obtain ⟨k, -, -, hk⟩ := exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale f
      (f.resLE V.1 W.1 hVW) V.1.ι W.1.ι (Scheme.Hom.resLE_comp_ι f hVW).symm I F
    exact fun y ↦ (hk y).mp (hIflat (k y))

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815]**, for the data `F/X/S` and
the open `U ⊆ S`, *under the source's own hypotheses*: granted hypotheses (2)-(5) of the source —
`f` locally of finite presentation, `F` of finite type, and `F|_U` of finite presentation and
flat over `U` — every chart of the data carries a flattening centre, that is,
`AlgebraicGeometry.AffineChartFlatteningCentre` holds.

**This is the predicate to carry.** Its hypotheses are what make it the affine case of the source
rather than something strictly stronger, and each of them restricts to a chart: `V` and `W` are
affine, hence quasi-compact and quasi-separated; the restriction of a morphism locally of finite
presentation is locally of finite presentation; and `F|_W` is of finite type, and of finite
presentation and flat over `V ∩ U`, wherever `F` is over `U`. So the affine case of the source,
once proved, discharges it — while
`AlgebraicGeometry.AffineChartFlatteningCentre`, the same statement with these four
hypotheses deleted, is FALSE in general by
`AlgebraicGeometry.affineChartFlatteningCentre_top_iff`. Asking the hypotheses of the data
rather than of each chart makes this predicate *weaker* than the chart-wise form, since they
restrict; so nothing is assumed that the source does not assume. -/
def AffineChartFlatteningCentreUnderSourceHypotheses {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (U : S.Opens) : Prop :=
  LocallyOfFinitePresentation f →
  F.IsFiniteType →
  (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
  IsFlatOver (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom (F.restrict (f ⁻¹ᵁ U).ι) →
  AffineChartFlatteningCentre f F U

/-- A module already flat over the base satisfies
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses`: the four hypotheses are
not needed, the unit ideal sheaf serving as a centre on every chart. -/
theorem AffineChartFlatteningCentreUnderSourceHypotheses.of_isFlatOver {S X : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (U : S.Opens) (hF : IsFlatOver f.toLRSHom.toShHom F) :
    AffineChartFlatteningCentreUnderSourceHypotheses f F U :=
  fun _ _ _ _ ↦ AffineChartFlatteningCentre.of_isFlatOver f F U hF

/-- The hypothesis-free form implies the form carrying the source's hypotheses. The converse is
false: see `AlgebraicGeometry.affineChartFlatteningCentre_top_iff`. -/
theorem AffineChartFlatteningCentre.toAffineChartFlatteningCentreUnderSourceHypotheses
    {S X : Scheme.{u}}
    {f : X ⟶ S} {F : X.Modules} {U : S.Opens} (H : AffineChartFlatteningCentre f F U) :
    AffineChartFlatteningCentreUnderSourceHypotheses f F U :=
  fun _ _ _ _ ↦ H

/-- **Stacks Project, Tag 0815, flatness assertion, with the source's hypotheses dropped into the
carried affine case.** This is the descent step on its own: finitely many affine opens of `X`
cover it, each inside the preimage of an affine open of `S`; those inclusions and the
restrictions of `f` between them form the étale squares that [Stacks, Tag 0814] descends along,
and the centres supplied on the charts are exactly its third condition.

No tag is registered here. The hypothesis it carries,
`AlgebraicGeometry.AffineChartFlatteningCentre`, is the affine case with hypotheses (2)-(5) of
the source deleted, and is false in general
(`AlgebraicGeometry.affineChartFlatteningCentre_top_iff`); the tag sits on
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCase`,
which assumes those hypotheses and carries only
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses`. This form is kept because
it is what the library's forms of [Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0EVC, 0F3W, 0F3Z] can
still call: their
morphisms are of finite *type*, not of finite presentation, so the source reaches the affine case
through the immersion into affine space of [Stacks, Tag 04II]. That immersion is taken in
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/AffineChartDescentFiniteType.lean`, where
`AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase` produces this form's hypothesis
for such a morphism out of the affine case under the source's hypotheses — given, as the source
gives, that the morphism is flat and locally of finite presentation over `U`. -/
theorem AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S))
    (H : AffineChartFlatteningCentre f F U) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  classical
  have hcharts (x : X) : ∃ (V : S.affineOpens) (W : X.affineOpens),
      x ∈ W.1 ∧ (W.1 : X.Opens) ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨V, hV⟩, ⟨W, hW⟩, hxW, hWV⟩
  choose V W hxW hWV using hcharts
  choose I hIfp hIdisj hIflat using fun x : X ↦ H (V x) (W x) (hWV x)
  obtain ⟨c, hc⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ ((W x).1 : Set X))
    (fun x ↦ (W x).1.isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩
  refine exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf f F U hU
    (ι := {x : X // x ∈ c}) (fun i ↦ (V i.1).1.toScheme) (fun i ↦ (W i.1).1.toScheme)
    (fun i ↦ (V i.1).1.ι) (fun i ↦ (W i.1).1.ι)
    (fun i ↦ f.resLE (V i.1).1 (W i.1).1 (hWV i.1)) (fun i ↦ I i.1)
    (fun i ↦ ⟨inferInstance, quasiCompact_ι_of_isCompact (V i.1).1 (V i.1).2.isCompact⟩)
    (fun _ ↦ inferInstance) ?_ (fun i ↦ (Scheme.Hom.resLE_comp_ι f (hWV i.1)).symm)
    (fun i ↦ ⟨hIfp i.1, hIdisj i.1⟩) fun i ↦ hIflat i.1
  intro x
  have hx : x ∈ ⋃ y ∈ c, ((W y).1 : Set X) := hc (Set.mem_univ x)
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨⟨y, hy⟩, ⟨x, hxy⟩, rfl⟩

/-- **Stacks Project, Tag 0815, flatness assertion.** Let `S` be a quasi-compact and
quasi-separated scheme, let `f : X ⟶ S` be a morphism locally of finite presentation with `X`
quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type, let `U ⊆ S` be a
quasi-compact open and assume `F|_U` is of finite presentation and flat over `U`. Granted the
affine case `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses`, there is a
centre `I` on `S`, finitely presented and supported away from `U`, exhibiting the blowup of `S`
in `I` as a
`U`-admissible blowup, such that the strict transform of `F` along that blowup is flat over it.

Every hypothesis of the source is present: (1) `X` quasi-compact, (2) `f` locally of finite
presentation, (3) `F` of finite type, (4) `F|_U` of finite presentation, (5) `F|_U` flat over
`U`, together with the standing quasi-compactness and quasi-separatedness of `S` and
quasi-compactness of `U`. The input is the affine case itself, under those same hypotheses; the
descent from the charts to `S` is
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`,
which is [Stacks, Tag 0814] over a finite affine cover.

**This declaration carries no `@[stacks 0815]` attribute.** [Stacks, Tag 0815] is registered, in
full and resting on its own hypotheses alone, on
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts` of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup`. That statement is
strictly the stronger of the two: it also gives the finite-presentation assertion of the
conclusion, which this one does not, and it needs no affine-case input. This reduction is kept
because the flatness half of the conclusion is reached here from the affine case directly, which
is the shape the chart-level development consumes. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCase
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hUfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (hUflat : IsFlatOver (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom
      (F.restrict (f ⁻¹ᵁ U).ι))
    (H : AffineChartFlatteningCentreUnderSourceHypotheses f F U) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) :=
  AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver f F U hU
    (H ‹LocallyOfFinitePresentation f› ‹F.IsFiniteType› hUfp hUflat)

/-- **The affine case of the flatness assertion of [Stacks, Tag 0815] is equivalent to that
assertion.** Under the tag's hypotheses on `S`, `X` and `U`,
`AlgebraicGeometry.AffineChartFlatteningCentre f F U` holds if and only if there is a single
centre on `S`, finitely presented and supported away from `U`, along whose blowup the strict
transform of `F` is flat.

The forward direction is
`AlgebraicGeometry.AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver`,
the source's first reduction — [Stacks, Tag 0814] over a finite affine cover. The reverse
direction is `AlgebraicGeometry.AffineChartFlatteningCentre.of_centre`, restriction of a global
centre to a chart.

This fixes exactly what is still owed. The predicate is a *proper special case* of the
conclusion — the conclusion restricted to affine `S` and affine `X` — and the equivalence shows
it is not an extra assumption smuggled in alongside the conclusion: every instance of it is an
instance of tag 0815 itself. What it is *not* is a proof; the only producers of the predicate
in this development are
`AlgebraicGeometry.AffineChartFlatteningCentre.of_isFlatOver`, which assumes `F` already flat
over the base, and this equivalence, which assumes the conclusion. -/
theorem affineChartFlatteningCentre_iff {S X : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsCompact (U : Set S)) :
    AffineChartFlatteningCentre f F U ↔
      ∃ I : S.IdealSheafData,
        FinitePresentation I.subschemeι ∧
        Disjoint (U : Set S) (I.support : Set S) ∧
        IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  refine ⟨fun H ↦ ?_, fun ⟨I, hIfp, hIdisj, hIflat⟩ ↦
    AffineChartFlatteningCentre.of_centre f F U I hIfp hIdisj hIflat⟩
  obtain ⟨I, hIfp, hIdisj, -, hIflat⟩ :=
    AffineChartFlatteningCentre.exists_isAdmissibleBlowup_isFlatOver f F U hU H
  exact ⟨I, hIfp, hIdisj, hIflat⟩

end AlgebraicGeometry

end
