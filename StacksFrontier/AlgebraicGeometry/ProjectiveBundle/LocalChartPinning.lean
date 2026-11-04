module

public import StacksFrontier.AlgebraicGeometry.ProjTwistPinnedChart.Pinning
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineRestrictTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocalSectionMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTransport

/-!
# The pinning match at the local chart of the projective bundle

Let `ℰ` be a quasi-coherent `𝒪_X`-module, `q : ℰ ⟶ ℒ` a map to another module, `V` an open of `X`
and `e` a trivialisation of `ℒ` over `V`. `Stacks.RelativeProj.localChartMap` is the morphism
`V ⟶ Proj Γ(V, Sym ℰ)` classified by the dehomogenisation
`Stacks.RelativeProj.localDehomogenize` of `Sym ℰ` at the trivialised quotient, and
`Stacks.RelativeProj.localSection` is that morphism carried into `𝐏(ℰ)` by the bundle's chart
over `V`.

**This file reads the absolute pinning match of
`StacksFrontier/AlgebraicGeometry/ProjTwistPinnedChart/Pinning.lean` at that morphism.** Fix a
section `m₀` of `ℰ` over `V` that the trivialised quotient carries to the unit section — which
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` supplies from the surjectivity of
`q` on sections, and which is the same `m₀` that makes
`Stacks.RelativeProj.localChartMap` well defined. Then the degree-one homogeneous section of
`Sym ℰ` attached to `m₀` frames the pulled-back twist, and for every section `m` of `ℰ` over `V`

`localChartMap⁎(degreeSection 1 m) |_W = (e (q m))|_W · localChartMap⁎(degreeSection 1 m₀) |_W`

over every open `W` of `V`. So in the frame pinned by `m₀` the pulled-back tautological section of
`m` is the trivialised quotient of `m`, on the nose.

## Why this file exists

The one statement left between step 2 and step 4 on the route to [Stacks, Tag 0B3V]'s bijection
is that the local
comparison isomorphism over a trivialising affine open must *carry the pulled-back tautological
map to `q`* and not merely exist. The sibling file proves that for an arbitrary graded ring and an
arbitrary ring map to global sections; this file supplies the instance the route actually needs,
in the vocabulary the route's local section is built from — `localDehomogenize`,
`Stacks.RelativeProj.trivializedQuotientHom` — so that nothing about graded rings is left for the
consumer to arrange.

What stands between this and the field
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` is listed in
`Not done here`; it is a transport across `AlgebraicGeometry.Scheme.Modules` isomorphisms and
contains no further arithmetic of fractions.

## Main definitions

* `Stacks.RelativeProj.localDegreeOne`: the degree-one homogeneous section of `Sym ℰ` over `V`
  attached to a section of `ℰ`, as an element of the degree-one piece of the graded section ring.

## Main results

* `Stacks.RelativeProj.localDehomogenize_localDegreeOne`: **the dehomogenisation in degree one is
  the trivialised quotient.** This is
  `Stacks.SymmetricDehomogenize.dehomogenize_of_one` at the trivialised quotient, named here
  because it is the dictionary entry the pinning match is read through.
* `Stacks.RelativeProj.localDehomogenize_localDegreeOne_eq_one`: the unit section gives the
  inverted element, which is what puts the whole chart inside its standard open.
* `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap`: **the pinning match at the
  local chart**, over every open of `V`.
* `Stacks.RelativeProj.exists_resT_pullbackDegreeSection_localChartMap`: the same with the frame
  produced rather than assumed, so that the statement above is not vacuous: the only hypothesis
  left is the surjectivity of `q` on sections over `V` that `localChartMap` already asks for.
* `Stacks.RelativeProj.chartFactorisationTwistIso` and
  `Stacks.RelativeProj.chartFactorisationPullbackTwistIso`: **the twist comparison at an
  arbitrary chart factorisation over `V`** — a pair `(g, h)` with
  `g ≫ bundlePresentationIso.inv = h ≫ chart V hV` and nothing else assumed of either morphism.
  The pullback of `𝒪_{𝐏(ℰ)}(1)` along `g` is the absolute twisting sheaf of `Γ(V, Sym ℰ)` pulled
  back along `h`, and then the
  `Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist` at
  `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor` that the pinning match above is
  stated on. See the implementation notes.
* `Stacks.RelativeProj.localSection_comp_bundlePresentationIso_inv`,
  `Stacks.RelativeProj.localSectionTwistIso` and
  `Stacks.RelativeProj.localSectionPullbackTwistIso`: **the same at `localChartMap`**, which is
  the chart factorisation the route's local section provides — the two comparisons are the two
  general ones above at that pair, not restatements of them.
* `Stacks.RelativeProj.preimage_basicOpen_localDegreeOne_eq_top`: the standard-open hypothesis
  `hg`, produced from the section `m₀` and its equation. Named because the discharge of
  `Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` needs `m₀`, its equation
  and `hg` *together*, which the existential statement above does not offer.
* `Stacks.RelativeProj.chartDegreeOneSection_eq_degreeSection_localDegreeOne` and
  `Stacks.RelativeProj.pullbackCongr_hom_pullbackSection_chartDegreeOneSection`: **the section
  the chart comparison produces is the one the pinning match is pinned by.**
  `Stacks.ProjectiveBundleConormal.chartDegreeOneSection` and the degree-one section of
  `localDegreeOne` are the same global section of `𝒪(1)` on the chart, and the last comparison of
  `chartFactorisationPullbackTwistIso` carries its pullback along `h` to the
  `Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackDegreeSection` the pinning match uses. The
  second is stated **at an arbitrary morphism `h` into the chart and over an arbitrary open**,
  not only over `⊤` of the chart: the
  consumer meets the composite over `V.ι ⁻¹ᵁ V`, which is `⊤` by
  `AlgebraicGeometry.Scheme.Opens.ι_preimage_self` but not definitionally, so a `⊤`-only version
  would put an `eqToHom` inside a section.

## Implementation notes

**The degree-one element is `DirectSum.of` of the generator of `Sym ℰ`**, not the
`Stacks.AlgebraicGeometry.ProjChartFromRatios` route and not
`Stacks.ProjectiveBundleConormal.chartPiece`: that is the spelling
`Stacks.SymmetricDehomogenize.dehomogenize_of_one` computes on and the spelling
`Stacks.RelativeProj.map_irrelevant_localDehomogenize_eq_top` already uses internally, so no
comparison of two degree-one spellings is introduced. `chartPiece` is a different term — it goes
through `Stacks.AlgebraicGeometry.AffinePieces.pieceSectionsEquiv` and needs `V` affine — and is
not used here.

**`hg` is a hypothesis and not an assumption.** That the chart morphism lands wholly inside the
standard open of the inverted element follows from
`localDehomogenize_localDegreeOne_eq_one` and
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`; it is taken as an argument only
because `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor` is indexed by it, so a
consumer must be able to supply its own proof without a transport in the index of the conclusion.
The same note is in the sibling file, for the same reason.

**No affineness and no epimorphism is used.** `V` is an arbitrary open and `q` an arbitrary
morphism of modules; what is needed of `q` is only the surjectivity on sections over `V` that
`localChartMap` already asks for, and what is needed of the quotient is only the section `m₀`
with its equation. Invertibility of `ℒ` appears nowhere below — it is the trivialisation `e` that
is used, not the invertibility it comes from.

**No `@[stacks 0B3V]` attribute is attached**, and none of any other tag. [Stacks, Tag 0B3V] is
the bijection between the sections of `π : 𝐏(ℰ) ⟶ X` and the invertible quotients of `ℰ` up to
isomorphism, and it is registered on
`Stacks.RelativeProj.projectiveBundleSectionsEquiv` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean`, the unconditional
bijection. What is proved here is one identity of sections over one open; registering the tag on
it would put the tag's name on a strictly weaker statement.

## Not done here

**The field `exists_classifies` is discharged**, and this file's statements are two of its
inputs. It is
`Stacks.RelativeProj.exists_classifies_tautologicalDatum` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean`: every invertible
quotient of `ℰ` is classified by a section of `π`, the section being
`Stacks.RelativeProj.globalSection` of the quotient map. The chain that got there reads the
pinning match above through
`…RelativeProj.chartFactorisationPullbackTwistIso_hom_pullbackSection` and
`…RelativeProj.globalSectionPullbackTwistIsoOnCover_hom_pullbackSection`, inverts the pinned
frame on it with `…RelativeProj.pinnedFrameIso_inv_resT_pullbackDegreeSection`, and compares the
two sides over `V.ι ⁻¹ᵁ V` by `Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen`. The
chain uses `pullbackCongr_hom_pullbackSection_chartDegreeOneSection` at an arbitrary open, the
generalisation below, and the cancellation
`resTop (V.ι ⁻¹ᵁ V) ∘ preimageSelfTopRingHom V = id`, which is
`…RelativeProj.resTop_preimageSelfTopRingHom`.

**The second field, `Stacks.RelativeProj.TautologicalDatum.IsUniversal.eq_of_classifies`, is
also discharged**, as
`Stacks.RelativeProj.eq_of_classifies_tautologicalDatum` of the same file, and the generalisation
of the two comparisons above to an arbitrary chart factorisation is what it was *for*: the
injectivity clause reads the twist comparison at `V.ι ≫ σ` for a section `σ` nothing is known
about, where the morphism into the chart is `Stacks.RelativeProj.sectionChartMap` rather than
`localChartMap`. With both fields, `…RelativeProj.isUniversal_tautologicalDatum` is an instance
and the bijection is `…RelativeProj.projectiveBundleSectionsEquiv`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjTwistPinnedChart
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.ProjGlobalSectionsAppTop (resTop)
open Stacks.ProjectiveFromSections (resT)
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent] (V : X.Opens) (q : F ⟶ L)
  (e : L.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V))

/-- **The degree-one homogeneous section of `Sym ℰ` over `V` attached to a section of `ℰ`**, as an
element of the degree-one piece of the graded section ring `Γ(V, Sym ℰ)`. This is the spelling
`Stacks.SymmetricDehomogenize.dehomogenize_of_one` computes on. -/
public def localDegreeOne (m : Γ(F, V)) :
    (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V 1 :=
  ⟨DirectSum.of ((schemeSheafGradedAlgebra F
      (isQuasicoherentPieces_of_isQuasicoherent F)).sectionPieces V) 1
      ((symmetricAlgebraGen X F).val.app (op V) m),
    SheafGradedAlgebra.of_mem_grading _ V _⟩

/-- **The dehomogenisation, in degree one, is the trivialised quotient.** This is the dictionary
entry the pinning match is read through: the scalar it produces is the value of
`Stacks.RelativeProj.trivializedQuotientHom` on the section, i.e. `e (q m)`. -/
public theorem localDehomogenize_localDegreeOne (m : Γ(F, V)) :
    localDehomogenize V q e (localDegreeOne V m).1 =
      preimageSelfTopRingHom V
        (ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m)) :=
  Stacks.SymmetricDehomogenize.dehomogenize_of_one V.ι F (trivializedQuotientHom V q e) V
    (preimageSelfTopRingHom V) (isQuasicoherentPieces_of_isQuasicoherent F) m

/-- **A section the trivialised quotient carries to the unit gives a degree-one element of value
`1`.** This is what puts the whole of `V` inside the standard open of that element, and it is the
hypothesis `f r = 1` of the absolute pinning match. -/
public theorem localDehomogenize_localDegreeOne_eq_one {m₀ : Γ(F, V)}
    (hm₀ : ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m₀) = 1) :
    localDehomogenize V q e (localDegreeOne V m₀).1 = 1 :=
  (localDehomogenize_localDegreeOne V q e m₀).trans
    ((congrArg (preimageSelfTopRingHom V) hm₀).trans (map_one (preimageSelfTopRingHom V)))

/-- **The pinning match at the local chart of `𝐏(ℰ)`.** Let `m₀` be a section of `ℰ` over `V`
that the trivialised quotient carries to the unit section, so that `localChartMap` lands wholly
inside the standard open of the degree-one element of `m₀` and
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection` makes the
pulled-back degree-one section of that element a frame of the pulled-back twist. **Then for every
section `m` of `ℰ` over `V` the pulled-back degree-one section of `m` is `e (q m)` times that
frame**, over every open of `V`.

This is the compatibility with the quotient maps that freeness alone does not give, in the
vocabulary of the route's local section. See `Not done here` for what the transport to
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` still owes. -/
public theorem resT_pullbackDegreeSection_localChartMap
    (hq : Function.Surjective (q.val.app (op V))) {m₀ : Γ(F, V)}
    (hm₀ : ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m₀) = 1)
    (hg : localChartMap V q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤)
    (m : Γ(F, V)) (W : V.toScheme.Opens) :
    resT W (pullbackDegreeSection _
        (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg)
        (localDegreeOne V m))
      = resTop W (preimageSelfTopRingHom V
            (ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m)))
        • resT W (pullbackDegreeSection _
            (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg)
            (localDegreeOne V m₀)) := by
  refine Eq.trans
    (resT_pullbackDegreeSection_eq_app_smul _ (localDehomogenize V q e)
      (map_irrelevant_localDehomogenize_eq_top V q e hq) Nat.one_pos (localDegreeOne V m₀)
      (localDegreeOne V m) (localDehomogenize_localDegreeOne_eq_one V q e hm₀) rfl hg W) ?_
  exact congrArg (fun z => z • _) (congrArg (resTop W) (localDehomogenize_localDegreeOne V q e m))

/-- **The local chart lands wholly inside the standard open of the degree-one element of a
section the trivialised quotient carries to the unit.** This is the hypothesis `hg` that
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor` is indexed by, produced from the
section `m₀` and its equation and nothing else:
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen` computes the preimage and
`localDehomogenize_localDegreeOne_eq_one` says the inverted element is `1`.

It is named rather than reconstructed because two consumers need it —
`exists_resT_pullbackDegreeSection_localChartMap` below, and the discharge of
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies`, which needs `m₀`, its
equation and `hg` *together* and so cannot read `hg` off the existential statement below. -/
public theorem preimage_basicOpen_localDegreeOne_eq_top
    (hq : Function.Surjective (q.val.app (op V))) {m₀ : Γ(F, V)}
    (hm₀ : ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m₀) = 1) :
    localChartMap V q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤ := by
  refine (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen _
    (localDehomogenize V q e) (map_irrelevant_localDehomogenize_eq_top V q e hq) Nat.one_pos
    (localDegreeOne V m₀).2).trans ?_
  rw [localDehomogenize_localDegreeOne_eq_one V q e hm₀]
  exact V.toScheme.basicOpen_of_isUnit isUnit_one

/-- **The pinning match with the frame produced rather than assumed.** The frame is the degree-one
element of a section the trivialised quotient carries to the unit, which
`Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` supplies from the surjectivity of
`q` on sections over `V` — the same hypothesis `Stacks.RelativeProj.localChartMap` already
carries — and the standard-open hypothesis is then
`AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen`. So the previous statement is
not vacuous, and a consumer of the route needs nothing of its own to reach it. -/
public theorem exists_resT_pullbackDegreeSection_localChartMap
    (hq : Function.Surjective (q.val.app (op V))) :
    ∃ (m₀ : Γ(F, V)) (hg : localChartMap V q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
          ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          (localDegreeOne V m₀).1 = ⊤),
      ∀ (m : Γ(F, V)) (W : V.toScheme.Opens),
        resT W (pullbackDegreeSection _
            (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg)
            (localDegreeOne V m))
          = resTop W (preimageSelfTopRingHom V
                (ofPushforwardUnit V.ι ((trivializedQuotientHom V q e).val.app (op V) m)))
            • resT W (pullbackDegreeSection _
                (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg)
                (localDegreeOne V m₀)) := by
  obtain ⟨m₀, hm₀⟩ := exists_app_trivializedQuotientHom_eq_one V q e hq
  have hg := preimage_basicOpen_localDegreeOne_eq_top V q e hq hm₀
  exact ⟨m₀, hg, resT_pullbackDegreeSection_localChartMap V q e hq hm₀ hg⟩

/-! ### The twist comparison at the local chart -/

/-- **The local section, composed with the inverse of the presentation comparison, is the morphism
into the chart followed by the chart.** `Stacks.RelativeProj.localSection` is by definition
`localChartMap ≫ chart ≫ bundlePresentationIso.hom`, so this is one cancellation. -/
public theorem localSection_comp_bundlePresentationIso_inv (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) :
    localSection V q e hV hq ≫ (bundlePresentationIso F).inv =
      localChartMap V q e hq ≫ (symGradedBundle F).chart V hV := by
  rw [localSection, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The twist of `𝐏(ℰ)` pulled back along a morphism factoring through the chart over `V` is
the absolute twisting sheaf of `Γ(V, Sym ℰ)` pulled back along the factorisation.**

A *chart factorisation over `V`* is a pair `(g, h)` with `g : Y ⟶ 𝐏(ℰ)`,
`h : Y ⟶ Proj Γ(V, Sym ℰ)` and `g ≫ bundlePresentationIso.inv = h ≫ chart V hV`. Nothing else
about either morphism is used. The route's local section is one such pair, with
`h = Stacks.RelativeProj.localChartMap` and the factorisation
`localSection_comp_bundlePresentationIso_inv` above; `localSectionTwistIso` below is this
comparison there. For an *arbitrary* section `σ` of `π : 𝐏(ℰ) ⟶ X` the pair is `(V.ι ≫ σ, h)`
with `h` supplied by `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver`, which is the case
the injectivity clause of [Stacks, Tag 0B3V] needs.

This is the comparison `Stacks.ProjectiveBundle.classifyingTwistIso` restated at an arbitrary such
pair. That declaration is stated for
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit`, whereas `localChartMap` is
`AlgebraicGeometry.Proj.fromOfGlobalSections` directly — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalSectionMap.lean` — so neither statement
follows from the other by unfolding, and this is the form the descent of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean` consumes.

The content is `Stacks.ProjectiveBundle.chartTwistIso`, the identification of the chart's
pullback of `Stacks.ProjectiveBundleSplitting.tautologicalTwist` with the absolute twisting sheaf,
together with three `AlgebraicGeometry.Scheme.Modules.pullback` comparisons: the twist of `𝐏(ℰ)`
is itself the pullback of that twist along `bundlePresentationIso.inv`, which is what makes
the factorisation the whole of the transport. -/
public def chartFactorisationTwistIso {Y : Scheme.{u}} (hV : IsAffineOpen V)
    (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV) :
    (Scheme.Modules.pullback g).obj (tautologicalDatumTwist F) ≅
      (Scheme.Modules.pullback h).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          1) :=
  (Scheme.Modules.pullbackComp g (bundlePresentationIso F).inv).app _ ≪≫
    (Scheme.Modules.pullbackCongr hgh).app _ ≪≫
    ((Scheme.Modules.pullbackComp h ((symGradedBundle F).chart V hV)).app _).symm ≪≫
    (Scheme.Modules.pullback h).mapIso
      (Stacks.ProjectiveBundle.chartTwistIso F
        (isQuasicoherentPieces_of_isQuasicoherent F) hV)

/-- **The twist comparison at a chart factorisation, read on the object the pinning match
pins.** `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection`
and the pinning match above are stated for
`Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist` at
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor`, the pullback along the factorisation
through the open `U_d` where the twist is invertible; this composes
`chartFactorisationTwistIso` with
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.toProj_chartFactor`, which says that factorisation
composes back to `h`.

So the pulled-back twist of `𝐏(ℰ)` along any morphism factoring through the chart over `V` is, by
an explicit isomorphism, the module on which the pulled-back degree-one section of a frame is a
basis and on which the identity of
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` holds. -/
public def chartFactorisationPullbackTwistIso {Y : Scheme.{u}} (hV : IsAffineOpen V)
    (g : Y ⟶ projectiveBundle X F)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    (hgh : g ≫ (bundlePresentationIso F).inv = h ≫ (symGradedBundle F).chart V hV)
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) :
    (Scheme.Modules.pullback g).obj (tautologicalDatumTwist F) ≅
      pullbackTwist _ (chartFactor _ (localDegreeOne V m₀).2 h hg) 1 :=
  chartFactorisationTwistIso V hV g h hgh ≪≫
    (Scheme.Modules.pullbackCongr
      (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).app _

/-- **The twist of `𝐏(ℰ)` pulled back along the local section is the absolute twisting sheaf of
`Γ(V, Sym ℰ)` pulled back along `Stacks.RelativeProj.localChartMap`.** This is
`chartFactorisationTwistIso` at the chart factorisation
`localSection_comp_bundlePresentationIso_inv`, which is the pair the descent of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean` consumes. -/
public def localSectionTwistIso (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) :
    (Scheme.Modules.pullback (localSection V q e hV hq)).obj (tautologicalDatumTwist F) ≅
      (Scheme.Modules.pullback (localChartMap V q e hq)).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
          1) :=
  chartFactorisationTwistIso V hV (localSection V q e hV hq) (localChartMap V q e hq)
    (localSection_comp_bundlePresentationIso_inv V q e hV hq)

/-- **The twist of `𝐏(ℰ)` pulled back along the local section, read on the object the pinning
match pins.** This is `chartFactorisationPullbackTwistIso` at the chart factorisation
`localSection_comp_bundlePresentationIso_inv`.

So the pulled-back twist of `𝐏(ℰ)` over `V` is, by an explicit isomorphism, the module on which
the pulled-back degree-one section of a frame is a basis and on which the identity of
`Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` holds. -/
public def localSectionPullbackTwistIso (hV : IsAffineOpen V)
    (hq : Function.Surjective (q.val.app (op V))) {m₀ : Γ(F, V)}
    (hg : localChartMap V q e hq ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤) :
    (Scheme.Modules.pullback (localSection V q e hV hq)).obj (tautologicalDatumTwist F) ≅
      pullbackTwist _
        (chartFactor _ (localDegreeOne V m₀).2 (localChartMap V q e hq) hg) 1 :=
  chartFactorisationPullbackTwistIso V hV (localSection V q e hV hq) (localChartMap V q e hq)
    (localSection_comp_bundlePresentationIso_inv V q e hV hq) hg

/-! ### The chart's degree-one section is the one the pinning match is stated on -/

/-- **`chartDegreeOneSection` is the degree-one section of `localDegreeOne`.** The two degree-one
elements of `Γ(V, Sym ℰ)` are the same element: `chartDegreeOneSection` is built from
`Stacks.ProjectiveBundleConormal.chartPiece`, which
`Stacks.ProjectiveBundleConormal.symmetricAlgebraGen_app` identifies with the value over `V` of
the generator `ℰ ⟶ Sym¹(ℰ)`, and that value is what `localDegreeOne` is `DirectSum.of` of.

So the section that
`Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection` computes —
the pulled-back value of `Stacks.ProjectiveBundleSplitting.tautologicalMap` carried across
`Stacks.ProjectiveBundle.chartTwistIso` — is the degree-one section of the element the pinning
match `resT_pullbackDegreeSection_localChartMap` is pinned by. -/
public theorem chartDegreeOneSection_eq_degreeSection_localDegreeOne (hV : IsAffineOpen V)
    (m : Γ(F, V)) :
    Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
          (isQuasicoherentPieces_of_isQuasicoherent F) hV m =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1
        (localDegreeOne V m) :=
  Stacks.ProjectiveBundleConormal.chartDegreeOneSection_eq_degreeSection F
    (isQuasicoherentPieces_of_isQuasicoherent F) hV m

/-- **The last comparison of `chartFactorisationPullbackTwistIso` carries the chart's degree-one
section to the pulled-back degree-one section of `localDegreeOne`**, over every open of the
source and **at an arbitrary morphism `h` into `Proj Γ(V, Sym ℰ)`.**

`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection` pulls the degree-one
section back along `Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj` of
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.chartFactor`, whereas everything upstream pulls
back along `h` itself; the two morphisms are equal by
`Stacks.AlgebraicGeometry.ProjTwistPinnedChart.toProj_chartFactor` but not definitionally, and
the transport is the comparison `chartFactorisationPullbackTwistIso` ends with. So this is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` at that equality, with
`chartDegreeOneSection_eq_degreeSection_localDegreeOne` rewriting the section first.

**It is stated over an arbitrary open `W`, not only over `⊤`.** The consumer — the chain of
section identifications that discharges
`Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` — meets the composite over
`V.ι ⁻¹ᵁ V`, which is `⊤` by `AlgebraicGeometry.Scheme.Opens.ι_preimage_self` but not
definitionally, so transporting a `⊤`-only version would put an `eqToHom` inside a section. The
right-hand side is therefore written as an
`AlgebraicGeometry.Scheme.Modules.pullbackSection` rather than as a
`pullbackDegreeSection`; at `W = ⊤` the two are the same term, which is
`Stacks.RelativeProj.pullbackDegreeSection_eq_pullbackSection` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean`.

Together with
`Stacks.ProjectiveBundleConormal.pullback_chartTwistIso_hom_pullbackSection` this closes the
passage from the pulled-back tautological map to the object the pinning match pins. -/
public theorem pullbackCongr_hom_pullbackSection_chartDegreeOneSection {Y : Scheme.{u}}
    (hV : IsAffineOpen V)
    (h : Y ⟶ AlgebraicGeometry.Proj
      ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V))
    {m₀ : Γ(F, V)}
    (hg : h ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
        ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
        (localDegreeOne V m₀).1 = ⊤)
    (m : Γ(F, V)) (W : Y.Opens) (hW : W ≤ h ⁻¹ᵁ ⊤)
    (hW' : W ≤ toProj _ (chartFactor _ (localDegreeOne V m₀).2 h hg) ⁻¹ᵁ ⊤) :
    ((Scheme.Modules.pullbackCongr
            (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).hom.app
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1)).val.app (op W)
        (Scheme.Modules.pullbackSection h _ ⊤ W hW
          (Stacks.ProjectiveBundleConormal.chartDegreeOneSection F
            (isQuasicoherentPieces_of_isQuasicoherent F) hV m))
      = Scheme.Modules.pullbackSection
          (toProj _ (chartFactor _ (localDegreeOne V m₀).2 h hg))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
            ((schemeSheafGradedAlgebra F
              (isQuasicoherentPieces_of_isQuasicoherent F)).grading V) 1) ⊤ W hW'
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
            ((schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)).grading V)
            1 (localDegreeOne V m)) :=
  (congrArg
      (fun z => ((Scheme.Modules.pullbackCongr
            (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm).hom.app _).val.app (op W)
        (Scheme.Modules.pullbackSection h _ ⊤ W hW z))
      (chartDegreeOneSection_eq_degreeSection_localDegreeOne V hV m)).trans
    (Scheme.Modules.pullbackSection_congr
      (toProj_chartFactor _ (localDegreeOne V m₀).2 h hg).symm _ ⊤ W hW hW' _)

end Stacks.RelativeProj

end
