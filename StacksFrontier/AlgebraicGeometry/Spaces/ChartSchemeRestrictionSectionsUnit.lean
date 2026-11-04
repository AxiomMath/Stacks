module

public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionPullbackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange

/-!
# The restriction to a chart scheme, read on sections at the sheafification unit

For an étale chart `U` of an algebraic space `F`,
`AlgebraicGeometry.Space.restrictToChartScheme` restricts an `𝒪_F`-module `M` to the Zariski site
of `chartScheme U` by sheafifying, and
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` identifies the result with the
direct image of `M` along the index functor of the chart.  Over a Zariski open `O` that
identification gives a `Γ(chartScheme U, O)`-linear equivalence between the sections of the
restriction and the sections of `M` over the étale chart `O` cuts out, namely
`AlgebraicGeometry.sectionsLinearEquivOfIso` at it.

This file computes that equivalence.  The computation is the one thing the identification was
missing: it is built from the *counit* of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, while every section computation for
the chart restriction —
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_app_toSheafify` and
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_app_pullbackSection_toSheafify` —
is stated at the *unit* `CategoryTheory.toSheafify` of the underlying presheaf of abelian groups.
Here the two meet: on the sheafification unit of a section `m`, the equivalence is `m.down`.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforwardTranspose` is the adjoint transpose
  of `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` along the sheafification
  adjunction of presheaves of modules: the morphism of presheaves of modules undoing the universe
  lift of the sections, pushed forward along
  `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`.

## Main results

The names below are in the namespace `AlgebraicGeometry`.

* `Space.sheafificationHomEquiv_restrictToChartSchemeIsoPushforward_hom`: the identification
  **is** the transpose of that morphism.
* `Space.sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify`: **the
  equivalence on a sheafification unit.**  Over a Zariski open `O` of `chartScheme U` the linear
  equivalence carries the Zariski sheafification unit of a section `m` of `M` over the étale chart
  `openChart U O` to `m` itself, the universe lift undone.
* `Space.sectionsLinearEquivOfIso_restrictToChartSchemePullbackComparison_app_pullbackSection`:
  **the inverse-image comparison of the two chart restrictions, read through the two
  identifications, is the restriction map of `M` along a morphism of étale charts.**  This holds
  for *every* section over `O`, with no affineness and no quasi-coherence hypothesis.

## Implementation notes

**Why this is the link the affine step needs.**  The affine comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is written over the rings of regular
functions `Γ(chartScheme U, O)` and `Γ(chartScheme V, O')`, and normalises the sections of an
inverse image by the pulled-back sections
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`); the chart comparison is
computed on exactly those sections by
`AlgebraicGeometry.Space.exists_restrictToChartSchemePullbackComparison_app_pullbackSection`, but
in terms of `CategoryTheory.toSheafify`.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIso.lean` record the
identification of the two spellings as the one unavailable link, and say what it would take:
computing `AlgebraicGeometry.sectionsLinearEquivOfIso` at
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` in terms of `toSheafify`, on one
side of the `CommRingCat`/`RingCat` boundary only.  That is what is done here, on the
`CommRingCat` side — the side the affine comparison is stated over — and nothing below mentions
the `RingCat`-valued sections.

**The boundary is crossed by no term here.**  The sections of the chart restriction over `O`
carry a `Module ((chartScheme U).ringCatSheaf.obj.obj (op O))` instance and *not* a
`Module Γ(chartScheme U, O)` one: instance search does not find the second, which is why the
type of the equivalence below cannot be written out and why it appears only inside the statement
of the computation, where its elaboration is driven by
`AlgebraicGeometry.sectionsLinearEquivOfIso`'s own type.  No bridging instance, `inferInstanceAs`
or reducibility attribute is introduced to paper over this; the statements are simply phrased on
the side where the terms live.

**How the computation goes.**  `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` is,
by construction and by `rfl`, the sheafification of
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforwardTranspose` followed by the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction`, which is
`CategoryTheory.Adjunction.homEquiv_counit` at that adjunction; so applying the adjunction's
`homEquiv` to it returns the transpose, by `Equiv.apply_symm_apply`.  The adjunction's `homEquiv`
is `CategoryTheory.PresheafOfModules.sheafificationHomEquiv` by
`CategoryTheory.PresheafOfModules.sheafificationAdjunction_homEquiv_apply`, and
`CategoryTheory.PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def` — which holds by
`rfl` — turns that into the composite of `toSheafify` with the identification, read on the
underlying presheaves of abelian groups.  Evaluating at `O` and applying to `m` is then the whole
proof.  Every step that crosses the fork between the sections of a `sheafCompose` and those of a
composite presheaf is written as a term, for the reason the implementation notes of
`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffineDegreeZero/AlgebraPushout.lean`
give: a `rewrite` has to build its motive at a transparency at which such a term is not
type-correct.  The one `congrArg` below carries an explicit type ascription on its bound variable
for the same reason.

**What is still owed, and the second spelling boundary it runs into.**  Nothing here says the
comparison is invertible.  With the square below, the remaining step over a pair of affine opens
`O`, `O'` is to recognise the restriction map of `M` along
`openChartHomOfLE V hle ≫ openChartRestrict g O` as a base change and to conclude.  Three of the
four inputs are available: `AlgebraicGeometry.isBaseChange_pullbackSection_of_isAffineOpen`
(in `StacksFrontier/AlgebraicGeometry/RelativeProjSituation/MorphismSections.lean`) makes the
pulled-back sections a base change over `Γ(chartScheme U, O)` and `Γ(chartScheme V, O')`;
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse`
gives bijectivity of `AlgebraicGeometry.Space.sectionsBaseChange` at *any* morphism of affine
étale charts, so in particular at that one; and
`AlgebraicGeometry.IsBaseChange.of_linearEquiv` transports a base change along the two
identifications computed here.

The input that is **not** available is the transport of bijectivity from the chart rings
`𝒪_F(openChart U O)`, `𝒪_F(openChart V O')` to the rings of regular functions
`Γ(chartScheme U, O)`, `Γ(chartScheme V, O')` *in this spelling of the charts*.  The transport
`AlgebraicGeometry.Space.bijective_liftBaseChange_iff_sectionsBaseChange` exists, but it is
written over `(chartOpens U).obj O` and `AlgebraicGeometry.Space.chartOpensRestrictLE`, whereas
every section computation for the comparison — here and in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean` — is written
over `AlgebraicGeometry.Space.openChart`.  The two readings of a Zariski open as an étale chart
are equal only propositionally, by `AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`, which is
not `rfl`; so composing the two needs either an `eqToHom` transport, which is the design debt this
tree avoids, or a restatement of the transport over `openChart`.  The pieces for that restatement
are already present in the `openChart` spelling:
`AlgebraicGeometry.Space.openChartTopRingHom` is the ring comparison
`𝒪_F(openChart U O) →+* Γ(chartScheme U, O)`,
`AlgebraicGeometry.Space.bijective_openChartTopRingHom` its bijectivity, and
`AlgebraicGeometry.resLE_appTop_comp_topIso_hom` together with
`AlgebraicGeometry.homOfLE_appTop_comp_topIso_hom` and
`AlgebraicGeometry.Space.toScheme_map_toOver_map_openChartHomOfLE` the commuting square for the
two factors of the chart morphism.  This is the same choice-of-side that the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartOpenSectionsRingTransport.lean` describe for the
`CommRingCat`/`RingCat` boundary, at a different boundary, and it is not made here.

**No `stacks` attribute is claimed.**  The content is the value of one isomorphism on sections.
The isomorphism itself is the identification of the chart restriction with an inverse image,
Stacks 03LY, which is registered elsewhere; the invertibility statement this feeds — cartesianness
of Descent, Proposition 03DX for the chart-restriction comparison — is not asserted here, and
still needs the identification of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` with a base change over an
affine pair.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

noncomputable section

variable (M : Modules.{u, u} B S hS F hF) (U : SmallEtale B S hS F)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(openChartFunctor B S hS F U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)]

/-! ### The transpose of the direct-image identification -/

/-- **The adjoint transpose of `AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward`.**
The restriction to the chart scheme sheafifies the presheaf of modules obtained from the
universe-lifted sections of `M` by pushing forward along
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom`; this is that pushforward of the
morphism undoing the universe lift, which is the morphism the identification is the transpose
of. -/
def restrictToChartSchemeIsoPushforwardTranspose :
    (PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
      (SheafOfModules.uliftForPresentation M).val ⟶
    (PresheafOfModules.restrictScalars (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
      ((SheafOfModules.forget _).obj
        ((SheafOfModules.pushforward.{u}
          (chartSchemeRestrictionSheafHom B S hS hF U)).obj M)) :=
  (PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).map
    ((SheafOfModules.forget _).map (SheafOfModules.uliftForPresentationSelfIso M).hom)

/-- **The direct-image identification of the chart restriction is the transpose of
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforwardTranspose`.**

The identification is the sheafification of that morphism followed by the counit of the
sheafification adjunction of presheaves of modules, so this is
`CategoryTheory.Adjunction.homEquiv_counit` at that adjunction together with
`Equiv.apply_symm_apply`. -/
theorem sheafificationHomEquiv_restrictToChartSchemeIsoPushforward_hom :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (chartScheme U).ringCatSheaf.obj)
        (restrictToChartSchemeIsoPushforward B S hS hF U M).hom =
      restrictToChartSchemeIsoPushforwardTranspose B S hS hF M U :=
  (PresheafOfModules.sheafificationAdjunction_homEquiv_apply
      (𝟙 (chartScheme U).ringCatSheaf.obj) _).symm.trans
    ((congrArg ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (chartScheme U).ringCatSheaf.obj)).homEquiv _ _)
      (Adjunction.homEquiv_counit (PresheafOfModules.sheafificationAdjunction
          (𝟙 (chartScheme U).ringCatSheaf.obj))
        (Y := (SheafOfModules.pushforward.{u}
          (chartSchemeRestrictionSheafHom B S hS hF U)).obj M)
        (g := restrictToChartSchemeIsoPushforwardTranspose B S hS hF M U)).symm).trans
      (Equiv.apply_symm_apply _ _))

/-! ### The identification on sections -/

/-- **The sections of the chart restriction, identified with the chart sections of `M`, on a
sheafification unit.**  Let `O` be a Zariski open of `chartScheme U` and `m` a section of `M`
over the étale chart `openChart U O`, with its universe raised.  The
`Γ(chartScheme U, O)`-linear equivalence that
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` induces on the sections over `O`
carries the Zariski sheafification unit of `m` to `m` itself, the universe lift undone.

This is the link the affine step of the chart-restriction comparison needs, and the one recorded
as unavailable in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionPullbackIso.lean`: the section
computations of that file and of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparisonSections.lean` produce
sheafification units, and
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is stated over `Γ(chartScheme U, O)`. -/
theorem sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify
    (O : (chartScheme U).Opens)
    (m : ((PresheafOfModules.pushforward
      (chartSchemeRestrictionRingHom B S hS F U)).obj
        (SheafOfModules.uliftForPresentation M).val).obj (op O)) :
    sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF U M) O
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward
            (chartSchemeRestrictionRingHom B S hS F U)).obj
              (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) m) =
      m.down := by
  have h2 := ConcreteCategory.congr_hom (congrArg (fun t => NatTrans.app t (op O))
    (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 (chartScheme U).ringCatSheaf.obj)
      (restrictToChartSchemeIsoPushforward B S hS hF U M).hom)) m
  refine Eq.trans ?_ ((congrArg (fun z : (PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (chartScheme U).ringCatSheaf.obj)).obj
        ((SheafOfModules.forget _).obj
          ((SheafOfModules.pushforward.{u}
            (chartSchemeRestrictionSheafHom B S hS hF U)).obj M)) => (ConcreteCategory.hom
      (((PresheafOfModules.toPresheaf (chartScheme U).ringCatSheaf.obj).map z).app (op O))) m)
      (sheafificationHomEquiv_restrictToChartSchemeIsoPushforward_hom B S hS hF M U)).trans rfl)
  refine Eq.trans ?_ h2.symm
  exact (ConcreteCategory.comp_apply
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
      ((PresheafOfModules.pushforward
        (chartSchemeRestrictionRingHom B S hS F U)).obj
          (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O))
    (((PresheafOfModules.toPresheaf (chartScheme U).ringCatSheaf.obj).map
      (restrictToChartSchemeIsoPushforward B S hS hF U M).hom.val).app (op O)) m).symm

end

/-! ### The inverse-image comparison, read through the two identifications -/

section Comparison

variable (M : Modules.{u, u} B S hS F hF) {U V : SmallEtale B S hS F} (g : V ⟶ U)
    [HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(openChartFunctor B S hS F U).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme U)) (SmallEtale.topology B S hS F)]
    [(openChartFunctor B S hS F V).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme V)) (SmallEtale.topology B S hS F)]

/-- **The inverse-image comparison of the two chart restrictions is the restriction map of `M`
along a morphism of étale charts, read through the two identifications of the chart
restrictions' sections with the chart sections of `M`.**

Let `O` be a Zariski open of the larger chart scheme and `O'` one of the smaller inside its
preimage.  On the section of `(chartSchemeMap g)^* M|_U` over `O'` pulled back from an
*arbitrary* section `a` of `M|_U` over `O`, the comparison agrees — after the two
`Γ`-linear identifications — with the restriction map of `M` along the morphism of étale charts
`openChartHomOfLE V hle ≫ openChartRestrict g O`.

This is the identification the affine step of the comparison needs.  It is
`AlgebraicGeometry.Space.exists_restrictToChartSchemePullbackComparison_app_pullbackSection`,
which produces the comparison's value as a sheafification unit, composed with
`AlgebraicGeometry.Space.sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify`
at both charts; the restriction map of the universe-lifted sections is the restriction map of `M`
on the underlying element, by `rfl`.  No open is assumed affine and `M` is not assumed
quasi-coherent: those hypotheses enter only when the restriction map is to be recognised as a
base change.

The chart morphism is written in the `AlgebraicGeometry.Space.openChart` spelling, which is the
one the section computations produce.  It is *not* interchangeable with
`AlgebraicGeometry.Space.chartOpensRestrictLE`: the two readings of a Zariski open as an étale
chart agree only propositionally, by
`AlgebraicGeometry.Space.chartOpens_obj_eq_openChart`, which is not `rfl`.  See the
implementation notes. -/
theorem sectionsLinearEquivOfIso_restrictToChartSchemePullbackComparison_app_pullbackSection
    (O : (chartScheme U).Opens) (O' : (chartScheme V).Opens)
    (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (a : (restrictToChartScheme B S hS F hF M U).val.obj (op O)) :
    sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF V M) O'
        ((restrictToChartSchemePullbackComparison B S hS F hF M g).val.app (op O')
          (Scheme.Modules.pullbackSection (chartSchemeMap g)
            (restrictToChartScheme B S hS F hF M U) O O' hle a)) =
      M.val.map (openChartHomOfLE B S hS F V hle ≫ openChartRestrict B S hS F g O).op
        (sectionsLinearEquivOfIso (restrictToChartSchemeIsoPushforward B S hS hF U M) O a) := by
  obtain ⟨m, hm, hc⟩ := exists_restrictToChartSchemePullbackComparison_app_pullbackSection
    B S hS F hF M g O O' hle a
  refine (congrArg (sectionsLinearEquivOfIso
    (restrictToChartSchemeIsoPushforward B S hS hF V M) O') hc).trans ?_
  refine (sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify
    B S hS hF M V O' _).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun z => M.val.map (openChartHomOfLE B S hS F V hle ≫
        openChartRestrict B S hS F g O).op z)
    ((congrArg (sectionsLinearEquivOfIso
        (restrictToChartSchemeIsoPushforward B S hS hF U M) O) hm.symm).trans
      (sectionsLinearEquivOfIso_restrictToChartSchemeIsoPushforward_toSheafify
        B S hS hF M U O m))).symm
  rfl

end Comparison

end AlgebraicGeometry.Space

end
