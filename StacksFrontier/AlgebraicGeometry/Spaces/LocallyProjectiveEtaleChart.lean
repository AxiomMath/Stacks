module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.InternalHom
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Local projectivity of a module on an algebraic space is tested on one étale chart

Let `F` be an algebraic space over a scheme `S` of a big fppf site and let `M` be an
`𝒪_F`-module.  Restricting `M` to an étale scheme chart `U` gives a sheaf of modules
`M|_U` on the Zariski site of `chartScheme U`
(`AlgebraicGeometry.Space.restrictToChartScheme`), to which the scheme-level notion of local
projectivity of Stacks 05JP applies.  This file proves Stacks 060Q: the restriction is
locally projective on *one* chart whose structure morphism is surjective on points exactly
when it is locally projective on *every* chart.  Stacks 060S, stability of that condition
under pullback along a morphism of algebraic spaces, follows.

The mathematical content is the source's own argument.  Given a surjective chart `U` and an
arbitrary chart `V`, the fibre product `U ×_F V` is again an étale chart `W` of `F`, lying over
both, and `chartScheme W ⟶ chartScheme V` is surjective and étale, hence an fpqc covering.
The restriction `M|_W` is the pullback of `M|_U` along `chartScheme W ⟶ chartScheme U`, so it
is locally projective by Stacks 060M, and it is also the pullback of `M|_V`, so Stacks 05JZ
descends local projectivity to `V`.

## Main results

* `AlgebraicGeometry.Space.exists_chart_over_of_isSurjective`: every étale chart of an
  algebraic space is dominated by an étale chart lying over a given chart surjective on
  points, by a surjective étale morphism of the underlying schemes.
* `AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_of_isSurjective`: the
  passage from one surjective chart to an arbitrary chart, which is the substance of
  Stacks 060Q.
* `AlgebraicGeometry.Space.exists_surjective_isLocallyProjective_iff_forall`:
  **Stacks Project, Tag 060Q.**
* `AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_modulePullback`:
  **Stacks Project, Tag 060S.**

## Implementation notes

The two tags are proved here from étale charts, and the hypotheses their statements carry differ.

Stacks 060Q, `exists_surjective_isLocallyProjective_iff_forall`, carries quasi-coherence of the
module and nothing else beyond the data of the tag: it is `SheafOfModules.IsQuasicoherentOnSite`
on the small étale site of `F`, the binder `hM`.  Both inputs its argument consumes are derived
from it in `StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionQuasicoherent.lean`.

Stacks 060S, `isLocallyProjective_restrictToChartScheme_modulePullback`, still carries its inputs
as the explicit hypotheses `hqcY`, `hqcX` and `hsquare`, and **every one of them is a theorem of
this development for a quasi-coherent module**, so that statement is a carried form and not the
final word: the discharged form is
`Space.isLocallyProjective_restrictToChartScheme_modulePullback_of_isQuasicoherentOnSite`
of `StacksFrontier/AlgebraicGeometry/Spaces/LocallyProjectivePullbackSpaces.lean`, which also holds
the discharged one-chart-to-every-chart step
`Space.isLocallyProjective_restrictToChartScheme_of_isSurjective_of_isQuasicoherentOnSite`.
What makes them available is the identification of a chart restriction with the identity-chart
restriction of an étale pullback,
`AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback_idEtaleChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionEtalePullback.lean`.

The first input is quasi-coherence of a chart restriction *on the Zariski site of the chart
scheme*, which Stacks 060M and Stacks 05JZ require of the modules they are applied to, whereas
quasi-coherence of an `𝒪_F`-module is `SheafOfModules.IsQuasicoherentOnSite` on the small étale
site of `F`.  Carrying it across the inclusion of the small Zariski site of the chart scheme is
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` — Descent, Proposition 03DX — and
the hypothesis is discharged for a quasi-coherent module by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`.  Note that local projectivity
itself, `AlgebraicGeometry.Scheme.Modules.IsLocallyProjective`, carries no quasi-coherence
requirement, so this input is forced only by the two results cited, not by the statements being
proved.

The second is the comparison of the two readings of a chart restriction: for a morphism
`g : W ⟶ U` of étale charts, the pullback of `M|_U` along `chartScheme W ⟶ chartScheme U` is
`M|_W`.  As the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparison.lean` record, the
canonical
comparison `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` exists for every
`𝒪_F`-module and is an isomorphism exactly for the quasi-coherent ones.  The proofs below use it
only to transport local projectivity, so what they consume is the existence of *some* such
isomorphism, not invertibility of the canonical comparison; that is
`AlgebraicGeometry.Space.nonempty_pullback_restrictToChartScheme`, obtained from the represented
case of the base change of a chart restriction together with Stacks 03LY, and in the étale-pullback
form `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange`.

Stacks 060S carries in addition the base-change identity `(f^*G)|_U ≅ ψ^*(G|_V)` for a
commuting square of charts of `f`, the binder `hsquare` below; it is the only place where the
pullback `AlgebraicGeometry.Space.modulePullback` of Stacks 03LU enters, and it is what the
source means by "`f^*G|_U` is the pullback of `G|_V`".  It is discharged for a quasi-coherent
`G` by `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_modulePullback_square`.  Its other
binder, `hqcX`, is quasi-coherence of `f^*G` on the small étale site of `X`; that is Stacks 03GA,
which holds along an arbitrary morphism of algebraic spaces by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackQuasicoherentFromChartDiagrams.lean`, so it
too is discharged for a quasi-coherent `G`.  No projectivity statement occurs in any of these
hypotheses.

The binders are nevertheless kept here, and the discharged form is a separate theorem rather
than a replacement, because each of the three is implied by — and strictly weaker than —
quasi-coherence of `G` on the small étale site.  Chartwise Zariski quasi-coherence of the chart
restrictions does not give it back: that is the essential surjectivity clause of Descent,
Proposition 03DX (2), recorded as unavailable in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssentialImage.lean`.  So
rewriting the statement below to consume the discharged inputs would narrow it.

The chart used by Stacks 060Q is `AlgebraicGeometry.Space.restrictToChartScheme`, the
restriction of an `𝒪_F`-module to the Zariski site of the chart scheme, which is the
construction the comparison above is available for.  The parallel construction
`AlgebraicGeometry.Space.restrictToChart`, through which
`AlgebraicGeometry.Space.IsLocallyProjective` of Stacks 060R is defined, is not identified with
it anywhere in this development.

The module universe is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` and
`AlgebraicGeometry.Space.modulePullback` are both available only there; see the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparison.lean` and of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`.  Local projectivity
itself, and its invariance under isomorphism proved here, are at a free module universe.

The fibre product of two étale charts is formed with the relative representability of the
structure morphism of a chart, which is part of being an étale chart, exactly as in
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`; its projection to the second
chart is surjective and étale because both properties of the structure morphism of the first
are asserted for every represented base change.  A single surjective étale morphism of schemes
is an fpqc covering through `AlgebraicGeometry.mem_fpqcPrecoverage_of_mem_coveringPrecoverage`,
étale morphisms being flat and locally of finite presentation, so no quasi-compactness is
checked.

## References

* [Stacks Project, Tag 060Q](https://stacks.math.columbia.edu/tag/060Q)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
* [Stacks Project, Tag 060M](https://stacks.math.columbia.edu/tag/060M)
* [Stacks Project, Tag 05JZ](https://stacks.math.columbia.edu/tag/05JZ)
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A single surjective étale morphism of schemes is an fpqc covering: an étale morphism is
flat and locally of finite presentation, hence open, so no quasi-compactness intervenes. -/
theorem ofArrows_mem_fpqcPrecoverage_of_surjective_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hs : Surjective f) (he : Etale f) :
    Presieve.ofArrows (fun _ : PUnit.{1} => X) (fun _ => f) ∈ Scheme.fpqcPrecoverage Y :=
  mem_fpqcPrecoverage_of_mem_coveringPrecoverage Scheme.etalePrecoverage
    (Or.inr (Or.inr (Or.inl rfl)))
    ((Scheme.ofArrows_mem_precoverage_iff (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
      (X := fun _ : PUnit.{1} => X) (f := fun _ => f)).2
      ⟨fun x => ⟨PUnit.unit, hs.surj x⟩, fun _ => he⟩)

/-- Local projectivity passes to a module isomorphic to the pullback of a quasi-coherent locally
projective module (Stacks 060M). -/
private theorem isLocallyProjective_of_iso_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Y.Modules} {N : X.Modules} [G.IsQuasicoherent]
    (e : (Scheme.Modules.pullback f).obj G ≅ N) (hG : Scheme.Modules.IsLocallyProjective G) :
    Scheme.Modules.IsLocallyProjective N :=
  Scheme.Modules.isLocallyProjective_of_iso e (pullback_isLocallyProjective f _ hG)

/-- Every étale chart `V` of an algebraic space is dominated by an étale chart lying over a
given étale chart `U` whose structure morphism is surjective on points, and the morphism of
chart schemes to `V` is surjective and étale.

The dominating chart is the fibre product `U ×_F V`, which is representable because the
structure morphism of `U` is relatively representable; its projection to `V` is surjective and
étale because both properties of the structure morphism of `U` hold for every represented base
change. -/
theorem exists_chart_over_of_isSurjective (hF : IsAlgebraicSpace B S hS F)
    (U : SmallEtale B S hS F) (hsurj : IsSurjective B S hS U.1.hom)
    (V : SmallEtale B S hS F) :
    ∃ (W : SmallEtale B S hS F) (a : W ⟶ V) (_ : W ⟶ U),
      Surjective (chartSchemeMap a) ∧ Etale (chartSchemeMap a) := by
  have hsurjP := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF
    U.1.left U.1.hom).2 hsurj
  have hrep : yoneda.relativelyRepresentable U.1.hom := U.property.rep
  set q : hrep.pullback V.1.hom ⟶ V.1.left := hrep.snd V.1.hom with hq
  set p : hrep.pullback V.1.hom ⟶ U.1.left := hrep.fst' V.1.hom with hp
  have hw : yoneda.map p ≫ U.1.hom = yoneda.map q ≫ V.1.hom := by
    rw [hp, Functor.relativelyRepresentable.map_fst']
    exact hrep.w V.1.hom
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    U.property.property V.1.hom (hrep.fst V.1.hom) (hrep.snd V.1.hom)
      (hrep.isPullback V.1.hom)
  have hqSurj : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    hsurjP.property V.1.hom (hrep.fst V.1.hom) (hrep.snd V.1.hom)
      (hrep.isPullback V.1.hom)
  exact ⟨⟨CostructuredArrow.mk (yoneda.map q ≫ V.1.hom),
      etale_comp_of_scheme B S hS q V.1.hom hqEtale V.property⟩,
    ObjectProperty.homMk (CostructuredArrow.homMk q rfl),
    ObjectProperty.homMk (CostructuredArrow.homMk p hw), hqSurj, hqEtale⟩

/-- **The substance of Stacks Project, Tag 060Q.** If the restriction of an `𝒪_F`-module to one
étale chart surjective on points is locally projective, then so is its restriction to every
étale chart.

The fibre product `W` of the two charts maps to both; `M|_W` is the pullback of `M|_U`, hence
locally projective by Stacks 060M, and it is also the pullback of `M|_V` along a surjective
étale, hence fpqc, covering, so Stacks 05JZ descends local projectivity to `V`.

Quasi-coherence of `M` supplies the two inputs described in the implementation notes: Zariski
quasi-coherence of the chart restrictions, and the identification of a chart restriction with
the pullback of the restriction to a larger chart. -/
theorem isLocallyProjective_restrictToChartScheme_of_isSurjective
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite)
    (U : SmallEtale B S hS F) (hsurj : IsSurjective B S hS U.1.hom)
    (hU : Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS F hF M U))
    (V : SmallEtale B S hS F) :
    Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS F hF M V) := by
  obtain ⟨W, a, b, hsurja, hetalea⟩ :=
    exists_chart_over_of_isSurjective B S hS F hF U hsurj V
  obtain ⟨eb⟩ := nonempty_pullback_restrictToChartScheme B S hS ⟨F, hF⟩ M hM b
  obtain ⟨ea⟩ := nonempty_pullback_restrictToChartScheme B S hS ⟨F, hF⟩ M hM a
  have hqcU : (restrictToChartScheme B S hS F hF M U).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS ⟨F, hF⟩ M hM U
  have hWproj : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS F hF M W) :=
    isLocallyProjective_of_iso_pullback (chartSchemeMap b) eb hU
  exact isLocallyProjective_of_pullback_fpqc _
    (isQuasicoherent_restrictToChartScheme B S hS ⟨F, hF⟩ M hM V)
    (fun _ : PUnit.{1} => chartScheme W) (fun _ => chartSchemeMap a)
    (ofArrows_mem_fpqcPrecoverage_of_surjective_etale _ hsurja hetalea)
    (fun _ => Scheme.Modules.isLocallyProjective_of_iso ea.symm hWproj)

/-- **Stacks Project, Tag 060Q.** The restriction of an `𝒪_F`-module to the Zariski site of an
étale chart scheme is locally projective for *some* chart whose structure morphism is surjective
on points if and only if it is locally projective for *every* étale chart.

The implication from one chart to all of them is
`AlgebraicGeometry.Space.isLocallyProjective_restrictToChartScheme_of_isSurjective`; the
converse needs only that an algebraic space has a chart surjective on points at all, namely its
atlas.  Quasi-coherence of `M` is the source's standing hypothesis on the module. -/
@[stacks 060Q]
theorem exists_surjective_isLocallyProjective_iff_forall
    (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) :
    (∃ U : SmallEtale B S hS F, IsSurjective B S hS U.1.hom ∧
        Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS F hF M U)) ↔
      ∀ U : SmallEtale B S hS F,
        Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS F hF M U) := by
  refine ⟨fun ⟨U, hsurj, hU⟩ =>
    isLocallyProjective_restrictToChartScheme_of_isSurjective B S hS F hF M hM U hsurj hU,
    fun h => ?_⟩
  obtain ⟨U, hU⟩ := exists_surjective_smallEtale_chart B S hS F hF
  exact ⟨U, hU, h U⟩

/-- **Stacks Project, Tag 060S.** The pullback of a locally projective `𝒪_Y`-module along a
morphism `f : X ⟶ Y` of algebraic spaces is locally projective.

The source's reduction: choose an étale chart `V` of `Y` surjective on points and lift it
through `f` to an étale chart `U` of `X` surjective on points together with `ψ : U ⟶ V` making
the square commute (Stacks 02X1).  Then `(f^*G)|_U` is the pullback of `G|_V` along `ψ`, so it
is locally projective by Stacks 060M, and Stacks 060Q propagates that to every chart of `X`.

See the implementation notes for the carried hypotheses: `hqcY` is Zariski quasi-coherence of the
chart restrictions of `G`, `hqcX` is quasi-coherence of `f^*G` on the small étale site of `X`,
and `hsquare` is the base-change identity `(f^*G)|_U ≅ ψ^*(G|_V)` at a commuting square of charts
of `f`. -/
@[stacks 060S]
theorem isLocallyProjective_restrictToChartScheme_modulePullback
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hqcY : ∀ V : SmallEtale B S hS Y.1,
      (restrictToChartScheme B S hS Y.1 Y.2 G V).IsQuasicoherent)
    (hqcX : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite)
    (hsquare : ∀ (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
        (ψ : U.1.left ⟶ V.1.left), U.1.hom ≫ f.hom = yoneda.map ψ ≫ V.1.hom →
      (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U ≅
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ)).obj
          (restrictToChartScheme B S hS Y.1 Y.2 G V)))
    (hG : ∀ V : SmallEtale B S hS Y.1,
      Scheme.Modules.IsLocallyProjective (restrictToChartScheme B S hS Y.1 Y.2 G V))
    (U : SmallEtale B S hS X.1) :
    Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U) := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  obtain ⟨U₀, p, ψ, hsq, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V.1.left V.1.hom
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 V.1.left V.1.hom).2 hV)
      V.property
  set U₀c : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hpEtale⟩ with hU₀c
  have hU₀surj : IsSurjective B S hS U₀c.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U₀ p).1 hpSurj
  have hqcV : (restrictToChartScheme B S hS Y.1 Y.2 G V).IsQuasicoherent := hqcY V
  have hU₀proj : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 ((modulePullback B S hS f).obj G) U₀c) :=
    isLocallyProjective_of_iso_pullback _ (hsquare U₀c V ψ hsq).symm (hG V)
  exact isLocallyProjective_restrictToChartScheme_of_isSurjective B S hS X.1 X.2
    ((modulePullback B S hS f).obj G) hqcX U₀c hU₀surj hU₀proj U

end Space

end AlgebraicGeometry

end
