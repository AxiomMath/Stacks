module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection

/-!
# The acting sheaf and the sheaf of lifts on one site

Let `X ⊆ X'` be a closed subspace of an algebraic space over a scheme `S` contained in a big
fppf site `C`, let `q : Y ⟶ Bb` be a morphism of algebraic spaces and let `a : X ⟶ Y` be a
morphism over `Bb`.  The two objects of [Stacks Project, Tag 061D] live on *different* sites:
the sheaf of lifts `AlgebraicGeometry.Space.liftsSubfunctor` is a sheaf on the small étale site
of the ambient space `X'`, while the acting sheaf
`AlgebraicGeometry.Space.liftActionSheaf = SheafHom_{𝒪_X}(a^*Ω_{Y/Bb}, 𝒞_{X/X'})` is a sheaf of
`𝒪_X`-modules, so it lives on the small étale site of the subspace `X`.  Before the action of the
one on the other can be an action of sheaves the two have to be put on one site.

This file does that, for `X ⊂ X'` a thickening: base change of étale scheme charts along the
inclusion exhibits the small étale site of `X'` as a dense subsite of the small étale site of
`X`, so the two sheaf topoi are equivalent — this is the chart form of [Stacks Project, Tag
05ZM], `AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` — and the acting sheaf is
carried across it to a sheaf of sets on the small étale site of `X'`, where the sheaf of lifts
already is.

The transport is a *restriction*: the inverse of the comparison equivalence of a dense subsite
is `CategoryTheory.Functor.sheafPushforwardContinuous`, so the sections of the transported
acting sheaf over an étale chart `U'` of `X'` are the sections of the acting sheaf over the
base-changed chart `X ×_{X'} U'`, on the nose
(`AlgebraicGeometry.Space.liftActionSheafTransport_obj`).  Nothing is lost, because the
comparison is an equivalence: the transported sheaf is carried back to the acting sheaf by
`AlgebraicGeometry.Space.liftActionSheafTransportIso`.

The payoff is that the chart-level results now describe the transported sheaf's sections at a
chart *of `X'`*, which is the chart the sheaf of lifts is indexed by.  A chart presentation `P`
of the lifting problem at `U'` presents the chart `X ×_{X'} U'`, which is the base change of
`U'` up to the canonical isomorphism of two pullbacks of one cospan
(`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`); through it the
identification of the chart-level sections of the acting sheaf with the acting group,
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`, becomes
`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv`, and the action is
simply transitive on the sections of the sheaf of lifts over `U'` with both sides read at `U'`.

## Main definitions

* `AlgebraicGeometry.Space.liftActionSheafTypeSheaf`: the sheaf of sets underlying the acting
  sheaf of [Stacks Project, Tag 061D] on the small étale site of `X`.
* `AlgebraicGeometry.Space.liftActionSheafTransport`: **the acting sheaf, transported to the
  small étale site of `X'`**, where the sheaf of lifts lives.
* `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`: the chart of `X` presented by
  a chart presentation at `U'` is the base change of `U'` along the inclusion of `X`.
* `AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv`: the sections of
  the transported acting sheaf over `U'` are the acting group of a chart presentation at `U'`.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection`: the action of a
  section of the transported acting sheaf over `U'` on the sheaf of lifts over `U'`.

## Main results

* `AlgebraicGeometry.Space.liftActionSheafTransport_obj` and
  `AlgebraicGeometry.Space.liftActionSheafTransport_map`: the sections of the transported acting
  sheaf over an étale chart of `X'`, and its restriction maps, are those of the acting sheaf over
  the base-changed chart of `X`, by `rfl`;
  `AlgebraicGeometry.Space.liftActionSheafTransport_map_apply` exhibits each restriction map as
  the map underlying a morphism of abelian groups.
* `AlgebraicGeometry.Space.liftActionSheafTransportIso`: the comparison equivalence carries the
  transported sheaf back to the acting sheaf, so the transport loses nothing.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective`: **the
  sections of the transported acting sheaf over `U'` act simply transitively on the sections of
  the sheaf of lifts over `U'`**, granted that the two charts of `q` of the presentation are
  étale — freeness and transitivity being those of
  `AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection`.  The bijection itself
  is `AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv`.
* `AlgebraicGeometry.Space.exists_chartLiftPresentation_transportSimplyTransitive_ofArrows`: **on
  a covering family of étale charts of `X'` the sections of the transported acting sheaf act
  simply transitively on the sections of the sheaf of lifts**, and a given section of the sheaf
  of lifts is the base point there.  This is
  `AlgebraicGeometry.Space.exists_chartLiftPresentation_simplyTransitive_ofArrows` with the
  acting group replaced by the sections of a sheaf on the same site as the sheaf of lifts.

## Implementation notes

The acting sheaf is a sheaf of modules whose module universe is `u + 1` — a section over an
étale chart is a morphism of modules on a slice of the small étale site, whose objects are in
`Type (u + 1)` — which is exactly the universe at which
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening` is stated, so no universe
bookkeeping is needed.  The sheaf of sets underlying a sheaf of modules is obtained by
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` at the forgetful functor of abelian groups;
the additive structure of the sections survives the transport untouched, since by
`AlgebraicGeometry.Space.liftActionSheafTransport_obj` they are the same type, and the instance
recording that is stated beside it.

A free-standing `map_add` for the transport's restriction maps is not stated here, but it is
**not** a budget wall: it is `AlgebraicGeometry.Space.liftActionSheafTransport_map_add`
(`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftTorsorSheaves.lean`).  The *statement*
at the transported spelling of the sections elaborates cheaply, for instance on its own as the
hypothesis of a `True`-valued theorem.  What exceeds the 200,000 heartbeats is the term-mode
proof `map_add φ.hom θ η`, because unifying an application of `Functor.map` of a `Type`-valued
functor with an application of `FunLike.coe` drives `whnf` through the transport and the
forgetful functor.  `AlgebraicGeometry.Space.liftActionSheafTransport_map_apply`, which is
`rfl` and free, is what avoids that: rewriting with it puts all three occurrences in the
`FunLike` spelling before `map_add` is applied, so additivity is indeed one rewrite away at
whatever spelling the consumer is working in.

The thickening hypothesis is used only for the equivalence of topoi.  The results about a chart
presentation use the first-order hypothesis only through the presentation itself, which carries
its own square-zero chart datum, so `AlgebraicGeometry.Space.liftActionSheafTransport` and
everything about a given presentation ask for `AlgebraicGeometry.Space.IsThickening` alone; only
the covering statement, which must produce presentations, asks for
`AlgebraicGeometry.Space.IsFirstOrderThickening`, and it derives the thickening hypothesis from
it by `AlgebraicGeometry.Space.IsNthOrderThickening.isThickening` rather than carrying both.

The comparison of the presented chart with the base-changed chart is the canonical isomorphism
of two pullbacks of one cospan, `CategoryTheory.IsPullback.isoIsPullback`, taken in presheaves
and pulled back along the Yoneda embedding, which is fully faithful; the triangle over `X` that
makes it an isomorphism of charts is `CategoryTheory.IsPullback.isoIsPullback_hom_fst`.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 061D]'s two sheaves are registered on
`AlgebraicGeometry.Space.liftsSubfunctor` and `AlgebraicGeometry.Space.liftActionSheaf`, and
[Stacks Project, Tag 05ZM] on the equivalence of topoi used here; moving one of the two sheaves
across that equivalence asserts neither tag.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

/-! ### The acting sheaf on the small étale site of the ambient space -/

/-- The sheaf of sets underlying the acting sheaf of [Stacks Project, Tag 061D] on the small
étale site of the closed subspace `X ⊆ X'`: the acting sheaf is a sheaf of `𝒪_X`-modules, and
forgetting the module structure of its sections leaves a sheaf of sets, because the forgetful
functor of abelian groups preserves limits. -/
def liftActionSheafTypeSheaf (Z : ClosedSubspaces C S hS X'.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    Sheaf (SmallEtale.topology C S hS Z.1.toFunctor) (Type (u + 1)) :=
  ⟨(liftActionSheaf C S hS Z q a).val.presheaf ⋙ forget AddCommGrpCat.{u + 1},
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ (liftActionSheaf C S hS Z q a).isSheaf⟩

/-- **The acting sheaf of [Stacks Project, Tag 061D], transported to the small étale site of the
ambient space `X'`**, which is where the sheaf of lifts
`AlgebraicGeometry.Space.liftsSubfunctor` lives.

For a thickening `X ⊂ X'` the two small étale sheaf topoi are equivalent, by the chart form of
[Stacks Project, Tag 05ZM] `AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening`, and
this is the image of the acting sheaf under the inverse of that equivalence — concretely,
restriction along base change of étale charts, so its sections over a chart `U'` of `X'` are the
sections of the acting sheaf over `X ×_{X'} U'`. -/
def liftActionSheafTransport (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    Sheaf (SmallEtale.topology C S hS X'.1) (Type (u + 1)) :=
  (smallEtaleSheafEquiv_of_isThickening C S hS hG).inverse.obj
    (liftActionSheafTypeSheaf C S hS Z q a)

/-- **The sections of the transported acting sheaf over an étale chart `U'` of `X'` are the
sections of the acting sheaf over the base-changed chart `X ×_{X'} U'`.**  The inverse of the
comparison equivalence of a dense subsite is restriction along the functor of sites, so this
holds on the nose. -/
theorem liftActionSheafTransport_obj (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U' : SmallEtale C S hS X'.1) :
    (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U') =
      (liftActionSheaf C S hS Z q a).val.obj
        (op ((thickeningChartBaseChange C S hS hG).obj U')) :=
  rfl

/-- **The restriction maps of the transported acting sheaf are those of the acting sheaf along
base change of charts**, again on the nose. -/
theorem liftActionSheafTransport_map (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U') :
    (liftActionSheafTransport C S hS Z hG q a).obj.map m.op =
      (liftActionSheafTypeSheaf C S hS Z q a).obj.map
        ((thickeningChartBaseChange C S hS hG).map m).op :=
  rfl

/-- The sections of the transported acting sheaf over an étale chart of `X'` are an abelian
group: by `AlgebraicGeometry.Space.liftActionSheafTransport_obj` they are the sections of a sheaf
of modules over the base-changed chart. -/
instance liftActionSheafTransport_addCommGroup (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U' : SmallEtale C S hS X'.1) :
    AddCommGroup ((liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :=
  inferInstanceAs (AddCommGroup ((liftActionSheaf C S hS Z q a).val.presheaf.obj
    (op ((thickeningChartBaseChange C S hS hG).obj U'))))

/-- **A restriction map of the transported acting sheaf is the additive map underlying a
restriction map of the acting sheaf**, so the transport is a sheaf of abelian groups on the small
étale site of `X'` and not merely a sheaf of sets: additivity of each restriction map is
`map_add` of the morphism of abelian groups on the right. -/
theorem liftActionSheafTransport_map_apply (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (x : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map m.op x =
      ((liftActionSheaf C S hS Z q a).val.presheaf.map
        ((thickeningChartBaseChange C S hS hG).map m).op).hom x :=
  rfl

/-- **The transport loses nothing.**  The comparison equivalence of the two small étale sheaf
topoi of a thickening carries the transported acting sheaf back to the acting sheaf, because it
is an equivalence. -/
def liftActionSheafTransportIso (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    (smallEtaleSheafEquiv_of_isThickening C S hS hG).functor.obj
        (liftActionSheafTransport C S hS Z hG q a) ≅
      liftActionSheafTypeSheaf C S hS Z q a :=
  (smallEtaleSheafEquiv_of_isThickening C S hS hG).counitIso.app
    (liftActionSheafTypeSheaf C S hS Z q a)

/-! ### The chart-level sections of the transported sheaf -/

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The chart of `X` presented by a chart presentation at `U'` is the base change of `U'` along
the inclusion of `X`.**  Both are étale charts of `X` fitting into a cartesian square over the
chart morphism of `U'` and the inclusion of `X`, so they are canonically isomorphic over `X`.

The isomorphism is `CategoryTheory.IsPullback.isoIsPullback` taken in presheaves and pulled back
along the Yoneda embedding, which is fully faithful; the triangle over `X` making it an
isomorphism of charts is `CategoryTheory.IsPullback.isoIsPullback_hom_fst`. -/
def subEtaleChartIso (hG : IsThickening C S hS X' Z.1) :
    P.subEtaleChart ≅ (thickeningChartBaseChange C S hS hG).obj U' :=
  (IsEtaleChart C S hS Z.1.toFunctor).isoMk
    (CostructuredArrow.isoMk
      (yoneda.preimageIso (P.isPullback.flip.isoIsPullback _ _
        ((isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.isPullback U'.1.hom)))
      (by
        rw [Functor.preimageIso_hom, Functor.map_preimage]
        exact IsPullback.isoIsPullback_hom_fst _ _ _ _))

/-- **The sections of the transported acting sheaf over `U'` are the acting group of a chart
presentation at `U'`**, granted that the two charts of `q` are étale.

This is the chart-level identification
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`, which reads the acting sheaf
at the chart of `X` that the presentation presents, moved to the base-changed chart along
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`, which is where the transported
sheaf reads it.  Both sides are now indexed by the chart `U'` of `X'`, the chart over which the
sheaf of lifts is read. -/
def transportActionSectionEquiv (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U') ≃ P.ActionSection :=
  (((liftActionSheafTypeSheaf C S hS Z q a).obj.mapIso
    (Iso.op (P.subEtaleChartIso C S hS hG))).toEquiv).trans
      (actionSectionEquiv C S hS P hw hv)

/-- **The action of a section of the transported acting sheaf over `U'` on the sheaf of lifts
over `U'`**: the translate of the presented lift by the acting group element the section
corresponds to.  Both the acting sheaf and the sheaf of lifts are now read at the same chart
`U'` of the small étale site of `X'`. -/
def translateTransportSection (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U') :=
  P.translateActionSection (P.transportActionSectionEquiv C S hS hG hw hv θ)

/-- **The sections of the transported acting sheaf over `U'` act simply transitively on the
sections of the sheaf of lifts over `U'`**, granted that the two charts of `q` are étale: the
action is free by
`AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection_injective` and transitive
by `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateActionSection_eq_of_isEtale`,
and the chart-level identification of the acting group with the transported sheaf's sections is
a bijection. -/
theorem translateTransportSection_bijective (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    Function.Bijective (P.translateTransportSection C S hS hG hw hv) :=
  ⟨(P.translateActionSection_injective hw).comp
      (P.transportActionSectionEquiv C S hS hG hw hv).injective,
    fun β => by
      obtain ⟨θ, hθ⟩ := P.exists_translateActionSection_eq_of_isEtale hw hv β
      exact ⟨(P.transportActionSectionEquiv C S hS hG hw hv).symm θ,
        by rw [translateTransportSection, Equiv.apply_symm_apply, hθ]⟩⟩

/-- **The transported acting sheaf and the sheaf of lifts have the same sections over `U'`**,
granted that the two charts of `q` of a presentation at `U'` are étale: the bijection is the
action on the presented lift. -/
def transportLiftsEquiv (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U') ≃
      (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U') :=
  Equiv.ofBijective _ (P.translateTransportSection_bijective C S hS hG hw hv)

/-- The bijection of `AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv` is the
action of the transported acting sheaf's sections on the presented lift. -/
theorem transportLiftsEquiv_apply (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    P.transportLiftsEquiv C S hS hG hw hv θ =
      P.translateTransportSection C S hS hG hw hv θ :=
  rfl

end ChartLiftPresentation

/-! ### The two sheaves on a covering family of charts of the ambient space -/

/-- **On a covering family of étale charts of `X'` the sections of the transported acting sheaf
act simply transitively on the sections of the sheaf of lifts, and a given section of the sheaf
of lifts is the base point there.**

This is `AlgebraicGeometry.Space.exists_chartLiftPresentation_simplyTransitive_ofArrows` with the
acting group of each presentation replaced by the sections of a sheaf living on the small étale
site of `X'`, the site of the sheaf of lifts — so the statement no longer mentions two sites.
A consumer that wants the bijection itself gets it from
`AlgebraicGeometry.Space.ChartLiftPresentation.transportLiftsEquiv`.

The covering family is part of the statement and not a weakness of it: a presentation needs an
affine chart of `Y`, which receives only part of the given chart of `X'`.

The thickening hypothesis the transport needs is derived from the first-order hypothesis by
`AlgebraicGeometry.Space.IsNthOrderThickening.isThickening`, so nothing beyond
`AlgebraicGeometry.Space.IsFirstOrderThickening` is assumed. -/
theorem exists_chartLiftPresentation_transportSimplyTransitive_ofArrows (p : X' ⟶ Bb)
    (q : Y ⟶ Bb) (Z : ClosedSubspaces C S hS X'.1)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (hX : IsFirstOrderThickening C S hS X' Z.1) (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    ∃ (I : Type u) (W : I → SmallEtale C S hS X'.1) (r : ∀ i, W i ⟶ U')
      (P : ∀ i, ChartLiftPresentation C S hS p q a.hom (W i))
      (hw : ∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).tgtChart)
      (hv : ∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).bseChart),
      (∀ i, (P i).liftSection =
        (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i).op β) ∧
      (∀ i, Function.Bijective
        ((P i).translateTransportSection C S hS hX.isThickening (hw i) (hv i))) ∧
      Sieve.ofArrows W r ∈ SmallEtale.topology C S hS X'.1 U' := by
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX U' β
  exact ⟨I, W, r, P, hw, hv, hval,
    fun i => (P i).translateTransportSection_bijective C S hS hX.isThickening (hw i) (hv i),
    hcov⟩

end AlgebraicGeometry.Space

end
