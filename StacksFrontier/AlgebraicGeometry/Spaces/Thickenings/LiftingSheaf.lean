module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# Lifting a morphism of algebraic spaces along a thickening

Let `B`, `X'` and `Y` be algebraic spaces over a scheme `S`, let `X ⊆ X'` be a subspace and let
`a : X ⟶ Y` be a morphism over `B`.  For an étale scheme chart `U'` of `X'` a *lift* of `a` over
`U'` is a morphism `a' : U' ⟶ Y` over `B` whose restriction to `X ×_{X'} U'` is the restriction
of `a`.  This file shows that the lifts form a sheaf of sets on the small étale site of `X'`,
constructs the sheaf of `𝒪_X`-module homomorphisms `a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` which acts on it, and
shows that the conormal module of the trivial thickening `Y ⊆ Y` vanishes, so that the
obstruction map out of its inverse image is zero.

## Main definitions

* `AlgebraicGeometry.Space.IsChartLift` is the lifting condition on a morphism from an étale chart.
* `AlgebraicGeometry.Space.liftsSubfunctor` is the sheaf of lifts, as a subfunctor of the
  restriction of `Y` to the small étale site of `X'`.
* `AlgebraicGeometry.Space.liftActionSheaf` is `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})`.
* `AlgebraicGeometry.Space.liftActionSheafChart` and
  `AlgebraicGeometry.Space.liftActionSheafAmbient` are that sheaf, as a sheaf of abelian
  groups, read on the small étale site and on the spaces-étale site of the ambient space `X'`,
  and `AlgebraicGeometry.Space.liftActionPresheafAmbient` is the underlying presheaf of the
  second — a presheaf of abelian groups on the spaces-étale site of `X'`, which is the shape
  the acting object `Θ` of Stacks 061C takes.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isContinuous_toOver_fppfTopology`: the canonical functor
  from the small étale site of a presheaf to the big fppf site of `S` is continuous, so an
  algebraic space restricts to a sheaf on the small étale site
  (`AlgebraicGeometry.Space.SmallEtale.isSheaf_comp_toOver`).
* `AlgebraicGeometry.Space.isSheaf_liftsSubfunctor`: the lifts form a sheaf of sets.
* `AlgebraicGeometry.Space.isChartLift_iff_restrict`: the lifting condition reads as the equality
  of the two restrictions to `X ×_{X'} U'`.
* `AlgebraicGeometry.Space.isZero_conormalModule_top`: the conormal module `𝒞_{Y/Y}` of an
  algebraic space in itself vanishes, and
  `AlgebraicGeometry.Space.eq_zero_of_isZero_conormalModule_top`: every morphism of
  `𝒪_X`-modules out of its inverse image is therefore zero.

## Implementation notes

The fibre product `X ×_{X'} U'` is `CategoryTheory.Subfunctor.preimage` of `X` along the chart
map, so no fibre product of algebraic spaces is formed; `isChartLift_iff_restrict` is the
comparison with that spelling, and the definition itself is the pointwise form, which says that
`a'` and `a` agree on every point of the chart lying in `X`.  The pointwise form is what makes the
restriction maps of the subfunctor and the sheaf condition direct.

The sheaf condition is the one of the source: morphisms into an algebraic space satisfy étale
descent.  Concretely, `CategoryTheory.Subfunctor.isSheaf_iff` reduces it to the assertion that a
section of `Y` over a chart which is a lift locally on a covering sieve is a lift, and each of
the two clauses of the lifting condition is then an equality of sections of a sheaf which holds
locally: for the clause over `B` on the chart itself, and for the clause along `X` on the test
object, whose covering sieve is the pullback of the pushforward of the given one.

No hypothesis on the subspace `X ⊆ X'` is used for the sheaf, so none is imposed; in the intended
application `X ⊂ X'` is a first order thickening.

The vanishing of the conormal module of `Y` in itself is the degenerate case of the conormal
module of a closed subspace: the defining ideal of the top closed subspace is zero on every étale
chart, because the inclusion of the top subspace is an isomorphism and therefore admits a
retraction.

## The transport to the ambient space, and what it does not need

`liftActionSheaf` is built on the small étale site of the closed subspace `X`, while the sheaf
of lifts it acts on lives over `X'`.  The two transport steps that close that gap are carried
out here and use nothing this library lacks.  The first is restriction along base change of
étale scheme charts, which is Equation Stacks 05ZL in the only form a transport of sheaves
uses; it is available at a thickening of *arbitrary* order, because base change exhibits the
small étale site of `X'` as a dense subsite of that of `X`
(`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`).  The equation as the
source states it, base change as an equivalence of the two *sites*, is neither used here nor
available at arbitrary order —
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean`
records that the equivalence of sites is proved only at first order.  The second step is the
Stacks 03G1 comparison `AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, taken at
sheaves of abelian groups.

**No part of Stacks 04CO is needed for this.**  One might expect that making the acting sheaf a
*functor* on the spaces-étale site of `X'` needs the conormal module to be functorial in the
étale source, which is the clause of Stacks 04CO that
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` leaves open.  It
does not: the functoriality in the object of the site is the functoriality of the transported
*sheaf*, and the conormal module `𝒞_{X/X'}` is formed once, at `X ⊂ X'` itself, inside
`liftActionSheaf`.  Functoriality of the conormal module would be needed only to define the
acting object pointwise, as `U' ↦ SheafHom(a_{U}^*Ω_{Y/B}, 𝒞_{U/U'})` with a separate conormal
module for each `U'`, and that is not how it is defined here.

## What this does not do

The *action* of `liftActionSheaf` on the lifts is not constructed here as an action of sheaves
(over an étale scheme chart it is, as recorded below).  Both inputs it needs are
available: what is left is the assembly of the second one, as the
rest of this section sets out.

The twisting of the structure map of a morphism by a derivation *is* carried, and it is
[Stacks Project, Tag 04D0] in full:
`AlgebraicGeometry.Space.existsUnique_hom_restrictedLiftDifferenceHom_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftSimpleTransitivity.lean` produces, from a
morphism `c₀ : X' ⟶ Y'` over the base agreeing with `a` on `X` and an `𝒪_X`-module map
`θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}`, the unique second such morphism whose difference from `c₀` is
`θ`.  It takes no stand-in: existence is
`AlgebraicGeometry.Space.exists_hom_of_movedThickeningLift` and uniqueness is
`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`, so neither
[Stacks Project, Tag 04KL] nor the identification of the small étale topoi is used.  That
statement is the simple transitivity of [Stacks Project, Tag 061C] at one object of the site,
with the acting group the *global* `𝒪_X`-linear maps.

What is still missing is reading those linear maps as the *sections* of `liftActionSheaf` over
an étale chart of `X'`.  The chart-level transport of the acting sheaf is
`AlgebraicGeometry.Space.chartAbelianSheafOnAmbient` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftActionSheafOnAmbient.lean`, whose
sections over a chart `V` are, by
`AlgebraicGeometry.Space.chartAbelianSheafOnAmbient_obj_obj` — an equality, not a comparison —
the sections of `liftActionSheaf` over the base-changed chart
`AlgebraicGeometry.Space.thickeningChartBaseChange` at `V`; and those sections are, by the
definition of `AlgebraicGeometry.Space.smallEtaleInternalHom`, morphisms of presheaves of
modules on the *slice* of the site there.  Identifying them with the global linear maps of the
chart read as an algebraic space needs the conormal module and the differentials of that chart.

**Both halves of that are available.**  For the conormal module it is the canonical-map
spelling, `AlgebraicGeometry.Space.isIso_conormalMap_of_isEtale` with
`AlgebraicGeometry.Space.conormalMap_comp`.  For the differentials — once recorded here as not
stated, which was wrong — it is the comparison of inverse images along a composite,
[Stacks Project, Tag 03LU], at the sheaf of differentials: writing `π : X ×_{X'} V ⟶ X` for the
projection of the base-changed chart,
`(AlgebraicGeometry.Space.modulePullbackCompIso B S hS π a).app`
`(AlgebraicGeometry.Space.sheafOfDifferentials B S hS q)` is
`π^*(a^*Ω_{Y/B}) ≅ (π ≫ a)^*Ω_{Y/B}`, and the right-hand side is the domain of the chart's own
`AlgebraicGeometry.Space.restrictedLiftDifferenceHom`.  The module being restricted is a
pullback of a module on the undeformed target, so no étaleness of `π` enters and the comparison
is Tag 03LU's and nothing more — unlike the conormal side, where `𝒞_{X_V/V}` is not a pullback
of a module on a fixed space and the étale clause of [Stacks Project, Tag 04CO] is needed.  No
declaration is added for the instance: a specialization of Tag 03LU's comparison would be a
second name for it, just as `AlgebraicGeometry.Space.conormalMap_comp` is not restated.

So what is missing is the **assembly** of the two halves across the slice, not an ingredient of
it.  The identification of the small étale site of `X` with that of `X'` is in any case
available for a thickening, as
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening`.

The *action* of `liftActionSheaf` on the lifts is constructed **over an étale scheme chart**,
in `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`: over a chart
presentation of the lifting problem the translate of a lift by a section of the acting sheaf is
`AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection`, it is again a section of
`liftsSubfunctor`, and the action is free and transitive on the lifts the chart presents.  The
translation itself is `Stacks.Smooth.addDerivationHom`, the reading back of the translated
structure map is `Spec` and not Stacks 04KL, the well-definedness is Stacks 04AL
(`AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq`), and the identification of the
acting group with the sections of the acting sheaf at the chart is
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`.

**The comparison of the acting group at a chart with the sections of `liftActionSheaf` there is
complete**, so what remains before this is an action of `liftActionSheaf` on
`liftsSubfunctor` as sheaves is the glueing alone.  The comparison is
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`): granted that
the two charts of `q` are étale, which is what Stacks 04CU needs, the sections of
`liftActionSheaf` over the étale chart of `X` presented by a chart presentation are exactly the
`Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ RingHom.ker i^♯` that the action acts by.  An earlier
version of this paragraph said the source comparison needed Stacks 0GN7 on the slice at the
chart under Stacks 03DT; neither is needed — the small étale half of 0GN7 is unconditional over
an arbitrary scheme, and the slice is matched with the small étale site of the chart *space* by
Stacks 04M0 (`AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv`) together with
Equation 03LW.

What is still missing, named precisely:

* The chartwise actions are not glued: the action is defined against a chart presentation, and
  a lift over an arbitrary chart factors through an affine chart of `Y` only locally.  An earlier
  version of this paragraph said that nothing in the tree restricts a chart presentation along a
  morphism of charts and that neither the action nor the identification of the acting group has a
  compatibility with restriction.  The first two are no longer true:
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` restricts a presentation along a
  morphism of étale charts of `X'` (and exists over every affine étale chart of a first-order
  thickening), and
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateActionSection` is the
  compatibility of the action with the restriction maps of the sheaf of lifts.  What is still
  owed is the naturality in the chart of
  `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`, stated as
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
  with its decomposition into four compatibilities and a citation for each; granted it, the
  naturality clause an action of sheaves asks for is
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `map_translateActionSection_actionSectionEquiv`.

The identification of the small étale site of `X` — where `liftActionSheaf` lives — with that of
`X'` — where the sheaf of lifts lives — is also
available.  It is carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafSiteTransport`: for a thickening
the chart form of Stacks 05ZM,
`AlgebraicGeometry.Space.smallEtaleSheafEquiv_of_isThickening`, carries the acting sheaf to a
sheaf `AlgebraicGeometry.Space.liftActionSheafTransport` on the small étale site of `X'`, whose
sections over a chart `U'` are the acting sheaf's sections over `X ×_{X'} U'`, so that
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv` reads at a chart of `X'` and
the action is simply transitive on the sections of `liftsSubfunctor` there, with both sides on
one site.

The factorization of the lift through an affine chart of `Y` that
`AlgebraicGeometry.Space.exists_chartLiftPresentation` asks for is **no longer missing**; it is
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftFactorization`, in both the forms the
action needs.  A given section of `liftsSubfunctor` over an étale chart is the presented lift of
a chart presentation on a *covering family* of affine étale charts,
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows` — the covering family
is unavoidable, since an affine chart of `Y` receives only part of the chart — and over a single
presentation whose chart of `Y` is étale *every* section of `liftsSubfunctor` factors through that
chart, `AlgebraicGeometry.Space.ChartLiftPresentation.exists_hom_tgtChart_app_eq`, by formal
étaleness of the chart: the section and the presented lift agree on the closed subscheme, both
lifting `a` there.  So the two transitivity statements hold for every section over the chart
(`AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateActionSection_eq_of_isEtale`), and
the action is simply transitive on a covering family,
`AlgebraicGeometry.Space.exists_chartLiftPresentation_simplyTransitive_ofArrows`.

The abstract principal-homogeneity the action would satisfy is unconditional, as
`Deformation.ToposThickening.LiftDiagram.translate_existsUnique` (Stacks 08UG).

Quasi-coherence of `liftActionSheaf`, which is what the vanishing of Stacks 061J — step (II) of
the proof of Stacks 04AM — consumes, is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafQuasicoherent`, granted finite
local freeness of `a^*Ω_{Y/B}`.

The acting object built here is also not connected to the action of Stacks 061C:
`liftsSubfunctor` is the sheaf of lifts into an *undeformed* target `Y`, whereas the action of
Stacks 061C is on `AlgebraicGeometry.Space.liftSubfunctor`, the lifts into a deformed target
`Y ⊂ Y'`, and nothing in this development relates the two sheaves.  What
`liftActionPresheafAmbient` supplies is a concrete value for the acting object `Θ` of
`AlgebraicGeometry.Space.LiftDerivationAction`, not the action datum itself.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 05ZL](https://stacks.math.columbia.edu/tag/05ZL)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the differentials half
  of the chart reading.
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), its conormal half.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Sites

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- The functor pushforward of a presieve and the image of that presieve generate the same sieve:
the image is contained in the pushforward, and the pushforward is contained in the sieve generated
by the image. -/
theorem generate_functorPushforward_eq_generate_map (G : D ⥤ E) {X : D} (P : Presieve X) :
    Sieve.generate (P.functorPushforward G) = Sieve.generate (P.map G) := by
  rw [← Sieve.arrows_generate_map_eq_functorPushforward]
  exact Sieve.generate_sieve _

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Restriction of a sheaf on the big fppf site to the small étale site -/

namespace SmallEtale

variable (F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)

/-- A covering family of étale charts of `F` has, as a family of objects of the big fppf site of
`S`, a sieve generating an fppf covering sieve: a selected étale covering family is in particular
a selected fppf covering family. -/
theorem precoverage_le_comap_fppfTopology :
    precoverage C S hS F ≤
      (BigFppfOver.topology C S hS).toPrecoverage.comap (toOver C S hS F) := by
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    Stacks.Sites.generate_functorPushforward_eq_generate_map]
  refine Precoverage.generate_mem_toGrothendieck ⟨E.map (toSchemes C S hS F), ?_, hE.1⟩
  simp only [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  rfl

/-- The canonical functor from the small étale site of `F` to the big fppf site of `S` is
continuous: it preserves fibre products of étale charts and carries covering families of charts to
fppf covering families. -/
instance isContinuous_toOver_fppfTopology :
    (toOver C S hS F).IsContinuous (topology C S hS F) (BigFppfOver.topology C S hS) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (precoverage_le_comap_fppfTopology C S hS F)

/-- Restriction along the canonical functor to the big fppf site of `S` carries a sheaf of types
on that site to a sheaf on the small étale site of `F`.  Applied to an algebraic space over `S` it
says that the morphisms from the étale charts of `F` into an algebraic space form a sheaf. -/
theorem isSheaf_comp_toOver {G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology C S hS) G) :
    Presheaf.IsSheaf (topology C S hS F) ((toOver C S hS F).op ⋙ G) :=
  (toOver C S hS F).op_comp_isSheaf_of_isSheaf _ _ G hG

end SmallEtale

/-! ### The lifting condition -/

variable {B X' Y : AlgebraicSpaces C S hS}

/-- A morphism `a' : U' ⟶ Y` from an étale scheme chart `U'` of `X'` *lifts* `a : X ⟶ Y` along the
subspace `X ⊆ X'` when it lies over `B` and agrees with `a` on every point of the chart which lies
in `X`, that is on `X ×_{X'} U'`. -/
def IsChartLift (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1)
    (U' : SmallEtale C S hS X'.1)
    (a' : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1) : Prop :=
  a' ≫ q.hom = U'.1.hom ≫ p.hom ∧
    ∀ (W : BigFppfOver C S hS) (k : W ⟶ (SmallEtale.toOver C S hS X'.1).obj U')
      (t : yoneda.obj W ⟶ X.toFunctor), yoneda.map k ≫ U'.1.hom = t ≫ X.ι →
      yoneda.map k ≫ a' = t ≫ a

/-- Being a lift is preserved by restriction to a smaller étale chart. -/
theorem IsChartLift.restrict {p : X' ⟶ B} {q : Y ⟶ B} {X : Subfunctor X'.1} {a : X.toFunctor ⟶ Y.1}
    {U' V' : SmallEtale C S hS X'.1}
    {a' : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1}
    (h : IsChartLift C S hS p q a U' a') (m : V' ⟶ U') :
    IsChartLift C S hS p q a V' (yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ a') := by
  have hw : yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ U'.1.hom = V'.1.hom :=
    CostructuredArrow.w _
  refine ⟨?_, fun W k t hkt => ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, hw]
  · have hk : yoneda.map (k ≫ (SmallEtale.toOver C S hS X'.1).map m) ≫ U'.1.hom = t ≫ X.ι := by
      rw [Functor.map_comp, Category.assoc, hw, hkt]
    have := h.2 W (k ≫ (SmallEtale.toOver C S hS X'.1).map m) t hk
    rwa [Functor.map_comp, Category.assoc] at this

/-- The lifting condition, in terms of the fibre product `X ×_{X'} U'`: a morphism out of a chart
is a lift exactly when it lies over `B` and its restriction to the preimage of `X` in the chart
agrees with the restriction of `a` there. -/
theorem isChartLift_iff_restrict (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1)
    (a' : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1) :
    IsChartLift C S hS p q a U' a' ↔
      a' ≫ q.hom = U'.1.hom ≫ p.hom ∧
        (X.preimage U'.1.hom).ι ≫ a' = X.fromPreimage U'.1.hom ≫ a := by
  refine and_congr_right' ⟨fun h => ?_, fun h W k t hkt => ?_⟩
  · ext Z x
    obtain ⟨Z⟩ := Z
    have hx : U'.1.hom.app (op Z) x.1 ∈ X.obj (op Z) := x.2
    set y : X.toFunctor.obj (op Z) := ⟨U'.1.hom.app (op Z) x.1, hx⟩
    have hty : yonedaEquiv (yonedaEquiv.symm y) = y := Equiv.apply_symm_apply _ _
    have hcompat : yoneda.map x.1 ≫ U'.1.hom = yonedaEquiv.symm y ≫ X.ι := by
      refine yonedaEquiv.injective ?_
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, hty]
      rfl
    have key := congrArg yonedaEquiv (h Z x.1 _ hcompat)
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, hty] at key
    exact key
  · refine yonedaEquiv.injective ?_
    have hval : U'.1.hom.app (op W) k = (yonedaEquiv t).1 := by
      have hh := congrArg yonedaEquiv hkt
      rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_comp] at hh
    have hk : k ∈ (X.preimage U'.1.hom).obj (op W) := by
      change U'.1.hom.app (op W) k ∈ X.obj (op W)
      rw [hval]
      exact (yonedaEquiv t).2
    have hxy := ConcreteCategory.congr_hom (congr_app h (op W))
      (⟨k, hk⟩ : (X.preimage U'.1.hom).toFunctor.obj (op W))
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_comp]
    refine hxy.trans ?_
    exact congrArg (ConcreteCategory.hom (a.app (op W))) (Subtype.ext hval)

/-! ### The sheaf of lifts -/

/-- **Stacks 061D.** The sheaf of lifts of `a : X ⟶ Y` along the subspace `X ⊆ X'`, in the case
where the target is not deformed: the subfunctor of the restriction of `Y` to the small étale site
of `X'` whose sections over a chart `U'` are the morphisms `a' : U' ⟶ Y` over `B` whose
restriction to `X ×_{X'} U'` is the restriction of `a`. -/
@[stacks 061D "the rule `U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}`"]
def liftsSubfunctor (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1) :
    Subfunctor ((SmallEtale.toOver C S hS X'.1).op ⋙ Y.1) where
  obj U' := {α | IsChartLift C S hS p q a U'.unop (yonedaEquiv.symm α)}
  map {U' V'} m := by
    intro α hα
    change IsChartLift C S hS p q a V'.unop
      (yonedaEquiv.symm (Y.1.map ((SmallEtale.toOver C S hS X'.1).map m.unop).op α))
    rw [← yonedaEquiv_symm_naturality_left]
    exact hα.restrict C S hS m.unop

/-- **Stacks 061D.** The lifts form a sheaf of sets on the small étale site of `X'`: morphisms
into an algebraic space satisfy étale descent, and both clauses of the lifting condition are
local. -/
@[stacks 061D "the rule of the remark is a sheaf of sets"]
theorem isSheaf_liftsSubfunctor (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) :
    Presheaf.IsSheaf (SmallEtale.topology C S hS X'.1)
      (liftsSubfunctor C S hS p q a).toFunctor := by
  have hYbig : Presheaf.IsSheaf (BigFppfOver.topology C S hS) Y.1 := Y.2.isSheaf
  have hY := SmallEtale.isSheaf_comp_toOver C S hS X'.1 hYbig
  have hB := SmallEtale.isSheaf_comp_toOver C S hS X'.1 B.2.isSheaf
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hY)]
  intro U' α hα
  have key : ∀ {V' : SmallEtale C S hS X'.1} (m : V' ⟶ U'.unop),
      ((liftsSubfunctor C S hS p q a).sieveOfSection α).arrows m →
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ U'.unop.1.hom = V'.1.hom ∧
        IsChartLift C S hS p q a V'
          (yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ yonedaEquiv.symm α) :=
    fun m hm => ⟨CostructuredArrow.w _, by rw [yonedaEquiv_symm_naturality_left]; exact hm⟩
  refine ⟨?_, ?_⟩
  · refine yonedaEquiv.injective ?_
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 hB _ hα).isSeparatedFor.ext ?_
    intro V' m hm
    obtain ⟨hw, hlift⟩ := key m hm
    change B.1.map ((SmallEtale.toOver C S hS X'.1).map m).op
        (yonedaEquiv (yonedaEquiv.symm α ≫ q.hom)) =
      B.1.map ((SmallEtale.toOver C S hS X'.1).map m).op
        (yonedaEquiv (U'.unop.1.hom ≫ p.hom))
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg _ ?_
    calc yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ yonedaEquiv.symm α ≫ q.hom
        = (yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ yonedaEquiv.symm α) ≫ q.hom := by
          rw [Category.assoc]
      _ = V'.1.hom ≫ p.hom := hlift.1
      _ = (yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ U'.unop.1.hom) ≫ p.hom := by
          rw [hw]
      _ = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ U'.unop.1.hom ≫ p.hom := by
          rw [Category.assoc]
  · intro W k t hkt
    refine yonedaEquiv.injective ?_
    have hR' := (CoverPreserving.of_isContinuous (SmallEtale.toOver C S hS X'.1)
      (SmallEtale.topology C S hS X'.1) (BigFppfOver.topology C S hS)).cover_preserve hα
    have hW := (BigFppfOver.topology C S hS).pullback_stable k hR'
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 hYbig _ hW).isSeparatedFor.ext ?_
    intro W₁ g hg
    obtain ⟨V', m, h, hm, hgk⟩ := hg
    obtain ⟨hw, hlift⟩ := key m hm
    have hkey := hlift.2 W₁ h (yoneda.map g ≫ t) <|
      calc yoneda.map h ≫ V'.1.hom
          = yoneda.map h ≫ yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫
              U'.unop.1.hom := by rw [hw]
        _ = yoneda.map (h ≫ (SmallEtale.toOver C S hS X'.1).map m) ≫ U'.unop.1.hom := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (g ≫ k) ≫ U'.unop.1.hom := by rw [hgk]
        _ = yoneda.map g ≫ yoneda.map k ≫ U'.unop.1.hom := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map g ≫ t ≫ X.ι := by rw [hkt]
        _ = (yoneda.map g ≫ t) ≫ X.ι := by rw [Category.assoc]
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg _ ?_
    calc yoneda.map g ≫ yoneda.map k ≫ yonedaEquiv.symm α
        = yoneda.map (g ≫ k) ≫ yonedaEquiv.symm α := by rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (h ≫ (SmallEtale.toOver C S hS X'.1).map m) ≫ yonedaEquiv.symm α := by
          rw [hgk]
      _ = yoneda.map h ≫ yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫
            yonedaEquiv.symm α := by rw [Functor.map_comp, Category.assoc]
      _ = (yoneda.map g ≫ t) ≫ a := hkey
      _ = yoneda.map g ≫ t ≫ a := by rw [Category.assoc]

/-! ### The conormal module of the trivial thickening -/

/-- **The conormal module `𝒞_{Y/Y}` of an algebraic space in itself vanishes.**  The inclusion of
the top closed subspace is an isomorphism, so it admits a retraction and its defining ideal is
zero on every étale chart; the conormal module is the inverse image of the associated sheaf of
ideals, and the inverse image of a zero module is zero. -/
theorem isZero_conormalModule_top (Y : AlgebraicSpaces C S hS) :
    IsZero (conormalModule C S hS Y ⟨⊤, isClosedSubspace_top C S hS Y⟩) := by
  have hret : (ObjectProperty.homMk (inv (⊤ : Subfunctor Y.1).ι) :
      Y ⟶ (⟨(⊤ : Subfunctor Y.1).toFunctor, (isClosedSubspace_top C S hS Y).1⟩ :
        AlgebraicSpaces C S hS)) ≫ ObjectProperty.homMk (⊤ : Subfunctor Y.1).ι = 𝟙 Y :=
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)
  have hbot := definingIdealAt_eq_bot_of_retraction C S hS Y
    ⟨⊤, isClosedSubspace_top C S hS Y⟩ _ hret
  have hidealZero : IsZero
      (definingIdealSheaf C S hS Y ⟨⊤, isClosedSubspace_top C S hS Y⟩).toSheafOfModules := by
    refine isZero_of_subsingleton_val_obj C S hS Y _ fun U => ?_
    change Subsingleton
      ((definingIdealSheaf C S hS Y ⟨⊤, isClosedSubspace_top C S hS Y⟩).obj U)
    have hsec : ∀ z : ((definingIdealSheaf C S hS Y
        ⟨⊤, isClosedSubspace_top C S hS Y⟩).obj U), z.1 = 0 := fun z => (hbot U).le z.2
    exact ⟨fun x y => Subtype.ext ((hsec x).trans (hsec y).symm)⟩
  rw [conormalModule_eq]
  have := modulePullback_additive
    (subspaceInclusion C S hS Y ⟨⊤, isClosedSubspace_top C S hS Y⟩)
  exact Functor.map_isZero _ hidealZero

/-- **Stacks 061D.** In the case where the target is not deformed the map `A` of the general
lifting problem is always zero: it is a morphism of `𝒪_X`-modules out of the inverse image of the
conormal module `𝒞_{Y/Y}`, which vanishes. -/
@[stacks 061D "the map `A` is always zero"]
theorem eq_zero_of_isZero_conormalModule_top (Z : ClosedSubspaces C S hS X'.1)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨(⊤ : Subfunctor Y.1).toFunctor, (isClosedSubspace_top C S hS Y).1⟩ :
        AlgebraicSpaces C S hS))
    (A : (modulePullback C S hS a).obj
        (conormalModule C S hS Y ⟨⊤, isClosedSubspace_top C S hS Y⟩) ⟶
      conormalModule C S hS X' Z) :
    A = 0 := by
  have := modulePullback_additive a
  exact (Functor.map_isZero _ (isZero_conormalModule_top C S hS Y)).eq_of_src A 0

/-! ### The sheaf acting on the lifts -/

/-- **Stacks 061D.** The sheaf acting on the lifts: the internal hom
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of `𝒪_X`-modules on the small étale site of the closed
subspace `X ⊆ X'`, for `a : X ⟶ Y` over `B`.  The sheaf of lifts it acts on is
`AlgebraicGeometry.Space.liftsSubfunctor` taken at the underlying morphism of presheaves
`a.hom`. -/
@[stacks 061D "the acting sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})`"]
noncomputable def liftActionSheaf (Z : ClosedSubspaces C S hS X'.1) (q : Y ⟶ B)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    Modules.{u, u + 1} C S hS Z.1.toFunctor Z.2.1 :=
  smallEtaleInternalHom C S hS Z.1.toFunctor Z.2.1
    ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
    (conormalModule C S hS X' Z)

/-! ### The acting sheaf read on the spaces-étale site of the ambient space -/

variable {G : Subfunctor X'.1}

/-- **The acting sheaf of Stacks 061D, read on the small étale site of the ambient space.**
`AlgebraicGeometry.Space.liftActionSheaf` is built on the small étale site of the closed
subspace `X` of a thickening `X ⊂ X'`, while the sheaf of lifts it acts on lives over `X'`.
This is its underlying sheaf of abelian groups restricted along base change of étale scheme
charts, `AlgebraicGeometry.Space.thickeningChartBaseChange`, so that its sections over a chart
`U'` of `X'` are the sections of the original over `X ×_{X'} U'`.

This is Equation Stacks 05ZL in the only form the transport of a sheaf uses, and it is
available at a thickening of arbitrary order because base change of charts exhibits the small
étale site of `X'` as a dense subsite of that of `X`,
`AlgebraicGeometry.Space.thickeningChartBaseChange_isDenseSubsite`.  The equation as the source
states it — base change as an equivalence of the two *sites* — is not used and is not available
at arbitrary order;
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEquivalence.lean`
records what of it is proved. -/
noncomputable def liftActionSheafChart (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    Sheaf (SmallEtale.topology C S hS X'.1) AddCommGrpCat.{u + 1} :=
  letI := thickeningChartBaseChange_isDenseSubsite C S hS hG
  ((thickeningChartBaseChange C S hS hG).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology C S hS X'.1)
        (SmallEtale.topology C S hS (IsThickening.space C S hS hG).1)).obj
    ((SheafOfModules.toSheaf _).obj (liftActionSheaf C S hS ⟨G, hG.1⟩ q a))

/-- The sections of `AlgebraicGeometry.Space.liftActionSheafChart` over a chart `U'` of the
ambient space are, on the nose, the sections of `AlgebraicGeometry.Space.liftActionSheaf` over
the base-changed chart `X ×_{X'} U'`: restriction along a functor changes no sections. -/
theorem liftActionSheafChart_val_obj (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) (U' : SmallEtale C S hS X'.1) :
    (liftActionSheafChart C S hS hG q a).obj.obj (op U') =
      AddCommGrpCat.of ((liftActionSheaf C S hS ⟨G, hG.1⟩ q a).val.obj
        (op ((thickeningChartBaseChange C S hS hG).obj U'))) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the sheaf pushforward along the comparison functor is heavy
/-- **The acting sheaf of Stacks 061D, read on the spaces-étale site of the ambient space.**
For a thickening `X ⊂ X'` of algebraic spaces and `a : X ⟶ Y` over `B`, the sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` transported to a sheaf of abelian groups on the
spaces-étale site of `X'`, which is where the action of Stacks 061C is indexed.

The second leg of the transport is the Stacks 03G1 comparison
`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, which identifies sheaves on the
small étale site of scheme charts of `X'` with sheaves on its spaces-étale site; the inverse of
that equivalence carries `AlgebraicGeometry.Space.liftActionSheafChart` across.

Both legs are instantiated at `AddCommGrpCat.{u + 1}`, the sheaves of abelian groups, rather
than at sheaves of sets as in
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening` or at sheaves of rings as in
`AlgebraicGeometry.Space.smallEtaleRingSheafEquiv_of_isThickening`.  Nothing beyond those two
identifications enters: the underlying abelian group sheaf of the module sheaf is taken by
`SheafOfModules.toSheaf`, and the restriction maps are those of the transported sheaf. -/
noncomputable def liftActionSheafAmbient (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    Sheaf (SpacesEtale.topology C S hS X') AddCommGrpCat.{u + 1} :=
  ((comparisonFunctor C S hS X').sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology C S hS X'.1) (SpacesEtale.topology C S hS X')).inv.obj
    (liftActionSheafChart C S hS hG q a)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the sheaf pushforward along the comparison functor is heavy
/-- The restriction of `AlgebraicGeometry.Space.liftActionSheafAmbient` to the small étale site
of scheme charts of `X'` is `AlgebraicGeometry.Space.liftActionSheafChart`, so the sections of
the acting sheaf at a chart are computed by
`AlgebraicGeometry.Space.liftActionSheafChart_val_obj`.  This is the counit of the Stacks 03G1
equivalence, the only comparison datum the second leg of the transport introduces. -/
noncomputable def liftActionSheafAmbientChartIso (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    ((comparisonFunctor C S hS X').sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology C S hS X'.1) (SpacesEtale.topology C S hS X')).obj
      (liftActionSheafAmbient C S hS hG q a) ≅ liftActionSheafChart C S hS hG q a :=
  ((comparisonFunctor C S hS X').sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology C S hS X'.1)
      (SpacesEtale.topology C S hS X')).asEquivalence.counitIso.app _

/-- **The acting presheaf of Stacks 061C at the acting sheaf of Stacks 061D.** The presheaf of
abelian groups on the spaces-étale site of the ambient space `X'` underlying
`AlgebraicGeometry.Space.liftActionSheafAmbient`.

This is a presheaf of exactly the shape that the action datum of Stacks 061C takes as its
acting object, so it is a concrete value for the `Θ` which
`AlgebraicGeometry.Space.LiftDerivationAction` leaves abstract.  Supplying it needs no
functoriality of the conormal module in the étale source, that is no part of Stacks 04CO: the
functoriality in the object of the site is the functoriality of the transported *sheaf*, and
the conormal module `𝒞_{X/X'}` is formed once, at `X ⊂ X'` itself, inside
`AlgebraicGeometry.Space.liftActionSheaf`. -/
noncomputable abbrev liftActionPresheafAmbient (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    (SpacesEtale C S hS X')ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (liftActionSheafAmbient C S hS hG q a).obj

/-- The acting presheaf on the spaces-étale site of the ambient space is a sheaf: it is the
underlying presheaf of a sheaf by construction. -/
theorem isSheaf_liftActionPresheafAmbient (hG : IsThickening C S hS X' G) (q : Y ⟶ B)
    (a : IsThickening.space C S hS hG ⟶ Y) :
    Presheaf.IsSheaf (SpacesEtale.topology C S hS X')
      (liftActionPresheafAmbient C S hS hG q a) :=
  (liftActionSheafAmbient C S hS hG q a).property

end AlgebraicGeometry.Space

end
