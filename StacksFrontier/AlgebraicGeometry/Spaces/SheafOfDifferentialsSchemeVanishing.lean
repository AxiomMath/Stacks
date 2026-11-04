module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedSheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalDerivationVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vanishing of the differentials of a morphism of schemes, read on algebraic spaces

Let `ψ : U ⟶ V` be a morphism of the big fppf category over a scheme `S` and let
`schemeSpaceMap ψ : schemeSpace U ⟶ schemeSpace V` be the morphism of algebraic spaces it
induces.  Two sheaves of differentials of `ψ` are then in play: the scheme-level `Ω_{U/V}` of
Stacks 01US, a module on the small Zariski site of `U`, and the spaces-level `Ω_{U/V}` of
Stacks 04CT, a module on the small étale site of `schemeSpace U`.  Stacks 04CS identifies the
second with the module associated to the first.  What is proved here is the half of the
vanishing consequence of that identification which needs no surjectivity of the comparison
map: if the scheme-level sheaf is a zero object then so is the spaces-level one.

The argument runs on sections, as the source's does.  By
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_iff` the spaces-level sheaf vanishes
exactly when its universal derivation annihilates every regular function on every étale chart
`W` of `schemeSpace U`, and that sheaf being a sheaf it is enough to see this on an open cover
of the scheme underlying `W`.  Cover that scheme by affine opens `A` each lying over an affine
open `V'` of `V`.  On such an `A` the universal derivation is an honest derivation of `Γ(A)`
relative to `Γ(V')`: additivity and the Leibniz rule are part of being a derivation, and that
it kills the functions pulled back from `V'` is
`AlgebraicGeometry.Space.universalDerivation_d_chartDiagramPullback`, the vanishing clause of
Stacks 04CT read on the square of étale charts that `A` and `V'` cut out.  Such a derivation
factors through the Kähler differentials of `Γ(V') ⟶ Γ(A)`, which are the sections over `A` of
the scheme-level sheaf of differentials of the restricted morphism by Stacks 01UT; and that
sheaf vanishes because `Ω_{U/V}` does and both restrictions are étale, by Stacks 04BX.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramDerivation`: the universal derivation of a morphism of
  algebraic spaces, read over the source chart of a chart diagram as a derivation of the
  regular functions there relative to the regular functions on the target chart.
* `AlgebraicGeometry.Space.openBaseChart`: a Zariski open of a scheme over `S`, read as an
  étale chart of the algebraic space that scheme defines.
* `AlgebraicGeometry.Space.openChartDiagram`: the chart diagram over `schemeSpaceMap ψ` cut out
  by an open of an étale chart of the source lying over an open of the target.

## Main results

* `AlgebraicGeometry.Space.universalDerivation_d_chartDiagramPullback`: the universal derivation
  of a morphism of algebraic spaces kills the functions pulled back along a chart diagram.
* `AlgebraicGeometry.Space.universalDerivation_d_eq_zero_of_subsingleton`: it therefore kills
  every function on the source chart of a chart diagram whose Kähler differentials vanish.
* `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_schemeSpaceMap_of_isZero`: if the sheaf
  of relative differentials of a morphism of schemes over `S` is a zero object, so is the sheaf
  of differentials of the induced morphism of algebraic spaces.
* `Space.isZero_modulePullback_sheafOfDifferentials_of_isZero_relativeDifferentials`:
  the same read through Stacks 04CU on a square of étale charts, which is the direction of the
  chart comparison of Stacks 04G9 that this supplies.
* `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_mp`: consequently the chart
  comparison `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison` is no longer an
  independent assumption — it follows from its `mp` half alone,
  `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparisonMp`, which is proved downstream
  as `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparisonMp` — and
  `AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials_of_mp` is
  Stacks 04G9 granted only that half.

## What is not proved here

The converse implication — that a vanishing spaces-level `Ω` forces the scheme-level one to
vanish — is not proved in this file; it is
`Space.isZero_relativeDifferentials_of_isZero_sheafOfDifferentials_schemeSpaceMap`
in `StacksFrontier/AlgebraicGeometry/Spaces/SchemeSpaceDifferentialsVanishing.lean`, which proves
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparisonMp` from it.  It is not a
consequence of anything in this file.  It needs
Stacks 04CS as an identification rather than as a comparison map: a derivation
`𝒪_{U_étale} ⟶ (Ω_{U/V})^a` together with the fact that `(Ω_{U/V})^a` is generated by its
image, so that the comparison is surjective.  Only the comparison map
`AlgebraicGeometry.SmallEtale.differentialsComparison` is available, and a zero target says
nothing about a source mapping into it.

Note also that no global-sections shortcut is possible: the statement for global sections alone
is false.  The disjoint union `⨆_{n ∈ ℕ} Spec ℚ ⟶ Spec ℚ` is étale, so its sheaf of relative
differentials vanishes, while `Ω[ℚ^ℕ⁄ℚ] ≠ 0`.  This is why the Kähler differentials are taken
on affine opens and not at the top open.

## Implementation notes

The square of étale charts is handed to the vanishing clause of Stacks 04CT through
`AlgebraicGeometry.Space.indexOfChartDiagram`, which turns a chart diagram of Stacks 03G3 into
an object of the index category over which the direct image of the structure sheaf is a limit;
`AlgebraicGeometry.Space.chartPullback_indexOfChartDiagram` records that the pullback of
functions along that index is the pullback along the diagram's own morphism of schemes, which
is what makes the vanishing clause applicable to a concrete regular function.

The vertical morphism of the chart diagram is `AlgebraicGeometry.Space.openSubMap`, the
restriction of a morphism of the site to an open of its source over an open of its target;
`AlgebraicGeometry.Space.toScheme_map_openSubMap` identifies the underlying morphism of schemes
with `Scheme.Hom.resLE`, which is the shape
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_resLE` speaks about.

The opens of an étale chart are taken in the `AlgebraicGeometry.Space.openChart` spelling,
because it is for that one that
`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology` supplies the covering sieve.

Only the Kähler differentials of the ring map `Γ(V') ⟶ Γ(A)` are needed, not the sheaf-level
universal property, so Stacks 01UT enters in the form
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso` at the
two top opens of the affine schemes `A` and `V'`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  small Zariski and small étale differentials of a morphism of schemes.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), its restriction to a
  square of étale charts.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), chart diagrams.
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US), the sheaf of relative
  differentials of a morphism of schemes.
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT), its sections on an
  affine open over an affine open.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the differentials of
  an étale localization of source and base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.AffineDifferentialsIso

universe u

/-- A derivation with values in a module over a ring map whose Kähler differentials are a
subsingleton vanishes identically: it factors through those Kähler differentials. -/
theorem ModuleCat.Derivation.d_eq_zero_of_subsingleton_kaehlerDifferential
    {A C : CommRingCat.{u}} {φ : A ⟶ C} {M : ModuleCat.{u} C} (D : M.Derivation φ)
    (hK : Subsingleton (CommRingCat.KaehlerDifferential φ)) (b : C) : D.d b = 0 := by
  rw [← D.desc_d b, hK.elim (CommRingCat.KaehlerDifferential.d b) 0, map_zero]

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **The universal derivation kills the functions pulled back along a chart diagram.** -/
theorem universalDerivation_d_chartDiagramPullback (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : (structureRingSheaf B S hS Y).obj.obj (op d.V)) :
    (universalDerivation B S hS f).d (chartDiagramPullback B S hS f d b) = 0 := by
  rw [← chartPullback_indexOfChartDiagram B S hS f d b]
  exact universalDerivation_d_chartPullback B S hS f d.V (indexOfChartDiagram B S hS f d) b

/-- The universal derivation of `f`, read on the sections over the source chart of a chart
diagram, as a derivation relative to the induced map of rings of functions. -/
noncomputable def chartDiagramDerivation (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ((sheafOfDifferentials B S hS f).val.obj (op d.U)).Derivation
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op) :=
  ModuleCat.Derivation.mk (fun a ↦ (universalDerivation B S hS f).d a)
    (fun a b ↦ map_add _ a b)
    (fun a b ↦ (universalDerivation B S hS f).d_mul a b)
    (fun r ↦ universalDerivation_d_chartDiagramPullback B S hS f d r)

/-- If the Kähler differentials of the ring map of a chart diagram vanish, then the universal
derivation kills every regular function on the diagram's source chart. -/
theorem universalDerivation_d_eq_zero_of_subsingleton (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hK : Subsingleton (CommRingCat.KaehlerDifferential
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op)))
    (a : (structureRingSheaf B S hS X).obj.obj (op d.U)) :
    (universalDerivation B S hS f).d a = 0 :=
  (chartDiagramDerivation B S hS f d).d_eq_zero_of_subsingleton_kaehlerDifferential hK a

section Representable

variable {U V : BigFppfOver B S hS}

/-- **The Kähler differentials of an affine piece of an étale chart vanish.**  If the sheaf of
relative differentials of `ψ` is a zero object, `t` is étale, `q` factors as `t` followed by the
morphism of schemes of `ψ`, and `A`, `V'` are affine opens with `A` over `V'`, then the Kähler
differentials of the induced map of rings of functions vanish: the restricted morphism has a
zero sheaf of relative differentials by Stacks 04BX, and its sections on `A` are those Kähler
differentials by Stacks 01UT. -/
theorem subsingleton_kaehlerDifferential_resLE (ψ : U ⟶ V)
    (hz : IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)))
    {T : Scheme.{u}} (t : T ⟶ (BigFppfOver.toScheme B S hS).obj U) [Etale t]
    (q : T ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hq : q = t ≫ (BigFppfOver.toScheme B S hS).map ψ)
    (A : T.Opens) (hA : IsAffineOpen A)
    (V' : ((BigFppfOver.toScheme B S hS).obj V).Opens) (hV' : IsAffineOpen V')
    (hAV' : A ≤ q ⁻¹ᵁ V') :
    Subsingleton (CommRingCat.KaehlerDifferential
      (Scheme.Γ.map (q.resLE V' A hAV').op)) := by
  subst hq
  set ψ' := (BigFppfOver.toScheme B S hS).map ψ
  set g := (t ≫ ψ').resLE V' A hAV'
  have hcomm : (A.ι ≫ t) ≫ ψ' = g ≫ V'.ι := by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
  have : IsIso (Scheme.Hom.relativeDifferentialsMap (A.ι ≫ t) ψ' g V'.ι hcomm) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_etale _ _ _ _ hcomm
  have hzq : IsZero (Scheme.Hom.relativeDifferentials g) :=
    (Functor.map_isZero (Scheme.Modules.pullback (A.ι ≫ t)) hz).of_iso
      (asIso (Scheme.Hom.relativeDifferentialsMap (A.ι ≫ t) ψ' g V'.ι hcomm)).symm
  have : IsAffine (A : Scheme.{u}) := hA
  have : IsAffine (V' : Scheme.{u}) := hV'
  have hsec : IsZero ((Scheme.Hom.relativeDifferentials g).val.obj (op ⊤)) :=
    Functor.map_isZero (PresheafOfModules.evaluation (A : Scheme.{u}).ringCatSheaf.obj (op ⊤))
      (Functor.map_isZero (Scheme.Modules.toPresheafOfModules (A : Scheme.{u})) hzq)
  obtain ⟨e, -, -⟩ := existsUnique_affineDifferentialsIso g
    (isAffineOpen_top (A : Scheme.{u})) le_top (isAffineOpen_top (V' : Scheme.{u}))
  have hker := ModuleCat.isZero_iff_subsingleton.mp (hsec.of_iso e.symm)
  have happ : Scheme.Γ.map g.op = g.appLE ⊤ ⊤ le_top :=
    (Scheme.Γ_map_op _).trans (Scheme.Hom.appLE_eq_app _).symm
  rw [happ]
  exact hker

/-- A Zariski open of the scheme underlying an object of the big fppf site, read as an étale
chart of the algebraic space that object defines: the inclusion of an open subscheme is étale,
and that is étale as a morphism of presheaves. -/
noncomputable def openBaseChart (V : BigFppfOver B S hS)
    (V' : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    SmallEtale B S hS (schemeSpace V).1 :=
  ⟨CostructuredArrow.mk (yoneda.map (openSubHom V V')),
    (presheaf_yoneda_map_etale_iff B S hS (openSubHom V V')).2
      (etale_toScheme_map_openSubHom B S hS V V')⟩

/-- The chart diagram cut out by an open `A` of an étale chart of the source lying over an open
`V'` of the base.

The vertical morphism of schemes over the base is the restriction
`AlgebraicGeometry.Space.openSubMap` of `w ≫ ψ` to the two opens, so that
`AlgebraicGeometry.Space.toScheme_map_openSubMap` identifies the induced map of rings of
functions with the one `AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_resLE` speaks
about. -/
noncomputable def openChartDiagram (ψ : U ⟶ V)
    (W : SmallEtale B S hS (schemeSpace U).1)
    (w : (SmallEtale.toOver B S hS (schemeSpace U).1).obj W ⟶ U)
    (hw : yoneda.map w = W.1.hom)
    (A : (chartScheme W).Opens)
    (V' : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hAV' : A ≤ (BigFppfOver.toScheme B S hS).map (w ≫ ψ) ⁻¹ᵁ V') :
    ChartDiagram B S hS (schemeSpace U).1 (schemeSpace V).1 (schemeSpaceMap ψ).hom where
  U := openChart B S hS (schemeSpace U).1 W A
  V := openBaseChart B S hS V V'
  g := openSubMap (w ≫ ψ) A V' hAV'
  comm := by
    have hkey := congrArg yoneda.map (openSubMap_comp_openSubHom (w ≫ ψ) A V' hAV')
    simp only [CategoryTheory.Functor.map_comp] at hkey
    have hkey2 : yoneda.map (openSubMap (w ≫ ψ) A V' hAV') ≫ yoneda.map (openSubHom V V') =
        yoneda.map (openSubHom ((SmallEtale.toOver B S hS (schemeSpace U).1).obj W) A) ≫
          W.1.hom ≫ yoneda.map ψ := by
      rw [← hw]
      exact hkey
    exact (Category.assoc _ _ _).trans hkey2.symm

/-- The map of rings of functions of `AlgebraicGeometry.Space.openChartDiagram` is the
restriction of `w ≫ ψ` to the two opens. -/
theorem toScheme_openChartDiagram_g (ψ : U ⟶ V)
    (W : SmallEtale B S hS (schemeSpace U).1)
    (w : (SmallEtale.toOver B S hS (schemeSpace U).1).obj W ⟶ U)
    (hw : yoneda.map w = W.1.hom)
    (A : (chartScheme W).Opens)
    (V' : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hAV' : A ≤ (BigFppfOver.toScheme B S hS).map (w ≫ ψ) ⁻¹ᵁ V') :
    (BigFppfOver.toScheme B S hS).map (openChartDiagram B S hS ψ W w hw A V' hAV').g =
      ((BigFppfOver.toScheme B S hS).map (w ≫ ψ)).resLE V' A hAV' :=
  toScheme_map_openSubMap (w ≫ ψ) A V' hAV'

/-- **One half of the vanishing shadow of Stacks 04CS.**  If the sheaf of relative
differentials of a morphism of schemes over `S` is a zero object, then so is the sheaf of
differentials of the induced morphism of algebraic spaces.

By `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_iff` it is enough that the universal
derivation annihilate every regular function on every étale chart `W` of `schemeSpace U`, and
`Ω` being a sheaf it is enough to see this on an open cover of the scheme underlying `W`.  Cover
that scheme by affine opens each lying over an affine open of `V`; on such a piece the universal
derivation is an honest derivation relative to the regular functions downstairs, so it factors
through the Kähler differentials of the induced ring map, and those vanish by
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_resLE`. -/
theorem isZero_sheafOfDifferentials_schemeSpaceMap_of_isZero (ψ : U ⟶ V)
    (hz : IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))) :
    IsZero (sheafOfDifferentials B S hS (schemeSpaceMap ψ)) := by
  rw [isZero_sheafOfDifferentials_iff]
  intro Wop a
  obtain ⟨W, rfl⟩ : ∃ W, op W = Wop := ⟨Wop.unop, rfl⟩
  have hw : yoneda.map (yoneda.preimage W.1.hom) = W.1.hom :=
    CategoryTheory.Functor.map_preimage _ _
  set w := yoneda.preimage W.1.hom
  have : Etale ((BigFppfOver.toScheme B S hS).map w) :=
    (presheaf_yoneda_map_etale_iff B S hS w).1 (by rw [hw]; exact W.property)
  choose A V' hxA hAV' using Scheme.exists_affineOpen_le_preimage_affineOpen
    ((BigFppfOver.toScheme B S hS).map (w ≫ ψ))
  have hcovTop : ⨆ x : chartScheme W, (A x).1 = ⊤ :=
    top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxA x⟩
  have hcov := ofArrows_openChartInclusion_mem_topology B S hS (schemeSpace U).1 W
    (fun x ↦ (A x).1) hcovTop
  have hpiece : ∀ x : chartScheme W,
      (universalDerivation B S hS (schemeSpaceMap ψ)).d
        ((structureRingSheaf B S hS (schemeSpace U)).obj.map
          (openChartInclusion B S hS (schemeSpace U).1 W (A x).1).op a) = 0 := by
    intro x
    refine universalDerivation_d_eq_zero_of_subsingleton B S hS (schemeSpaceMap ψ)
      (openChartDiagram B S hS ψ W w hw (A x).1 (V' x).1 (hAV' x)) ?_ _
    rw [toScheme_openChartDiagram_g]
    exact subsingleton_kaehlerDifferential_resLE B S hS ψ hz
      ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map (w ≫ ψ))
      ((BigFppfOver.toScheme B S hS).map_comp w ψ)
      (A x).1 (A x).2 (V' x).1 (V' x).2 (hAV' x)
  refine (sheafOfDifferentials B S hS (schemeSpaceMap ψ)).isSheaf.isSeparated _ _ hcov _ 0 ?_
  rintro Z g ⟨Z', h, fi, ⟨x⟩, rfl⟩
  have hres := ((universalDerivation B S hS (schemeSpaceMap ψ)).d_map
    (openChartInclusion B S hS (schemeSpace U).1 W (A x).1).op a).symm.trans (hpiece x)
  refine Eq.trans ?_ (map_zero _).symm
  erw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hres]
  exact map_zero _

/-- **The vanishing half of the chart comparison, in the direction Stacks 04CS supplies
here.**  In a commutative square of étale charts over a morphism `f : X ⟶ Y` of algebraic
spaces whose horizontal arrow is the morphism of schemes `ψ`, the restriction of `Ω_{X/Y}` to
the chart is a zero object as soon as the scheme-level sheaf of relative differentials of `ψ`
is: the restriction is the spaces-level `Ω_{U/V}` by Stacks 04CU, and that vanishes by
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_schemeSpaceMap_of_isZero`. -/
theorem isZero_modulePullback_sheafOfDifferentials_of_isZero_relativeDifferentials
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : schemeSpace U ⟶ X) (b : schemeSpace V ⟶ Y)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = schemeSpaceMap ψ ≫ b)
    (hz : IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))) :
    IsZero ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS f)) :=
  (isZero_sheafOfDifferentials_schemeSpaceMap_of_isZero B S hS ψ hz).of_iso
    (sheafOfDifferentialsEtaleLocalizationIso B S hS f a (schemeSpaceMap ψ) b ha hb hcomm)

/-- **Stacks 04G9, the forward implication, with no hypothesis.**  A formally unramified
morphism `f : X ⟶ Y` of algebraic spaces over `S` has a zero sheaf of differentials.

This is `AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials` in the one
direction whose input is available: that theorem assumes the chart comparison
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`, an equivalence, and the forward
implication spends only its `mpr` half, which is
`Space.isZero_modulePullback_sheafOfDifferentials_of_isZero_relativeDifferentials`.

The argument is the source's: formal unramifiedness of `f` gives, by Stacks 04G8, a commuting
square of étale scheme charts with surjective source chart whose scheme morphism `ψ` is formally
unramified; that is `Ω_ψ = 0` by Stacks 02H9; the chart comparison turns it into the vanishing of
`Ω_{X/Y}` restricted to the chart, and
`AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_chart` — the faithfulness of pullback
along a surjective étale chart — into the vanishing of `Ω_{X/Y}` itself. -/
@[ega "IV 17.2.1" "necessity"]
theorem isZero_sheafOfDifferentials_of_formallyUnramified (f : X ⟶ Y)
    (hf : FormallyUnramified f.hom) : IsZero (sheafOfDifferentials B S hS f) := by
  obtain ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, -, hdiag, hψ⟩ :=
    (formallyUnramified_iff_surjectiveEtaleChart B S hS X.2 Y.2 f.hom).mp hf
  refine isZero_of_isZero_modulePullback_chart B S hS U (ObjectProperty.homMk a)
    (isEtale_of_presheaf_etale B S hS haEtale) haSurj ?_
  exact isZero_modulePullback_sheafOfDifferentials_of_isZero_relativeDifferentials B S hS f ψ
    (ObjectProperty.homMk a) (ObjectProperty.homMk b)
    (isEtale_of_presheaf_etale B S hS haEtale) (isEtale_of_presheaf_etale B S hS hbEtale)
    (ObjectProperty.hom_ext _ hdiag.symm)
    ((Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials _).mp hψ)

/-- **The chart comparison of Stacks 04G9 in the direction this development can prove.**  The
`mpr` half of `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`, stated for every
commuting square of étale scheme charts, without the surjectivity the full comparison asks for:
the vanishing of the scheme-level differentials of the square's scheme morphism gives the
vanishing of the restriction of `Ω_{X/Y}` to the chart.

The converse half is not available; see the "What is not proved" section of this module. -/
theorem sheafOfDifferentialsChartComparison_mpr (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hdiag : yoneda.map ψ ≫ b = a ≫ f.hom)
    (hz : IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))) :
    IsZero ((modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj (sheafOfDifferentials B S hS f)) :=
  isZero_modulePullback_sheafOfDifferentials_of_isZero_relativeDifferentials B S hS f ψ
    (ObjectProperty.homMk a) (ObjectProperty.homMk b)
    (isEtale_of_presheaf_etale B S hS ha) (isEtale_of_presheaf_etale B S hS hb)
    (ObjectProperty.hom_ext _ hdiag.symm) hz

/-- **The half of the chart comparison of Stacks 04G9 that is still open**, on its own: on a
surjective étale chart square, the vanishing of the restriction of `Ω_{X/Y}` to the chart gives
the vanishing of the scheme-level sheaf of relative differentials of the square's scheme
morphism.

This is the `mp` half of `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`, and
after `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_mpr` it is all of that
equivalence that is not proved.  It is the direction the comparison map of Stacks 04CS cannot
give: that map lands *in* the small-étale differentials, so a zero target says nothing about its
source without surjectivity.  Anything that used to assume the equivalence should assume this
instead, and recover the equivalence by
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_mp`. -/
abbrev SheafOfDifferentialsChartComparisonMp (f : X ⟶ Y) : Prop :=
  ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1) (ψ : U ⟶ V),
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    yoneda.map ψ ≫ b = a ≫ f.hom →
    IsZero ((modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj (sheafOfDifferentials B S hS f)) →
    IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))

/-- **The chart comparison of Stacks 04G9 from its open half alone.**  The equivalence
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison` follows from
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparisonMp`: the `mpr` half is
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_mpr`, which is proved, and which
needs neither the surjectivity of the chart nor the hypothesis. -/
theorem sheafOfDifferentialsChartComparison_of_mp (f : X ⟶ Y)
    (hmp : SheafOfDifferentialsChartComparisonMp B S hS f) :
    SheafOfDifferentialsChartComparison B S hS f :=
  fun U V a b ψ ha hb hs hdiag =>
    ⟨hmp U V a b ψ ha hb hs hdiag,
      sheafOfDifferentialsChartComparison_mpr B S hS f U V a b ψ ha hb hdiag⟩

/-- **Stacks 04G9, granted only the open half of the chart comparison.**  This is
`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials` with the `mpr` half
of its hypothesis discharged by
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_mpr`, so that what is assumed is
exactly what remains open.  It carries no registration, the registered form of Stacks 04G9 being
the one in `StacksFrontier/AlgebraicGeometry/Spaces/FormallyUnramifiedSheafOfDifferentials.lean`.

Its forward implication needs nothing at all and is
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`. -/
theorem formallyUnramified_iff_isZero_sheafOfDifferentials_of_mp (f : X ⟶ Y)
    (hmp : SheafOfDifferentialsChartComparisonMp B S hS f) :
    FormallyUnramified f.hom ↔ IsZero (sheafOfDifferentials B S hS f) :=
  formallyUnramified_iff_isZero_sheafOfDifferentials B S hS f

end Representable

end AlgebraicGeometry.Space

end
