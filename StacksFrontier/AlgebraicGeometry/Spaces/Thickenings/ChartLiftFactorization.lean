module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction

/-!
# Every lift over a chart factors through the chart of the target

Let `X ⊆ X'` be a subspace of an algebraic space over a scheme `S`, let `a : X ⟶ Y` be a
morphism over `B` and let `q : Y ⟶ B`.  The action of the chart derivations on the sheaf of
lifts of `a` is defined against a chart presentation
`AlgebraicGeometry.Space.ChartLiftPresentation` of the lifting problem, whose last field is a
factorization of the presented lift through an affine chart of `Y`, and both transitivity
statements of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` take such a
factorization of the *given* section as a hypothesis.  This file supplies both factorizations.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.exists_hom_tgtChart_app_eq`: **every section of
  the sheaf of lifts over the chart factors through the chart of `Y` of a presentation**, granted
  that that chart is étale.  No refinement of the chart is needed, and this is the whole reason
  the factorization carried by the two transitivity statements is not a restriction on them: the
  given section and the presented lift agree on the closed subscheme of the chart, because both
  lift `a` there, so formal étaleness of the chart of `Y` — [Stacks Project, Tag 04AL] — extends
  the factorization of the presented lift over the closed subscheme to a factorization of the
  given section over the whole chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateSection_eq` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateActionSection_eq`,
  the hypothesis-free forms
  `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateSection_eq_of_isEtale` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateActionSection_eq_of_isEtale`:
  **the action is transitive on all the sections of the sheaf of lifts over the chart**, granted
  that the two charts of `q` are étale — not only on those which factor through the chart of `Y`.
* `AlgebraicGeometry.Space.exists_affine_chartSquare_hom_ofArrows`: **a morphism out of an étale
  scheme chart factors through an affine chart square of `q` on a covering family of affine étale
  charts**.  This is the factorization that a *single* chart does not admit: an affine chart of
  `Y` receives only part of the given chart, so the covering family is part of the statement and
  not a weakening of it.  No lifting condition is used, and the source may be an étale chart of
  an arbitrary presheaf.
* `AlgebraicGeometry.Space.exists_chartLiftPresentation_ofArrows` and
  `AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows`: **every section of
  the sheaf of lifts over an étale chart is the presented lift of a chart presentation on a
  covering family of affine étale charts**, with both charts of `q` affine and étale.
* `AlgebraicGeometry.Space.exists_chartLiftPresentation_simplyTransitive_ofArrows`: the two
  halves together — **on a covering family of affine étale charts the action of the sections of
  the acting sheaf is simply transitive on all the sections of the sheaf of lifts**, and a given
  section is the presented lift of the member's presentation.

## Implementation notes

The covering family is produced exactly as [Stacks Project, Tag 03G2]
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`) produces its own, but for a tower
of three morphisms rather than a square, and for the given section rather than for the structure
morphism of the chart: an atlas of `B` is lifted along `q` to an atlas of `Y` over it
([Stacks Project, Tag 02X1], `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`),
that atlas is lifted along the given section to a surjective étale cover of the chart — the chart
is a *representable* algebraic space, [Stacks Project, Tag 025Z], which is what lets the section
play the part of a morphism of algebraic spaces there — and the resulting tower is restricted to
affine opens of its three terms.  The affine opens of a scheme form a basis, so the restrictions
cover; the square of charts of `q` they carry is the restriction
`AlgebraicGeometry.Space.ChartDiagram.restrictOpens` of Tag 03G2's own construction.

The presentation itself is then `AlgebraicGeometry.Space.exists_chartLiftPresentation` at each
member of the family, whose remaining input — the square-zero chart datum — is supplied there by
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
variable {B X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {p : X' ⟶ B} {q : Y ⟶ B} {X : Subfunctor X'.1} {a : X.toFunctor ⟶ Y.1}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a U')

/-- **Every section of the sheaf of lifts over the chart factors through the chart of `Y`**,
granted that that chart is étale.

The presented lift and the given section are both lifts of `a`, so they agree on the closed
subscheme `X ×_{X'} U'` of the chart; the presented lift factors there through the chart of `Y`,
by restricting its own factorization; and the closed subscheme is cut out by a square-zero ideal,
so formal étaleness of the chart of `Y` — [Stacks Project, Tag 04AL] — extends that factorization
over the whole chart, compatibly with the given section. -/
theorem exists_hom_tgtChart_app_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    {y : Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj U'))}
    (hy : IsChartLift C S hS p q a U' (yonedaEquiv.symm y)) :
    ∃ b : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.tgt,
      y = P.tgtChart.app (op ((SmallEtale.toOver C S hS X'.1).obj U')) b := by
  have h₁ := hy.2 P.sub P.incl P.subChart P.incl_comp_chart
  have h₂ := P.isLift.2 P.sub P.incl P.subChart P.incl_comp_chart
  have hval : y = yonedaEquiv (yonedaEquiv.symm y) := (Equiv.apply_symm_apply _ _).symm
  have hxy : P.tgtChart.app (op P.sub) (P.incl ≫ P.liftHom) = Y.1.map P.incl.op y := by
    rw [app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.incl ≫ P.liftHom), hval,
      yonedaEquiv_naturality, h₁, Functor.map_comp, Category.assoc, h₂]
  obtain ⟨z, hz, -⟩ := formallyEtale_of_etale C S hS P.tgtChart hw P.sub
    ((SmallEtale.toOver C S hS X'.1).obj U') P.isAffineSub P.isAffineAmbient P.incl P.squareZero
    (P.incl ≫ P.liftHom) y hxy
  exact ⟨z, hz.2.symm⟩

/-- **Every section of the sheaf of lifts over the chart factors through the chart of `Y`** of a
presentation, granted that that chart is étale. -/
theorem exists_hom_tgtChart_app_eq_coe
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    ∃ b : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.tgt,
      β.1 = P.tgtChart.app (op ((SmallEtale.toOver C S hS X'.1).obj U')) b :=
  P.exists_hom_tgtChart_app_eq hw β.2

/-- **Transitivity of the action on every section of the sheaf of lifts over the chart**, granted
that the two charts of `q` are étale: the factorization through the chart of `Y` that
`AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateSection_eq` asks for is not a
restriction, because `exists_hom_tgtChart_app_eq` supplies it for every section. -/
theorem exists_translateSection_eq_of_isEtale
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    ∃ δ : P.Deriv, P.translateSection δ = β :=
  let ⟨b, hb⟩ := P.exists_hom_tgtChart_app_eq_coe hw β
  P.exists_translateSection_eq hw hv β b hb

/-- **Transitivity of the action of the sections of the acting sheaf on every section of the
sheaf of lifts over the chart**, granted that the two charts of `q` are étale. -/
theorem exists_translateActionSection_eq_of_isEtale
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    ∃ θ : P.ActionSection, P.translateActionSection θ = β :=
  let ⟨b, hb⟩ := P.exists_hom_tgtChart_app_eq_coe hw β
  P.exists_translateActionSection_eq hw hv β b hb

end ChartLiftPresentation

/-! ### Factoring a morphism out of a chart through an affine chart square of `q` -/

variable (C S hS)

/-- **A morphism from an étale scheme chart into an algebraic space factors, on a covering family
of affine étale charts, through an affine chart square of a morphism out of its target.**

For `q : Y ⟶ B` and a morphism `g : U' ⟶ Y` out of an étale scheme chart `U'` of a presheaf `F`
there is a covering family of affine étale charts `Z i ⟶ U'` of `F`, for each of which `g`
restricted to `Z i` factors through an affine étale chart `W i` of `Y` sitting in a commuting
square over `q` with an affine étale chart `V i` of `B`.

The covering family is not a weakness of the statement but its content: an affine chart of `Y`
receives only part of the chart `U'`.  The construction is the one of [Stacks Project, Tag 03G2]
for a tower of three morphisms: an atlas of `B` lifts along `q` to an atlas of `Y` over it, that
atlas lifts along `g` to a surjective étale cover of `U'` — which is where `U'` is used as a
*representable* algebraic space, [Stacks Project, Tag 025Z] — and the three terms of the resulting
tower are cut down to affine opens, which cover because the affine opens of a scheme form a
basis. -/
theorem exists_affine_chartSquare_hom_ofArrows {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (q : Y ⟶ B) (U' : SmallEtale C S hS F)
    (g : yoneda.obj ((SmallEtale.toOver C S hS F).obj U') ⟶ Y.1) :
    ∃ (I : Type u) (Z : I → SmallEtale C S hS F) (r : ∀ i, Z i ⟶ U')
      (W : I → SmallEtale C S hS Y.1) (V : I → SmallEtale C S hS B.1)
      (ψ : ∀ i, (SmallEtale.toOver C S hS Y.1).obj (W i) ⟶
        (SmallEtale.toOver C S hS B.1).obj (V i))
      (c : ∀ i, (SmallEtale.toOver C S hS F).obj (Z i) ⟶
        (SmallEtale.toOver C S hS Y.1).obj (W i)),
      (∀ i, IsAffine ((BigFppfOver.toScheme C S hS).obj
        ((SmallEtale.toOver C S hS F).obj (Z i)))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme C S hS).obj
        ((SmallEtale.toOver C S hS Y.1).obj (W i)))) ∧
      (∀ i, IsAffine ((BigFppfOver.toScheme C S hS).obj
        ((SmallEtale.toOver C S hS B.1).obj (V i)))) ∧
      (∀ i, yoneda.map (ψ i) ≫ (V i).1.hom = (W i).1.hom ≫ q.hom) ∧
      (∀ i, yoneda.map ((SmallEtale.toOver C S hS F).map (r i)) ≫ g
        = yoneda.map (c i) ≫ (W i).1.hom) ∧
      Sieve.ofArrows Z r ∈ SmallEtale.topology C S hS F U' := by
  classical
  obtain ⟨VB, bB, hbBS, hbBE⟩ := B.2.exists_atlas
  obtain ⟨WY, pY, ψ₀, hcommY, hpYS, hpYE⟩ :=
    exists_surjective_etale_presentation_lift C S hS Y.2 B.2 q.hom VB bB hbBS hbBE
  obtain ⟨U₀, pr, α, hcomm₀, hprS, hprE⟩ :=
    exists_surjective_etale_presentation_lift C S hS
      (isAlgebraicSpace_yoneda C S hS ((SmallEtale.toOver C S hS F).obj U')) Y.2 g WY pY
      hpYS hpYE
  -- the morphism of the site underlying the cover of the chart
  have hpr₀ : yoneda.map (Yoneda.fullyFaithful.preimage pr) = pr :=
    Yoneda.fullyFaithful.map_preimage pr
  have key : ∀ {P : MorphismProperty Scheme.{u}},
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme C S hS)).presheaf pr →
      P ((BigFppfOver.toScheme C S hS).map (Yoneda.fullyFaithful.preimage pr)) := fun {P} h =>
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme C S hS)) (F := yoneda)
      (by rw [hpr₀]; exact h)
  have hprEt := key hprE
  have hprSu := key hprS
  -- the global commuting square of the two atlases over `q`
  set dglob : ChartDiagram C S hS Y.1 B.1 q.hom :=
    { U := ⟨CostructuredArrow.mk pY, hpYE⟩
      V := ⟨CostructuredArrow.mk bB, hbBE⟩
      g := ψ₀
      comm := hcommY } with hdglob
  -- the cover of the chart, as an étale chart over it
  set Uc : SmallEtale C S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map (Yoneda.fullyFaithful.preimage pr) ≫ U'.1.hom),
      etale_comp_of_scheme C S hS _ U'.1.hom hprEt U'.property⟩ with hUc
  set UctoU' : Uc ⟶ U' :=
    ObjectProperty.homMk (CostructuredArrow.homMk (Yoneda.fullyFaithful.preimage pr) rfl)
    with hUctoU'
  refine ⟨Σ PB : ((BigFppfOver.toScheme C S hS).obj VB).affineOpens,
      Σ OY : {O : ((BigFppfOver.toScheme C S hS).obj WY).affineOpens //
        (O : _) ≤ (BigFppfOver.toScheme C S hS).map ψ₀ ⁻¹ᵁ (PB : _)},
      {OU : ((BigFppfOver.toScheme C S hS).obj U₀).affineOpens //
        (OU : _) ≤ (BigFppfOver.toScheme C S hS).map α ⁻¹ᵁ (OY.1 : _)},
    fun i => openChart C S hS F Uc i.2.2.1.1,
    fun i => openChartInclusion C S hS F Uc i.2.2.1.1 ≫ UctoU',
    fun i => (dglob.restrictOpens i.2.1.1.1 i.1.1 i.2.1.2).U,
    fun i => (dglob.restrictOpens i.2.1.1.1 i.1.1 i.2.1.2).V,
    fun i => (dglob.restrictOpens i.2.1.1.1 i.1.1 i.2.1.2).g,
    fun i => openSubMap α i.2.2.1.1 i.2.1.1.1 i.2.2.2,
    fun i => inferInstanceAs (IsAffine ((i.2.2.1 : _) : Scheme)),
    fun i => inferInstanceAs (IsAffine (i.2.1.1.1 : Scheme)),
    fun i => inferInstanceAs (IsAffine (i.1.1 : Scheme)),
    fun i => (dglob.restrictOpens i.2.1.1.1 i.1.1 i.2.1.2).comm.symm,
    fun i => ?_, ?_⟩
  · -- the restriction of `g` to the member factors through the member's chart of `Y`
    change yoneda.map (openSubHom _ i.2.2.1.1 ≫ Yoneda.fullyFaithful.preimage pr) ≫ g
      = yoneda.map (openSubMap α i.2.2.1.1 i.2.1.1.1 i.2.2.2) ≫
        yoneda.map (openSubHom _ i.2.1.1.1) ≫ pY
    rw [← Category.assoc, ← Functor.map_comp,
      openSubMap_comp_openSubHom α i.2.2.1.1 i.2.1.1.1 i.2.2.2,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hpr₀, hcomm₀]
  · -- the members cover: the cover of the chart is surjective and affine opens form a basis
    refine SmallEtale.ofArrows_mem_topology C S hS F _ _ ?_
    rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x => ?_, fun i => etale_toScheme_toOver_map C S hS F _⟩
    obtain ⟨y, hy⟩ := hprSu.surj x
    obtain ⟨PB, hPB, hPBmem, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme C S hS).obj VB))
        (show (BigFppfOver.toScheme C S hS).map ψ₀
          ((BigFppfOver.toScheme C S hS).map α y) ∈ (⊤ : _) from trivial)
    obtain ⟨OY, hOY, hOYmem, hOYsub⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme C S hS).obj WY))
        (show (BigFppfOver.toScheme C S hS).map α y ∈
          (BigFppfOver.toScheme C S hS).map ψ₀ ⁻¹ᵁ PB from hPBmem)
    obtain ⟨OU, hOU, hOUmem, hOUsub⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme C S hS).obj U₀))
        (show y ∈ (BigFppfOver.toScheme C S hS).map α ⁻¹ᵁ OY from hOYmem)
    refine ⟨⟨⟨PB, hPB⟩, ⟨⟨OY, hOY⟩, hOYsub⟩, ⟨⟨OU, hOU⟩, hOUsub⟩⟩, ?_⟩
    obtain ⟨z, hz⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme C S hS).obj U₀) OU).ge
      hOUmem
    refine ⟨z, ?_⟩
    have hmap : (BigFppfOver.toScheme C S hS).map ((SmallEtale.toOver C S hS F).map
          (openChartInclusion C S hS F Uc OU ≫ UctoU')) =
        Scheme.Opens.ι OU ≫
          (BigFppfOver.toScheme C S hS).map (Yoneda.fullyFaithful.preimage pr) := by
      rw [Functor.map_comp, Functor.map_comp,
        toScheme_map_toOver_map_openChartInclusion C S hS F Uc OU]
      rfl
    rw [hmap]
    change ((BigFppfOver.toScheme C S hS).map (Yoneda.fullyFaithful.preimage pr))
      ((Scheme.Opens.ι OU) z) = x
    rw [hz]
    exact hy

/-! ### Existence of a chart presentation of a given lift -/

/-- `AlgebraicGeometry.Space.exists_chartLiftPresentation` with the étaleness of the two charts
of `q` carried into the conclusion, which is where the transitivity statements want it: the
presentation it produces has the given charts, but a presentation produced by an existential
statement has forgotten them. -/
theorem exists_chartLiftPresentation_of_isEtale (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (hX : IsFirstOrderThickening C S hS X' X)
    (U' : SmallEtale C S hS X'.1)
    (hU' : IsAffine
      ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')))
    {W V : BigFppfOver C S hS}
    (hW : IsAffine ((BigFppfOver.toScheme C S hS).obj W))
    (hV : IsAffine ((BigFppfOver.toScheme C S hS).obj V))
    (w : yoneda.obj W ⟶ Y.1) (v : yoneda.obj V ⟶ B.1) (ψ : W ⟶ V)
    (hsq : yoneda.map ψ ≫ v = w ≫ q.hom)
    (c : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ W)
    (hc : IsChartLift C S hS p q a U' (yoneda.map c ≫ w))
    (hwE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf w)
    (hvE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf v) :
    ∃ P : ChartLiftPresentation C S hS p q a U',
      P.liftValue = yonedaEquiv (yoneda.map c ≫ w) ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf P.bseChart := by
  obtain ⟨T₀, i₀, u₀, hpb, -, -, hsz⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening C S hS hX
      ((SmallEtale.toOver C S hS X'.1).obj U') U'.1.hom
      ((isEtale_iff_presheaf_of_yoneda C S hS U'.1.hom).2 U'.property) hU'
  exact
    ⟨{ sub := T₀
       incl := i₀
       subChart := u₀
       isPullback := hpb
       squareZero := hsz
       isAffineAmbient := hU'
       tgt := W
       isAffineTgt := hW
       bse := V
       isAffineBse := hV
       tgtChart := w
       bseChart := v
       chartHom := ψ
       chartSq := hsq
       liftHom := c
       isLift := hc }, rfl, hwE, hvE⟩

/-- **Every lift of `a` over an étale scheme chart of `X'` is presented by a chart presentation
on a covering family of affine étale charts**, whose two charts of `q` are affine and étale.

This is `AlgebraicGeometry.Space.exists_chartLiftPresentation` with its last input — a
factorization of the lift through an affine chart of `Y` — supplied, by
`AlgebraicGeometry.Space.exists_affine_chartSquare_hom_ofArrows`.  The covering family is part of
the statement: an affine chart of `Y` receives only part of the given chart of `X'`, so a single
presentation of the given lift over the whole chart cannot be asked for. -/
theorem exists_chartLiftPresentation_ofArrows (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (hX : IsFirstOrderThickening C S hS X' X)
    (U' : SmallEtale C S hS X'.1)
    {y : Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj U'))}
    (hy : IsChartLift C S hS p q a U' (yonedaEquiv.symm y)) :
    ∃ (I : Type u) (Z : I → SmallEtale C S hS X'.1) (r : ∀ i, Z i ⟶ U')
      (P : ∀ i, ChartLiftPresentation C S hS p q a (Z i)),
      (∀ i, (P i).liftValue = Y.1.map ((SmallEtale.toOver C S hS X'.1).map (r i)).op y) ∧
      (∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).tgtChart) ∧
      (∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).bseChart) ∧
      Sieve.ofArrows Z r ∈ SmallEtale.topology C S hS X'.1 U' := by
  classical
  obtain ⟨I, Z, r, W, V, ψ, c, haffZ, haffW, haffV, hsq, hfac, hcov⟩ :=
    exists_affine_chartSquare_hom_ofArrows C S hS q U' (yonedaEquiv.symm y)
  choose P hP hPw hPv using fun i => exists_chartLiftPresentation_of_isEtale C S hS p q a hX
    (Z i) (haffZ i) (haffW i) (haffV i) (W i).1.hom (V i).1.hom (ψ i) (hsq i) (c i)
    (by rw [← hfac i]; exact hy.restrict C S hS (r i)) (W i).property (V i).property
  refine ⟨I, Z, r, P, fun i => ?_, hPw, hPv, hcov⟩
  rw [hP i, ← hfac i, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

/-- **Every section of the sheaf of lifts over an étale scheme chart of `X'` is the presented
lift of a chart presentation on a covering family of affine étale charts**, whose two charts of
`q` are affine and étale. -/
theorem exists_chartLiftPresentation_liftSection_ofArrows (p : X' ⟶ B) (q : Y ⟶ B)
    {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1) (hX : IsFirstOrderThickening C S hS X' X)
    (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    ∃ (I : Type u) (Z : I → SmallEtale C S hS X'.1) (r : ∀ i, Z i ⟶ U')
      (P : ∀ i, ChartLiftPresentation C S hS p q a (Z i)),
      (∀ i, (P i).liftSection = (liftsSubfunctor C S hS p q a).toFunctor.map (r i).op β) ∧
      (∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).tgtChart) ∧
      (∀ i, (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme C S hS)).presheaf (P i).bseChart) ∧
      Sieve.ofArrows Z r ∈ SmallEtale.topology C S hS X'.1 U' := by
  obtain ⟨I, Z, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_ofArrows C S hS p q a hX U' β.2
  exact ⟨I, Z, r, P, fun i => Subtype.ext (hval i), hw, hv, hcov⟩

/-- **The action of the sections of the acting sheaf on the sheaf of lifts is simply transitive
on a covering family of affine étale charts**, on which moreover a given section of the sheaf of
lifts is the presented lift.

This is what the two halves of this file give together, and it is the form the glueing of the
chartwise actions consumes: the covering family comes from
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows`, whose two charts of
`q` are étale, and transitivity holds for *every* section over a member — not only for those
factoring through the member's chart of `Y` — by
`AlgebraicGeometry.Space.ChartLiftPresentation.exists_hom_tgtChart_app_eq`. -/
theorem exists_chartLiftPresentation_simplyTransitive_ofArrows (p : X' ⟶ B) (q : Y ⟶ B)
    {X : Subfunctor X'.1} (a : X.toFunctor ⟶ Y.1) (hX : IsFirstOrderThickening C S hS X' X)
    (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    ∃ (I : Type u) (Z : I → SmallEtale C S hS X'.1) (r : ∀ i, Z i ⟶ U')
      (P : ∀ i, ChartLiftPresentation C S hS p q a (Z i)),
      (∀ i, (P i).liftSection = (liftsSubfunctor C S hS p q a).toFunctor.map (r i).op β) ∧
      (∀ i, Function.Injective (P i).translateActionSection) ∧
      (∀ (i) (γ : (liftsSubfunctor C S hS p q a).toFunctor.obj (op (Z i))),
        ∃ θ : (P i).ActionSection, (P i).translateActionSection θ = γ) ∧
      Sieve.ofArrows Z r ∈ SmallEtale.topology C S hS X'.1 U' := by
  obtain ⟨I, Z, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a hX U' β
  exact ⟨I, Z, r, P, hval, fun i => (P i).translateActionSection_injective (hw i),
    fun i γ => (P i).exists_translateActionSection_eq_of_isEtale (hw i) (hv i) γ, hcov⟩

end AlgebraicGeometry.Space

end
