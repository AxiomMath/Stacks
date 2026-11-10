module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FibrewiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The flat locus of a morphism of algebraic spaces and base change

Consider a commutative triangle of algebraic spaces over a scheme `S` given by `f : X ⟶ Y`,
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`, with `p` locally of finite presentation and flat
and `q` locally of finite type. The locus of points of `|X|` at which `f` is flat is then open,
and its formation commutes with base change along an arbitrary morphism `Z' ⟶ Z`: the base change
of `f` over `Z` is flat at a point of its source exactly when `f` is flat at the image of that
point in `|X|`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_baseChangeOverBase_iff`: the base change of `f` over `Z` is
  flat at a point of its source exactly when `f` is flat at the image of that point in `|X|`.
* `AlgebraicGeometry.Space.flatLocusOpenAndStableUnderBaseChange` is **Stacks 05X3**: the two
  assertions together.

## Implementation notes

The openness assertion is
`AlgebraicGeometry.Space.isOpen_setOf_isFlatAt_of_isLocallyOfFinitePresentation_comp`. The
base-change assertion is the scheme-level statement `AlgebraicGeometry.setOf_isFlatAt_baseChange`
read on a tower of étale charts: a chart `W` of `Z`, a chart `V` of `Y` with a morphism `V ⟶ W`
over `q`, a chart `U` of `X` with a morphism `U ⟶ V` over `f`, and a chart `W' ⟶ W` of `Z'`,
chosen so that `V ×_W W'` is a chart of `Y ×_Z Z'` and `U ×_V (V ×_W W')` one of `X ×_Z Z'`. The
two cartesian squares of schemes this produces are exactly the stacked pair the scheme-level
statement asks for, and a field-valued point of the top chart turns the configuration into
pointed étale charts of the base change and of `f` whose selected scheme points correspond.

That a fibre product of two morphisms of charts is again a chart is
`exists_etale_chart_of_isPullback`, a form of
`AlgebraicGeometry.Space.exists_compatible_etale_charts` in which the three charts it is built
from are given rather than chosen, and which reads the chart off an arbitrary cartesian square
rather than off the chosen fibre product; it is applied twice, once for each of the two squares.
The step joining the two applications is that `V ×_W W'` is a chart of `V ×_Y (Y ×_Z Z')`: that
fibre product is also `V ×_W (Z' ×_Z W)`, because the two morphisms `V ⟶ Z` agree, so the chart
is a base change of the chart `W' ⟶ Z' ×_Z W`.

Flatness at a point of an algebraic space is `AlgebraicGeometry.Space.IsFlatAt`, part (2) of
Stacks 03ML; on a pointed chart it is flatness of the germ morphism of Stacks 04ND, which for a
morphism of schemes is flatness of the stalk map.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 05VK](https://stacks.math.columbia.edu/tag/05VK)
* [Stacks Project, Tag 05X2](https://stacks.math.columbia.edu/tag/05X2)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Germ flatness at a point of a scheme -/

/-- The germ morphism induced by a morphism of schemes at a point of its source is flat, in the
sense of Stacks 04ND, exactly when the induced homomorphism of local rings at that point is
flat. -/
private theorem isFlat_germ_iff_isFlatAt {U V : Scheme.{u}} (k : U ⟶ V) (x : U) :
    MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom k x) ↔
      _root_.AlgebraicGeometry.IsFlatAt k.toLRSHom.toShHom x := by
  refine ⟨flatAt_of_isFlat_germ k x, fun hk => ?_⟩
  refine ⟨⟨⊤, by simp, U.topIso.hom ≫ k, rfl⟩, rfl, ?_⟩
  change ((U.topIso.hom ≫ k).stalkMap ⟨x, by simp⟩).hom.Flat
  exact (congrArg (fun j => j.hom.Flat)
    (Scheme.Hom.stalkMap_comp U.topIso.hom k ⟨x, by simp⟩)).mpr
      (hk.comp (Flat.stalkMap U.topIso.hom ⟨x, by simp⟩))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_flatLocusBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_flatLocusBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_flatLocusBaseChange B S hS).has_limit _

/-! ### Relatively representable properties of chart morphisms -/

/-- A morphism of presheaves on the big fppf site over `S` is *chart-surjective* when it is
relatively representable with surjective base changes to the objects of the site. -/
private abbrev ChartSurjective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a

/-- A morphism of presheaves on the big fppf site over `S` is *chart-étale* when it is relatively
representable with étale base changes to the objects of the site. -/
private abbrev ChartEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a

/-- A morphism of presheaves on the big fppf site over `S` is *chart-surjective* when it is
relatively representable with surjective base changes to the objects of the site.  This is the
statement of `ChartSurjective` as a declaration public signatures may mention. -/
public abbrev IsRelativelySurjectiveOnCharts {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a

/-- A morphism of presheaves on the big fppf site over `S` is *chart-étale* when it is relatively
representable with étale base changes to the objects of the site.  This is the statement of
`ChartEtale` as a declaration public signatures may mention. -/
public abbrev IsRelativelyEtaleOnCharts {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a

/-- A relatively representable property of chart morphisms inherited from a property of scheme
morphisms stable under composition is itself stable under composition. -/
private theorem chartProperty_comp (P : MorphismProperty Scheme.{u})
    (hP : P.IsStableUnderComposition) {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf b) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (a ≫ b) := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  let _ : Q.IsStableUnderComposition := inverseImage_isStableUnderComposition B S hS hP
  let _ : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  exact MorphismProperty.comp_mem Q.presheaf _ _ ha hb

/-- A relatively representable property of chart morphisms is stable under base change. -/
private theorem chartProperty_of_isPullback (P : MorphismProperty Scheme.{u})
    {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : K ⟶ F} {b : K ⟶ G} {c : F ⟶ H} {d : G ⟶ H}
    (hsq : IsPullback a b c d)
    (hd : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf d) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a := by
  let Q := P.inverseImage (BigFppfOver.toScheme B S hS)
  let _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback hsq.flip hd

/-- The first projection of a fibre product of presheaves inherits a relatively representable
property of chart morphisms from the morphism it is a base change of. -/
private theorem chartProperty_pullback_fst (P : MorphismProperty Scheme.{u})
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ H) (b : G ⟶ H)
    (hb : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf b) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst a b) :=
  chartProperty_of_isPullback B S hS P (IsPullback.of_hasPullback a b) hb

/-- A morphism into a fibre product of presheaves, composed with its first projection, has a
relatively representable property of chart morphisms when it and the second leg have it. -/
private theorem chartProperty_comp_pullback_fst (P : MorphismProperty Scheme.{u})
    (hP : P.IsStableUnderComposition) {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {b : F ⟶ H} {c : G ⟶ H} {a : K ⟶ pullback b c}
    (ha : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a)
    (hc : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf c) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (a ≫ pullback.fst b c) :=
  chartProperty_comp B S hS P hP _ _ ha (chartProperty_pullback_fst B S hS P _ _ hc)

/-- The flatness of a morphism of presheaves at a point is the flatness of the scheme morphism
between the charts of a pointed étale chart, at the chart's source point. -/
private theorem isFlatAt_iff_of_etaleChartAtPoint {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {x : points B S hS F} (c : EtaleChartAtPoint B S hS f x) :
    IsFlatAt B S hS f x ↔ _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map c.h).toLRSHom.toShHom (c.sourcePoint B S hS) :=
  (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat _ _ c).trans
      (isFlat_germ_iff_isFlatAt _ _)

/-! ### A compatible étale chart of a cartesian square -/

/-- **An étale chart of a fibre product, from étale charts of its ingredients.** Let `f : X ⟶ Y`
and `g : Y' ⟶ Y` be morphisms of presheaves and let `P` be a fibre product of them. A chart
`v : V ⟶ Y`, a chart `U ⟶ X ×_Y V` and a chart `V' ⟶ Y' ×_Y V`, all surjective and étale, induce
a surjective étale chart of `P` carried by the fibre product of the two induced morphisms of
charts `U ⟶ V` and `V' ⟶ V`. -/
private theorem exists_etale_chart_of_isPullback
    {X Y Y' P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y' ⟶ Y)
    {π : P ⟶ X} {ρ : P ⟶ Y'} (sq : IsPullback π ρ f g)
    {U V V' : BigFppfOver B S hS} (α : U ⟶ V) (δ : V' ⟶ V) (v : yoneda.obj V ⟶ Y)
    (aU : yoneda.obj U ⟶ pullback f v) (bV : yoneda.obj V' ⟶ pullback g v)
    (hα : yoneda.map α = aU ≫ pullback.snd f v)
    (hδ : yoneda.map δ = bV ≫ pullback.snd g v)
    (hvS : ChartSurjective B S hS v) (hvE : ChartEtale B S hS v)
    (haS : ChartSurjective B S hS aU) (haE : ChartEtale B S hS aU)
    (hbS : ChartSurjective B S hS bV) (hbE : ChartEtale B S hS bV) :
    ∃ c : yoneda.obj (pullback α δ) ⟶ P,
      ChartSurjective B S hS c ∧ ChartEtale B S hS c ∧
        c ≫ π = yoneda.map (pullback.fst α δ) ≫ aU ≫ pullback.fst f v ∧
        c ≫ ρ = yoneda.map (pullback.snd α δ) ≫ bV ≫ pullback.fst g v := by
  have hsite : IsPullback (yoneda.map (pullback.fst α δ)) (yoneda.map (pullback.snd α δ))
      (yoneda.map α) (yoneda.map δ) := (IsPullback.of_hasPullback α δ).map yoneda
  let d : yoneda.obj V' ⟶ Y' := bV ≫ pullback.fst g v
  have hd : d = bV ≫ pullback.fst g v := rfl
  have hcommG : yoneda.map δ ≫ v = d ≫ g := by
    rw [hd, hδ, Category.assoc, Category.assoc, pullback.condition]
  let k₁ : yoneda.obj (pullback α δ) ⟶ pullback (pullback.snd f v) (yoneda.map δ) :=
    pullback.lift (yoneda.map (pullback.fst α δ) ≫ aU) (yoneda.map (pullback.snd α δ)) (by
      rw [Category.assoc, ← hα]
      exact hsite.w)
  have hk₁fst : k₁ ≫ pullback.fst (pullback.snd f v) (yoneda.map δ) =
      yoneda.map (pullback.fst α δ) ≫ aU := pullback.lift_fst _ _ _
  have hk₁snd : k₁ ≫ pullback.snd (pullback.snd f v) (yoneda.map δ) =
      yoneda.map (pullback.snd α δ) := pullback.lift_snd _ _ _
  have hk₁ : IsPullback k₁ (yoneda.map (pullback.fst α δ))
      (pullback.fst (pullback.snd f v) (yoneda.map δ)) aU := by
    refine IsPullback.of_right ?_ hk₁fst
      (t := (IsPullback.of_hasPullback (pullback.snd f v) (yoneda.map δ)).flip)
    rw [hk₁snd, ← hα]
    exact hsite.flip
  let k₂ : pullback (pullback.snd f v) (yoneda.map δ) ⟶ P :=
    sq.lift (pullback.fst (pullback.snd f v) (yoneda.map δ) ≫ pullback.fst f v)
      (pullback.snd (pullback.snd f v) (yoneda.map δ) ≫ d) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, hcommG, ← Category.assoc])
  have hk₂fst : k₂ ≫ π =
      pullback.fst (pullback.snd f v) (yoneda.map δ) ≫ pullback.fst f v := sq.lift_fst _ _ _
  have hk₂snd : k₂ ≫ ρ =
      pullback.snd (pullback.snd f v) (yoneda.map δ) ≫ d := sq.lift_snd _ _ _
  have hk₂ : IsPullback k₂ (pullback.snd (pullback.snd f v) (yoneda.map δ)) ρ d := by
    refine IsPullback.of_right ?_ hk₂snd sq
    rw [hk₂fst, ← hcommG]
    exact (IsPullback.of_hasPullback (pullback.snd f v) (yoneda.map δ)).paste_horiz
      (IsPullback.of_hasPullback f v)
  refine ⟨k₁ ≫ k₂, ?_, ?_, ?_, ?_⟩
  · exact chartProperty_comp B S hS _ surjective_isStableUnderComposition _ _
      (chartProperty_of_isPullback B S hS _ hk₁ haS)
      (chartProperty_of_isPullback B S hS _ hk₂
        (chartProperty_comp_pullback_fst B S hS _ surjective_isStableUnderComposition hbS hvS))
  · exact chartProperty_comp B S hS _ etale_isStableUnderComposition _ _
      (chartProperty_of_isPullback B S hS _ hk₁ haE)
      (chartProperty_of_isPullback B S hS _ hk₂
        (chartProperty_comp_pullback_fst B S hS _ etale_isStableUnderComposition hbE hvE))
  · rw [Category.assoc, hk₂fst, ← Category.assoc, hk₁fst, Category.assoc]
  · rw [Category.assoc, hk₂snd, ← Category.assoc, hk₁snd, hd]

/-! ### A tower of étale charts of a base change over the base -/

/-- **A tower of étale charts of a base change over the base.** For `f : X ⟶ Y` and `q : Y ⟶ Z`
and a base change of the pair along `h : Z' ⟶ Z`, presented by cartesian squares
`IsPullback g q' q h` and `IsPullback g' f' f g`, this bundles a chart `W` of `Z`, a chart `V`
of `Y` with a morphism `β : V ⟶ W` over `q`, a chart `U` of `X` with a morphism `α : U ⟶ V`
over `f`, and a chart `W'` of `Z'` with a morphism `γ : W' ⟶ W` over `h`, together with the
resulting charts `cV` of `Y'` carried by `V ×_W W'` and `cU` of `X'` carried by
`U ×_V (V ×_W W')`.

The point of the tower is that the two squares of chart schemes it leaves behind are the
*stacked* cartesian pair that the scheme-level statements of Stacks 05VJ and Stacks 05VK ask
for: `V ×_W W' ⟶ V` is the second of them and the first at the same time, so no comparison
between independently chosen charts of `Y'` is needed. -/
structure BaseChangeChartTower {X Y Z Y' Z' X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (q : Y ⟶ Z) (h : Z' ⟶ Z) (g : Y' ⟶ Y) (q' : Y' ⟶ Z')
    (g' : X' ⟶ X) (f' : X' ⟶ Y') where
  /-- the chart of the base `Z` -/
  W : BigFppfOver B S hS
  /-- the chart of `Y`, lying over `W` -/
  V : BigFppfOver B S hS
  /-- the chart of `X`, lying over `V` -/
  U : BigFppfOver B S hS
  /-- the chart of the new base `Z'`, lying over `W` -/
  W' : BigFppfOver B S hS
  /-- the morphism of charts over `q` -/
  β : V ⟶ W
  /-- the morphism of charts over `f` -/
  α : U ⟶ V
  /-- the morphism of charts over `h` -/
  γ : W' ⟶ W
  /-- the structure morphism of the chart of `Z` -/
  w : yoneda.obj W ⟶ Z
  /-- the structure morphism of the chart of `Y` -/
  v : yoneda.obj V ⟶ Y
  /-- the structure morphism of the chart of `X` -/
  u : yoneda.obj U ⟶ X
  /-- the chart of `Z` is surjective -/
  wSurjective : IsRelativelySurjectiveOnCharts B S hS w
  /-- the chart of `Z` is étale -/
  wEtale : IsRelativelyEtaleOnCharts B S hS w
  /-- the chart of `Y` is surjective -/
  vSurjective : IsRelativelySurjectiveOnCharts B S hS v
  /-- the chart of `Y` is étale -/
  vEtale : IsRelativelyEtaleOnCharts B S hS v
  /-- the chart of `X` is étale -/
  uEtale : IsRelativelyEtaleOnCharts B S hS u
  /-- the chart morphism `β` lies over `q` -/
  commQ : yoneda.map β ≫ w = v ≫ q
  /-- the chart morphism `α` lies over `f` -/
  commF : yoneda.map α ≫ v = u ≫ f
  /-- the induced chart of `Y'` -/
  cV : yoneda.obj (pullback β γ) ⟶ Y'
  /-- the induced chart of `X'` -/
  cU : yoneda.obj (pullback α (pullback.fst β γ)) ⟶ X'
  /-- the chart of `Y'` is étale -/
  cVEtale : IsRelativelyEtaleOnCharts B S hS cV
  /-- the chart of `X'` is étale -/
  cUEtale : IsRelativelyEtaleOnCharts B S hS cU
  /-- the chart of `X'` is surjective -/
  cUSurjective : IsRelativelySurjectiveOnCharts B S hS cU
  /-- the chart of `X'` lies over the chart of `X` along `g'` -/
  cUfst : cU ≫ g' = yoneda.map (pullback.fst α (pullback.fst β γ)) ≫ u
  /-- the chart of `X'` lies over the chart of `Y'` along `f'` -/
  cUsnd : cU ≫ f' = yoneda.map (pullback.snd α (pullback.fst β γ)) ≫ cV

namespace BaseChangeChartTower

variable {B S hS}
variable {X Y Z Y' Z' X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {q : Y ⟶ Z} {h : Z' ⟶ Z} {g : Y' ⟶ Y} {q' : Y' ⟶ Z'}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} (C : BaseChangeChartTower B S hS f q h g q' g' f')

/-- The morphism of charts `V ×_W W' ⟶ V` induced by `γ`. -/
noncomputable abbrev pV : pullback C.β C.γ ⟶ C.V := pullback.fst C.β C.γ

/-- The morphism of charts `V ×_W W' ⟶ W'` induced by `β`. -/
noncomputable abbrev pW' : pullback C.β C.γ ⟶ C.W' := pullback.snd C.β C.γ

/-- The morphism of charts `U ×_V (V ×_W W') ⟶ U` induced by `pV`. -/
noncomputable abbrev qU : pullback C.α C.pV ⟶ C.U := pullback.fst C.α C.pV

/-- The morphism of charts `U ×_V (V ×_W W') ⟶ V ×_W W'` induced by `α`. -/
noncomputable abbrev fU : pullback C.α C.pV ⟶ pullback C.β C.γ := pullback.snd C.α C.pV

/-- The lower cartesian square of chart schemes: the chart of `Y'` over the chart of `Y`. -/
theorem isPullbackY :
    IsPullback ((BigFppfOver.toScheme B S hS).map C.pV)
      ((BigFppfOver.toScheme B S hS).map C.pW')
      ((BigFppfOver.toScheme B S hS).map C.β) ((BigFppfOver.toScheme B S hS).map C.γ) :=
  (IsPullback.of_hasPullback C.β C.γ).map (BigFppfOver.toScheme B S hS)

/-- The upper cartesian square of chart schemes: the chart of `X'` over the chart of `X`. -/
theorem isPullbackX :
    IsPullback ((BigFppfOver.toScheme B S hS).map C.qU)
      ((BigFppfOver.toScheme B S hS).map C.fU)
      ((BigFppfOver.toScheme B S hS).map C.α) ((BigFppfOver.toScheme B S hS).map C.pV) :=
  (IsPullback.of_hasPullback C.α C.pV).map (BigFppfOver.toScheme B S hS)

/-- The composite chart morphism `U ⟶ W` lies over the composite `f ≫ q`. -/
theorem commP : yoneda.map (C.α ≫ C.β) ≫ C.w = C.u ≫ (f ≫ q) := by
  rw [Functor.map_comp, Category.assoc, C.commQ, ← Category.assoc, C.commF, Category.assoc]

end BaseChangeChartTower

/-- **Every base change over the base admits a tower of étale charts.** The charts are chosen
from the top of the triangle downwards — a chart of `Z`, a chart of `Y` over it, a chart of `X`
over that, and a chart of `Z'` over the chart of `Z` — and the two charts of the base change are
then the fibre products of the resulting morphisms of charts, by
`AlgebraicGeometry.Space.exists_etale_chart_of_isPullback` applied once for each of the two
cartesian squares.

The step joining the two applications is that `V ×_W W'` is also a chart of `V ×_Y Y'`: that
fibre product is `V ×_W (Z' ×_Z W)` as well, because the two morphisms `V ⟶ Z` agree, so the
chart is a base change of the chart `W' ⟶ Z' ×_Z W`. -/
theorem exists_baseChangeChartTower
    {X Y Z Y' Z' X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    {f : X ⟶ Y} {q : Y ⟶ Z} {h : Z' ⟶ Z} {g : Y' ⟶ Y} {q' : Y' ⟶ Z'}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sqY : IsPullback g q' q h) (sqX : IsPullback g' f' f g) :
    Nonempty (BaseChangeChartTower B S hS f q h g q' g' f') := by
  obtain ⟨W, w, hwS, hwE⟩ := hZ.exists_atlas
  have hWsp := isAlgebraicSpace_yoneda B S hS W
  obtain ⟨V, a₀, haS, haE⟩ := (isAlgebraicSpace_pullback B S hS q w hY hWsp hZ).exists_atlas
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨v, hv⟩ : ∃ v : yoneda.obj V ⟶ Y, v = a₀ ≫ pullback.fst q w := ⟨_, rfl⟩
  let β : V ⟶ W := yoneda.preimage (a₀ ≫ pullback.snd q w)
  have hβ : yoneda.map β = a₀ ≫ pullback.snd q w := yoneda.map_preimage _
  have hvS : IsRelativelySurjectiveOnCharts B S hS v := by
    rw [hv]
    exact chartProperty_comp_pullback_fst B S hS _ surjective_isStableUnderComposition haS hwS
  have hvE : IsRelativelyEtaleOnCharts B S hS v := by
    rw [hv]
    exact chartProperty_comp_pullback_fst B S hS _ etale_isStableUnderComposition haE hwE
  have hcommQ : yoneda.map β ≫ w = v ≫ q := by
    rw [hβ, hv, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨U, b₀, hbS, hbE⟩ := (isAlgebraicSpace_pullback B S hS f v hX hVsp hY).exists_atlas
  obtain ⟨u, hu⟩ : ∃ u : yoneda.obj U ⟶ X, u = b₀ ≫ pullback.fst f v := ⟨_, rfl⟩
  let α : U ⟶ V := yoneda.preimage (b₀ ≫ pullback.snd f v)
  have hαeq : yoneda.map α = b₀ ≫ pullback.snd f v := yoneda.map_preimage _
  have huE : IsRelativelyEtaleOnCharts B S hS u := by
    rw [hu]
    exact chartProperty_comp_pullback_fst B S hS _ etale_isStableUnderComposition hbE hvE
  have hcommF : yoneda.map α ≫ v = u ≫ f := by
    rw [hαeq, hu, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨W', c₀, hcS, hcE⟩ := (isAlgebraicSpace_pullback B S hS h w hZ' hWsp hZ).exists_atlas
  let γ : W' ⟶ W := yoneda.preimage (c₀ ≫ pullback.snd h w)
  have hγ : yoneda.map γ = c₀ ≫ pullback.snd h w := yoneda.map_preimage _
  obtain ⟨cV, -, hcVE, hcV1, hcV2⟩ := exists_etale_chart_of_isPullback B S hS q h
    sqY β γ w a₀ c₀ hβ hγ hwS hwE haS haE hcS hcE
  set pV : pullback β γ ⟶ V := pullback.fst β γ with hpV
  set pW' : pullback β γ ⟶ W' := pullback.snd β γ with hpW'
  have hcVfst : cV ≫ g = yoneda.map pV ≫ v := by rw [hcV1, hv]
  let dV : yoneda.obj (pullback β γ) ⟶ pullback g v := pullback.lift cV (yoneda.map pV) hcVfst
  have hdVfst : dV ≫ pullback.fst g v = cV := pullback.lift_fst _ _ _
  have hdVsnd : dV ≫ pullback.snd g v = yoneda.map pV := pullback.lift_snd _ _ _
  let N : pullback g v ⟶ pullback h w :=
    pullback.lift (pullback.fst g v ≫ q') (pullback.snd g v ≫ yoneda.map β) (by
      rw [Category.assoc, ← sqY.w, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, hcommQ])
  have hNfst : N ≫ pullback.fst h w = pullback.fst g v ≫ q' := pullback.lift_fst _ _ _
  have hNsnd : N ≫ pullback.snd h w = pullback.snd g v ≫ yoneda.map β := pullback.lift_snd _ _ _
  have hN : IsPullback N (pullback.snd g v) (pullback.snd h w) (yoneda.map β) := by
    have hP := (IsPullback.of_hasPullback g v).paste_horiz sqY.flip
    rw [← hcommQ] at hP
    refine IsPullback.of_right ?_ hNsnd (IsPullback.of_hasPullback h w)
    rw [hNfst]
    exact hP
  have hdVcomm : dV ≫ N = yoneda.map pW' ≫ c₀ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hNfst, ← Category.assoc, hdVfst, hcV2, Category.assoc]
    · rw [Category.assoc, hNsnd, ← Category.assoc, hdVsnd, Category.assoc, ← hγ,
        ← Functor.map_comp, ← Functor.map_comp, hpV, hpW', pullback.condition]
  have hdV : IsPullback dV (yoneda.map pW') N c₀ := by
    refine IsPullback.of_right ?_ hdVcomm hN.flip
    rw [hdVsnd, ← hγ, hpV, hpW']
    exact (IsPullback.of_hasPullback β γ).map yoneda
  have hdVS : IsRelativelySurjectiveOnCharts B S hS dV :=
    chartProperty_of_isPullback B S hS _ hdV hcS
  have hdVE : IsRelativelyEtaleOnCharts B S hS dV := chartProperty_of_isPullback B S hS _ hdV hcE
  obtain ⟨cU, hcUS, hcUE, hcU1, hcU2⟩ := exists_etale_chart_of_isPullback B S hS f g
    sqX α pV v b₀ dV hαeq hdVsnd.symm hvS hvE hbS hbE hdVS hdVE
  exact ⟨{ W := W, V := V, U := U, W' := W', β := β, α := α, γ := γ
           w := w, v := v, u := u
           wSurjective := hwS, wEtale := hwE
           vSurjective := hvS, vEtale := hvE, uEtale := huE
           commQ := hcommQ, commF := hcommF
           cV := cV, cU := cU
           cVEtale := hcVE, cUEtale := hcUE, cUSurjective := hcUS
           cUfst := by rw [hcU1, hu]
           cUsnd := by rw [hcU2, hdVfst] }⟩

/-! ### Flatness at a point and base change on the base -/

/-- **Stacks 05X3, the base-change assertion.** Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If `p` is locally of finite presentation and flat
and `q` is locally of finite type, then for every morphism `g : Z' ⟶ Z` of algebraic spaces the
base change of `f` over `Z` along `g` is flat at a point of its source exactly when `f` is flat
at the image of that point in `|X|`.

A tower of étale charts — a chart `W` of `Z`, a chart `V` of `Y` over it, a chart `U` of `X` over
that, and a chart `W'` of `Z'` over `W` — makes `V ×_W W'` a chart of `Y ×_Z Z'` and
`U ×_V (V ×_W W')` a chart of `X ×_Z Z'`, and the two resulting cartesian squares of schemes are
the stacked pair of `AlgebraicGeometry.setOf_isFlatAt_baseChange`. A field-valued point of the
top chart makes the configuration into pointed étale charts of the base change and of `f` whose
selected scheme points correspond, so each side becomes flatness of a morphism of schemes at
corresponding points of that stacked pair. -/
theorem isFlatAt_baseChangeOverBase_iff
    {X Y Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p) (g : Z' ⟶ Z)
    (hp : IsLocallyOfFinitePresentation B S hS p) (hpflat : IsFlat B S hS p)
    (hq : IsLocallyOfFiniteType B S hS q) (x' : points B S hS (pullback p g)) :
    IsFlatAt B S hS (baseChangeOverBase B S hS f p q hfq g) x' ↔
      IsFlatAt B S hS f (pointsMap B S hS (pullback p g) (pullback.fst p g) x') := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨C⟩ := exists_baseChangeChartTower B S hS hX hY hZ hZ'
    (IsPullback.of_hasPullback q g) (isPullback_baseChangeOverBase B S hS f p q hfq g)
  have hcommP : yoneda.map (C.α ≫ C.β) ≫ C.w = C.u ≫ p := by rw [C.commP, hfq]
  have _ : LocallyOfFinitePresentation (T.map C.α ≫ T.map C.β) := by
    rw [← Functor.map_comp]
    exact hp C.U C.W C.u C.w (C.α ≫ C.β) C.uEtale C.wEtale hcommP
  have _ : _root_.AlgebraicGeometry.Flat (T.map C.α ≫ T.map C.β) := by
    rw [← Functor.map_comp]
    exact hpflat C.U C.W C.u C.w (C.α ≫ C.β) C.uEtale C.wEtale hcommP
  have _ : LocallyOfFiniteType (T.map C.β) := hq C.V C.W C.v C.w C.β C.vEtale C.wEtale C.commQ
  have hpt (y : T.obj (pullback C.α C.pV)) :
      _root_.AlgebraicGeometry.IsFlatAt (T.map C.fU).toLRSHom.toShHom y ↔
        _root_.AlgebraicGeometry.IsFlatAt (T.map C.α).toLRSHom.toShHom (T.map C.qU y) := by
    simpa only [Set.mem_ofPred_eq, Set.mem_preimage] using Set.ext_iff.mp
      (_root_.AlgebraicGeometry.setOf_isFlatAt_baseChange C.isPullbackY C.isPullbackX) y
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS (pullback p g)
    (isAlgebraicSpace_pullback B S hS p g hX hZ' hZ) (pullback C.α C.pV) C.cU).mp
      C.cUSurjective x'
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hzr : pointsMap B S hS (yoneda.obj (pullback C.α C.pV)) C.cU
      (r.class B S hS (yoneda.obj (pullback C.α C.pV))) = x' := hz
  let chartBC : EtaleChartAtPoint B S hS (baseChangeOverBase B S hS f p q hfq g) x' :=
    { U := pullback C.α C.pV, V := pullback C.β C.γ, a := C.cU, b := C.cV, h := C.fU
      a_etale := C.cUEtale, b_etale := C.cVEtale, comm := C.cUsnd.symm
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := hzr }
  let chartF : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (pullback p g) (pullback.fst p g) x') :=
    { U := C.U, V := C.V, a := C.u, b := C.v, h := C.α
      a_etale := C.uEtale, b_etale := C.vEtale, comm := C.commF
      representative :=
        FieldValuedPoint.map B S hS (yoneda.obj (pullback C.α C.pV)) (yoneda.map C.qU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        change (pointsMap B S hS (yoneda.obj C.U) C.u ∘
          pointsMap B S hS (yoneda.obj (pullback C.α C.pV)) (yoneda.map C.qU))
            (r.class B S hS (yoneda.obj (pullback C.α C.pV))) = _
        rw [← pointsMap_comp B S hS (yoneda.obj (pullback C.α C.pV)) (yoneda.map C.qU) C.u,
          ← C.cUfst,
          pointsMap_comp B S hS (yoneda.obj (pullback C.α C.pV)) C.cU (pullback.fst p g)]
        simp only [Function.comp_apply, hzr] }
  have hsource : chartF.sourcePoint B S hS = T.map C.qU (chartBC.sourcePoint B S hS) := by
    change T.map (r.value ≫ C.qU) (IsLocalRing.closedPoint r.carrier) =
      T.map C.qU ((T.map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  refine (isFlatAt_iff_of_etaleChartAtPoint B S hS chartBC).trans
    (Iff.trans ?_ (isFlatAt_iff_of_etaleChartAtPoint B S hS chartF).symm)
  rw [hsource]
  exact hpt _

/-! ### Stacks 05X3 -/

/-- **Stacks 05X3.** For a commutative triangle of algebraic spaces over `S` given by
`f : X ⟶ Y`, `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`, with `p` locally of finite
presentation and flat and `q` locally of finite type, the locus of points of `|X|` at which `f`
is flat is open and its formation commutes with base change along any morphism `Z' ⟶ Z`.

The openness assertion is
`AlgebraicGeometry.Space.isOpen_setOf_isFlatAt_of_isLocallyOfFinitePresentation_comp` and the
base-change assertion is `AlgebraicGeometry.Space.isFlatAt_baseChangeOverBase_iff`. -/
@[stacks 05X3 "openness and base change of the relative flat locus"]
theorem flatLocusOpenAndStableUnderBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFinitePresentation B S hS p) (hpflat : IsFlat B S hS p)
    (hq : IsLocallyOfFiniteType B S hS q) :
    IsOpen {x : points B S hS X | IsFlatAt B S hS f x} ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z' →
        ∀ (g : Z' ⟶ Z) (x' : points B S hS (pullback p g)),
          IsFlatAt B S hS (baseChangeOverBase B S hS f p q hfq g) x' ↔
            IsFlatAt B S hS f
              (pointsMap B S hS (pullback p g) (pullback.fst p g) x') :=
  ⟨isOpen_setOf_isFlatAt_of_isLocallyOfFinitePresentation_comp B S hS hX hY hZ f p q hfq hp hq,
    fun _ hZ' g x' =>
      isFlatAt_baseChangeOverBase_iff B S hS hX hY hZ hZ' f p q hfq g hp hpflat hq x'⟩

end AlgebraicGeometry.Space

end
