module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeBaseChangeProjection

/-!
# The ring half of the chart base-change square

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let `V` be an
étale scheme chart of `Y` and let `U = V ×_Y X` be the base-changed chart of `X`, with
`ψ : U ⟶ V` the cartesian projection.  `AlgebraicGeometry.Space.chartSchemeBaseChangeIso` fills
the square

```
 chartSchemeSite V --- base change along ψ ---> chartSchemeSite U
        |                                              |
 chartSchemeEquivalence                    chartSchemeEquivalence
        v                                              v
     Over V -------- Over.post (smallBaseChange f) -> Over U
```

with a natural isomorphism of functors of sites, and
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeBaseChangeStructureMap.lean` supplies the two
composite comparisons of structure sheaves that the two ways round the square carry.  This file
proves that those two comparisons agree, which is the hypothesis
`CategoryTheory.SheafOfModules.pushforwardCongr₂` consumes and so is what carries the square from
sites to sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.chartSchemeBaseChangeIso_hom_app_left_comp_fst`: **the content of the
  square**, that the comparison is a morphism over the chart: composed with the cartesian
  projection to an étale scheme `W` over the chart scheme of `V` it is the projection of
  `W ×_Y X` to `W`.
* `AlgebraicGeometry.Space.chartSchemeBaseChangeSharp_square`: **the two composite comparisons of
  structure sheaves agree.**

## Implementation notes

Over an étale scheme `W` over the chart scheme of `V` both composite comparisons pull a global
function back along a morphism of schemes, so the square reduces to one identity of morphisms of
the bounded category of schemes.  That reduction is
`AlgebraicGeometry.Space.chartSchemeBaseChangeSharp_square_of_hom`, which takes the comparison
isomorphism of the square as an *argument*: with the isomorphism opaque, the definitional
unfolding that reconciles the two spellings of the structure sheaf of a slice cannot descend into
it, and the reduction elaborates within the heartbeat budget.  Instantiated at
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` it is the square itself.

The identity of morphisms of schemes is proved at the spelling
`AlgebraicGeometry.Space.chartSchemeBaseChangeIso` rather than at the spelling
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso`: the two name the same isomorphism,
but the first states its type through the chart localization, which is the spelling the three
compatibilities of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeBaseChangeProjection.lean` are stated at, while
the second states it through `AlgebraicGeometry.Space.chartSchemeEquivalence` and so records every
intermediate object of the composite at a spelling that has to be unfolded through
`CategoryTheory.Equivalence.congrFullSubcategory` before any of them applies.
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso_hom_app_left_comp_fst` transports the
identity to the second spelling, which costs one definitional check of the two types rather than
one inside every step of the chain.

The chain itself is five steps, in the slice `Over U`: push the cartesian projection leftwards
through base change of the small étale sites of the chart schemes, fire the comparison of the
represented base change on the cartesian projections, fire the localized base change on the
projections to the chart, and cancel the two remaining factors — the counit of the chart-scheme
identification and the unit of its inverse — which compose to the identity.  Each step is applied
by `refine`, never by `rw` or `simp`: the implicit middle object of each junction is recorded at
one of two definitionally equal spellings, and only unification at default transparency
reconciles them.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- One step of a composite rewritten from the right: if the last factor composed with `w` is
`x` and the rest composed with `x` is `y`, the whole composite with `w` is `y`.  Stated for
abstract morphisms so that it can be applied by `refine`, which reconciles the two spellings of
the junction object by unification. -/
private theorem stepL {C : Type*} [Category C] {P Q R T : C}
    {u : P ⟶ Q} {v : Q ⟶ R} {w : R ⟶ T} {x : Q ⟶ T} {y : P ⟶ T}
    (h1 : v ≫ w = x) (h2 : u ≫ x = y) : (u ≫ v) ≫ w = y := by
  rw [Category.assoc, h1, h2]

/-- Two mutually inverse factors at the head of a composite cancel. -/
private theorem idCompOf {C : Type*} [Category C] {P Q T : C} {u : P ⟶ Q} {v : Q ⟶ P}
    (h : u ≫ v = 𝟙 P) (s : P ⟶ T) : u ≫ v ≫ s = s := by
  rw [← Category.assoc, h, Category.id_comp]

/-- The image of a pair of mutually inverse morphisms under two successive functors is again a
pair of mutually inverse morphisms. -/
private theorem mapmapCompEqId {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {A A' : C} (a : A ⟶ A') (b : A' ⟶ A) (h : a ≫ b = 𝟙 A) :
    G.map (F.map a) ≫ G.map (F.map b) = 𝟙 (G.obj (F.obj A)) := by
  rw [← G.map_comp, ← F.map_comp, h, F.map_id, G.map_id]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- **The content of the chart base-change square.**  At an étale scheme `W` over the chart
scheme of `V` the comparison isomorphism of
`AlgebraicGeometry.Space.chartSchemeBaseChangeIso` is a morphism over `W`: composed with the
cartesian projection `W ×_{V} U ⟶ W` it is the projection of `W ×_Y X` to `W`.

The chain is the three compatibilities of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeBaseChangeProjection.lean` together with the
cancellation of the counit of the chart-scheme identification against the unit of its inverse. -/
theorem chartSchemeBaseChangeIso_hom_app_left_comp_fst (W : chartSchemeSite B S hS Y V) :
    ((chartSchemeBaseChangeIso B S hS f hrep V).hom.app W).left.hom.left.left ≫
        pullback.fst W.obj.hom (baseChangeChartHom B S hS f hrep V).left =
      (hrep.snd (((chartReprEquivalence B S hS V).inverse.obj W).obj.hom ≫
        V.obj.hom)).left := by
  have h12 : (chartReprEquivalence B S hS V).inverse.map
        ((chartReprEquivalence B S hS V).counitInv.app W) ≫
      (chartReprEquivalence B S hS V).unitInv.app
        ((chartReprEquivalence B S hS V).inverse.obj W) = 𝟙 _ := by
    rw [← Equivalence.unit_app_inverse]
    simp
  have hc12 := mapmapCompEqId (SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor
    (Over.post (smallBaseChange B S hS f hrep)) _ _ h12
  simp only [chartSchemeBaseChangeIso,
    chartSchemeBaseChangeInnerIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Equivalence.invFunIdAssoc_hom_app,
    Equivalence.invFunIdAssoc_inv_app, Equivalence.funInvIdAssoc_hom_app, Functor.comp_map,
    Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  apply stepL
  · apply stepL
    · apply stepL
      · apply stepL
        · exact (chartSchemeBaseChange_map_left_comp_fst B S hS f hrep V
            ((chartReprEquivalence B S hS V).counit.app W)).trans (Category.comp_id _)
        · exact (isPullback_representedChart_schemes B S hS
            (baseChangeChartHom B S hS f hrep V)
            (chartProjectionRepresentable B S hS f hrep V)
            ((chartReprEquivalence B S hS V).inverse.obj W)).isoIsPullback_hom_fst _ _ _
      · exact chartLocalizationBaseChangeObjIso_hom_left_comp_snd B S hS f hrep V
          ((chartReprEquivalence B S hS V).inverse.obj W)
    · exact rfl
  · refine idCompOf ?_ _
    exact congrArg (fun m => m.left.hom.left.left) hc12

/-- `AlgebraicGeometry.Space.chartSchemeBaseChangeIso_hom_app_left_comp_fst` with the
chart-scheme identification named, which is the form the square of ringed sites consumes. -/
theorem chartSchemeEquivalenceBaseChangeIso_hom_app_left_comp_fst
    (W : chartSchemeSite B S hS Y V) :
    ((chartSchemeEquivalenceBaseChangeIso B S hS f hrep V).hom.app W).left.hom.left.left ≫
        pullback.fst W.obj.hom (baseChangeChartHom B S hS f hrep V).left =
      (hrep.snd (((chartSchemeEquivalence B S hS Y V).functor.obj W).left.obj.hom)).left :=
  chartSchemeBaseChangeIso_hom_app_left_comp_fst B S hS f hrep V W

/-- **The two composite comparisons of structure sheaves of the chart base-change square agree**,
for any isomorphism `e` of the two composite functors of sites which is a morphism over the
chart.  Over an étale scheme `W` over the chart scheme of `V` both composites pull a global
function back along a morphism of schemes, and the two morphisms of schemes agree by `key`.

The isomorphism is an argument rather than
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` itself so that the definitional
unfolding which reconciles the two spellings of the structure sheaf of a slice cannot descend
into it; see the implementation notes. -/
theorem chartSchemeBaseChangeSharp_square_of_hom
    (e : (chartSchemeEquivalence B S hS Y V).functor ⋙
          Over.post (X := V) (smallBaseChange B S hS f hrep) ≅
        chartSchemeBaseChange B S hS f hrep V ⋙
          (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor)
    (key : ∀ W : chartSchemeSite B S hS Y V,
      (e.hom.app W).left.hom.left.left ≫
          pullback.fst W.obj.hom (baseChangeChartHom B S hS f hrep V).left =
        (hrep.snd (((chartSchemeEquivalence B S hS Y V).functor.obj W).left.obj.hom)).left) :
    @SheafOfModules.comparisonComp
        (chartSchemeSite B S hS Y V) _
        (chartSchemeSite B S hS X (baseChangeChart B S hS f hrep V)) _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        (chartSchemeTopology B S hS Y V)
        (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (chartSchemeBaseChange B S hS f hrep V)
        (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor
        (isContinuous_chartSchemeBaseChange B S hS f hrep V)
        (isContinuous_chartSchemeIdentification_functor B S hS X
          (baseChangeChart B S hS f hrep V))
        (isContinuous_chartSchemeBaseChangeComp B S hS f hrep V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hrep V))
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O)
        (chartSchemeBaseChangeSharp B S hS f hrep V)
        (chartSchemeEquivSharp B S hS X (baseChangeChart B S hS f hrep V)) ≫
      (@Functor.sheafPushforwardContinuousNatTrans
        (chartSchemeSite B S hS Y V) _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        _ _
        e.hom RingCat.{u} _
        (chartSchemeTopology B S hS Y V)
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (isContinuous_chartSchemeLocalizationComp B S hS f hrep V)
        (isContinuous_chartSchemeBaseChangeComp B S hS f hrep V)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O) =
    @SheafOfModules.comparisonComp
        (chartSchemeSite B S hS Y V) _
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        (chartSchemeTopology B S hS Y V)
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (chartSchemeEquivalence B S hS Y V).functor
        (Over.post (X := V) (smallBaseChange B S hS f hrep))
        (isContinuous_chartSchemeIdentification_functor B S hS Y V)
        (isContinuous_overPost_smallBaseChange B S hS f hrep V)
        (isContinuous_chartSchemeLocalizationComp B S hS f hrep V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O)
        (chartSchemeEquivSharp B S hS Y V)
        (chartLocalizedSharp B S hS f hrep V) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  have hcomp := congrArg (fun m => (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map (B.inclusion.map m).op)) (key W.unop)
  dsimp only at hcomp
  exact hcomp

/-- **The ring half of the chart base-change square**: the two composite comparisons of structure
sheaves that the two ways round the square of
`AlgebraicGeometry.Space.chartSchemeEquivalenceBaseChangeIso` carry are equal.

This is the hypothesis `CategoryTheory.SheafOfModules.pushforwardCongr₂` consumes, and so is what
carries the square from sites to sheaves of modules. -/
theorem chartSchemeBaseChangeSharp_square :
    @SheafOfModules.comparisonComp
        (chartSchemeSite B S hS Y V) _
        (chartSchemeSite B S hS X (baseChangeChart B S hS f hrep V)) _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        (chartSchemeTopology B S hS Y V)
        (chartSchemeTopology B S hS X (baseChangeChart B S hS f hrep V))
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (chartSchemeBaseChange B S hS f hrep V)
        (chartSchemeEquivalence B S hS X (baseChangeChart B S hS f hrep V)).functor
        (isContinuous_chartSchemeBaseChange B S hS f hrep V)
        (isContinuous_chartSchemeIdentification_functor B S hS X
          (baseChangeChart B S hS f hrep V))
        (isContinuous_chartSchemeBaseChangeComp B S hS f hrep V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (chartSchemeSiteStructureSheaf B S hS X (baseChangeChart B S hS f hrep V))
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O)
        (chartSchemeBaseChangeSharp B S hS f hrep V)
        (chartSchemeEquivSharp B S hS X (baseChangeChart B S hS f hrep V)) ≫
      (@Functor.sheafPushforwardContinuousNatTrans
        (chartSchemeSite B S hS Y V) _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        _ _
        (chartSchemeEquivalenceBaseChangeIso B S hS f hrep V).hom RingCat.{u} _
        (chartSchemeTopology B S hS Y V)
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (isContinuous_chartSchemeLocalizationComp B S hS f hrep V)
        (isContinuous_chartSchemeBaseChangeComp B S hS f hrep V)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O) =
    @SheafOfModules.comparisonComp
        (chartSchemeSite B S hS Y V) _
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).C _
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).C _
        (chartSchemeTopology B S hS Y V)
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).J
        ((smallEtaleRingedSite B S hS X.1 X.2).over (baseChangeChart B S hS f hrep V)).J
        (chartSchemeEquivalence B S hS Y V).functor
        (Over.post (X := V) (smallBaseChange B S hS f hrep))
        (isContinuous_chartSchemeIdentification_functor B S hS Y V)
        (isContinuous_overPost_smallBaseChange B S hS f hrep V)
        (isContinuous_chartSchemeLocalizationComp B S hS f hrep V)
        (chartSchemeSiteStructureSheaf B S hS Y V)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS Y.1 Y.2).over V).O)
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over
          (baseChangeChart B S hS f hrep V)).O)
        (chartSchemeEquivSharp B S hS Y V)
        (chartLocalizedSharp B S hS f hrep V) :=
  chartSchemeBaseChangeSharp_square_of_hom B S hS f hrep V
    (chartSchemeEquivalenceBaseChangeIso B S hS f hrep V)
    (chartSchemeEquivalenceBaseChangeIso_hom_app_left_comp_fst B S hS f hrep V)

end AlgebraicGeometry.Space

end
