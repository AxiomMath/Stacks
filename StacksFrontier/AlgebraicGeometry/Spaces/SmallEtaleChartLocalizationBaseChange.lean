module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.CategoryTheory.Sites.YonedaRepresentableMorphism

/-!
# The localized chart base change is the chart base change of the chart projection

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` and let `V` be
an étale scheme chart of `Y`, with `U = V ×_Y X` the base-changed chart of `X` and
`ψ : U ⟶ V` the cartesian projection, a morphism of the big fppf category over `S`.

Stacks 04CF uses the *localization* `Over.post (smallBaseChange f) : Y_étale/V ⥤ X_étale/U` of
chart base change at `V`.  This file identifies it, through the comparison of Stacks 04M0, with
chart base change along the morphism of algebraic spaces *represented by* `ψ`: the square

```
 SmallEtale (yoneda.obj V) --- chart base change along ψ ---> SmallEtale (yoneda.obj U)
          |                                                            |
 chartLocalizationEquivalence                        chartLocalizationEquivalence
          v                                                            v
      Over V ------------- Over.post (smallBaseChange f) --------->  Over U
```

commutes up to a canonical natural isomorphism.  Objectwise it is the associativity comparison

`W ×_V (V ×_Y X) ≅ W ×_Y X`

for `W` an étale chart of the algebraic space represented by `V`: on the right the chosen
representability witness of `f` at the composite chart `W ⟶ V ⟶ Y`, on the left the chosen
representability witness of `yoneda.map ψ` at `W ⟶ V`.  Both are fibre products of the *same*
cospan, the left one after pasting the representability square of `ψ` below the one of `f`, so
the two are canonically isomorphic over `U`.

Composed with `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, which is the same
square for the other half of `AlgebraicGeometry.Space.chartSchemeEquivalence`, this identifies
the localized chart base change with base change of small étale sites of *schemes* along the
morphism of schemes underlying `ψ`.

## Main definitions

* `AlgebraicGeometry.Space.chartProjectionRepresentable`: the representability witness of the
  morphism of algebraic spaces represented by `ψ`, which is what chart base change along `ψ`
  is formed from.
* `AlgebraicGeometry.Space.chartLocalizationBaseChangeObjIso`: the comparison
  `W ×_Y X ≅ W ×_V U` on the underlying objects of the big fppf category over `S`.
* `AlgebraicGeometry.Space.chartLocalizationBaseChangeComponent`: the comparison at a single
  chart, as an isomorphism of the slice over `U`.
* `AlgebraicGeometry.Space.chartLocalizationBaseChangeIso`: **the natural isomorphism filling
  the square above.**

## Main results

* `AlgebraicGeometry.Space.isPullback_chartLocalizationBaseChange`: `W ×_V U` is a fibre product
  of `W ⟶ Y` and `f`, by pasting the two representability squares.  This is the content of the
  comparison.
* `AlgebraicGeometry.Space.chartLocalizationBaseChange_naturality`: the naturality square, read
  on underlying morphisms of the big fppf category over `S`.

## Implementation notes

The file is a twin of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChange.lean` and shares its
shape for the same reason.  Everything is computed on underlying morphisms of the big fppf
category over `S`, the two `rfl`-lemmas
`AlgebraicGeometry.Space.chartLocalizationBaseChange_lhs_map` and
`AlgebraicGeometry.Space.chartLocalizationBaseChange_rhs_map` reduce the two functors to that
level, and naturality is stated and proved there rather than rewritten inside the construction
of the natural isomorphism.  That separation is what keeps every rewritten goal type-correct at
`implicit` transparency: the apex of a chosen representability witness and the underlying object
of a base-changed chart are definitionally but not syntactically equal, and a rewrite whose
motive crosses that boundary fails.

For the same reason the two base-changed morphisms of charts are given explicitly, as
`AlgebraicGeometry.Space.chartLocalizationChartHom` and
`AlgebraicGeometry.Space.chartLocalizationPullbackMap`, each with the universal-property
condition it needs proved *at the spelling of this file*
(`AlgebraicGeometry.Space.chartLocalizationChartHom_cond` and
`AlgebraicGeometry.Space.chartLocalizationPullbackMap_cond`) rather than taken from
`AlgebraicGeometry.Space.representablePullback_lift_cond`, whose statement mentions the chart
produced by the comparison functor; a condition stated there cannot be matched by `rw` against
the goals below even though it is the same proposition.

The comparison depends on the chosen representability witness `hrep` of `f`, because
`AlgebraicGeometry.Space.smallBaseChange` does, and on the one of `yoneda.map ψ`, which is
canonical: fibre products exist in the big fppf category over `S` and `yoneda` preserves them,
which is `AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map`.

## References

* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- The representability witness of the morphism of algebraic spaces represented by the
cartesian projection `ψ : V ×_Y X ⟶ V`.  It is canonical: the big fppf category over `S` has
fibre products and `yoneda` preserves them. -/
noncomputable abbrev chartProjectionRepresentable :
    yoneda.relativelyRepresentable
      (representedSpaceMap B S hS (hrep.snd V.1.hom)).hom :=
  relativelyRepresentable_yoneda_map B S hS (hrep.snd V.1.hom)

variable (A : SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)))

/-- **The content of the comparison.**  The fibre product `W ×_V U` of an étale chart `W` of the
algebraic space represented by `V` with `U = V ×_Y X` over `V` is a fibre product of `W ⟶ Y` and
`f : X ⟶ Y`: paste the representability square of `ψ` at `W` below the representability square
of `f` at `V`. -/
theorem isPullback_chartLocalizationBaseChange :
    IsPullback
      ((chartProjectionRepresentable B S hS f hrep V).fst A.1.hom ≫ hrep.fst V.1.hom)
      (yoneda.map ((chartProjectionRepresentable B S hS f hrep V).snd A.1.hom))
      f.hom (A.1.hom ≫ V.1.hom) :=
  ((chartProjectionRepresentable B S hS f hrep V).isPullback A.1.hom).paste_horiz
    (hrep.isPullback V.1.hom)

/-- **The comparison `W ×_Y X ≅ W ×_V U`** on the underlying objects of the big fppf category
over `S`.  Both are fibre products of the same cospan — on the left the chosen representability
witness of `f` at the composite chart `W ⟶ V ⟶ Y`, on the right the pasted square — and `yoneda`
is fully faithful, so the comparison of presheaves descends to the site. -/
noncomputable def chartLocalizationBaseChangeObjIso :
    hrep.pullback (A.1.hom ≫ V.1.hom) ≅
      (chartProjectionRepresentable B S hS f hrep V).pullback A.1.hom :=
  yoneda.preimageIso
    ((hrep.isPullback (A.1.hom ≫ V.1.hom)).isoIsPullback _ _
      (isPullback_chartLocalizationBaseChange B S hS f hrep V A))

/-- The comparison of objects, read in presheaves. -/
theorem yoneda_map_chartLocalizationBaseChangeObjIso_hom :
    yoneda.map (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom =
      ((hrep.isPullback (A.1.hom ≫ V.1.hom)).isoIsPullback _ _
        (isPullback_chartLocalizationBaseChange B S hS f hrep V A)).hom := by
  simp [chartLocalizationBaseChangeObjIso]

/-- The comparison is compatible with the projections to `X`. -/
theorem chartLocalizationBaseChangeObjIso_hom_comp_fst :
    yoneda.map (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom ≫
        ((chartProjectionRepresentable B S hS f hrep V).fst A.1.hom ≫ hrep.fst V.1.hom) =
      hrep.fst (A.1.hom ≫ V.1.hom) := by
  rw [yoneda_map_chartLocalizationBaseChangeObjIso_hom, IsPullback.isoIsPullback_hom_fst]

/-- The comparison is compatible with the projections to the chart, in presheaves. -/
theorem chartLocalizationBaseChangeObjIso_hom_comp_snd :
    yoneda.map (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom ≫
        yoneda.map ((chartProjectionRepresentable B S hS f hrep V).snd A.1.hom) =
      yoneda.map (hrep.snd (A.1.hom ≫ V.1.hom)) := by
  rw [yoneda_map_chartLocalizationBaseChangeObjIso_hom, IsPullback.isoIsPullback_hom_snd]

/-- The comparison is compatible with the projections to the chart, on the site. -/
theorem chartLocalizationBaseChangeObjIso_hom_comp_snd' :
    (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom ≫
        (chartProjectionRepresentable B S hS f hrep V).snd A.1.hom =
      hrep.snd (A.1.hom ≫ V.1.hom) := by
  apply yoneda.map_injective
  rw [Functor.map_comp]
  exact chartLocalizationBaseChangeObjIso_hom_comp_snd B S hS f hrep V A

/-- The projection of `W ×_V U` to `U`, followed by `ψ`, is the projection to `W` followed by
the structure morphism of `W`: the representability square of `ψ` at `W`, read on the site. -/
theorem chartProjection_comp_snd :
    yonedaEquiv ((chartProjectionRepresentable B S hS f hrep V).fst A.1.hom) ≫
        hrep.snd V.1.hom =
      (chartProjectionRepresentable B S hS f hrep V).snd A.1.hom ≫ yonedaEquiv A.1.hom := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, CategoryTheory.yoneda_map_yonedaEquiv,
    CategoryTheory.yoneda_map_yonedaEquiv]
  exact (chartProjectionRepresentable B S hS f hrep V).w A.1.hom

/-- The comparison is a morphism over `U`: its composite with the structure morphism of the
right-hand chart is the structure morphism of the left-hand one.  Both are morphisms into the
chosen representability witness of `f` at `V`, so they are compared on its two projections. -/
theorem chartLocalizationBaseChangeComponent_over :
    (chartLocalizationBaseChangeObjIso B S hS f hrep V A).hom ≫
        yonedaEquiv ((chartProjectionRepresentable B S hS f hrep V).fst A.1.hom) =
      ((smallBaseChange B S hS f hrep).map
        ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor.obj A).hom).hom.left := by
  refine hrep.hom_ext ?_ ?_
  · rw [Functor.map_comp, CategoryTheory.yoneda_map_yonedaEquiv, Category.assoc,
      chartLocalizationBaseChangeObjIso_hom_comp_fst B S hS f hrep V A]
    exact (CostructuredArrow.w ((smallBaseChange B S hS f hrep).map
      ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor.obj A).hom).hom).symm
  · rw [Category.assoc, chartProjection_comp_snd B S hS f hrep V A,
      ← Category.assoc, chartLocalizationBaseChangeObjIso_hom_comp_snd' B S hS f hrep V A]
    exact (smallBaseChange_map_snd B S hS f hrep
      ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor.obj A).hom).symm

/-- **The comparison of the two localized base changes at a single chart**, as an isomorphism of
the slice of the small étale site of `X` over `U`. -/
noncomputable def chartLocalizationBaseChangeComponent :
    ((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
        Over.post (X := V) (smallBaseChange B S hS f hrep)).obj A ≅
      (smallBaseChange B S hS (representedSpaceMap B S hS (hrep.snd V.1.hom))
          (chartProjectionRepresentable B S hS f hrep V) ⋙
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          ((smallBaseChange B S hS f hrep).obj V)).functor).obj A :=
  Over.isoMk (ObjectProperty.isoMk _
    (CostructuredArrow.isoMk (chartLocalizationBaseChangeObjIso B S hS f hrep V A)
      (chartLocalizationBaseChangeObjIso_hom_comp_fst B S hS f hrep V A)))
    (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (chartLocalizationBaseChangeComponent_over B S hS f hrep V A)))

section Naturality

variable {A₁ A₂ : SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))}
  (k : A₁ ⟶ A₂)

/-- The universal-property condition of a relatively representable morphism for a map `h` of
test objects lying over the given maps to the base. -/
private theorem relativelyRepresentable_fst_comp_eq {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f) {a b : C}
    {g : F.obj a ⟶ Y} {g' : F.obj b ⟶ Y} (h : a ⟶ b) (e : F.map h ≫ g' = g) :
    hf.fst g ≫ f = F.map (hf.snd g ≫ h) ≫ g' := by
  rw [hf.w g, Functor.map_comp, Category.assoc, e]

/-- The universal-property condition for the base change of a morphism of charts along `f`,
stated at the spelling of this file. -/
theorem chartLocalizationChartHom_cond :
    hrep.fst (A₁.1.hom ≫ V.1.hom) ≫ f.hom =
      yoneda.map (hrep.snd (A₁.1.hom ≫ V.1.hom) ≫ k.hom.left) ≫ (A₂.1.hom ≫ V.1.hom) := by
  exact relativelyRepresentable_fst_comp_eq hrep k.hom.left
    (by rw [← Category.assoc, CostructuredArrow.w k.hom])

/-- The universal-property condition for the base change of a morphism of charts along `ψ`,
stated at the spelling of this file. -/
theorem chartLocalizationPullbackMap_cond :
    (chartProjectionRepresentable B S hS f hrep V).fst A₁.1.hom ≫
        (representedSpaceMap B S hS (hrep.snd V.1.hom)).hom =
      yoneda.map ((chartProjectionRepresentable B S hS f hrep V).snd A₁.1.hom ≫ k.hom.left) ≫
        A₂.1.hom := by
  exact relativelyRepresentable_fst_comp_eq _ k.hom.left (CostructuredArrow.w k.hom)

/-- Base change along `f` of a morphism of charts of `Y`, read on the underlying objects of the
big fppf category over `S`: the morphism supplied by the universal property of the chosen
representability witness of `f`. -/
noncomputable abbrev chartLocalizationChartHom :
    hrep.pullback (A₁.1.hom ≫ V.1.hom) ⟶ hrep.pullback (A₂.1.hom ≫ V.1.hom) :=
  hrep.lift (hrep.fst (A₁.1.hom ≫ V.1.hom))
    (hrep.snd (A₁.1.hom ≫ V.1.hom) ≫ k.hom.left)
    (chartLocalizationChartHom_cond B S hS f hrep V k)

/-- Base change along `ψ` of a morphism of charts, read on the underlying objects of the big
fppf category over `S`. -/
noncomputable abbrev chartLocalizationPullbackMap :
    (chartProjectionRepresentable B S hS f hrep V).pullback A₁.1.hom ⟶
      (chartProjectionRepresentable B S hS f hrep V).pullback A₂.1.hom :=
  (chartProjectionRepresentable B S hS f hrep V).lift
    ((chartProjectionRepresentable B S hS f hrep V).fst A₁.1.hom)
    ((chartProjectionRepresentable B S hS f hrep V).snd A₁.1.hom ≫ k.hom.left)
    (chartLocalizationPullbackMap_cond B S hS f hrep V k)

/-- The localization of chart base change at `V`, after the comparison of Stacks 04M0, acts on
underlying morphisms of the big fppf category over `S` by
`AlgebraicGeometry.Space.chartLocalizationChartHom`. -/
theorem chartLocalizationBaseChange_lhs_map :
    ((smallBaseChange B S hS f hrep).map
        (((SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor.map k).left)).hom.left =
      chartLocalizationChartHom B S hS f hrep V k := rfl

/-- Chart base change along the morphism represented by `ψ`, followed by the comparison of
Stacks 04M0, acts on underlying morphisms of the big fppf category over `S` by
`AlgebraicGeometry.Space.chartLocalizationPullbackMap`. -/
theorem chartLocalizationBaseChange_rhs_map :
    ((smallBaseChange B S hS (representedSpaceMap B S hS (hrep.snd V.1.hom))
        (chartProjectionRepresentable B S hS f hrep V)).map k).hom.left =
      chartLocalizationPullbackMap B S hS f hrep V k := rfl

/-- **The naturality square of the comparison**, read on underlying morphisms of the big fppf
category over `S`.  Both sides are morphisms into the apex of the pasted square, so they are
compared on its two projections. -/
theorem chartLocalizationBaseChange_naturality :
    chartLocalizationChartHom B S hS f hrep V k ≫
        (chartLocalizationBaseChangeObjIso B S hS f hrep V A₂).hom =
      (chartLocalizationBaseChangeObjIso B S hS f hrep V A₁).hom ≫
        chartLocalizationPullbackMap B S hS f hrep V k := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  unfold chartLocalizationChartHom chartLocalizationPullbackMap
  refine (isPullback_chartLocalizationBaseChange B S hS f hrep V A₂).hom_ext ?_ ?_
  · rw [Category.assoc, chartLocalizationBaseChangeObjIso_hom_comp_fst B S hS f hrep V A₂,
      hrep.lift_fst, Category.assoc,
      ← Category.assoc (yoneda.map (chartLocalizationPullbackMap B S hS f hrep V k)),
      (chartProjectionRepresentable B S hS f hrep V).lift_fst,
      chartLocalizationBaseChangeObjIso_hom_comp_fst B S hS f hrep V A₁]
  · rw [Category.assoc, chartLocalizationBaseChangeObjIso_hom_comp_snd B S hS f hrep V A₂,
      ← Functor.map_comp, hrep.lift_snd, Category.assoc, ← Functor.map_comp,
      (chartProjectionRepresentable B S hS f hrep V).lift_snd, Functor.map_comp,
      Functor.map_comp, ← Category.assoc,
      chartLocalizationBaseChangeObjIso_hom_comp_snd B S hS f hrep V A₁]

end Naturality

/-- **The localized chart base change is the chart base change of the chart projection.**  For a
representable morphism `f : X ⟶ Y` of algebraic spaces over `S` and an étale scheme chart `V` of
`Y`, the localization at `V` of base change of charts along `f`, read through the comparison of
Stacks 04M0 at both ends, is base change of charts along the morphism of algebraic spaces
represented by the cartesian projection `ψ : V ×_Y X ⟶ V`.

At a chart both composites are fibre products of the same cospan in the big fppf category over
`S`, which is `AlgebraicGeometry.Space.chartLocalizationBaseChangeComponent`, and naturality is
checked on the two projections of the pasted square. -/
noncomputable def chartLocalizationBaseChangeIso :
    (SmallEtale.chartLocalizationEquivalence B S hS Y.1 V).functor ⋙
        Over.post (X := V) (smallBaseChange B S hS f hrep) ≅
      smallBaseChange B S hS (representedSpaceMap B S hS (hrep.snd V.1.hom))
          (chartProjectionRepresentable B S hS f hrep V) ⋙
        (SmallEtale.chartLocalizationEquivalence B S hS X.1
          ((smallBaseChange B S hS f hrep).obj V)).functor :=
  NatIso.ofComponents (chartLocalizationBaseChangeComponent B S hS f hrep V) fun k =>
    Over.OverMorphism.ext
      (ObjectProperty.hom_ext _
        (CostructuredArrow.hom_ext _ _
          (chartLocalizationBaseChange_naturality B S hS f hrep V k)))

end AlgebraicGeometry.Space

end
