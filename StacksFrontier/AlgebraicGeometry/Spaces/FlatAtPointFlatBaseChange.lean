module

public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Flatness at a point under a flat base change

Consider a cartesian square of algebraic spaces over a scheme `S`

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

and a point `x'` of `|X'|`. If `f` is flat at the image of `x'` in `|X|`, then `f'` is flat at
`x'`, whatever `g` is. If `g` is flat, the converse holds as well: the stalk of `X'` at a point
over `x'` is flat over the stalk of `Y'`, which is flat over the stalk of `Y` because `g` is
flat, and it is faithfully flat over the stalk of `X` because `g'` is flat and the stalk map is
local; so the stalk of `X` is flat over the stalk of `Y`. This is the structure sheaf case of
**Stacks 05VW**, and it is what makes the open locus of points at which a morphism locally of
finite presentation is flat commute with flat base change (**Stacks 05WW**).

## Main results

* `AlgebraicGeometry.Space.isFlatAt_iff_of_isPullback_of_isFlat`: in a cartesian square of
  algebraic spaces whose base morphism is flat, the base change is flat at a point exactly when
  the original morphism is flat at the image of that point.

## Implementation notes

Flatness at a point of a morphism of algebraic spaces is `AlgebraicGeometry.Space.IsFlatAt`,
the germ condition of part (2) of **Stacks 03ML** read on pointed étale charts, and flatness of
germs is étale local on source and target (**Stacks 04ND**), so it may be read in any one
pointed chart (**Stacks 04NC**). Compatible surjective étale charts of the square
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`) consist of a chart `V` of `Y`, a
chart `U ⟶ V` of `f`, a chart `V' ⟶ V` of `g` and the induced chart `U' = U ×_V V' ⟶ V'` of
`f'`; a field-valued point of `U'` over `x'` makes them pointed charts of `f'` at `x'` and of
`f` at its image, with corresponding selected points. Flatness of `g` makes the chart
`V' ⟶ V` a flat morphism of schemes, and the statement becomes the one for schemes,
`AlgebraicGeometry.isFlatAt_iff_of_isPullback`.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05WW](https://stacks.math.columbia.edu/tag/05WW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance (priority := high) hasPullback_presheaf_FlatAtPointFlatBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- **Flatness at a point is invariant under flat base change.** In a cartesian square of
algebraic spaces over `S` whose base morphism `g` is flat, the base change `f'` is flat at a
point `x'` of its source exactly when `f` is flat at the image of `x'`.

On compatible pointed étale charts of the square both sides become flatness at corresponding
points of a cartesian square of schemes whose base morphism, a chart of `g`, is flat; that is
`AlgebraicGeometry.isFlatAt_iff_of_isPullback`. -/
theorem isFlatAt_iff_of_isPullback_of_isFlat
    {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀} (sq : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (x' : points B S hS X₁.1) :
    IsFlatAt B S hS f'.hom x' ↔ IsFlatAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') := by
  classical
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS f g
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ Limits.pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ Limits.pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = Limits.pullback.snd f.hom g.hom :=
    e.inv_comp_eq.mpr (congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))).symm
  have hBEtale := MorphismProperty.comp_mem _ b (Limits.pullback.snd v g.hom) hbEtale
    (hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale)
  have hcommG : yoneda.map q ≫ v = (b ≫ Limits.pullback.snd v g.hom) ≫ g.hom := by
    rw [← hbq, Category.assoc, Limits.pullback.condition, Category.assoc]
  have _ : Flat ((BigFppfOver.toScheme B S hS).map q) :=
    hg V' V (b ≫ Limits.pullback.snd v g.hom) v q hBEtale hvEtale hcommG
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (Limits.pullback f.hom g.hom)
      (isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property)
      U' c).mp hcSurj (pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      pointsMap B S hS X₁.1 e.hom x' := hz
  let chartF : EtaleChartAtPoint B S hS f.hom
      (pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ Limits.pullback.snd v f.hom
      b := v
      h := p
      a_etale := MorphismProperty.comp_mem _ a _ haEtale
        (hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale)
      b_etale := hvEtale
      comm := by rw [← hap, Category.assoc, Limits.pullback.condition, Category.assoc]
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U) (a ≫ Limits.pullback.snd v f.hom)
            ((FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            pointsMap B S hS (yoneda.obj U')
              (yoneda.map pU ≫ a ≫ Limits.pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        have h₂ : pointsMap B S hS (yoneda.obj U')
            (c ≫ Limits.pullback.fst f.hom g.hom) (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (Limits.pullback f.hom g.hom)
              (Limits.pullback.fst f.hom g.hom)
              (pointsMap B S hS (yoneda.obj U') c
                (r.class B S hS (yoneda.obj U'))) := rfl
        have h₃ : pointsMap B S hS (Limits.pullback f.hom g.hom)
            (Limits.pullback.fst f.hom g.hom) (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ Limits.pullback.fst f.hom g.hom) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom
            (Limits.pullback.fst f.hom g.hom)) x').symm
        rw [h₁, ← hcX, h₂, hz', h₃, heFst] }
  let chartF' : EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ Limits.pullback.snd v g.hom
      h := pV'
      a_etale :=
        have : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
        MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
      b_etale := hBEtale
      comm := by simpa only [Category.assoc, heInvSnd] using hcY.symm
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U') (c ≫ e.inv)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (Limits.pullback f.hom g.hom) e.inv
              (pointsMap B S hS (yoneda.obj U') c
                (r.class B S hS (yoneda.obj U'))) := rfl
        have h₂ : pointsMap B S hS (Limits.pullback f.hom g.hom) e.inv
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ e.inv) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom e.inv) x').symm
        rw [h₁, hz', h₂, e.hom_inv_id, pointsMap_id, id_eq] }
  have hsource : chartF.sourcePoint B S hS =
      (BigFppfOver.toScheme B S hS).map pU (chartF'.sourcePoint B S hS) := by
    show ((BigFppfOver.toScheme B S hS).map (r.value ≫ pU))
        (IsLocalRing.closedPoint r.carrier) =
      (BigFppfOver.toScheme B S hS).map pU
        (((BigFppfOver.toScheme B S hS).map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  refine ((holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f'.hom x' chartF').trans
      (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _)).trans (Iff.trans ?_
    ((holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
      MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f.hom _ chartF).trans
        (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _)).symm)
  rw [hsource]
  exact _root_.AlgebraicGeometry.isFlatAt_iff_of_isPullback hcharts
    (chartF'.sourcePoint B S hS)

end AlgebraicGeometry.Space

end
