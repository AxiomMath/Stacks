module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Diagram
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Cartesian finite-order deformations of algebraic spaces

A *cartesian finite-order deformation* over a scheme `S` is a commutative diagram

```
(X ⊂ X') --(f, f')--> (Y ⊂ Y')
         ↘                ↙
            (B ⊂ B')
```

of thickenings of algebraic spaces over `S` in which the base thickening `B ⊂ B'` is of
finite order, the ambient source `X'` is flat over the ambient base `B'`, and both unprimed
spaces are the base changes of their primed counterparts along `B ⟶ B'`. The question Stacks
0CG6 answers is which properties the two horizontal morphisms `f` and `f'` share.

For every property of morphisms of schemes which is étale local on the source and target the
answer is the scheme-level answer, because the whole diagram has compatible surjective
étale scheme charts whose unprimed corners are the base changes of the primed ones: a chart
of the ambient base lifts to a chart of the ambient target and then to a chart of the ambient
source, and the three thickenings pull back along those charts to thickenings of schemes, the
base one of finite order. The resulting diagram of schemes is a
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram`.

## Main definitions

* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation` packages the six algebraic
  spaces, the three thickenings, the two horizontal morphisms, the two structure morphisms
  and all the hypotheses.

## Main results

* `AlgebraicGeometry.Space.exists_thickening_chart_pullback_subfunctor`: a thickening of
  algebraic spaces pulls back along an étale scheme chart of the ambient space to a
  thickening of schemes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation`:
  **this is the content of Stacks 0CG6** for every property étale local on the source and
  target. Such a property holds on every étale chart of `f` exactly when it holds on every
  étale chart of `f'`, as soon as it is invariant under every cartesian finite-order
  deformation of schemes.

## Implementation notes

As in the source, each unprimed space is given as a `CategoryTheory.Subfunctor` of its primed
space, and the thickening conditions are `AlgebraicGeometry.Space.IsThickening` and
`AlgebraicGeometry.Space.IsFiniteOrderThickening`; the thickening conditions already imply
that those subfunctors are algebraic spaces. The structure morphism of the source over the
base is the composite `f ≫ g` of the horizontal morphism with the structure morphism of the
target, which is exactly the commutativity of the triangle.

The two base-change assertions are recorded by `CategoryTheory.IsPullback`, so no
identification with a particular fibre-product object is chosen. Both pasting arguments
identifying the charts of the unprimed corners as fibre products run in the presheaf
category, where composition is associative by definition, and are transported to the site by
faithfulness of the Yoneda embedding.

## References

* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

/-! ### Thickenings pull back to thickenings on étale charts -/

/-- **A thickening is read on étale charts.** A thickening of algebraic spaces pulls back
along any scheme chart of the ambient space to a thickening of schemes: the inclusion is
representable with closed-immersion base changes, and it is surjective on points, hence so
is every base change of it. -/
theorem exists_thickening_chart_pullback_subfunctor (T : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : T.Contains S) {X : AlgebraicSpaces T S hS} {G : Subfunctor X.1}
    (hG : IsThickening T S hS X G) (U : BigFppfOver T S hS) (q : yoneda.obj U ⟶ X.1) :
    ∃ (U₀ : BigFppfOver T S hS) (j : U₀ ⟶ U) (p : yoneda.obj U₀ ⟶ G.toFunctor),
      IsPullback p (yoneda.map j) G.ι q ∧
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme T S hS).map j) := by
  have hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T S hS)).presheaf G.ι :=
    (surjective_iff_pointsMap_surjective T S hS hG.1.1 X.property G.ι hG.1.2.rep).2 hG.2
  exact ⟨hG.1.2.rep.pullback q, hG.1.2.rep.snd q, hG.1.2.rep.fst q, hG.1.2.rep.isPullback q,
    hG.1.2.property q _ _ (hG.1.2.rep.isPullback q),
    (hsurj.property q _ _ (hG.1.2.rep.isPullback q)).surj⟩

/-! ### The standing situation -/

/-- A cartesian finite-order deformation of algebraic spaces over a scheme: a morphism of
thickenings over a finite-order thickening of bases, with cartesian unprimed corners and the
ambient source flat over the ambient base. -/
structure CartesianFiniteOrderDeformation (T : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : T.Contains S) where
  /-- The ambient source `X'`. -/
  X' : AlgebraicSpaces T S hS
  /-- The ambient target `Y'`. -/
  Y' : AlgebraicSpaces T S hS
  /-- The ambient base `B'`. -/
  B' : AlgebraicSpaces T S hS
  /-- The source of the morphism under study, as a closed subspace `X ⊂ X'`. -/
  X : Subfunctor X'.1
  /-- The target of the morphism under study, as a closed subspace `Y ⊂ Y'`. -/
  Y : Subfunctor Y'.1
  /-- The base, as a closed subspace `B ⊂ B'`. -/
  B : Subfunctor B'.1
  /-- The base thickening is of finite order. -/
  base_finiteOrder : IsFiniteOrderThickening T S hS B' B
  /-- The source inclusion is a thickening. -/
  source_thickening : IsThickening T S hS X' X
  /-- The target inclusion is a thickening. -/
  target_thickening : IsThickening T S hS Y' Y
  /-- The morphism under study. -/
  f : X.toFunctor ⟶ Y.toFunctor
  /-- Its ambient deformation. -/
  f' : X'.1 ⟶ Y'.1
  /-- The structure morphism of the target over the base. -/
  g : Y.toFunctor ⟶ B.toFunctor
  /-- The structure morphism of the ambient target over the ambient base. -/
  g' : Y'.1 ⟶ B'.1
  /-- The horizontal morphisms form a morphism of thickenings. -/
  comm_f : f ≫ Y.ι = X.ι ≫ f'
  /-- The structure morphisms form a morphism of thickenings. -/
  comm_g : g ≫ B.ι = Y.ι ≫ g'
  /-- The source is the base change of the ambient source along the base thickening. -/
  isPullback_X : IsPullback X.ι (f ≫ g) (f' ≫ g') B.ι
  /-- The target is the base change of the ambient target along the base thickening. -/
  isPullback_Y : IsPullback Y.ι g g' B.ι
  /-- The ambient source is flat over the ambient base. -/
  flat_X' : IsFlat T S hS (f' ≫ g')

/-! ### Reduction to a cartesian finite-order deformation of schemes -/

/-- **Stacks 0CG6, the étale-local cases.** A property of morphisms of schemes which is étale
local on the source and target holds on every étale chart of the morphism of special fibres of
a cartesian finite-order deformation of algebraic spaces exactly when it holds on every étale
chart of the ambient morphism, as soon as it is invariant under every cartesian finite-order
deformation of schemes. -/
theorem holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation
    (T : BigFppfSite.{u}) (S : Scheme.{u}) (hS : T.Contains S)
    (D : CartesianFiniteOrderDeformation T S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ E : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u},
      P E.f ↔ P E.f') :
    HoldsOnEveryEtaleChart T S hS P D.f ↔ HoldsOnEveryEtaleChart T S hS P D.f' := by
  let Tscheme := BigFppfOver.toScheme T S hS
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- Compatible charts of the three ambient corners.
  obtain ⟨U', qB', hqB'surj, hqB'etale⟩ := D.B'.property.exists_atlas
  obtain ⟨V', qY', α, hqYcomm, hqYsurj, hqYetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.Y'.property D.B'.property D.g'
      U' qB' hqB'surj hqB'etale
  obtain ⟨W', qX', β, hqXcomm, hqXsurj, hqXetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.X'.property D.Y'.property D.f'
      V' qY' hqYsurj hqYetale
  -- The three thickenings pull back to thickenings of schemes on those charts.
  obtain ⟨U₀, jB, pB, hpbB, hBfinite⟩ :=
    exists_finiteOrderThickening_chart_pullback T S hS D.base_finiteOrder U' qB' hqB'etale
  obtain ⟨V₀, jY, pY, hpbY, hYthick⟩ :=
    exists_thickening_chart_pullback_subfunctor T S hS D.target_thickening V' qY'
  obtain ⟨W₀, jX, pX, hpbX, hXthick⟩ :=
    exists_thickening_chart_pullback_subfunctor T S hS D.source_thickening W' qX'
  have hqY₀surj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pY :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbY.flip hqYsurj
  have hqY₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pY :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbY.flip hqYetale
  have hqX₀surj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbX.flip hqXsurj
  have hqX₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbX.flip hqXetale
  -- The charts of the unprimed corners lie over the chart of the unprimed base.
  have hgcompat : pY ≫ D.g ≫ D.B.ι = yoneda.map (jY ≫ α) ≫ qB' := by
    rw [D.comm_g, reassoc_of% hpbY.w, hqYcomm, Functor.map_comp, Category.assoc]
  have hfcompat : pX ≫ D.f ≫ D.Y.ι = yoneda.map (jX ≫ β) ≫ qY' := by
    rw [D.comm_f, reassoc_of% hpbX.w, hqXcomm, Functor.map_comp, Category.assoc]
  let g₀ : V₀ ⟶ U₀ := yoneda.preimage (hpbB.lift (pY ≫ D.g) (yoneda.map (jY ≫ α)) hgcompat)
  let f₀ : W₀ ⟶ V₀ := yoneda.preimage (hpbY.lift (pX ≫ D.f) (yoneda.map (jX ≫ β)) hfcompat)
  have hf₀map : yoneda.map f₀ = hpbY.lift (pX ≫ D.f) (yoneda.map (jX ≫ β)) hfcompat :=
    yoneda.map_preimage _
  have hg₀map : yoneda.map g₀ = hpbB.lift (pY ≫ D.g) (yoneda.map (jY ≫ α)) hgcompat :=
    yoneda.map_preimage _
  have hf₀jY : f₀ ≫ jY = jX ≫ β := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hf₀map]
    simpa only [Category.assoc, ← Functor.map_comp] using
      hpbY.lift_snd (pX ≫ D.f) (yoneda.map (jX ≫ β)) hfcompat
  have hg₀jB : g₀ ≫ jB = jY ≫ α := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hg₀map]
    simpa only [Category.assoc, ← Functor.map_comp] using
      hpbB.lift_snd (pY ≫ D.g) (yoneda.map (jY ≫ α)) hgcompat
  have hf₀pY : yoneda.map f₀ ≫ pY = pX ≫ D.f := by rw [hf₀map, IsPullback.lift_fst]
  have hg₀pB : yoneda.map g₀ ≫ pB = pY ≫ D.g := by rw [hg₀map, IsPullback.lift_fst]
  -- Both unprimed charts are cartesian over the unprimed base chart.
  have hpbYouter : IsPullback (yoneda.map jY) (pY ≫ D.g) (qY' ≫ D.g') D.B.ι :=
    hpbY.flip.paste_vert D.isPullback_Y
  have hpbYouter' : IsPullback (yoneda.map jY) (yoneda.map g₀ ≫ pB)
      (yoneda.map α ≫ qB') D.B.ι := by
    rwa [hg₀pB, ← hqYcomm]
  have hpbYchart : IsPullback (yoneda.map jY) (yoneda.map g₀) (yoneda.map α)
      (yoneda.map jB) :=
    hpbYouter'.of_bot (by
      simpa only [Functor.map_comp] using congrArg yoneda.map hg₀jB.symm) hpbB.flip
  have hf₀g₀pB : yoneda.map (f₀ ≫ g₀) ≫ pB = pX ≫ D.f ≫ D.g := by
    rw [Functor.map_comp, Category.assoc, hg₀pB, reassoc_of% hf₀pY]
  have hβaQ : yoneda.map (β ≫ α) ≫ qB' = qX' ≫ D.f' ≫ D.g' := by
    rw [Functor.map_comp, Category.assoc, ← hqYcomm, ← reassoc_of% hqXcomm]
  have hpbXouter : IsPullback (yoneda.map jX) (pX ≫ D.f ≫ D.g)
      (qX' ≫ D.f' ≫ D.g') D.B.ι :=
    hpbX.flip.paste_vert D.isPullback_X
  have hpbXouter' : IsPullback (yoneda.map jX) (yoneda.map (f₀ ≫ g₀) ≫ pB)
      (yoneda.map (β ≫ α) ≫ qB') D.B.ι := by
    rwa [hf₀g₀pB, hβaQ]
  have hpbXchart : IsPullback (yoneda.map jX) (yoneda.map (f₀ ≫ g₀)) (yoneda.map (β ≫ α))
      (yoneda.map jB) :=
    hpbXouter'.of_bot (by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg yoneda.map (show jX ≫ β ≫ α = f₀ ≫ g₀ ≫ jB by
          rw [← reassoc_of% hf₀jY, hg₀jB])) hpbB.flip
  have hpbYchartSite : IsPullback jY g₀ α jB := IsPullback.of_map_of_faithful yoneda hpbYchart
  have hpbXchartSite : IsPullback jX (f₀ ≫ g₀) (β ≫ α) jB :=
    IsPullback.of_map_of_faithful yoneda hpbXchart
  -- Flatness of the ambient source over the ambient base, read on the charts.
  have hqX'flat : Flat (Tscheme.map (β ≫ α)) :=
    D.flat_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβaQ
  -- The resulting cartesian finite-order deformation diagram of schemes.
  let E : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} :=
    { S := Tscheme.obj U₀
      S' := Tscheme.obj U'
      iS := Tscheme.map jB
      iS_finiteOrder := hBfinite
      X := Tscheme.obj W₀
      X' := Tscheme.obj W'
      iX := Tscheme.map jX
      iX_thickening := hXthick
      Y := Tscheme.obj V₀
      Y' := Tscheme.obj V'
      iY := Tscheme.map jY
      iY_thickening := hYthick
      pX := Tscheme.map (f₀ ≫ g₀)
      pX' := Tscheme.map (β ≫ α)
      pY := Tscheme.map g₀
      pY' := Tscheme.map α
      f := Tscheme.map f₀
      f' := Tscheme.map β
      f_over_S := by simp
      f'_over_S' := by simp
      f_thickening_comm := by
        simpa only [Functor.map_comp] using congrArg Tscheme.map hf₀jY
      X_cartesian := hpbXchartSite.map Tscheme
      Y_cartesian := hpbYchartSite.map Tscheme
      X'_flat := hqX'flat }
  constructor
  · intro hAll
    rw [holdsOnEveryEtaleChart_iff_surjectiveChart T S hS P hP D.X'.property D.Y'.property D.f']
    exact ⟨W', V', qX', qY', β, hqXetale, hqYetale, hqXsurj, hqXcomm.symm,
      (hSchemes E).mp (hAll W₀ V₀ pX pY f₀ hqX₀etale hqY₀etale hf₀pY)⟩
  · intro hAll'
    rw [holdsOnEveryEtaleChart_iff_surjectiveChart T S hS P hP
      D.source_thickening.1.1 D.target_thickening.1.1 D.f]
    exact ⟨W₀, V₀, pX, pY, f₀, hqX₀etale, hqY₀etale, hqX₀surj, hf₀pY,
      (hSchemes E).mpr (hAll' W' V' qX' qY' β hqXetale hqYetale hqXcomm.symm)⟩

end AlgebraicGeometry.Space

end
