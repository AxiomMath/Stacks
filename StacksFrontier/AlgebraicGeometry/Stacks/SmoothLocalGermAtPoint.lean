module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# A smooth-local property of germs of schemes at a point of an algebraic stack

Let `𝒳` be an algebraic stack over `S`, let `x` be a point of `𝒳` in the sense of Stacks 04XG,
and let `P` be a property of germs of schemes which is smooth local (**Stacks 04N1**). Four
conditions compare `P` against the smooth charts of `𝒳` through `x`: that *every*, respectively
*some*, smooth chart by a scheme has `P` at its point above `x`, and that *every*, respectively
*some*, smooth chart by an algebraic space has property `P` at its point above `x` in the sense
of **Stacks 04RC**. This module proves the four equivalent, which is **Stacks 04YI**, and reads
the common value on an algebraic space and on a scheme.

**Stacks 04YJ** then *defines* "`𝒳` has property `P` at `x`" to be any one of those four
conditions. The existential algebraic-space condition is the form taken here, so it carries that
tag; the equivalence above is what makes the choice immaterial.

The argument is the source's. Two smooth charts `a : U ⟶ 𝒳` and `b : V ⟶ 𝒳` by schemes, at
points `u` and `v` over `x`, are compared through the 2-fibre product `V ×_𝒳 U`: it is an
algebraic stack representable by an algebraic space, both of its projections are smooth, and it
carries a point over `u` and `v` by **Stacks 04XH**. An étale scheme chart `W` of that algebraic
space through such a point — which exists by **Stacks 03H5** — is then smooth over both `U` and
`V`, as a composite of an étale and a smooth morphism of algebraic spaces (**Stacks 04XX** and
**Stacks 03ZD**), so `P(U, u) ⟺ P(W, w) ⟺ P(V, v)` by smooth locality of `P`.

## Main definitions

* `AlgebraicGeometry.Stack.GermPropertyAtEverySchemeChart` and
  `AlgebraicGeometry.Stack.GermPropertyAtSomeSchemeChart`: conditions (1) and (2), the universal
  and existential conditions over smooth charts by a scheme.
* `AlgebraicGeometry.Stack.GermPropertyAtEverySpaceChart` and
  `AlgebraicGeometry.Stack.GermPropertyAtSomeSpaceChart`: conditions (3) and (4), the universal
  and existential conditions over smooth charts by an algebraic space.
* `AlgebraicGeometry.Stack.HasPropertyAtPoint`: **Stacks 04YJ**, an algebraic stack having a
  smooth-local property of germs of schemes at a point of it, taken at condition (4).

## Main results

* `AlgebraicGeometry.Stack.tfae_germProperty_at_point`: **Stacks 04YI**, the four conditions are
  equivalent.
* `AlgebraicGeometry.Stack.germ_iff_of_smooth_charts`: the chart independence the equivalence
  rests on — two smooth charts by schemes at points with the same image in the space of points
  of the stack agree on a smooth-local property of germs.
* `AlgebraicGeometry.Stack.germPropertyAtSomeSpaceChart_algebraicSpaceStack_iff`: on the
  algebraic stack of an algebraic space the conditions are that algebraic space having property
  `P` at the corresponding point, which is the second addendum of the source.
* `AlgebraicGeometry.Stack.germPropertyAtSomeSpaceChart_yoneda_iff`: on the algebraic stack of a
  scheme they are `P` of the germ of that scheme at the corresponding point, which is the first
  addendum of the source.
* `AlgebraicGeometry.Stack.hasPropertyAtPoint_iff_germPropertyAtEverySchemeChart`,
  `AlgebraicGeometry.Stack.hasPropertyAtPoint_iff_germPropertyAtSomeSchemeChart` and
  `AlgebraicGeometry.Stack.hasPropertyAtPoint_iff_germPropertyAtEverySpaceChart`: the definition
  of **Stacks 04YJ** read against each of the other three conditions of **Stacks 04YI**.

## Implementation notes

A scheme over `S` enters as the algebraic space it represents, so a chart by a scheme `U` is a
1-morphism out of `AlgebraicGeometry.Stack.algebraicSpaceStack` at `yoneda.obj U` rather than out
of `AlgebraicGeometry.Stack.schemeStack`. The two algebraic stacks of a scheme are equivalent but
not equal, and the former is the one whose underlying category fibred in groupoids is the category
of elements of a presheaf, which is what `AlgebraicGeometry.Stack.spacePointMap` — the canonical
map from the points of an algebraic space to the points of an algebraic stack it charts — takes as
its source. The point of a chart by a scheme is therefore a field-valued point of `yoneda.obj U`
in the sense of Stacks 03BU, and the scheme point it determines is
`AlgebraicGeometry.Space.schemePoint`; the two addenda relate the conditions back to
`AlgebraicGeometry.Stack.schemeStack` through `AlgebraicGeometry.Space.HasPropertyAtPoint`.

Of the four conditions the definition of **Stacks 04YJ** is taken at the existential
algebraic-space one, `AlgebraicGeometry.Stack.GermPropertyAtSomeSpaceChart`. That is the
condition the two addenda above are already stated against, so they read directly as the
specializations of the definition — on the algebraic stack of an algebraic space it is that
algebraic space having `P` at the corresponding point in the sense of **Stacks 04RC**, and on the
algebraic stack of a scheme it is `P` of the germ of that scheme — and it is the shape of
`AlgebraicGeometry.Space.HasPropertyAtPoint`, the same notion one level down. Being existential it
is also the condition a chart of either kind supplies a witness for directly, while the universal
conditions are what the definition is consumed through; the equivalence converts between them, and
the three `iff` lemmas below record each conversion. As for **Stacks 04RC**, stating the one
condition needs neither smooth locality of `P` nor any surjectivity.

None of the four conditions asks a chart to be surjective. Surjectivity is replaced by the
requirement that the chart's point lie over `x`, and a chart through `x` is produced where one is
needed — in the implication from the universal to the existential scheme condition — out of a
smooth surjective presentation of `𝒳`.

The categorical content of the comparison is isolated in a lemma which takes the 2-commutative
square and its universal property as data, so that the concrete 2-fibre product of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` appears only in the one-line
instantiation. Spelling the square out inside the argument makes the proof term large enough for
the kernel to reject it.

A point of an algebraic stack is recorded against an arbitrary witness that its underlying
category is fibred in groupoids, and `AlgebraicGeometry.Stack.AlgebraicStacks.points` chooses one
out of the existential defining an algebraic stack. Since being fibred in groupoids is a
proposition the two spellings are definitionally equal, so the terms built here are transported
between them by `Eq.trans` and `congrArg` rather than by rewriting, which is syntactic.

Smoothness of a 1-morphism of algebraic stacks is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (**Stacks 075U**), and reading it on
representing algebraic spaces — one half of **Stacks 06FM** — needs smoothness of morphisms of
algebraic spaces to be smooth local on the source and target, supplied by
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth`.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 04N1](https://stacks.math.columbia.edu/tag/04N1)
* [Stacks Project, Tag 04RC](https://stacks.math.columbia.edu/tag/04RC)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 04YI](https://stacks.math.columbia.edu/tag/04YI)
* [Stacks Project, Tag 04YJ](https://stacks.math.columbia.edu/tag/04YJ)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smooth locality of a property of germs, read on schemes and on algebraic spaces -/

/-- A smooth-local property of germs of schemes is étale local: an étale morphism of germs is
smooth. -/
private theorem isEtaleLocal_of_isSmoothLocal (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsSmoothLocal P) : GermOfScheme.IsEtaleLocal P := fun f hf =>
  hP f (by obtain ⟨g, hg, hge⟩ := hf; exact ⟨g, hg, have := hge; inferInstance⟩)

/-- A smooth morphism of schemes identifies a smooth-local property of germs at a point of its
source with the property at the image of that point. The morphism itself, restricted to the whole
of its source, represents the morphism of germs. -/
private theorem germ_iff_of_smooth (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsSmoothLocal P) {W U : Scheme.{u}} (g : W ⟶ U) (hg : Smooth g) (w : W) :
    P ⟨U, g w⟩ ↔ P ⟨W, w⟩ := by
  let X : GermOfScheme.{u} := ⟨W, w⟩
  let r : MorphismOfGerms.Representative X ⟨U, g w⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := X.scheme.topIso.hom ≫ g
      map_point := rfl }
  exact hP (MorphismOfGerms.mk r) ⟨r, rfl, inferInstance⟩

/-- A scheme chart `W` of an algebraic space `R` which is smooth over a scheme `U` reads a
smooth-local property of germs: a point of `W` and its image in `U` have the same value of `P`.

The composite of the étale chart and the smooth morphism is a smooth morphism of algebraic spaces
between representable presheaves (**Stacks 04XX** and **Stacks 03ZD**), hence `yoneda.map` of a
smooth morphism of the site by Yoneda fullness. -/
private theorem germ_iff_of_smooth_space_map (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsSmoothLocal P) {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) {U W : BigFppfOver B S hS}
    (c : yoneda.obj W ⟶ R) (hc : Space.IsEtale B S hS c)
    (r : R ⟶ yoneda.obj U) (hr : Space.IsSmooth B S hS r)
    (w : Space.FieldValuedPoint B S hS (yoneda.obj W))
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U))
    (hwp : Space.pointsMap B S hS R r
        (Space.pointsMap B S hS (yoneda.obj W) c (w.class B S hS (yoneda.obj W))) =
      p.class B S hS (yoneda.obj U)) :
    P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩ ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj W, Space.schemePoint B S hS W w⟩ := by
  have hgmap : yoneda.map (yoneda.preimage (c ≫ r)) = c ≫ r := yoneda.map_preimage _
  have hgsm : Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ r))) := by
    refine Space.smooth_of_isSmooth_yonedaMap B S hS _ ?_
    rw [hgmap]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS W) hR
      (isAlgebraicSpace_yoneda B S hS U) c r (Space.isSmooth_of_isEtale B S hS hR hc) hr
  have hpt : (BigFppfOver.toScheme B S hS).map (yoneda.preimage (c ≫ r))
      (Space.schemePoint B S hS W w) = Space.schemePoint B S hS U p := by
    have h1 := Space.pointsToScheme_pointsMap B S hS (yoneda.preimage (c ≫ r))
      (w.class B S hS (yoneda.obj W))
    rw [hgmap, Space.pointsMap_comp, Function.comp_apply, hwp] at h1
    exact h1.symm
  rw [← hpt]
  exact germ_iff_of_smooth P hP _ hgsm _

/-- The property of germs at a point of the algebraic space represented by a scheme `U` is the
property of the germ of `U` at the corresponding scheme point. This is **Stacks 04N2** at the
identity presentation. -/
private theorem hasPropertyAtPoint_yoneda_iff (U : BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsEtaleLocal P) :
    Space.HasPropertyAtPoint B S hS (yoneda.obj U) (p.class B S hS (yoneda.obj U)) P ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩ := by
  simpa only [Iso.refl_hom, Space.pointsMap_id, id_eq] using
    Space.exists_etale_chart_iff_of_representable B S hS (yoneda.obj U) U
      (Iso.refl (yoneda.obj U)) p P hP

/-! ### Charts of an algebraic stack by an algebraic space -/

/-- Every point of an algebraic space is the image of a field-valued point of a scheme under an
étale scheme chart (**Stacks 03H5**). -/
private theorem exists_etale_chart_point {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B S hS R) (z : Space.points B S hS R) :
    ∃ (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ R) (_ : Space.IsEtale B S hS c)
      (w : Space.FieldValuedPoint B S hS (yoneda.obj W)),
      Space.pointsMap B S hS (yoneda.obj W) c (w.class B S hS (yoneda.obj W)) = z := by
  obtain ⟨W, c, hcSurj, hcEt⟩ := hR.exists_atlas
  obtain ⟨zW, hzW⟩ :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B S hS R hR W c).mp hcSurj z
  obtain ⟨w, rfl⟩ := Quot.exists_rep zW
  exact ⟨W, c, (Space.isEtale_iff_presheaf_of_yoneda B S hS c).2 hcEt, w, hzW⟩

/-- A smooth morphism of algebraic spaces composes with a smooth chart of an algebraic stack to a
smooth chart, and the two charts agree on points.

The 1-morphism of algebraic stacks inducing the given morphism of algebraic spaces is **Stacks
04SW**, its smoothness is one half of **Stacks 06FM**, and the agreement on points is the
naturality of the canonical map of **Stacks 04XL**. -/
private theorem exists_smooth_chart_of_isSmooth_map
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (b : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒳)
    (hb : AlgebraicStacks.IsSmooth B S hS b)
    (h : F ⟶ G) (hh : Space.IsEtale B S hS h) :
    ∃ c : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳,
      AlgebraicStacks.IsSmooth B S hS c ∧
        ∀ z : Space.points B S hS F,
          spacePointMap B S hS F 𝒳.val c.hom.hom z =
            spacePointMap B S hS G 𝒳.val b.hom.hom (Space.pointsMap B S hS F h z) := by
  obtain ⟨f, hf⟩ := exists_oneMorphism_representingMap_eq
    (𝒳 := algebraicSpaceStack.{u, w} B S hS F hF)
    (𝒴 := algebraicSpaceStack.{u, w} B S hS G hG) B S hS F G
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) h
  refine ⟨f ≫ b, AlgebraicStacks.isSmooth_comp B S hS f b
    (isSmooth_of_isSmooth_representingMap B S hS F G hF hG
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) f
      (hf ▸ Space.isSmooth_of_isEtale B S hS hG hh)) hb, fun z => ?_⟩
  have nat := spacePointMap_representing_naturality B S hS F G
    (algebraicSpaceStack.{u, w} B S hS F hF).val
    (algebraicSpaceStack.{u, w} B S hS G hG).val
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) f.hom z
  rw [hf] at nat
  have L := congrFun (spacePointMap_eq_pointsMap_comp B S hS F 𝒳.val (f ≫ b).hom.hom) z
  have R := congrFun (spacePointMap_eq_pointsMap_comp B S hS G 𝒳.val b.hom.hom)
    (Space.pointsMap B S hS F h z)
  simp only [Function.comp_apply] at L R
  exact L.trans (((pointsMap_comp B S hS
      (algebraicSpaceStack.{u, w} B S hS F hF).val.val
      (algebraicSpaceStack.{u, w} B S hS F hF).val.property
      (algebraicSpaceStack.{u, w} B S hS G hG).val.property
      𝒳.val.property f.hom.hom b.hom.hom _).symm).trans
    ((congrArg (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS G hG).val.val
      (algebraicSpaceStack.{u, w} B S hS G hG).val.property 𝒳.val.property b.hom.hom)
      nat.symm).trans R.symm))

/-- Every point of an algebraic stack is the image of a field-valued point of a scheme under a
smooth chart. The chart is a smooth surjective presentation of the stack by a scheme, read on the
algebraic space that scheme represents. -/
private theorem exists_smooth_scheme_chart_at_point (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    ∃ (U : BigFppfOver B S hS)
      (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
      (p : Space.FieldValuedPoint B S hS (yoneda.obj U)),
      AlgebraicStacks.IsSmooth B S hS a ∧
        spacePointMap B S hS (yoneda.obj U) 𝒳.val a.hom.hom
          (p.class B S hS (yoneda.obj U)) = x := by
  obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒳
  obtain ⟨e, heSmooth, heSurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom B S hS U
  have hsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS (e ≫ a)) := by
    rw [AlgebraicStacks.pointsMap_comp]
    exact haSurj.comp heSurj
  obtain ⟨z, hz⟩ := hsurj x
  obtain ⟨zs, hzs⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U)).surjective z
  obtain ⟨p, rfl⟩ := Quot.exists_rep zs
  refine ⟨U, e ≫ a, p, AlgebraicStacks.isSmooth_comp B S hS e a heSmooth haSmooth, ?_⟩
  have L := congrFun
    (spacePointMap_eq_pointsMap_comp B S hS (yoneda.obj U) 𝒳.val (e ≫ a).hom.hom)
    (p.class B S hS (yoneda.obj U))
  simp only [Function.comp_apply] at L
  exact L.trans ((congrArg (pointsMap B S hS
    (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).val.val
    (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).val.property
    𝒳.val.property (e ≫ a).hom.hom) hzs).trans hz)

/-! ### Two smooth charts through one point are dominated by a common one -/

/-- Two smooth charts of an algebraic stack by algebraic spaces, at points with the same image in
the space of points of the stack, are dominated by a common algebraic space smooth over both and
carrying a point over both.

This is the content of the 2-fibre product of the two charts: its projections are smooth by
**Stacks 075W**, it is representable by an algebraic space, and it carries the required point by
**Stacks 04XH**. The square and its universal property are taken as data, so that no concrete
2-fibre product appears in the proof term. -/
private theorem exists_smooth_common_point_of_square
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) (hb : AlgebraicStacks.IsSmooth B S hS b)
    (Q : Bicategory.TwoCommSq a b) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hrep : Stack.IsRepresentableByAlgebraicSpace B S hS Q.pt.val)
    (x : Space.points B S hS F) (y : Space.points B S hS G)
    (hxy : spacePointMap B S hS F 𝒳.val a.hom.hom x =
      spacePointMap B S hS G 𝒳.val b.hom.hom y) :
    ∃ (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS R)
      (r₁ : R ⟶ F) (r₂ : R ⟶ G) (z : Space.points B S hS R),
      Space.IsSmooth B S hS r₁ ∧ Space.IsSmooth B S hS r₂ ∧
        Space.pointsMap B S hS R r₁ z = x ∧ Space.pointsMap B S hS R r₂ z = y := by
  have hsm := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  obtain ⟨R, hR, ⟨eR⟩⟩ := hrep
  have hr₁ := isSmooth_representingMap_of_isSmooth B S hS hsm R F hR hF eR
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst
    (AlgebraicStacks.isSmooth_baseChange B S hS b a Q hQ hb)
  have hr₂ := isSmooth_representingMap_of_isSmooth B S hS hsm R G hR hG eR
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd
    (AlgebraicStacks.isSmooth_baseChange B S hS a b Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) ha)
  have e1 := congrFun (spacePointMap_eq_pointsMap_comp B S hS F 𝒳.val a.hom.hom) x
  have e2 := congrFun (spacePointMap_eq_pointsMap_comp B S hS G 𝒳.val b.hom.hom) y
  simp only [Function.comp_apply] at e1 e2
  obtain ⟨pbar, hbar₁, hbar₂⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Q hQ
    _ _ (e1.symm.trans (hxy.trans e2))
  obtain ⟨zR, hzR⟩ :=
    (bijective_spacePointMap_representing B S hS R Q.pt.val eR).surjective pbar
  have nat₁ := spacePointMap_representing_naturality B S hS R F Q.pt.val
    (algebraicSpaceStack.{u, w} B S hS F hF).val eR
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst.hom zR
  have nat₂ := spacePointMap_representing_naturality B S hS R G Q.pt.val
    (algebraicSpaceStack.{u, w} B S hS G hG).val eR
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom zR
  refine ⟨R, hR, _, _, zR, hr₁, hr₂,
    (spacePointMap_id_bijective B S hS F).injective
      (nat₁.trans ((congrArg (pointsMap B S hS Q.pt.val.val Q.pt.val.property
        (algebraicSpaceStack.{u, w} B S hS F hF).val.property Q.fst.hom.hom) hzR).trans hbar₁)),
    (spacePointMap_id_bijective B S hS G).injective
      (nat₂.trans ((congrArg (pointsMap B S hS Q.pt.val.val Q.pt.val.property
        (algebraicSpaceStack.{u, w} B S hS G hG).val.property Q.snd.hom.hom) hzR).trans hbar₂))⟩

/-- `AlgebraicGeometry.Stack.exists_smooth_common_point_of_square` at the canonical 2-fibre
product square of the two charts (**Stacks 04T2**), whose apex is representable by an algebraic
space because one of the charts has algebraic space source and the other is representable by
algebraic spaces. -/
private theorem exists_smooth_common_point
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) (hb : AlgebraicStacks.IsSmooth B S hS b)
    (x : Space.points B S hS F) (y : Space.points B S hS G)
    (hxy : spacePointMap B S hS F 𝒳.val a.hom.hom x =
      spacePointMap B S hS G 𝒳.val b.hom.hom y) :
    ∃ (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS R)
      (r₁ : R ⟶ F) (r₂ : R ⟶ G) (z : Space.points B S hS R),
      Space.IsSmooth B S hS r₁ ∧ Space.IsSmooth B S hS r₂ ∧
        Space.pointsMap B S hS R r₁ z = x ∧ Space.pointsMap B S hS R r₂ z = y :=
  exists_smooth_common_point_of_square B S hS hF hG a b ha hb
    (twoFibreProductSquareAlgebraicStacks B S hS a b)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a b)
    (isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val _ _ a.hom.hom b.hom.hom
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_fibredCategory B S hS G hG) b.hom)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF))
    x y hxy

/-- **Chart independence.** Two smooth charts of an algebraic stack by schemes, at field-valued
points with the same image in the space of points of the stack, have the same value of a
smooth-local property of germs of schemes.

The two charts are dominated by a common algebraic space smooth over both and carrying a point
over both; an étale scheme chart of that algebraic space through that point (**Stacks 03H5**) is
smooth over both schemes, and smooth locality of `P` is applied along the two resulting smooth
morphisms of schemes. -/
theorem germ_iff_of_smooth_charts {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U V : BigFppfOver B S hS}
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V) ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) (hb : AlgebraicStacks.IsSmooth B S hS b)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U))
    (q : Space.FieldValuedPoint B S hS (yoneda.obj V))
    (hpq : spacePointMap B S hS (yoneda.obj U) 𝒳.val a.hom.hom
        (p.class B S hS (yoneda.obj U)) =
      spacePointMap B S hS (yoneda.obj V) 𝒳.val b.hom.hom (q.class B S hS (yoneda.obj V)))
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsSmoothLocal P) :
    P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩ ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj V, Space.schemePoint B S hS V q⟩ := by
  obtain ⟨R, hR, r₁, r₂, z, hr₁, hr₂, hz₁, hz₂⟩ :=
    exists_smooth_common_point B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) a b ha hb _ _ hpq
  obtain ⟨W, c, hcEt, w, hzW⟩ := exists_etale_chart_point B S hS hR z
  exact (germ_iff_of_smooth_space_map B S hS P hP hR c hcEt r₁ hr₁ w p
      ((congrArg (Space.pointsMap B S hS R r₁) hzW).trans hz₁)).trans
    (germ_iff_of_smooth_space_map B S hS P hP hR c hcEt r₂ hr₂ w q
      ((congrArg (Space.pointsMap B S hS R r₂) hzW).trans hz₂)).symm

/-! ### The four conditions -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (x : points B S hS 𝒳.val.val 𝒳.val.property) (P : GermOfScheme.{u} → Prop)

/-- **Condition (1) of Stacks 04YI.** Every smooth chart of `𝒳` by a scheme has the property `P`
of germs at every one of its field-valued points lying over `x`. -/
abbrev GermPropertyAtEverySchemeChart : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳),
    AlgebraicStacks.IsSmooth B S hS a →
    ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U),
      spacePointMap B S hS (yoneda.obj U) 𝒳.val a.hom.hom
          (p.class B S hS (yoneda.obj U)) = x →
        P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩

/-- **Condition (2) of Stacks 04YI.** Some smooth chart of `𝒳` by a scheme has the property `P`
of germs at some field-valued point lying over `x`. -/
abbrev GermPropertyAtSomeSchemeChart : Prop :=
  ∃ (U : BigFppfOver B S hS)
    (a : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U)),
    AlgebraicStacks.IsSmooth B S hS a ∧
      spacePointMap B S hS (yoneda.obj U) 𝒳.val a.hom.hom
          (p.class B S hS (yoneda.obj U)) = x ∧
        P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩

/-- **Condition (3) of Stacks 04YI.** Every smooth chart of `𝒳` by an algebraic space has
property `P` at every one of its points lying over `x`, in the sense of **Stacks 04RC**. -/
abbrev GermPropertyAtEverySpaceChart : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳),
    AlgebraicStacks.IsSmooth B S hS a →
    ∀ z : Space.points B S hS F,
      spacePointMap B S hS F 𝒳.val a.hom.hom z = x →
        Space.HasPropertyAtPoint B S hS F z P

/-- **Condition (4) of Stacks 04YI.** Some smooth chart of `𝒳` by an algebraic space has
property `P` at some point lying over `x`, in the sense of **Stacks 04RC**. -/
abbrev GermPropertyAtSomeSpaceChart : Prop :=
  ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) (z : Space.points B S hS F),
    AlgebraicStacks.IsSmooth B S hS a ∧
      spacePointMap B S hS F 𝒳.val a.hom.hom z = x ∧
        Space.HasPropertyAtPoint B S hS F z P

/-- **Stacks 04YI.** Let `𝒳` be an algebraic stack over `S`, let `x` be a point of `𝒳`, and let
`P` be a smooth-local property of germs of schemes (**Stacks 04N1**). Then the four conditions
comparing `P` against the smooth charts of `𝒳` through `x` — every scheme chart, some scheme
chart, every algebraic space chart, some algebraic space chart — are equivalent. -/
@[stacks 04YI]
theorem tfae_germProperty_at_point (hP : GermOfScheme.IsSmoothLocal P) :
    [GermPropertyAtEverySchemeChart B S hS 𝒳 x P,
      GermPropertyAtSomeSchemeChart B S hS 𝒳 x P,
      GermPropertyAtEverySpaceChart B S hS 𝒳 x P,
      GermPropertyAtSomeSpaceChart B S hS 𝒳 x P].TFAE := by
  tfae_have 1 → 2 := fun h =>
    let ⟨U, a, p, haSmooth, hax⟩ := exists_smooth_scheme_chart_at_point B S hS 𝒳 x
    ⟨U, a, p, haSmooth, hax, h U a haSmooth p hax⟩
  tfae_have 2 → 4 := fun ⟨U, a, p, haSmooth, hax, hPp⟩ =>
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, a, p.class B S hS (yoneda.obj U),
      haSmooth, hax,
      (hasPropertyAtPoint_yoneda_iff B S hS U p P (isEtaleLocal_of_isSmoothLocal P hP)).mpr hPp⟩
  tfae_have 4 → 3 := by
    rintro ⟨F, hF, a, z, haSmooth, hax, hPz⟩ G hG b hbSmooth y hby
    obtain ⟨U, c, hcEt, p, hcp, hPp⟩ := hPz
    obtain ⟨a', ha'Smooth, ha'pt⟩ := exists_smooth_chart_of_isSmooth_map B S hS
      (isAlgebraicSpace_yoneda B S hS U) hF a haSmooth c
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS c).2 hcEt)
    obtain ⟨V, d, hdEt, q, hyV⟩ := exists_etale_chart_point B S hS hG y
    obtain ⟨b', hb'Smooth, hb'pt⟩ := exists_smooth_chart_of_isSmooth_map B S hS
      (isAlgebraicSpace_yoneda B S hS V) hG b hbSmooth d hdEt
    exact ⟨V, d, (Space.isEtale_iff_presheaf_of_yoneda B S hS d).1 hdEt, q, hyV,
      (germ_iff_of_smooth_charts B S hS a' b' ha'Smooth hb'Smooth p q
        (((ha'pt (p.class B S hS (yoneda.obj U))).trans
          (((congrArg (spacePointMap B S hS F 𝒳.val a.hom.hom) hcp).trans hax).trans
            ((congrArg (spacePointMap B S hS G 𝒳.val b.hom.hom) hyV).trans hby).symm)).trans
          (hb'pt (q.class B S hS (yoneda.obj V))).symm) P hP).mp hPp⟩
  tfae_have 3 → 1 := fun h U a haSmooth p hax =>
    (hasPropertyAtPoint_yoneda_iff B S hS U p P (isEtaleLocal_of_isSmoothLocal P hP)).mp
      (h (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) a haSmooth
        (p.class B S hS (yoneda.obj U)) hax)
  tfae_finish

/-! ### The two addenda: an algebraic space, and a scheme -/

/-- The identity 1-morphism of the algebraic stack of an algebraic space is smooth: it is
representable by algebraic spaces and the morphism of algebraic spaces it induces is the
identity, which is smooth. -/
private theorem isSmooth_id_algebraicSpaceStack
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    AlgebraicStacks.IsSmooth B S hS (𝟙 (algebraicSpaceStack.{u, w} B S hS F hF)) :=
  hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ _ F hF
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (isRelativelySmooth_id B S hS
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF))
    (Space.isSmooth_id B S hS hF)

/-- **Stacks 04YI, the algebraic space addendum.** On the algebraic stack of an algebraic space
`F` over `S` the four conditions say that `F` has property `P` at the corresponding point of `F`,
in the sense of **Stacks 04RC**. The chart realizing the existential condition is the identity. -/
@[stacks 04YI "algebraic space case"]
theorem germPropertyAtSomeSpaceChart_algebraicSpaceStack_iff
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (z : Space.points B S hS F) (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsSmoothLocal P) :
    GermPropertyAtSomeSpaceChart B S hS (algebraicSpaceStack.{u, w} B S hS F hF)
        (spacePointMap B S hS F (fibredCategory B S hS F)
          (BasedFunctor.id (fibredCategory B S hS F).val) z) P ↔
      Space.HasPropertyAtPoint B S hS F z P := by
  refine ⟨fun h => ?_, fun h => ⟨F, hF, 𝟙 _, z,
    isSmooth_id_algebraicSpaceStack.{u, w} B S hS hF, rfl, h⟩⟩
  have key : GermPropertyAtEverySpaceChart B S hS (algebraicSpaceStack.{u, w} B S hS F hF)
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) z) P :=
    ((tfae_germProperty_at_point B S hS (algebraicSpaceStack.{u, w} B S hS F hF)
      (spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) z) P hP).out 4 3).mp h
  exact key F hF (𝟙 _) (isSmooth_id_algebraicSpaceStack.{u, w} B S hS hF) z rfl

/-- **Stacks 04YI, the representable addendum.** On the algebraic stack of a scheme `U` over `S`
the four conditions say that the germ of `U` at the corresponding scheme point has `P`. -/
@[stacks 04YI "representable case"]
theorem germPropertyAtSomeSpaceChart_yoneda_iff (U : BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) (P : GermOfScheme.{u} → Prop)
    (hP : GermOfScheme.IsSmoothLocal P) :
    GermPropertyAtSomeSpaceChart B S hS
        (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U))
        (spacePointMap B S hS (yoneda.obj U) (fibredCategory B S hS (yoneda.obj U))
          (BasedFunctor.id (fibredCategory B S hS (yoneda.obj U)).val)
          (p.class B S hS (yoneda.obj U))) P ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj U, Space.schemePoint B S hS U p⟩ :=
  (germPropertyAtSomeSpaceChart_algebraicSpaceStack_iff.{u, w} B S hS
      (isAlgebraicSpace_yoneda B S hS U) _ P hP).trans
    (hasPropertyAtPoint_yoneda_iff B S hS U p P (isEtaleLocal_of_isSmoothLocal P hP))

/-! ### An algebraic stack with a property of germs at a point -/

/-- **Stacks 04YJ.** Let `P` be a property of germs of schemes which is smooth local (**Stacks
04N1**), let `𝒳` be an algebraic stack over `S` and let `x` be a point of `𝒳` (**Stacks 04XG**).
Then `𝒳` *has property* `P` *at* `x` when some smooth chart of `𝒳` by an algebraic space has
property `P` at some point of it lying over `x`, in the sense of **Stacks 04RC**.

The source defines this by any of the four equivalent conditions of **Stacks 04YI**; this is the
fourth of them, and `AlgebraicGeometry.Stack.tfae_germProperty_at_point` identifies it with the
other three for a smooth-local `P`, which is what makes the choice immaterial. As for **Stacks
04RC**, stating this one condition needs neither that hypothesis nor surjectivity of the chart.
Its specializations are the two addenda above:
`AlgebraicGeometry.Stack.germPropertyAtSomeSpaceChart_algebraicSpaceStack_iff` on the algebraic
stack of an algebraic space and
`AlgebraicGeometry.Stack.germPropertyAtSomeSpaceChart_yoneda_iff` on that of a scheme. -/
@[stacks 04YJ]
abbrev HasPropertyAtPoint : Prop := GermPropertyAtSomeSpaceChart B S hS 𝒳 x P

/-- For a smooth-local property of germs, `𝒳` has `P` at `x` exactly when every smooth chart of
`𝒳` by a scheme has `P` at every one of its field-valued points over `x`: the definition of
**Stacks 04YJ** read against condition (1) of **Stacks 04YI**. -/
theorem hasPropertyAtPoint_iff_germPropertyAtEverySchemeChart
    (hP : GermOfScheme.IsSmoothLocal P) :
    HasPropertyAtPoint B S hS 𝒳 x P ↔ GermPropertyAtEverySchemeChart B S hS 𝒳 x P :=
  (tfae_germProperty_at_point B S hS 𝒳 x P hP).out 4 1

/-- For a smooth-local property of germs, `𝒳` has `P` at `x` exactly when some smooth chart of
`𝒳` by a scheme has `P` at some field-valued point over `x`: the definition of **Stacks 04YJ**
read against condition (2) of **Stacks 04YI**. -/
theorem hasPropertyAtPoint_iff_germPropertyAtSomeSchemeChart
    (hP : GermOfScheme.IsSmoothLocal P) :
    HasPropertyAtPoint B S hS 𝒳 x P ↔ GermPropertyAtSomeSchemeChart B S hS 𝒳 x P :=
  (tfae_germProperty_at_point B S hS 𝒳 x P hP).out 4 2

/-- For a smooth-local property of germs, `𝒳` has `P` at `x` exactly when every smooth chart of
`𝒳` by an algebraic space has `P` at every one of its points over `x`: the definition of **Stacks
04YJ** read against condition (3) of **Stacks 04YI**. -/
theorem hasPropertyAtPoint_iff_germPropertyAtEverySpaceChart
    (hP : GermOfScheme.IsSmoothLocal P) :
    HasPropertyAtPoint B S hS 𝒳 x P ↔ GermPropertyAtEverySpaceChart B S hS 𝒳 x P :=
  (tfae_germProperty_at_point B S hS 𝒳 x P hP).out 4 3

end AlgebraicGeometry.Stack

end
