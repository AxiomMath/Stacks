module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionReindex

/-!
# Reindexing the transition morphism of Stacks 06WT into a common target

`AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition` computes the
reindexing of the transition morphism `α` of Stacks 06WT along `a : P ⟶ R` through two comparison
maps of equation 076R landing in `(x ∘ s ∘ a)^*ℱ|_{P_étale}`.  To compare reindexings along
several morphisms `P ⟶ R` (as the cocycle condition of Stacks 0441 requires) the comparison maps
must land in one module.  This file redoes the computation with the target `(x ∘ s ∘ a)` replaced
by any 1-morphism `π : 𝒮_P ⟶ [U/R]` together with a vertical 2-isomorphism
`ψ : x ∘ s ∘ a ≅ π`.

## Main definitions

* `AlgebraicGeometry.Stack.twistedTargetComparison` and
  `AlgebraicGeometry.Stack.twistedSourceComparison`: the comparison maps
  `(a ≫ t)^*𝒢 ⟶ π^*ℱ|_{P_étale} ⟵ (a ≫ s)^*𝒢`.

## Main results

* `AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition_twisted`: the
  reindexed transition morphism followed by the second comparison map is the first.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  {P : AlgebraicSpaces C S hS} (a : P ⟶ G.arrows)
  (π : (fibredCategory C S hS P.obj).val.obj ⥤ (quotientStack G).obj)
  (hπ : (fibredCategory C S hS P.obj).val.p.IsFibredOneMorphism (quotientStack G).p π)
  (ψ : reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G) ≅ π)
  (hψ : ∀ X, (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj (π.obj X)))
    (ψ.inv.app X))

/-- The 2-isomorphism `x ∘ t ∘ a ≅ π`: the inverse of the 2-morphism of Stacks 044S whiskered by
`a`, followed by `ψ`. -/
noncomputable abbrev twistedTargetIso :
    (reindexLeg G a ⋙ quotientStackTargetLeg G) ⋙ quotientStackProj G ≅ π :=
  Functor.isoWhiskerLeft (reindexLeg G a) (quotientStackTwoArrowIso G) ≪≫ ψ

include hψ in
/-- The components of `twistedTargetIso` lie over identities. -/
theorem isHomLift_twistedTargetIso (X : (fibredCategory C S hS P.obj).val.obj) :
    (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj (π.obj X)))
      ((twistedTargetIso G a π ψ).inv.app X) := by
  have := hψ X
  have := isHomLift_quotientStackTwoArrowNat G ((reindexLeg G a).obj X)
  exact IsHomLift.comp_lift_id_right' (p := (quotientStack G).p) _ (ψ.inv.app X)
    ((quotientStack G).p.obj ((quotientStackSourceLeg G ⋙ quotientStackProj G).obj
      ((reindexLeg G a).obj X)))
    ((quotientStackTwoArrowNat G).app ((reindexLeg G a).obj X))

variable (F : QuotientStackModules G) (hF : F.IsQuasicoherentOnSite)

/-- The comparison map `a^*((x ∘ s)^*ℱ|_{R_étale}) ⟶ π^*ℱ|_{P_étale}` of equation 076R of the
triangle through `a`, carried by `ψ`. -/
noncomputable abbrev twistedArrowComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.arrows.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (reindexLeg G a) π (quotientStackSourceLeg G ⋙ quotientStackProj G)
    hπ (isFibredOneMorphism_quotientStackSourceProj G)
    ψ a (reindexChartIso G a) (isFiberedInGroupoids_quotientStack G)
    hψ (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison map `(a ≫ t)^*𝒢 ⟶ π^*ℱ|_{P_étale}` of equation 076R of the triangle through
`t ∘ a`, carried by `twistedTargetIso`. -/
noncomputable abbrev twistedTargetComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a ⋙ quotientStackTargetLeg G) π (quotientStackProj G)
    hπ (isFibredOneMorphism_quotientStackProj G)
    (twistedTargetIso G a π ψ) (a ≫ G.target)
    (reindexTargetChartIso G a) (isFiberedInGroupoids_quotientStack G)
    (isHomLift_twistedTargetIso G a π ψ hψ)
    (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison map `(a ≫ s)^*𝒢 ⟶ π^*ℱ|_{P_étale}` of equation 076R of the triangle through
`s ∘ a`, carried by `ψ`. -/
noncomputable abbrev twistedSourceComparison :=
  Space.comparisonAlgebraicSpacesModules C S hS (fibredCategory C S hS P.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a ⋙ quotientStackSourceLeg G) π (quotientStackProj G)
    hπ (isFibredOneMorphism_quotientStackProj G)
    ψ (a ≫ G.source)
    (reindexSourceChartIso G a) (isFiberedInGroupoids_quotientStack G)
    hψ (fun _ => IsHomLift.id rfl) ((quotientStackToEtale G).obj F)

/-- The comparison morphisms of the triangle through `t ∘ a` are the composites of those of the
triangle through `a` and of the triangle through `t`. -/
theorem twistedTarget_comparisonMorphism_comp {U₀ : Space.SmallEtale C S hS P.obj}
    {V₀ : Space.SmallEtale C S hS G.arrows.obj} {W₀ : Space.SmallEtale C S hS G.objects.obj}
    (x : (Space.SmallEtale.toOver C S hS P.obj).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀)
    (y : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (hx : U₀.1.hom ≫ a.hom = yoneda.map x ≫ V₀.1.hom)
    (hy : V₀.1.hom ≫ G.target.hom = yoneda.map y ≫ W₀.1.hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G a ⋙ quotientStackTargetLeg G) π (quotientStackProj G)
        (twistedTargetIso G a π ψ) (a ≫ G.target)
        (reindexTargetChartIso G a) (Space.ChartDiagram.comp C S hS a G.target x y hx hy) =
      Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
          (fibredCategory C S hS G.arrows.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (reindexLeg G a) π (quotientStackSourceLeg G ⋙ quotientStackProj G) ψ a
          (reindexChartIso G a) ⟨U₀, V₀, x, hx⟩ ≫
        Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
          (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
          (quotientStackTargetLeg G)
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
          (quotientStackTwoArrowIso G) G.target (quotientStackTargetChartIso G)
          ⟨V₀, W₀, y, hy⟩ := by
  simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexTargetChartIso,
    reindexChartIso, quotientStackTargetChartIso, quotientStackTwoArrowIso, Iso.refl_hom,
    NatTrans.id_app, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, asIso_hom, Category.assoc]
  congr 1
  rw [← Category.assoc, (quotientStackTwoArrowNat G).naturality, Category.assoc]
  congr 1
  rw [Functor.comp_map, ← Functor.map_comp]
  congr 1
  exact fibredCategory_hom_ext _ _ rfl

/-- The comparison morphisms of the triangle through `s ∘ a` are the composites of those of the
triangle through `a` and of the triangle through `s`. -/
theorem twistedSource_comparisonMorphism_comp {U₀ : Space.SmallEtale C S hS P.obj}
    {V₀ : Space.SmallEtale C S hS G.arrows.obj} {W₀ : Space.SmallEtale C S hS G.objects.obj}
    (x : (Space.SmallEtale.toOver C S hS P.obj).obj U₀ ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀)
    (y : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V₀ ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W₀)
    (hx : U₀.1.hom ≫ a.hom = yoneda.map x ≫ V₀.1.hom)
    (hy : V₀.1.hom ≫ G.source.hom = yoneda.map y ≫ W₀.1.hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G a ⋙ quotientStackSourceLeg G) π (quotientStackProj G)
        ψ (a ≫ G.source)
        (reindexSourceChartIso G a) (Space.ChartDiagram.comp C S hS a G.source x y hx hy) =
      Space.comparisonMorphism C S hS (fibredCategory C S hS P.obj).val.p
          (fibredCategory C S hS G.arrows.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (reindexLeg G a) π (quotientStackSourceLeg G ⋙ quotientStackProj G) ψ a
          (reindexChartIso G a) ⟨U₀, V₀, x, hx⟩ ≫
        Space.comparisonMorphism C S hS (fibredCategory C S hS G.arrows.obj).val.p
          (fibredCategory C S hS G.objects.obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
          (quotientStackSourceLeg G)
          (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
          (Iso.refl _) G.source (quotientStackSourceChartIso G)
          ⟨V₀, W₀, y, hy⟩ := by
  simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexSourceChartIso,
    reindexChartIso, quotientStackSourceChartIso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.assoc]
  congr 1
  rw [Functor.comp_map, ← Functor.map_comp]
  refine congrArg (quotientStackProj G).map (fibredCategory_hom_ext _ _ ?_)
  exact (by simp : 𝟙 _ ≫ (x ≫ y) = (𝟙 _ ≫ x) ≫ (𝟙 _ ≫ y))

/-- **The composition law through the target**: `a^*(c_t) ≫ c_a` is the comparison of
Stacks 03LU followed by the comparison through `t ∘ a`. -/
theorem modulePullback_map_targetComparison_comp_twisted :
    (Space.modulePullback C S hS a).map (quotientStackTargetComparison G F) ≫
        twistedArrowComparison G a π hπ ψ hψ F =
      (Space.modulePullbackCompIso C S hS a G.target).hom.app _ ≫
        twistedTargetComparison G a π hπ ψ hψ F :=
  Space.comparisonAlgebraicSpacesModules_comp C S hS
    (fibredCategory C S hS P.obj).val.p (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a) (quotientStackTargetLeg G) (reindexLeg G a ⋙ quotientStackTargetLeg G)
    π (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
    hπ (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G)
    ψ (quotientStackTwoArrowIso G) (twistedTargetIso G a π ψ)
    a G.target (reindexChartIso G a) (quotientStackTargetChartIso G) (reindexTargetChartIso G a)
    (isFiberedInGroupoids_quotientStack G) hψ
    (isHomLift_quotientStackTwoArrowNat G)
    (isHomLift_twistedTargetIso G a π ψ hψ)
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl)
    (fun x y hx hy => twistedTarget_comparisonMorphism_comp G a π ψ x y hx hy) _

/-- **The composition law through the source**: `a^*(c_s) ≫ c_a` is the comparison of
Stacks 03LU followed by the comparison through `s ∘ a`. -/
theorem modulePullback_map_sourceComparison_comp_twisted :
    (Space.modulePullback C S hS a).map (quotientStackSourceComparison G F) ≫
        twistedArrowComparison G a π hπ ψ hψ F =
      (Space.modulePullbackCompIso C S hS a G.source).hom.app _ ≫
        twistedSourceComparison G a π hπ ψ hψ F :=
  Space.comparisonAlgebraicSpacesModules_comp C S hS
    (fibredCategory C S hS P.obj).val.p (fibredCategory C S hS G.arrows.obj).val.p
    (fibredCategory C S hS G.objects.obj).val.p (quotientStack G).p
    (fibredCategory C S hS P.obj).property (fibredCategory C S hS G.arrows.obj).property
    (fibredCategory C S hS G.objects.obj).property
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS P.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.arrows.obj).val.p)
    (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
    (reindexLeg G a) (quotientStackSourceLeg G) (reindexLeg G a ⋙ quotientStackSourceLeg G)
    π (quotientStackSourceLeg G ⋙ quotientStackProj G) (quotientStackProj G)
    hπ (isFibredOneMorphism_quotientStackSourceProj G)
    (isFibredOneMorphism_quotientStackProj G)
    ψ (Iso.refl _) ψ
    a G.source (reindexChartIso G a) (quotientStackSourceChartIso G) (reindexSourceChartIso G a)
    (isFiberedInGroupoids_quotientStack G) hψ
    (fun _ => IsHomLift.id rfl) hψ
    (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl) (fun _ => IsHomLift.id rfl)
    (fun x y hx hy => twistedSource_comparisonMorphism_comp G a π ψ x y hx hy) _

include hF in
/-- **The reindexed transition morphism, into a common target.**  For a quasi-coherent `ℱ` on
`[U/R]`, `a : P ⟶ R` and a vertical 2-isomorphism `ψ : x ∘ s ∘ a ≅ π`, the reindexing of the
transition morphism of Stacks 06WT along `a`, followed by the comparison map through `s ∘ a`
(carried by `ψ`), is the comparison map through `t ∘ a`. -/
theorem groupoidPullbackTransition_quotientStackTransition_twisted :
    Space.groupoidPullbackTransition C S hS G _ (quotientStackTransition G F hF) a ≫
        twistedSourceComparison G a π hπ ψ hψ F =
      twistedTargetComparison G a π hπ ψ hψ F :=
  Space.groupoidPullbackTransition_comp_eq G a
    (modulePullback_map_sourceComparison_comp_twisted G a π hπ ψ hψ F)
    (modulePullback_map_targetComparison_comp_twisted G a π hπ ψ hψ F) _
    (quotientStackTransition_comp_sourceComparison G F hF)

end AlgebraicGeometry.Stack

end
