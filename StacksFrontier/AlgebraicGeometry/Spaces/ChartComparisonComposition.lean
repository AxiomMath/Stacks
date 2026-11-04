module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonGeometric
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeComparisonCocycle

/-!
# The chart comparison of sheaves of sets is compatible with composition

For representable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces,
`AlgebraicGeometry.Space.chartComparison` identifies the small étale direct image of sheaves of
sets with restriction along base change of étale scheme charts.  This file proves that those
identifications are compatible with composition: the composite of the two comparisons, followed
by the composition comparison of the chart base changes, is the composition comparison of
Stacks 03G2, part (3) followed by the comparison of the composite.

## Main results

* `AlgebraicGeometry.Space.chartComparison_comp`: the composition law.
* `AlgebraicGeometry.Space.natTrans_eq_of_app_comparisonRestriction`: two natural
  transformations out of a functor on the small étale topos agree once they agree on the
  restrictions of spaces-étale sheaves.
* `AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU_comp`: the base-change
  square comparison composes, on restriction of sheaves.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

universe v₁ u₁

/-- A threefold restriction of sections equals a twofold one when the underlying composites of
morphisms agree. -/
theorem presheafMap_three_eq_two {D : Type u₁} [Category.{v₁} D] (H : Dᵒᵖ ⥤ Type u)
    {A₁ A₂ A₃ A₄ A₅ : D} (q₃ : A₁ ⟶ A₂) (q₂ : A₂ ⟶ A₃) (q₁ : A₃ ⟶ A₄) (q₅ : A₁ ⟶ A₅)
    (q₄ : A₅ ⟶ A₄) (h : q₃ ≫ q₂ ≫ q₁ = q₅ ≫ q₄) (a : H.obj (op A₄)) :
    H.map q₃.op (H.map q₂.op (H.map q₁.op a)) = H.map q₅.op (H.map q₄.op a) := by
  simpa only [op_comp, Functor.map_comp_apply] using congrArg (fun q ↦ H.map q.op a) h

/-- In a category, if `xu = x ≫ u`, `u ≫ c = cy ≫ w`, `cy = v ≫ d`, `d ≫ w ≫ r = s ≫ t` and
`x ≫ v ≫ s = k ≫ n`, then `xu ≫ c ≫ r = k ≫ n ≫ t`. -/
theorem assembleCompLaw {Q : Type u₁} [Category.{v₁} Q]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : Q} (xu : O₁ ⟶ O₃) (x : O₁ ⟶ O₂) (u : O₂ ⟶ O₃)
    (c : O₃ ⟶ O₅) (r : O₅ ⟶ O₆) (cy : O₂ ⟶ O₄) (w : O₄ ⟶ O₅) (v : O₂ ⟶ O₇)
    (d : O₇ ⟶ O₄) (s : O₇ ⟶ O₈) (t : O₈ ⟶ O₆) (k : O₁ ⟶ O₉) (n : O₉ ⟶ O₈)
    (h1 : xu = x ≫ u) (h2 : u ≫ c = cy ≫ w) (h3 : cy = v ≫ d)
    (h4 : d ≫ w ≫ r = s ≫ t) (h5 : x ≫ v ≫ s = k ≫ n) :
    xu ≫ c ≫ r = k ≫ n ≫ t := by
  rw [h1, Category.assoc, ← Category.assoc u, h2, h3]
  simp only [Category.assoc]
  rw [h4, ← Category.assoc v s t, ← Category.assoc x (v ≫ s) t, h5, Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two natural transformations out of a functor on the sheaves of sets on the small étale site of
`X` agree as soon as they agree on the restrictions of spaces-étale sheaves along the comparison
functor of Stacks 03G1. -/
theorem natTrans_eq_of_app_comparisonRestriction (X : AlgebraicSpaces B S hS) {D : Type u₁}
    [Category.{v₁} D] {Φ Ψ : Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤ D} (α β : Φ ⟶ Ψ)
    (h : ∀ H : Sheaf (SpacesEtale.topology B S hS X) (Type u),
      α.app ((smallEtaleComparisonRestriction B S hS X).obj H) =
        β.app ((smallEtaleComparisonRestriction B S hS X).obj H)) :
    α = β := by
  refine NatTrans.ext (funext fun P ↦ ?_)
  have hα := α.naturality (comparisonRanPresentation B S hS X P).hom
  have hβ := β.naturality (comparisonRanPresentation B S hS X P).hom
  rw [h ((smallEtaleComparisonRan B S hS X).obj P)] at hα
  exact (Iso.cancel_iso_hom_right _ _ (Ψ.mapIso (comparisonRanPresentation B S hS X P))).mp
    (hα.symm.trans hβ)

variable {X Y Z : AlgebraicSpaces B S hS}

/-! ### The cocycle for the base-change square comparison, on sections -/

/-- The composition comparison of restriction along base change of étale scheme charts, read on
sections: restriction along the inverse of `AlgebraicGeometry.Space.smallBaseChange_comp`. -/
theorem sheafPushforwardContinuousComp'_smallBaseChange_comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (M : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Z.1)
    (a : ((((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)) ⋙
      ((smallBaseChange B S hS g hg).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1))).obj M).obj.obj
        (op V)) :
    (((Functor.sheafPushforwardContinuousComp'
          (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
          (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1)).hom.app M).hom.app (op V)) a =
      M.obj.map ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V).op a :=
  rfl

/-- The composition comparison of restriction along spaces-étale base change, read on
sections. -/
theorem spacesBaseChange_pushforward_compTypeU_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (W : SpacesEtale B S hS Z)
    (a : ((((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)) ⋙
      ((spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y))).obj H).obj.obj
        (op W)) :
    (((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app H).hom.app (op W)) a =
      H.obj.map ((spacesBaseChange_comp B S hS f g).inv.app W).op a :=
  rfl

/-- The two base-change square comparisons of `f` and `g`, composed with the composition comparison
of the chart base changes, agree on the restriction of a spaces-étale sheaf with the composition
comparison of the spaces-étale base changes followed by the base-change square comparison of
`f ≫ g`. -/
theorem smallBaseChange_pushforward_comparisonTypeU_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (smallBaseChange_pushforward_comparisonTypeU B S hS g hg).inv.app
          (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H) ≫
        ((smallBaseChange B S hS g hg).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)).map
          ((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H) ≫
        (Functor.sheafPushforwardContinuousComp'
            (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
            (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
            (SmallEtale.topology B S hS X.1)).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H) =
      (smallEtaleComparisonRestriction B S hS Z).map
          ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app H) ≫
        (smallBaseChange_pushforward_comparisonTypeU B S hS (f ≫ g) hfg).inv.app H :=
  CategoryTheory.Sheaf.hom_ext_sections fun V a ↦ presheafMap_three_eq_two H.obj
    ((comparisonFunctor B S hS X).map
      ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app V.unop))
    ((smallBaseChange_comparison B S hS f hf).hom.app
      ((smallBaseChange B S hS g hg).obj V.unop))
    ((spacesBaseChange B S hS f).functor.map
      ((smallBaseChange_comparison B S hS g hg).hom.app V.unop))
    ((smallBaseChange_comparison B S hS (f ≫ g) hfg).hom.app V.unop)
    ((spacesBaseChange_comp B S hS f g).inv.app ((comparisonFunctor B S hS Z).obj V.unop))
    (smallBaseChange_comparison_comp B S hS f g hf hg hfg V.unop) a

/-! ### The composition law -/

/-- The composition law at a sheaf presented as the restriction of a spaces-étale sheaf along
the comparison functor of Stacks 03G1. -/
theorem chartComparison_comp_app_comparisonRestriction (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (smallEtaleDirectImage B S hS g).map
          ((chartComparison B S hS f hf).hom.app
            ((smallEtaleComparisonRestriction B S hS X).obj H)) ≫
        (chartComparison B S hS g hg).hom.app
          (((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
            ((smallEtaleComparisonRestriction B S hS X).obj H)) ≫
        (Functor.sheafPushforwardContinuousComp'
            (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
            (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
            (SmallEtale.topology B S hS X.1)).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H) ≫
        (chartComparison B S hS (f ≫ g) hfg).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H) := by
  rw [chartComparison_hom_app_comparisonRestriction B S hS f hf H,
    chartComparison_hom_app_comparisonRestriction B S hS (f ≫ g) hfg H]
  exact assembleCompLaw _
    ((smallEtaleDirectImage B S hS g).map
      ((smallToposMorphismTypeU_comparison B S hS f).hom.app H))
    ((smallEtaleDirectImage B S hS g).map
      ((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H))
    _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Functor.map_comp (smallEtaleDirectImage B S hS g)
      ((smallToposMorphismTypeU_comparison B S hS f).hom.app H)
      ((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H))
    ((chartComparison B S hS g hg).hom.naturality
      ((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H))
    (chartComparison_hom_app_comparisonRestriction B S hS g hg
      (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj H))
    (smallBaseChange_pushforward_comparisonTypeU_comp B S hS f g hf hg hfg H)
    (smallToposMorphismTypeU_comp_comparison B S hS f g H)

/-- The chart comparison of sheaves of sets is compatible with composition: for representable
`f : X ⟶ Y` and `g : Y ⟶ Z`, the composite of the identifications of the small étale direct images
with restriction along base change of étale scheme charts, followed by the composition comparison
of the chart base changes, is the composition comparison of Stacks 03G2, part (3) followed by the
identification attached to `f ≫ g`. -/
theorem chartComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    Functor.whiskerRight (chartComparison B S hS f hf).hom
            (smallEtaleDirectImage B S hS g) ≫
          Functor.whiskerLeft ((smallBaseChange B S hS f hf).sheafPushforwardContinuous
              (Type u) (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1))
            (chartComparison B S hS g hg).hom ≫
        (Functor.sheafPushforwardContinuousComp'
          (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
          (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1)).hom =
      (smallToposMorphismTypeU_comp B S hS f g).hom ≫
        (chartComparison B S hS (f ≫ g) hfg).hom :=
  natTrans_eq_of_app_comparisonRestriction B S hS X _ _
    (chartComparison_comp_app_comparisonRestriction B S hS f g hf hg hfg)

end AlgebraicGeometry.Space

end
