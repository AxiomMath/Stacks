module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection

/-!
# The chart comparison is the geometric comparison of Stacks 03G8

For a representable morphism `f : X ⟶ Y` of algebraic spaces two isomorphisms with the same
endpoints identify the small étale direct image of sheaves of sets with restriction along base
change of étale scheme charts:

* `AlgebraicGeometry.Space.chartComparison`, the chart projection of the right Kan extension
  form of the direct image, which is the one computable on sections;
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`, which is the geometric
  comparison of Stacks 03G8 transported along the direct-image comparison of the small and
  spaces-étale base-change square.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoChartProjection.lean` record that the two
have the same endpoints and are not identified.  This file identifies them.

## Main results

* `AlgebraicGeometry.Space.chartComparison_hom_app_comparisonRestriction`: on a sheaf of sets
  presented as the restriction of a spaces-étale sheaf along the comparison functor of
  Stacks 03G1, the chart comparison is the geometric comparison of Stacks 03G8 followed by the
  inverse of the base-change square comparison.
* `AlgebraicGeometry.Space.chartComparison_hom_app_of_presentation`: the same for an arbitrary
  presentation of an arbitrary sheaf, which is the form a consumer uses.

## Implementation notes

The quasi-inverse `AlgebraicGeometry.Space.smallEtaleComparisonRanIso` of the comparison
equivalence of Stacks 03G1 is a `CategoryTheory.Adjunction.rightAdjointUniq` and therefore has
no description of its own values; it is used here **only** through the cancellation
`AlgebraicGeometry.Space.ranCounit_comparisonRanIso_app`, which is
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit` read on sections: composed with the
counit of the Kan-extension adjunction it is the counit of the comparison equivalence.  That
counit, at a restricted sheaf, is the inverse unit of the equivalence by
`CategoryTheory.Equivalence.counit_app_functor`, which is what makes the whole comparison
computable although neither factor is.

The remaining steps are naturality of the two comparisons in the site object and the fact that
the structure morphism of the base-changed chart used by
`AlgebraicGeometry.Space.smallBaseChangeIndex` is the comparison of the two base changes, so
that it cancels against the one appearing in the base-change square comparison.

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

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The only use made of the Kan-extension comparison -/

/-- **The quasi-inverse comparison cancels against the counit of the Kan-extension
adjunction.**  `AlgebraicGeometry.Space.smallEtaleComparisonRanIso` followed by the counit of
the Kan-extension adjunction is the counit of the comparison equivalence of Stacks 03G1 — the
defining property of `CategoryTheory.Adjunction.rightAdjointUniq`, read on sections.

This is the only place where that comparison is used; it has no description of its own values,
being built from `Classical.choice`. -/
theorem ranCounit_comparisonRanIso_app (X : AlgebraicSpaces B S hS)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS X.1)
    (b : (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse).obj P).obj.obj
      (op ((comparisonFunctor B S hS X).obj W))) :
    ((comparisonFunctor B S hS X).op.ranCounit.app P.obj).app (op W)
        (((smallEtaleComparisonRanIso B S hS X).hom.app P).hom.app
          (op ((comparisonFunctor B S hS X).obj W)) b) =
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.counit.app P).hom.app
        (op W)) b := by
  have hc : ((((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app P).hom) =
      (comparisonFunctor B S hS X).op.ranCounit.app P.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  rw [← hc]
  exact CategoryTheory.Sheaf.hom_congr_app_apply
    (Adjunction.rightAdjointUniq_hom_app_counit
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
      ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) P) (op W) b

/-- The counit of the comparison equivalence of Stacks 03G1 at a restricted sheaf is the
inverse unit of the equivalence, read on sections. -/
theorem counit_app_comparisonRestriction_app (X : AlgebraicSpaces B S hS)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (W : SmallEtale B S hS X.1)
    (b : (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse).obj
      ((smallEtaleComparisonRestriction B S hS X).obj H)).obj.obj
        (op ((comparisonFunctor B S hS X).obj W))) :
    (((smallEtaleComparisonRestriction B S hS X).asEquivalence.counit.app
          ((smallEtaleComparisonRestriction B S hS X).obj H)).hom.app (op W)) b =
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H).hom.app
        (op ((comparisonFunctor B S hS X).obj W))) b :=
  CategoryTheory.Sheaf.hom_congr_app_apply
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counit_app_functor H) (op W) b

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The two comparisons on sections -/

/-- The chart comparison on sections: the Kan-extension comparison, then restriction along the
comparison of the two base changes, then the counit of the Kan-extension adjunction.  This is
the definition of `AlgebraicGeometry.Space.chartRanApp` with
`AlgebraicGeometry.Space.ranChartCone_π_apply` applied. -/
theorem chartComparison_hom_app_hom_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (((chartComparison B S hS f hf).hom.app P).hom.app (op V)) a =
      ((comparisonFunctor B S hS X).op.ranCounit.app P.obj).app
          (op ((smallBaseChange B S hS f hf).obj V))
        (((comparisonFunctor B S hS X).op.ran.obj P.obj).map
          (smallBaseChangeComparisonIso B S hS f hf V).hom.op
          ((((smallEtaleComparisonRanIso B S hS X).hom.app P).hom.app
            (op (chartBaseChange B S hS f V))) a)) :=
  rfl

/-- The geometric comparison of Stacks 03G8 on sections: the inverse unit of the comparison
equivalence of Stacks 03G1, read over the base-changed spaces-étale chart. -/
theorem smallToposMorphismTypeU_comparison_hom_app_hom_app (f : X ⟶ Y)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((smallEtaleComparisonRestriction B S hS X ⋙
      (smallToposMorphismTypeU B S hS f).pushforward).obj H).obj.obj (op V)) :
    (((smallToposMorphismTypeU_comparison B S hS f).hom.app H).hom.app (op V)) a =
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H).hom.app
        (op (chartBaseChange B S hS f V))) a :=
  rfl

/-- The inverse of the direct-image comparison of the small and spaces-étale base-change square
on sections: restriction along the comparison of the two base changes. -/
theorem smallBaseChange_pushforward_comparisonTypeU_inv_app_hom_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
      smallEtaleComparisonRestriction B S hS Y).obj H).obj.obj (op V)) :
    (((smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H).hom.app (op V)) a =
      H.obj.map (smallBaseChangeComparisonIso B S hS f hf V).hom.op a :=
  rfl

/-! ### The identification -/

/-- **The chart comparison is the geometric comparison, on sections.**  For a sheaf of sets
presented as the restriction of a spaces-étale sheaf `H` along the comparison functor of
Stacks 03G1, the chart comparison reads a section of the direct image over an étale chart `V`
of `Y` as the inverse unit of the comparison equivalence, restricted along the comparison of
the two base changes of `V`. -/
theorem chartComparison_hom_app_comparisonRestriction_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) (V : SmallEtale B S hS Y.1)
    (a : ((smallEtaleDirectImage B S hS f).obj
      ((smallEtaleComparisonRestriction B S hS X).obj H)).obj.obj (op V)) :
    (((chartComparison B S hS f hf).hom.app
          ((smallEtaleComparisonRestriction B S hS X).obj H)).hom.app (op V)) a =
      H.obj.map (smallBaseChangeComparisonIso B S hS f hf V).hom.op
        ((((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app
          H).hom.app (op (chartBaseChange B S hS f V))) a) := by
  refine Eq.trans (chartComparison_hom_app_hom_app B S hS f hf
    ((smallEtaleComparisonRestriction B S hS X).obj H) V a) ?_
  have hnat := NatTrans.naturality_apply
    ((smallEtaleComparisonRanIso B S hS X).hom.app
      ((smallEtaleComparisonRestriction B S hS X).obj H)).hom
    (smallBaseChangeComparisonIso B S hS f hf V).hom.op a
  refine Eq.trans (congrArg
    (fun y ↦ ((comparisonFunctor B S hS X).op.ranCounit.app
        ((smallEtaleComparisonRestriction B S hS X).obj H).obj).app
        (op ((smallBaseChange B S hS f hf).obj V)) y) hnat.symm) ?_
  refine Eq.trans (ranCounit_comparisonRanIso_app B S hS X
    ((smallEtaleComparisonRestriction B S hS X).obj H)
    ((smallBaseChange B S hS f hf).obj V) _) ?_
  refine Eq.trans (counit_app_comparisonRestriction_app B S hS X H
    ((smallBaseChange B S hS f hf).obj V) _) ?_
  exact NatTrans.naturality_apply
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.inv.app H).hom
    (smallBaseChangeComparisonIso B S hS f hf V).hom.op a

/-- **The chart comparison is the geometric comparison of Stacks 03G8.**  On a sheaf of sets
presented as the restriction of a spaces-étale sheaf along the comparison functor of
Stacks 03G1, `AlgebraicGeometry.Space.chartComparison` is the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison` followed by the inverse of the
direct-image comparison
`AlgebraicGeometry.Space.smallBaseChange_pushforward_comparisonTypeU` of the small and
spaces-étale base-change square.

This identifies the two isomorphisms with the same endpoints that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoChartProjection.lean` record as
unidentified; the corollary at an arbitrary presentation is
`AlgebraicGeometry.Space.chartComparison_hom_app_of_presentation`. -/
theorem chartComparison_hom_app_comparisonRestriction (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (chartComparison B S hS f hf).hom.app
        ((smallEtaleComparisonRestriction B S hS X).obj H) =
      (smallToposMorphismTypeU_comparison B S hS f).hom.app H ≫
        (smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H :=
  by
  refine CategoryTheory.Sheaf.hom_ext_sections (fun V a ↦ ?_)
  refine (chartComparison_hom_app_comparisonRestriction_apply B S hS f hf H V.unop a).trans ?_
  refine Eq.trans (congrArg (H.obj.map
      (smallBaseChangeComparisonIso B S hS f hf V.unop).hom.op)
    (smallToposMorphismTypeU_comparison_hom_app_hom_app B S hS f H V.unop a).symm) ?_
  exact (smallBaseChange_pushforward_comparisonTypeU_inv_app_hom_app B S hS f hf H V.unop _).symm

/-- **The chart comparison at an arbitrary presentation.**  For any sheaf of sets `P` on the
small étale site of `X` and any isomorphism of it with the restriction of a spaces-étale sheaf
`H` along the comparison functor of Stacks 03G1, the chart comparison transported along that
presentation is the geometric comparison of Stacks 03G8 followed by the inverse base-change
square comparison.

This is `AlgebraicGeometry.Space.chartComparison_hom_app_comparisonRestriction` with
naturality of the chart comparison, in the shape in which
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison` is stated. -/
theorem chartComparison_hom_app_of_presentation (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (e : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H) :
    (chartComparison B S hS f hf).hom.app P ≫
        ((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).map e.hom =
      (smallEtaleDirectImage B S hS f).map e.hom ≫
        (smallToposMorphismTypeU_comparison B S hS f).hom.app H ≫
          (smallBaseChange_pushforward_comparisonTypeU B S hS f hf).inv.app H := by
  refine Eq.trans ((chartComparison B S hS f hf).hom.naturality e.hom).symm ?_
  exact congrArg (fun m ↦ (smallEtaleDirectImage B S hS f).map e.hom ≫ m)
    (chartComparison_hom_app_comparisonRestriction B S hS f hf H)

end AlgebraicGeometry.Space

end
