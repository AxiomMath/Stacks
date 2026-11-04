module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.EtaleLocalSolutionComparison

/-!
# The two geometric fibres of step (3) of Stacks 04I6, in coordinates

Step (3) of the proof of [Stacks Project, Tag 04I6] compares, at a geometric point `x̄` of `X`, the
fibre of `g⁻¹h_V` with the fibre of `h_{X ×_Y V}`.  Both fibres have been computed as solution
sets of the system `P` presenting the affine étale chart `V` of an affine `Y`:
`AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions` computes the lifts of a geometric
point to `V` as the solutions in the étale local ring there, and
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions` computes the lifts of `x̄` to
`X ×_Y V` as the solutions in `𝒪^{ét}_{X,x̄}`.

Both computations are composites of three isomorphisms, and neither says what the *coordinates* of
the solution attached to a lift are.  This file says it, for each:

* a lift `u` of `s̄` to `V` goes to the tuple of **germs at `(V, u)` of the coordinate functions**
  `AlgebraicGeometry.presCoord` of the presentation;
* a lift `v` of `x̄` to `X ×_Y V` goes to the tuple of germs at `(X ×_Y V, v)` of those same
  coordinate functions **pulled back along the projection** `X ×_Y V ⟶ V`.

That is what identifies the fibre of `AlgebraicGeometry.comparisonSheafHom` with the solution-set
map of [Stacks Project, Tag 04GX]: the fibre of a morphism of sheaves carries the germ of a
section to the germ of its image (`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`'s
naturality), the section here is the identity of the chart, and
`AlgebraicGeometry.toScheme_map_comparisonChartHom_comp_baseChangeProj` says that the comparison
followed by the projection is `AlgebraicGeometry.comparisonSchemeHom`, whose ring map on global
functions is `AlgebraicGeometry.comparisonRingHom`.

## Main results

* `AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions_coe` — the coordinates of the
  solution attached to a lift of a geometric point to an affine chart are the germs of the
  coordinate functions of the presentation.
* `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_coe` — the coordinates of the
  solution attached to a lift of a geometric point of `X` to the base-changed chart `X ×_Y V` are
  the germs of the coordinate functions pulled back along the projection to `V`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-! ### The fibre of the representable sheaf of an affine chart -/

/-- The inverse of the stalk-comparison equivalence sends a lift `u` to the germ of the identity
section. -/
private theorem yonedaCompEtaleStalkPresheafFunctorIso_app_toEquiv_symm (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) (V : SmallEtale B S hS)
    (u : (geometricPointSitePoint B S hS s).fiber.obj V) :
    ((yonedaCompEtaleStalkPresheafFunctorIso B S hS s).app V).toEquiv.symm u =
      (geometricPointSitePoint B S hS s).toPresheafFiber V u
        ((SmallEtale.topology B S hS).yoneda.obj V).obj (CategoryStruct.id V) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.symm ?_
  refine (smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm B S hS s V
    (Functor.elementsMk (geometricPointFiber B S hS s) V u) (CategoryStruct.id V)).trans ?_
  exact (geometricPointFiber B S hS s).map_id_apply V u

section Source

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  [IsAffine S] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)}

/-- **The solution attached to a lift of a geometric point is the tuple of germs of the coordinate
functions.**  Under
`AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions` — the identification of the lifts
of `s̄` to an affine étale chart `V` with the solutions of a presentation of `V` in the étale local
ring `𝒪^{ét}_{S,s̄}` — a lift `u` goes to the tuple whose `i`-th entry is the germ at `(V, u)` of
the `i`-th coordinate function `AlgebraicGeometry.presCoord` of the presentation.

The three isomorphisms composing that identification are each evaluated at the germ of the
*identity* morphism of `V`, which is the section of `h_V` over `V` that the lift `u` names:
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm` carries that
germ to `u`, `Stacks.EtaleCohomology.representableIsoSolutionPresheaf` carries the identity to the
tuple of coordinate functions, and
`AlgebraicGeometry.geometricFiberSolutionsDesc_toPresheafFiber` takes germs coordinatewise. -/
theorem geometricPointFiberEquivEtaleLocalSolutions_coe (V : SmallEtale B S hS)
    [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
    (pres : StandardPresentationOver ((SmallEtale.toScheme B S hS).obj V)
      (schemeStructureHom B S hS V) P)
    (u : (geometricPointSitePoint B S hS s).fiber.obj V) (i : Fin n) :
    (geometricPointFiberEquivEtaleLocalSolutions B S hS s V pres u).1 i =
      etaleLocalRingGerm B S hS s V u (presCoord B hS V pres i) := by
  have hsymm := yonedaCompEtaleStalkPresheafFunctorIso_app_toEquiv_symm B S hS s V u
  have hval : (geometricPointFiberEquivEtaleLocalSolutions B S hS s V pres u) =
      geometricFiberSolutionsEquiv B S hS s P
        ((geometricPointSitePoint B S hS s).presheafFiber.map
          (representableIsoSolutionPresheaf B S hS V pres).hom
          (((yonedaCompEtaleStalkPresheafFunctorIso B S hS s).app V).toEquiv.symm u)) := rfl
  rw [hval, hsymm,
    (geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply
      (representableIsoSolutionPresheaf B S hS V pres).hom V u (CategoryStruct.id V)]
  refine (congrArg (fun z : EtaleLocalSolutions B S hS s P => z.1 i)
    (geometricFiberSolutionsDesc_toPresheafFiber B S hS s P V u
      (siteHomEquivSolutions B S hS V pres V (CategoryStruct.id V)))).trans ?_
  refine congrArg (etaleLocalRingGerm B S hS s V u) ?_
  change (homOverEquivSolutions ((SmallEtale.toScheme B S hS).obj V)
      ((SmallEtale.toScheme B S hS).obj V) (schemeStructureHom B S hS V)
      (schemeStructureHom B S hS V) P pres
      (homEquivOver B S hS V V (CategoryStruct.id V))).1 i = _
  rw [homOverEquivSolutions_apply_coe, homEquivOver_apply_coe, CategoryTheory.Functor.map_id,
    Scheme.Hom.id_appTop, Category.comp_id]
  rfl

end Source

/-! ### The fibre of the representable sheaf of the base-changed chart -/

section BaseChange

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property)
  [IsAffine Y.obj] [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}

/-- **The solution attached to a lift of a geometric point of `X` to `X ×_Y V` is the tuple of
germs of the coordinate functions pulled back along the projection.**  Under
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions` — the identification of the lifts
of a geometric point `x̄` of `X` to `X ×_Y V` with the solutions of the system presenting `V` in
`𝒪^{ét}_{X,x̄}` — a lift `v` goes to the tuple whose `i`-th entry is the germ at `(X ×_Y V, v)` of
the image of the `i`-th coordinate function `AlgebraicGeometry.presCoord` under the projection
`AlgebraicGeometry.SmallEtale.baseChangeProj`.

This is the same computation as
`AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions_coe`, run on the chart `X ×_Y V`
of `X`: the section of `h_{X ×_Y V}` that `v` names is the identity of `X ×_Y V`, and
`AlgebraicGeometry.SmallEtale.baseChangeHomEquiv` sends it to the projection. -/
theorem baseChangeGeometricPointFiberEquivSolutions_coe
    (pres : StandardPresentationOver ((SmallEtale.toScheme B Y.obj Y.property).obj V)
      (schemeStructureHom B Y.obj Y.property V) P)
    (x : GeometricPoint X.obj)
    (v : (geometricPointSitePoint B X.obj X.property x).fiber.obj
      ((smallEtaleBaseChange B f).obj V)) (i : Fin n) :
    (baseChangeGeometricPointFiberEquivSolutions B f V pres x v).1 i =
      etaleLocalRingGerm B X.obj X.property x ((smallEtaleBaseChange B f).obj V) v
        ((SmallEtale.baseChangeProj B f V).appTop.hom (presCoord B Y.property V pres i)) := by
  have hsymm := yonedaCompEtaleStalkPresheafFunctorIso_app_toEquiv_symm B X.obj X.property x
    ((smallEtaleBaseChange B f).obj V) v
  have hval : (baseChangeGeometricPointFiberEquivSolutions B f V pres x v).1 =
      (geometricFiberSolutionsEquiv B X.obj X.property x
        (baseChangePresentationSystem B f (P := P))
        ((geometricPointSitePoint B X.obj X.property x).presheafFiber.map
          (baseChangeRepresentableIsoSolutionPresheaf B f V pres).hom
          (((yonedaCompEtaleStalkPresheafFunctorIso B X.obj X.property x).app
            ((smallEtaleBaseChange B f).obj V)).toEquiv.symm v))).1 := rfl
  rw [hval, hsymm,
    (geometricPointSitePoint B X.obj X.property x).toPresheafFiber_naturality_apply
      (baseChangeRepresentableIsoSolutionPresheaf B f V pres).hom
      ((smallEtaleBaseChange B f).obj V) v
      (CategoryStruct.id ((smallEtaleBaseChange B f).obj V))]
  refine (congrArg (fun z : EtaleLocalSolutions B X.obj X.property x
      (baseChangePresentationSystem B f (P := P)) => z.1 i)
    (geometricFiberSolutionsDesc_toPresheafFiber B X.obj X.property x
      (baseChangePresentationSystem B f (P := P)) ((smallEtaleBaseChange B f).obj V) v
      (baseChangeSiteHomEquivSolutions B f V pres ((smallEtaleBaseChange B f).obj V)
        (CategoryStruct.id ((smallEtaleBaseChange B f).obj V))))).trans ?_
  refine congrArg (etaleLocalRingGerm B X.obj X.property x
    ((smallEtaleBaseChange B f).obj V) v) ?_
  change (SmallEtale.baseChangeHomEquivSolutions B f V ((smallEtaleBaseChange B f).obj V) pres
      (CategoryStruct.id ((smallEtaleBaseChange B f).obj V))).1 i = _
  change (homOverEquivSolutions _ _ _ _ P pres
      (SmallEtale.baseChangeHomEquiv B f V ((smallEtaleBaseChange B f).obj V)
        (CategoryStruct.id ((smallEtaleBaseChange B f).obj V)))).1 i = _
  rw [homOverEquivSolutions_apply_coe, SmallEtale.baseChangeHomEquiv_apply_coe,
    CategoryTheory.Functor.map_id, Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply]
  rfl

end BaseChange

end AlgebraicGeometry

end
