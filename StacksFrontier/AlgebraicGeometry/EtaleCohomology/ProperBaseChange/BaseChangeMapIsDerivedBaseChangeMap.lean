module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformationAcyclic

/-!
# The étale base change map is the generic derived base change map

For a commutative square of schemes, `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`
(Stacks 0A2A) is the descent of the degreewise base change comparison
`Stacks.EtaleCohomology.etaleAbelianBaseChange` along the universal property of
`Rf_* ⋙ g⁻¹`. The generic construction
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap` is the descent of the same
transformation, so the two agree: both satisfy the same defining equation
(`Stacks.Cohomology.UnboundedComplexes.eq_derivedBaseChangeMap_of_fac`). This makes the generic
calculus of derived base change maps (computation on complexes computing the derived functors,
comparison along a cube of exact functors) available for the étale base change map.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap`.

Standard model: uses `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, which exists only
there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/- The same preferred route to the `Preadditive` structure as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap`, so that the
statements below carry the spelling of the equation they are derived from. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The étale base change map of Stacks 0A2A is the derived base change map** of the degreewise
comparison `Stacks.EtaleCohomology.etaleAbelianBaseChange`, for the derived direct images and
their derived-functor units. -/
public theorem etaleAbelianDerivedBaseChange_eq_derivedBaseChangeMap :
    etaleAbelianDerivedBaseChange.{u, v} f g g' f' h =
      Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
        (etaleAbelianInverseImage.{u, v} g') (etaleAbelianInverseImage.{u, v} g)
        (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f')
        (etaleAbelianDerivedDirectImageUnit.{u, v} f)
        (etaleAbelianDerivedDirectImageUnit.{u, v} f')
        (etaleAbelianBaseChange.{u, v} f g g' f' h) := by
  refine Stacks.Cohomology.UnboundedComplexes.eq_derivedBaseChangeMap_of_fac _ _ _ _ _ _ _ _ _ _
    fun K => ?_
  have e := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h K
  rw [etaleAbelianHomotopyBaseChange_app] at e
  exact e

end Stacks.EtaleCohomology

end
