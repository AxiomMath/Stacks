module

public import StacksFrontier.Cotangent.ProductDecompositionBase
public import StacksFrontier.Cotangent.ProductDecompositionCriterion

/-!
# The second component of Tag 08SC, in the adjoint shape

`CommAlgCat.quasiIso_cotangentComplexProductMap` of
`StacksFrontier/Cotangent/ProductDecompositionBase.lean` is [Stacks, Tag 08SC] at chain level over
an arbitrary base: the canonical map `L_{B×C/A} ⟶ L_{B/A} ⊕ L_{C/A}` is a quasi-isomorphism of
complexes of `B × C`-modules. This file reads off from it the statement about the second
projection alone,

`L_{B×C/A} ⊗_{B×C} C ⟶ L_{C/A}` is a quasi-isomorphism,

in the adjoint shape of [Stacks, Tag 08QQ] — extension of scalars of the functoriality map of
[Stacks, Tag 08PN] followed by the counit. That is the shape in which the descent of the
fundamental triangle along `B × C → C` consumes it.

## Main results

* `CommAlgCat.quasiIso_cotangentExtendScalars_productSnd`: **the second component of
  [Stacks, Tag 08SC], over an arbitrary base.**

## Implementation notes

Base change along the second projection is exact, the projection being flat
(`RingHom.flat_snd`), so it carries the quasi-isomorphism of Tag 08SC to one; composing with the
projection of the biproduct onto its second summand — invertible after that base change by
`CommAlgCat.isIso_extendScalars_biprod_snd`, the first summand being killed — leaves the base
change of the second component alone. The counit is invertible because the projection is
surjective.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B C : CommAlgCat.{u} A)

/-- **The second component of [Stacks, Tag 08SC], over an arbitrary base.** For ring maps
`A → B` and `A → C` the map

`L_{B×C/A} ⊗_{B×C} C ⟶ L_{C/A}`

— extension of scalars along the second projection of the functoriality map of
[Stacks, Tag 08PN], followed by the counit — is a quasi-isomorphism.

This is `CommAlgCat.quasiIso_cotangentComplexProductMap` base changed along the second
projection, which is exact, and composed with the two isomorphisms
`CommAlgCat.isIso_extendScalars_biprod_snd` and
`ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex`. -/
theorem quasiIso_cotangentExtendScalars_productSnd :
    QuasiIso (((ModuleCat.extendScalars
            (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (squareCotangentComplexMap.{u, u, u} (productSndSquare.{u, u} A B C)) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (productSndSquare.{u, u} A B C).map
          (ComplexShape.up ℤ) (cotangentComplex.{u, u} A C)) := by
  have : (ModuleCat.extendScalars.{u, u, u}
      (productSndSquare.{u, u} A B C).map).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} _
      (RingHom.flat_snd (B : Type u) (C : Type u))
  have : QuasiIso (cotangentComplexProductMap.{u, u} A B C) :=
    quasiIso_cotangentComplexProductMap A B C
  have := isIso_extendScalars_biprod_snd.{u, u} A B C
  have hq1 : QuasiIso (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (cotangentComplexProductMap.{u, u} A B C)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hq2 : QuasiIso (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (biprod.snd (X :=
          ((ModuleCat.restrictScalars (productFstSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) (Y :=
          ((ModuleCat.restrictScalars (productSndSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A C)))) :=
    quasiIso_of_isIso _
  have hcomp : QuasiIso ((((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (cotangentComplexProductMap.{u, u} A B C)) ≫
      (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (biprod.snd (X :=
          ((ModuleCat.restrictScalars (productFstSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) (Y :=
          ((ModuleCat.restrictScalars (productSndSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A C))))) :=
    quasiIso_comp _ _ (hφ := hq1) (hφ' := hq2)
  have heq : (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (cotangentComplexProductMap.{u, u} A B C)) ≫
      (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (biprod.snd (X :=
          ((ModuleCat.restrictScalars (productFstSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) (Y :=
          ((ModuleCat.restrictScalars (productSndSquare.{u, u} A B C).map).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A C)))) =
      ((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (squareCotangentComplexMap.{u, u, u} (productSndSquare.{u, u} A B C)) := by
    rw [← Functor.map_comp, cotangentComplexProductMap_snd]
  have hq3 : QuasiIso (((ModuleCat.extendScalars
          (productSndSquare.{u, u} A B C).map).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (squareCotangentComplexMap.{u, u, u} (productSndSquare.{u, u} A B C))) := by
    rw [← heq]; exact hcomp
  have := ModuleCat.isIso_extendRestrictScalarsAdjCounitComplex
    (productSndSquare.{u, u} A B C).map (ComplexShape.up ℤ)
    (RingHom.surjective_snd (B : Type u) (C : Type u)) (cotangentComplex.{u, u} A C)
  have hq4 : QuasiIso (ModuleCat.extendRestrictScalarsAdjCounitComplex
      (productSndSquare.{u, u} A B C).map (ComplexShape.up ℤ)
      (cotangentComplex.{u, u} A C)) := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := hq3) (hφ' := hq4)

end CommAlgCat

end
