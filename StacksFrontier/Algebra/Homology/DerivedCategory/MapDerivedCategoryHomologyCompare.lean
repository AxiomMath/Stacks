module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# The two descents of "an exact functor commutes with `Hⁿ`" agree

For an exact additive functor `F : C₁ ⥤ C₂` between abelian categories the project carries two
copies of the natural isomorphism

`F.mapDerivedCategory ⋙ Hⁿ ≅ Hⁿ ⋙ F`,

namely `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`.  They are assembled differently —
the first descends a comparison already written with its target on the derived category, the
second descends a comparison whose target is still at the level of cochain complexes and lets the
`Localization.Lifting` instance for the homology functor supply the last factor — and they are not
`rfl`-equal.  This file proves they are equal.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`:
  the two descents are the same isomorphism.

## Implementation notes

Both are `CategoryTheory.Localization.liftNatIso` along `DerivedCategory.Q`, so
`CategoryTheory.Localization.natTrans_ext` reduces the equality to the images of cochain
complexes, where `CategoryTheory.Localization.liftNatTrans_app` evaluates both sides.  The two
`Localization.Lifting` instances on the source side are literally the same, and the two on the
target side — `Localization.Lifting.compLeft` for the first copy, `Localization.Lifting.compRight`
applied to `DerivedCategory.liftingHomologyFunctor` for the second — differ exactly by the factor
`F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K)` that the first copy carries
inside its descended transformation instead.  What is left is that the two complex-level
comparisons agree, and they do by definition: both are `ShortComplex.mapHomologyIso F` at the
short complex `K.sc n`.
-/

@[expose] public noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

namespace DerivedCategory

/-- The lifting isomorphism of `DerivedCategory.liftingHomologyFunctor` is
`DerivedCategory.homologyFunctorFactors`.  Stated because the instance is given by the anonymous
constructor, so `simp` has no equation to rewrite its projection with. -/
theorem liftingHomologyFunctor_iso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] (n : ℤ) :
    Localization.Lifting.iso (Q : CochainComplex C ℤ ⥤ _)
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n) =
      homologyFunctorFactors C n := rfl

end DerivedCategory

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The `Localization.Lifting` instance by which `CategoryTheory.Functor.mapDerivedCategory`
descends the degreewise functor is `CategoryTheory.Functor.mapDerivedCategoryFactors`.  Mathlib
declares that instance anonymously, so `simp` has no equation to rewrite its projection with. -/
theorem lifting_iso_mapDerivedCategory :
    Localization.Lifting.iso (DerivedCategory.Q : CochainComplex C₁ ℤ ⥤ _)
        (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
        (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        F.mapDerivedCategory =
      F.mapDerivedCategoryFactors := rfl

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- **The two complex-level comparisons agree**: both
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` and
`CategoryTheory.Functor.mapHomologicalComplexHomologyFunctorIso` are, at a complex `K`, the
comparison `CategoryTheory.ShortComplex.mapHomologyIso` at the short complex `K.sc n`. -/
theorem mapHomologicalComplexHomologyIso_hom_app_eq (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K =
      (F.mapHomologicalComplexHomologyFunctorIso n).hom.app K := rfl

/-- **The two descents of "an exact functor commutes with `Hⁿ`" are the same isomorphism.**
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` have the same type and are not
`rfl`-equal; they are equal. -/
theorem mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategoryHomologyIso n = F.mapDerivedCategoryHomologyFunctorIso n := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun K => ?_)
  simp [mapDerivedCategoryHomologyIso, mapDerivedCategoryHomologyFunctorIso,
    mapDerivedCategoryHomologyIsoAux, mapHomologicalComplexHomologyIso_hom_app_eq,
    DerivedCategory.liftingHomologyFunctor_iso]

end CategoryTheory.Functor

end
