module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero

/-!
# The comparison of the derived functor of a composite, on the image of the localization

`CategoryTheory.Functor.mapDerivedCategoryComp` identifies the functor induced on unbounded
derived categories by a composite `F ⋙ G` of exact functors with the composite of the induced
functors.  It is a lift along the localization `DerivedCategory.Q`, so it is constrained only on
the objects `Q.obj K` for `K` a cochain complex, and a diagram chase that descends an identity of
derived functors to the level of complexes needs the formula there.

The companion formula for the inverse,
`CategoryTheory.Functor.mapDerivedCategoryComp_inv_app_Q`, is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction`; this file supplies
the one for the forward direction.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryComp_hom_app_Q`: the comparison of the derived
  functor of a composite with the composite of the derived functors, at an object in the image
  of `DerivedCategory.Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- **The comparison of the derived functor of a composite of exact functors with the composite
of the derived functors, at an object in the image of the localization.**  The two factorizations
of `CategoryTheory.Functor.mapDerivedCategoryFactors` for `F` and for `G`, the one for `F ⋙ G`
and the degreewise identification of `(F ⋙ G).mapHomologicalComplex` with the composite of the
two `mapHomologicalComplex`es are the whole content of the comparison. -/
theorem Functor.mapDerivedCategoryComp_hom_app_Q (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryComp F G).hom.app (DerivedCategory.Q.obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℤ)).inv.app K) ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  rw [Functor.mapDerivedCategoryComp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

end CategoryTheory

end
