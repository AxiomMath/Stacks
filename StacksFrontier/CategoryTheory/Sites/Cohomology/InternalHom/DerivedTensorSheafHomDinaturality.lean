module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingOnModels

/-!
# Dinaturality of the adjunction of Stacks 08J8 in the middle variable

On a ringed site, for `v : Q' ⟶ Q` and `θ : A ⟶ RSheafHom(Q, M)` in `D(O)`, the bijection of
Stacks 08J8 carries `θ ≫ RSheafHom(v, M)` to `A ⊗^L v` followed by the image of `θ`; and the
inverse hom-set bijection of the adjunction `- ⊗^L Q ⊣ RSheafHom(Q, -)` is that bijection.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_homEquiv_symm_apply`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The inverse hom-set bijection of the adjunction of Stacks 08J8 is the bijection
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` it is built from. -/
theorem derivedTensorSheafHomAdjunction_homEquiv_symm_apply
    (A B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (f : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    ((derivedTensorSheafHomAdjunction X B).homEquiv A Z).symm f =
      derivedCurryHomEquiv X A B Z f := by
  rw [derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end

end AlgebraicGeometry.RingedSite

end
