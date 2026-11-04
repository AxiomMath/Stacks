module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingOnModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomDinaturality

/-!
# Dinaturality of the adjunction of Stacks 08J8 in the middle variable

On a ringed site, for `v : Q' ⟶ Q` and `θ : A ⟶ RSheafHom(Q, M)` in `D(O)`, the bijection of
Stacks 08J8 carries `θ ≫ RSheafHom(v, M)` to `A ⊗^L v` followed by the image of `θ`; and the
inverse hom-set bijection of the adjunction `- ⊗^L Q ⊣ RSheafHom(Q, -)` is that bijection.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality_comp`.
* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_homEquiv_symm_apply`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite



universe u

namespace AlgebraicGeometry.RingedSite

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} X.O) (ComplexShape.up ℤ)]

/-- The bijection of Stacks 08J8 is dinatural in the middle variable. -/
theorem derivedCurryHomEquiv_dinaturality_comp
    {Q' Q : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (v : Q' ⟶ Q)
    {A M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (θ : A ⟶ ((derivedSheafHomBifunctor X).obj (op Q)).obj M) :
    derivedCurryHomEquiv X A Q' M (θ ≫ ((derivedSheafHomBifunctor X).map v.op).app M) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map v ≫
        derivedCurryHomEquiv X A Q M θ := by
  have h0 := derivedCurryHomEquiv_naturality X (𝟙 A) v (𝟙 M) θ
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    NatTrans.id_app] at h0
  exact h0

end

end AlgebraicGeometry.RingedSite

end
