module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula

/-!
# A map killing the transpose kills the tensored map

Let `(C, O)` be a ringed site and let `u : A ⊗^𝐋_O P ⟶ E` be a morphism of `D(O)`, with transpose
`u♭ : A ⟶ RSheafHom(P, E)` under the tensor–internal-Hom bijection of **Stacks 08J8**,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`. For `f : I ⟶ A`, if `f ≫ u♭ = 0` then
`(f ⊗^𝐋_O 1_P) ≫ u = 0`: the bijection is natural in its source variable and additive.

## Main results

* `derivedTensorProductFunctor_map_app_comp_eq_zero_of_comp_derivedCurryHomEquiv_symm`:
  if `f ≫ u♭ = 0` then `(f ⊗^𝐋_O 1_P) ≫ u = 0`.

## Implementation notes

The statement is over a variable ringed site and variable objects, in the spelling in which
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is declared; its consumers instantiate it.
Proved where a different (definitionally equal) `Abelian` instance on the sheaves of modules is
preferred, the composite `f ≫ u♭` is formed in a category whose instances are spelled differently
from those the bijection expects, and comparing the two exhausts the recursion budget.

Even here the proof rewrites the goal, never the naturality equation: rewriting `f ≫ u♭ = 0`
inside that equation, or reading it off `AddEquiv.map_eq_zero_iff`, exhausts the recursion budget.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (Y : RingedSite.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} Y.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **Killing the transpose kills the map.** For `f : I ⟶ A` and `u : A ⊗^𝐋 P ⟶ E`, if `f`
followed by the transpose of `u` under the bijection of Stacks 08J8 is zero, then so is
`(f ⊗^𝐋 1_P) ≫ u`. -/
theorem derivedTensorProductFunctor_map_app_comp_eq_zero_of_comp_derivedCurryHomEquiv_symm
    (A I P E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (f : I ⟶ A) (u : ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).obj A).obj P ⟶ E)
    (hf : f ≫ (derivedCurryHomEquiv Y A P E).symm u = 0) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).map f).app P ≫ u = 0 := by
  have h := derivedCurryHomEquiv_naturality_source' Y A I P E f
    ((derivedCurryHomEquiv Y A P E).symm u)
  rw [← (derivedCurryHomEquiv Y A P E).apply_symm_apply u, ← h, hf, map_zero]

end AlgebraicGeometry.RingedSite

end
