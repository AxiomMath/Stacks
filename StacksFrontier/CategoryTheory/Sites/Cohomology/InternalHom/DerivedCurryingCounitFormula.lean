module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor–internal-Hom bijection is tensoring and then evaluating

Let `(C, O)` be a ringed site. The tensor–internal-Hom bijection of [Stacks, Tag 08J8],
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, identifies morphisms `K ⟶ RSheafHom(A, B)`
of `D(O)` with morphisms `K ⊗^𝐋_O A ⟶ B`. It is given by the formula

`g ↦ (g ⊗^𝐋_O 1_A) ≫ e`,

where `e : RSheafHom(A, B) ⊗^𝐋_O A ⟶ B` is the evaluation morphism
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit`, that is, the morphism the bijection
matches with the identity of `RSheafHom(A, B)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source'`: the naturality of
  Stacks 08J8 in its source variable with the four objects taken as explicit arguments.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`: **the bijection of Stacks 08J8 is
  `g ↦ (g ⊗ 1) ≫ e`.**

## Implementation notes

The statements are over a variable ringed site and variable objects, with the objects of the
naturality clause explicit: instantiated at the slice site `C/U` and at restrictions of objects
of `D(O)` they elaborate, whereas the same proofs written at those composite terms exhaust the
recursion budget. For the same reason the evaluation morphism is opened by `unfold` and the
`g ≫ 𝟙` produced by the naturality clause is removed by `rw` against explicitly stated
equations.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
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

/-- **Naturality of the bijection of [Stacks, Tag 08J8] in its source variable, with the objects
explicit.** This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source` with
`K`, `K'`, `A` and `B` taken as explicit arguments. -/
theorem derivedCurryHomEquiv_naturality_source'
    (K K' A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (u : K' ⟶ K)
    (h : K ⟶ ((derivedSheafHomBifunctor Y).obj (op A)).obj B) :
    derivedCurryHomEquiv Y K' A B (u ≫ h) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).map u).app A ≫
        derivedCurryHomEquiv Y K A B h :=
  derivedCurryHomEquiv_naturality_source Y u h

/-- **The tensor–internal-Hom bijection is tensoring and then evaluating.** For objects `K`, `A`,
`B` of `D(O)` it carries `g : K ⟶ RSheafHom(A, B)` to

`(g ⊗^𝐋_O 1_A) ≫ e`,

with `e : RSheafHom(A, B) ⊗^𝐋_O A ⟶ B` the evaluation morphism
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit`. -/
@[stacks 08J8 "the bijection is tensoring with the identity followed by the evaluation morphism"]
theorem derivedCurryHomEquiv_apply
    (K A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (g : K ⟶ ((derivedSheafHomBifunctor Y).obj (op A)).obj B) :
    derivedCurryHomEquiv Y K A B g =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor Y).map g).app A ≫
        derivedSheafHomCounit Y A B := by
  unfold derivedSheafHomCounit
  have hc : derivedCurryHomEquiv Y K A B
        (g ≫ 𝟙 (((derivedSheafHomBifunctor Y).obj (op A)).obj B)) =
      derivedCurryHomEquiv Y K A B g :=
    congrArg (fun v : K ⟶ ((derivedSheafHomBifunctor Y).obj (op A)).obj B =>
      derivedCurryHomEquiv Y K A B v) (Category.comp_id g)
  have h0 := derivedCurryHomEquiv_naturality_source' Y
    (((derivedSheafHomBifunctor Y).obj (op A)).obj B) K A B g
    (𝟙 (((derivedSheafHomBifunctor Y).obj (op A)).obj B))
  rw [← hc, h0]

end AlgebraicGeometry.RingedSite

end
