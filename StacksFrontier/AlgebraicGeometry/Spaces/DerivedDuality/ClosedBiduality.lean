module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorMonoidalClosed

/-!
# The duality functor of a ringed site and the triangle identity of biduality

Let `(C, O)` be a ringed site and `K` an object of `D(O)`. The closed symmetric monoidal
structure of `D(O)` (`AlgebraicGeometry.RingedSite.derivedTensorMonoidalClosed`) has internal
Hom `R𝓗om(B, -)` on the nose, and its biduality morphism is the biduality morphism
`AlgebraicGeometry.RingedSite.derivedBiduality` of Stacks 0A89. This file records that the
functoriality of the closed structure in the dualized variable is the functoriality of the
derived internal Hom bifunctor, so that the duality functor `D = R𝓗om(-, K)` of
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` satisfies the triangle identity

`β_{D L} ≫ D(β_L) = 𝟙_{D L}`.

## Main results

* `AlgebraicGeometry.RingedSite.pre_app_eq_derivedSheafHomBifunctor_map`: the precomposition
  of the closed structure is the action of the derived internal Hom on its first variable.
* `AlgebraicGeometry.RingedSite.derivedBiduality_comp_map_derivedBiduality`: **the triangle
  identity of biduality.**

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- `D(O)` at the standard model, the model at which the closed structure and the biduality
morphism are stated. -/
abbrev StdDerived : Type (u + 1) :=
  @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
    _ _ (HasDerivedCategory.standard _)

/-- The derived internal Hom bifunctor `R𝓗om(-, -)` of `D(O)`, at the standard model. -/
abbrev stdSheafHom : (StdDerived X)ᵒᵖ ⥤ StdDerived X ⥤ StdDerived X :=
  @derivedSheafHomBifunctor X (HasDerivedCategory.standard _)

/-- The cohomology sheaves `H^n : D(O) ⥤ Mod(O)`, at the standard model. -/
abbrev stdHomology (n : ℤ) :
    StdDerived X ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n

attribute [local instance] derivedTensorMonoidal derivedTensorSymmetric
  derivedTensorMonoidalClosed

/-- **The precomposition of the closed structure of `D(O)` is the action of the derived internal
Hom on its first variable.** -/
theorem pre_app_eq_derivedSheafHomBifunctor_map {A B : StdDerived X} (f : A ⟶ B)
    (K : StdDerived X) :
    (MonoidalClosed.pre f).app K = ((stdSheafHom X).map f.op).app K := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
  apply MonoidalClosed.uncurry_injective
  refine (MonoidalClosed.uncurry_pre f K).trans ?_
  refine Eq.trans ?_
    (uncurry_derivedTensorMonoidalClosed X (((stdSheafHom X).map f.op).app K)).symm
  have hsymm : ∀ P Q : StdDerived X, (β_ P Q).inv = (derivedTensorBraiding X Q P).hom :=
    fun P Q => (SymmetricCategory.braiding_swap_eq_inv_braiding P Q).symm
  have hwr : f ▷ (((stdSheafHom X).obj (op B)).obj K) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
        (((stdSheafHom X).obj (op B)).obj K) := rfl
  have key : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app
        (((stdSheafHom X).obj (op B)).obj K) ≫
        (derivedTensorBraiding X B (((stdSheafHom X).obj (op B)).obj K)).hom ≫
          derivedSheafHomCounit X B K =
      (derivedTensorBraiding X A (((stdSheafHom X).obj (op B)).obj K)).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (((stdSheafHom X).map f.op).app K)).app A ≫ derivedSheafHomCounit X A K := by
    rw [← Category.assoc, derivedTensorBraiding_naturality_left, Category.assoc,
      derivedSheafHomCounit_dinatural X K f]
  have e1 : (ihom.ev B).app K =
      (derivedTensorBraiding X B (((stdSheafHom X).obj (op B)).obj K)).hom ≫
        derivedSheafHomCounit X B K :=
    (ihom_ev_app_derivedTensorMonoidalClosed X B K).trans (by rw [hsymm]; rfl)
  rw [e1]
  refine (congrArg (fun z => z ≫
      (derivedTensorBraiding X B (((stdSheafHom X).obj (op B)).obj K)).hom ≫
        derivedSheafHomCounit X B K) hwr).trans (key.trans ?_)
  exact congrArg (fun z => z ≫ ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
      (((stdSheafHom X).map f.op).app K)).app A ≫ derivedSheafHomCounit X A K) (hsymm _ _).symm

/-- **The triangle identity of biduality**: for objects `K`, `L` of `D(O)`, the biduality
morphism of `R𝓗om(L, K)` followed by `R𝓗om(-, K)` of the biduality morphism of `L` is the
identity of `R𝓗om(L, K)`. -/
theorem derivedBiduality_comp_map_derivedBiduality (K L : StdDerived X) :
    derivedBiduality X K (derivedDualInto X K L) ≫
        ((stdSheafHom X).map (derivedBiduality X K L).op).app K =
      𝟙 (derivedDualInto X K L) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
  have h := MonoidalClosed.closedBidualityApp_triangle K L
  rw [pre_app_eq_derivedSheafHomBifunctor_map, closedBidualityApp_eq_derivedBiduality,
    closedBidualityApp_eq_derivedBiduality] at h
  exact h

end AlgebraicGeometry.RingedSite

end
