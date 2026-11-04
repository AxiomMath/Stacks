module

public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# A product-preserving functor applied termwise to a Čech complex

For a family `U : ι → C` in a category with finite products, a presheaf `P : Cᵒᵖ ⥤ A` and an
additive functor `G : A ⥤ B` preserving the products indexed by the tuples of indices, applying
`G` termwise to the Čech complex of `P` gives the Čech complex of `P ⋙ G`, the isomorphism being
the product comparison map of `G` in each degree.

All names are in the namespace `Stacks.CategoryTheory.CechComplex`.

## Main definitions

* `mapCechIso`: the isomorphism between `G` applied termwise to the Čech complex of `P` and the
  Čech complex of `P ⋙ G`.

## Main results

* `mapCechIso_hom_f_comp_π`: in each degree, the component of `mapCechIso` followed by a
  projection of the product is `G` applied to that projection.
* `mapCechIso_hom_naturality`: `mapCechIso` is natural in the presheaf.
* `isIso_cechComplexFunctor_map`: a morphism of presheaves which is invertible on the finite
  intersections of the family induces an isomorphism of Čech complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.CechComplex

variable {C : Type*} [Category* C] [HasFiniteProducts C] {A B : Type*} [Category* A]
  [Category* B] [Preadditive A] [Preadditive B] [HasProducts.{0} A] [HasProducts.{0} B]
  {ι : Type} (G : A ⥤ B) [G.Additive]
  [∀ n : ℕ, PreservesLimitsOfShape (Discrete (Fin (n + 1) → ι)) G] (U : ι → C) (P : Cᵒᵖ ⥤ A)

omit [G.Additive] in
/-- The product comparison isomorphism of `G` in degree `n`, followed by the projection of the
Čech term of `P ⋙ G` at `x`, is `G` applied to the projection of the Čech term of `P` at `x`. -/
theorem preservesProductIso_hom_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    (PreservesProduct.iso G (fun x : Fin (n + 1) → ι ↦ P.obj (op (inter U x)))).hom ≫
      π U (P ⋙ G) n x = G.map (π U P n x) := by
  rw [PreservesProduct.iso_hom]
  exact piComparison_comp_π G _ x

/-- **Applying a product-preserving additive functor termwise to a Čech complex gives the Čech
complex of the composite**, with components the product comparison maps. -/
def mapCechIso :
    (G.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ PreservesProduct.iso G (fun x : Fin (n + 1) → ι ↦ P.obj (op (inter U x))))
    (by
      rintro n _ rfl
      refine hom_ext U (P ⋙ G) fun y ↦ ?_
      have h1 := preservesProductIso_hom_comp_π G U P (n + 1) y
      have h2 := preservesProductIso_hom_comp_π G U P n
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (d_comp_π U (P ⋙ G) n y)).trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans
        (congrArg (G.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫ ·) h1)).symm
      refine Eq.trans ?_ (G.map_comp _ _)
      rw [d_comp_π U P n y, G.map_sum, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Preadditive.comp_zsmul, G.map_zsmul, ← Category.assoc]
      exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
        ((congrArg (· ≫ (P ⋙ G).map (interMap U y i.succAbove).op) (h2 (y ∘ i.succAbove))).trans
          (G.map_comp _ _).symm))

/-- The component of `mapCechIso` in degree `n`, followed by the projection at `x`, is `G` applied
to the projection at `x`. -/
theorem mapCechIso_hom_f_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    (mapCechIso G U P).hom.f n ≫ π U (P ⋙ G) n x = G.map (π U P n x) :=
  preservesProductIso_hom_comp_π G U P n x

/-- The map of Čech complexes induced by a morphism of presheaves `τ`, followed by the projection
at `x`, is the projection at `x` followed by the component of `τ` at `inter U x`. -/
theorem cechComplexFunctor_map_f_comp_π {P' : Cᵒᵖ ⥤ A} (τ : P ⟶ P') (n : ℕ)
    (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map τ).f n ≫ π U P' n x = π U P n x ≫ τ.app (op (inter U x)) :=
  Limits.Pi.map_π (fun x : Fin (n + 1) → ι => τ.app (op (inter U x))) x

/-- **`mapCechIso` is natural in the presheaf.** -/
theorem mapCechIso_hom_naturality {P' : Cᵒᵖ ⥤ A} (τ : P ⟶ P') :
    (G.mapHomologicalComplex _).map ((cechComplexFunctor U).map τ) ≫ (mapCechIso G U P').hom =
      (mapCechIso G U P).hom ≫ (cechComplexFunctor U).map (Functor.whiskerRight τ G) := by
  ext n : 1
  refine hom_ext U _ fun x => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    mapCechIso_hom_f_comp_π, cechComplexFunctor_map_f_comp_π, ← Category.assoc,
    mapCechIso_hom_f_comp_π, Functor.mapHomologicalComplex_map_f, ← G.map_comp,
    cechComplexFunctor_map_f_comp_π, G.map_comp]
  rfl

section IsIso

variable {C : Type*} [Category* C] [HasFiniteProducts C] {A : Type*} [Category* A]
  [Preadditive A] [HasProducts.{0} A] {ι : Type} (U : ι → C)

/-- **A morphism of presheaves invertible on the finite intersections of the family induces an
isomorphism of Čech complexes.** -/
theorem isIso_cechComplexFunctor_map {P Q : Cᵒᵖ ⥤ A} (τ : P ⟶ Q)
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (τ.app (op (inter U x)))) :
    IsIso ((cechComplexFunctor U).map τ) := by
  have hn : ∀ n : ℕ, IsIso (((cechComplexFunctor U).map τ).f n) := fun n => by
    have : ∀ x : Fin (n + 1) → ι, IsIso (τ.app (op (inter U x))) := h n
    exact inferInstanceAs (IsIso (Limits.Pi.map fun x : Fin (n + 1) → ι => τ.app (op (inter U x))))
  exact HomologicalComplex.Hom.isIso_of_components _

end IsIso

end Stacks.CategoryTheory.CechComplex

end
