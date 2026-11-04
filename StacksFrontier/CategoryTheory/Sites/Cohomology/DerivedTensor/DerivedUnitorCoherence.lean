module

public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# Naturality of the unit law of the total tensor complex

Let `(C, 𝒪)` be a ringed site.  The structure sheaf in degree zero is a right unit for the
total tensor complex, and `Stacks.SheafOfModules.tensorComplexUnitIso` provides the
isomorphism `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` one complex at a time.  This file proves that it is
**natural in `K`**, together with the naturality of the two comparisons it is assembled from.

## Main results

* `Stacks.SheafOfModules.rowComplexUnitIso_naturality`: the termwise unit law
  `(p ↦ K^p ⊗_𝒪 𝒪) ≅ K` is natural in `K`.
* `Stacks.SheafOfModules.tensorComplexUnitIso_naturality` and `…'`: **the unit law
  `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` is natural in `K`**, in the `HomologicalComplex.mapBifunctorMap` and
  the `tensorComplex` spellings of the induced map.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

/-! ## Naturality of the unit law on complexes of modules -/

namespace Stacks.SheafOfModules

open CochainComplex.KFlatBifunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).Additive]

/-- `rowComplexMap` against the structure sheaf is the action on complexes of the functor
`- ⊗_𝒪 𝒪`. -/
private lemma rowComplexMap_eq {K K' : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ} (φ : K ⟶ K') :
    rowComplexMap (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R) φ
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).flip.obj
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf R))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ :=
  rfl

/-- **The termwise unit law `(p ↦ K^p ⊗_𝒪 𝒪) ≅ K` is natural in `K`.** -/
lemma rowComplexUnitIso_naturality {K K' : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ} (φ : K ⟶ K') :
    rowComplexMap (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R) φ
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≫
        (Stacks.SheafOfModules.rowComplexUnitIso R K').hom =
      (Stacks.SheafOfModules.rowComplexUnitIso R K).hom ≫ φ := by
  rw [rowComplexMap_eq]
  exact (NatIso.mapHomologicalComplex (Stacks.SheafOfModules.sheafTensorUnitNatIso R)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.naturality φ

variable
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R).obj
    M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R)
      (ComplexShape.up ℤ)]

/-- The unit law on complexes is the single-row total comparison followed by the termwise unit
law. -/
private lemma tensorComplexUnitIso_hom (K : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    (Stacks.SheafOfModules.tensorComplexUnitIso R K).hom =
      (totalSingleIso
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R) K
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom ≫
        (Stacks.SheafOfModules.rowComplexUnitIso R K).hom :=
  rfl

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[0]) ≅ K` is natural in `K`.** -/
lemma tensorComplexUnitIso_naturality {K K' : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ} (φ : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap φ
        (𝟙 ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} R)
        (ComplexShape.up ℤ) ≫
        (Stacks.SheafOfModules.tensorComplexUnitIso R K').hom =
      (Stacks.SheafOfModules.tensorComplexUnitIso R K).hom ≫ φ := by
  rw [tensorComplexUnitIso_hom, tensorComplexUnitIso_hom, ← Category.assoc,
    totalSingleIso_hom_naturality, Category.assoc, rowComplexUnitIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- The naturality of the unit law with the induced map written as the action of the tensor
bifunctor on complexes rather than as `HomologicalComplex.mapBifunctorMap`. -/
lemma tensorComplexUnitIso_naturality' {K K' : CochainComplex (_root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ} (φ : K ⟶ K') :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).map φ).app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ≫
        (Stacks.SheafOfModules.tensorComplexUnitIso R K').hom =
      (Stacks.SheafOfModules.tensorComplexUnitIso R K).hom ≫ φ :=
  tensorComplexUnitIso_naturality R φ

end Stacks.SheafOfModules

end
