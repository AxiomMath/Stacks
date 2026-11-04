module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# The Koszul symmetry of the total tensor complex, on a homogeneous summand

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` is an isomorphism
`Tot(K ⊗_R L) ≅ Tot(L ⊗_R K)` of total tensor complexes. This file computes it on a homogeneous
summand: the summand of bidegree `(p, q)` of `Tot(K ⊗_R L)` is carried to the summand of bidegree
`(q, p)` of `Tot(L ⊗_R K)` by the sectionwise symmetry of the tensor product sheaf, times the
Koszul sign `(-1)^{pq}`. Since a morphism out of a total complex is determined by its restrictions
to the summands (`HomologicalComplex.mapBifunctor.hom_ext`), this characterises
`tensorComplexFlipIso`.

## Main results

* `Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom`: the value of the Koszul symmetry
  on the summand of bidegree `(p, q)`.

## References

* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor R) (ComplexShape.up ℤ)]

/-- The Koszul symmetry of the total tensor complex on the summand of bidegree `(p, q)`.

The total tensor complex `Tot(K ⊗_R L)` in degree `n` is the direct sum of the sheaves
`K^p ⊗_R L^q` over the bidegrees with `p + q = n`. The symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` carries that summand to the summand
`L^q ⊗_R K^p` of bidegree `(q, p)` of `Tot(L ⊗_R K)`, by the sectionwise symmetry of the tensor
product of sheaves of modules — the component of
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` at `(K^p, L^q)` — multiplied by the Koszul
sign `(-1)^{pq}`. -/
@[reassoc]
theorem ι_tensorComplexFlipIso_hom
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    HomologicalComplex.ιMapBifunctor K L (sheafTensor R) (ComplexShape.up ℤ) p q n hpq ≫
        (tensorComplexFlipIso R K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) •
        (((sheafTensorBraiding R).hom.app (K.X p)).app (L.X q) ≫
          HomologicalComplex.ιMapBifunctor L K (sheafTensor R) (ComplexShape.up ℤ) q p n hqp) := by
  have hsig : ComplexShape.σ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) q p =
      ((p * q).negOnePow : ℤˣ) := congrArg Int.negOnePow (mul_comm q p)
  show HomologicalComplex.ιMapBifunctor K L (sheafTensor R) (ComplexShape.up ℤ) p q n hpq ≫
        ((HomologicalComplex.mapBifunctorNatIso K L (ComplexShape.up ℤ)
            (sheafTensorBraiding R)).hom.f n ≫
          (HomologicalComplex.mapBifunctorFlipIso L K (sheafTensor R)
            (ComplexShape.up ℤ)).hom.f n) = _
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorNatIso_hom, Category.assoc,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom, hsig, Linear.comp_units_smul]

end Stacks.SheafOfModules.Tensor

end
