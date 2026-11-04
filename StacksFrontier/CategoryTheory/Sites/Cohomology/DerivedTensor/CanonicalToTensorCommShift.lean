module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToTensorCommShift

/-!
# The canonical map to the total tensor complex, for the canonical derived tensor product

`Stacks.SheafOfModules.toTensorNatTrans` is stated for
`Stacks.SheafOfModules.derivedTensorBifunctor`.  The canonical derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` is that construction made opaque
(`irreducible_def`), so the map is transported here along its defining equation
`Stacks.SheafOfModules.canonicalDerivedTensorProduct_def`, together with its commutation with the
shifts and its invertibility at a K-flat complex.

## Main definitions

* `Stacks.SheafOfModules.canonicalToTensorNatTrans`: `Q K ⊗^L Q - ⟶ Q Tot(K ⊗ -)` for the
  canonical derived tensor product.

## Main results

* `Stacks.SheafOfModules.canonicalToTensorNatTrans_commShift`: it commutes with the shifts.
* `Stacks.SheafOfModules.isIso_canonicalToTensorNatTrans_app_of_kFlat`: it is invertible at a
  K-flat complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

variable {X} in
/-- Transport of a map `Q K ⊗^L Q - ⟶ Q Tot(K ⊗ -)` along an equality `T₀ = T` of derived tensor
products. -/
def toTensorNatTransOfEq
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {T₀ T : DerivedTensorProduct.{c, u, u, d} X} (hT : T₀ = T)
    (x : DerivedCategory.Q ⋙ T₀.tensor.obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ T.tensor.obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q :=
  hT ▸ x

variable {X} in
/-- Transport along an equality of derived tensor products keeps the commutation with the
shifts. -/
theorem commShift_toTensorNatTransOfEq
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {T₀ T : DerivedTensorProduct.{c, u, u, d} X}
    (hT : T₀ = T)
    (x : DerivedCategory.Q ⋙ T₀.tensor.obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q)
    (hx : NatTrans.CommShift x ℤ) : NatTrans.CommShift (toTensorNatTransOfEq hT x) ℤ := by
  subst hT
  exact hx

variable {X} in
/-- Transport along an equality of derived tensor products keeps invertibility of a component. -/
theorem isIso_toTensorNatTransOfEq_app
    {K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {T₀ T : DerivedTensorProduct.{c, u, u, d} X}
    (hT : T₀ = T)
    (x : DerivedCategory.Q ⋙ T₀.tensor.obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hx : IsIso (x.app L)) : IsIso ((toTensorNatTransOfEq hT x).app L) := by
  subst hT
  exact hx

variable (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The canonical map `Q K ⊗^L Q L ⟶ Q Tot(K ⊗ L)` of Stacks 0FPH for the canonical derived
tensor product**, natural in `L`: `Stacks.SheafOfModules.toTensorNatTrans`, transported along
`Stacks.SheafOfModules.canonicalDerivedTensorProduct_def`. -/
def canonicalToTensorNatTrans :
    DerivedCategory.Q ⋙
        (canonicalDerivedTensorProduct.{c, u, d} X).tensor.obj (DerivedCategory.Q.obj K) ⟶
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K ⋙ DerivedCategory.Q :=
  toTensorNatTransOfEq (canonicalDerivedTensorProduct_def X).symm (toTensorNatTrans X K)

/-- **The canonical map of Stacks 0FPH commutes with the shifts**, for the canonical derived
tensor product. -/
instance canonicalToTensorNatTrans_commShift :
    NatTrans.CommShift (canonicalToTensorNatTrans X K) ℤ :=
  commShift_toTensorNatTransOfEq _ _ (toTensorNatTrans_commShift X K)

/-- The canonical map of Stacks 0FPH for the canonical derived tensor product is invertible at a
K-flat complex. -/
theorem isIso_canonicalToTensorNatTrans_app_of_kFlat
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : IsKFlat X.O L) : IsIso ((canonicalToTensorNatTrans X K).app L) :=
  isIso_toTensorNatTransOfEq_app _ _ L (isIso_toTensor_of_kFlat_right X K L hL)

end Stacks.SheafOfModules

end
