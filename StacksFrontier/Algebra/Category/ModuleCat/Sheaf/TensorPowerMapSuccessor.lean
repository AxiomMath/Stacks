module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc

/-!
# The comparison of tensor powers along a functor is compatible with the successor

Let `L` be an invertible sheaf of modules on a ringed site, let `R` be a functor to sheaves of
modules on a second ringed site which is compatible with the tensor product by `L` in the sense
of `Stacks.SheafOfModules.TensorPower.TensorComparison`, and let
`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso` be the resulting comparison
`R(L^{⊗ n}) ≅ (R L)^{⊗ n}` of the integral tensor powers. This file proves that the comparison
commutes with the successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`:

    R(L^{⊗ n} ⊗ L) ───R(succ)───> R(L^{⊗ (n + 1)})
          │                              │
          α                              ≅
          v                              v
    R(L^{⊗ n}) ⊗ R L ──≅ ▷ R L──> (R L)^{⊗ n} ⊗ R L ──succ──> (R L)^{⊗ (n + 1)}

commutes, in every integer degree.

## Main results

* `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_tensorPowerSuccIso`: the square above
  commutes in every integer degree.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u v' u' w

namespace Stacks.Equivalence

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- A square whose lower edge ends in `F x` followed by a square whose upper edge begins with
`F y` compose to the square whose lower edge is `F (x ≫ y)`. -/
private theorem comp_map_transfer {V : Type u} [Category.{v} V] {V' : Type u'}
    [Category.{v'} V'] (F : V ⥤ V') {A₁ A₂ A₃ : V} {W X Y Z : V'} {a : W ⟶ X} {b : X ⟶ Y}
    {k : Y ⟶ Z} {c : W ⟶ F.obj A₁} {x : A₁ ⟶ A₂} {y : A₂ ⟶ A₃} {f : F.obj A₂ ⟶ Y}
    {h : F.obj A₃ ⟶ Z} (h₁ : a ≫ b = c ≫ F.map x ≫ f) (h₂ : F.map y ≫ h = f ≫ k) :
    a ≫ b ≫ k = c ≫ F.map (x ≫ y) ≫ h := by
  rw [F.map_comp, Category.assoc, h₂, reassoc_of% h₁]

end Stacks.Equivalence

namespace Stacks.SheafOfModules.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (O' : Dᵒᵖ ⥤ CommRingCat.{w})
  (hO' : Presheaf.IsSheaf K (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O'))
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]
  (R : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).IsEquivalence]

/-- The comparison of integral tensor powers along a functor commutes with the successor
comparison: pulling `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` through `R` and then comparing the
`(n + 1)`st powers agrees with splitting the outer factor by the tensor comparison, comparing
the `n`th powers, and only then multiplying by the first power. -/
theorem mapTensorPowerIso_tensorPowerSuccIso (α : TensorComparison O hO O' hO' R L)
    (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
      _root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO')) (n : ℤ) :
    R.map (tensorPowerSuccIso O hO L n).hom ≫
        (mapTensorPowerIso O hO O' hO' R L α hunit (n + 1)).hom =
      (α (tensorPower O hO L n)).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).map
            (mapTensorPowerIso O hO O' hO' R L α hunit n).hom ≫
          (tensorPowerSuccIso O' hO' (R.obj L) n).hom := by
  have hsq := Stacks.Equivalence.powIntertwineObj_succIso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).asEquivalence R (fun M ↦ α M) n
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  have hnat := Stacks.Equivalence.powSuccIso_naturality
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).asEquivalence n hunit.hom
  exact Stacks.Equivalence.comp_map_transfer
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
        (R.obj L)).asEquivalence.functor hsq hnat

end Stacks.SheafOfModules.TensorPower

end
