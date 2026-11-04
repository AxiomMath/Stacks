module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# The canonical map `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` in the first variable, and on complexes

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `G` a sheaf of
`O_C`-modules. The canonical map of Stacks 03EL/04G0,
`Stacks.SheafOfModules.pushforwardTensorMap f F G : F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)`, is
natural in `F`. This file packages it as a natural transformation of functors of `F`, as a natural
isomorphism when every component is invertible, and applies it degreewise to a complex: for a
complex `P` of `O_D`-modules the termwise complex `p ↦ Pᵖ ⊗ f_*G` is then `f_*` of the termwise
complex `p ↦ f^*Pᵖ ⊗ G`.

This is the complex-level form of the projection formula used to compute a derived tensor
product with a direct image along a closed immersion (Stacks 0DK5 for a closed immersion, read on
a K-flat representative): with `P` K-flat the left side computes `P ⊗^L f_*G`.

## Main definitions

* `Stacks.SheafOfModules.pushforwardTensorNatTrans`: the canonical map, natural in `F`.
* `Stacks.SheafOfModules.pushforwardTensorNatIso`: the same, as an isomorphism of functors, given
  that its components are invertible.
* `Stacks.SheafOfModules.rowComplexPushforwardIso`: the termwise complex
  `p ↦ Pᵖ ⊗ f_*G` is `f_*(p ↦ f^*Pᵖ ⊗ G)`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod

namespace Stacks.SheafOfModules

universe w w' v u v' u'

open Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The canonical map `F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)` of
`Stacks.SheafOfModules.pushforwardTensorMap`, as a natural transformation in `F`. -/
@[simps]
def pushforwardTensorNatTrans (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (Tensor.sheafTensor Y.O).flip.obj ((pushforwardModules f).obj G) ⟶
      f.pullbackModules ⋙ (Tensor.sheafTensor X.O).flip.obj G ⋙ pushforwardModules f where
  app F := pushforwardTensorMap f F G
  naturality {F F'} k := by
    have h := pushforwardTensorMap_natural f k (𝟙 G)
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
    simpa using h

/-- The canonical map `F ⊗_{O_D} f_*G ⟶ f_*(f^*F ⊗_{O_C} G)` as a natural isomorphism in `F`,
granted that every component is invertible. -/
def pushforwardTensorNatIso (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (h : ∀ F, IsIso (pushforwardTensorMap f F G)) :
    (Tensor.sheafTensor Y.O).flip.obj ((pushforwardModules f).obj G) ≅
      f.pullbackModules ⋙ (Tensor.sheafTensor X.O).flip.obj G ⋙ pushforwardModules f :=
  NatIso.ofComponents (fun F => @asIso _ _ _ _ (pushforwardTensorMap f F G) (h F))
    (fun {_ _} k => (pushforwardTensorNatTrans f G).naturality k)

variable [(Tensor.sheafTensor.{u', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj M).Additive]
  [(Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [f.pullbackModules.Additive] [(pushforwardModules f).Additive]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]

/-- **The canonical map, on the termwise tensor complex.**  For a complex `P` of `O_D`-modules,
`p ↦ P^p ⊗ f_*G` is `f_*` of `p ↦ f^*P^p ⊗ G`, granted that every component of the canonical map
is invertible. -/
def rowComplexPushforwardIso (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (h : ∀ F, IsIso (pushforwardTensorMap f F G))
    (P : CochainComplex (_root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) ℤ) :
    CochainComplex.KFlatBifunctor.rowComplex (Tensor.sheafTensor Y.O) P
        ((pushforwardModules f).obj G) ≅
      ((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.KFlatBifunctor.rowComplex (Tensor.sheafTensor X.O)
          ((f.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) G) :=
  (NatIso.mapHomologicalComplex (pushforwardTensorNatIso f G h) (ComplexShape.up ℤ)).app P

end Stacks.SheafOfModules
