module

public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# The tensorator of the monoidal functor induced on homological complexes

For a monoidal additive functor `F : C ⥤ D` preserving the antidiagonal coproducts of the total
complex, `CategoryTheory.Functor.mapHomologicalComplexMonoidal` makes `F.mapHomologicalComplex c`
a monoidal functor whose tensorator is `CategoryTheory.Functor.mapHomologicalComplexTensorator`.
This file records that identification for `CategoryTheory.Functor.LaxMonoidal.μ`, together with
its value on the summands of the total complex, which is the form in which a consumer that only
ever sees `μ` computes the tensorator.

## Main results

* `CategoryTheory.Functor.mu_mapHomologicalComplex`: the tensorator of
  `F.mapHomologicalComplex c` is `CategoryTheory.Functor.mapHomologicalComplexTensorator`.
* `CategoryTheory.Functor.ι_mu_mapHomologicalComplex`: its value on the summands of its source.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalCategory D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ X₁ : D, ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

section

variable [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ : GradedObject I D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂ : D, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject I D, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject I D, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ n : I, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) F]


/-- **The tensorator of the monoidal structure on `F.mapHomologicalComplex c` is
`CategoryTheory.Functor.mapHomologicalComplexTensorator`.**  The structure is built from that
isomorphism by `CategoryTheory.Functor.CoreMonoidal.toMonoidal`, so the two agree by
definition. -/
public lemma mu_mapHomologicalComplex (K₁ K₂ : HomologicalComplex C c) :
    Functor.LaxMonoidal.μ (F.mapHomologicalComplex c) K₁ K₂ =
      (mapHomologicalComplexTensorator F K₁ K₂).hom :=
  rfl

/-- **The tensorator of `F.mapHomologicalComplex c` on the summands of its source**, stated for
`Functor.LaxMonoidal.μ` rather than for
`CategoryTheory.Functor.mapHomologicalComplexTensorator`: this is
`CategoryTheory.Functor.ι_mapHomologicalComplexTensorator_hom` read through
`CategoryTheory.Functor.mu_mapHomologicalComplex`. -/
@[reassoc]
public lemma ι_mu_mapHomologicalComplex (K₁ K₂ : HomologicalComplex C c) (p q n : I)
    (h : p + q = n) :
    HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex c).obj K₁)
        ((F.mapHomologicalComplex c).obj K₂) p q n h ≫
      (Functor.LaxMonoidal.μ (F.mapHomologicalComplex c) K₁ K₂).f n =
      μ F (K₁.X p) (K₂.X q) ≫ F.map (HomologicalComplex.ιTensorObj K₁ K₂ p q n h) :=
  ι_mapHomologicalComplexTensorator_hom F K₁ K₂ p q n h

end

end CategoryTheory.Functor

end
