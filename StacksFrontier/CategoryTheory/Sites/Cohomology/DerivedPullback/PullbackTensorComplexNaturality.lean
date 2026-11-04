module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# Naturality of the comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`

For a morphism of ringed topoi `f` the comparison
`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso` of the pullback of a total tensor complex
with the total tensor complex of the pullbacks (Stacks 03EL in each bidegree) is natural in the
second complex.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_hom_naturality_right`: the comparison
  is natural in the second complex.
* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalNatIso`: the comparison as an isomorphism
  of functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.Sheaves.DerivedPullback

open Stacks.SheafOfModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M :
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).Additive]
  [∀ M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj M :
      SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
        SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)]

/-- **The comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` is natural in `L`.** -/
lemma pullbackTensorTotalIso_hom_naturality_right
    (K : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    {L L' : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (v : L ⟶ L') :
    (pullbackComplexFunctor f).map (HomologicalComplex.mapBifunctorMap (𝟙 K) v
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)) ≫
      (pullbackTensorTotalIso f K L').hom =
    (pullbackTensorTotalIso f K L).hom ≫
      HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplexFunctor f).obj K))
        ((pullbackComplexFunctor f).map v)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ) := by
  ext n : 1
  refine hom_ext_pullbackTotal f K L n fun p q hpq => ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, ← Functor.map_comp, HomologicalComplex.ι_mapBifunctorMap,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ι_pullbackTensorTotalIso_hom f K L' p q n hpq,
    reassoc_of% (ι_pullbackTensorTotalIso_hom f K L p q n hpq),
    HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  rw [← Category.assoc, pullbackTensorIso_hom_naturality_snd, Category.assoc]

/-- **The comparison `f^*Tot(K ⊗ -) ≅ Tot(f^*K ⊗ f^*-)` as an isomorphism of functors.** -/
def pullbackTensorTotalNatIso
    (K : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K ⋙
        pullbackComplexFunctor f ≅
      pullbackComplexFunctor f ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
          ((pullbackComplexFunctor f).obj K) :=
  NatIso.ofComponents (fun L => pullbackTensorTotalIso f K L)
    (fun v => pullbackTensorTotalIso_hom_naturality_right f K v)

end Stacks.Sheaves.DerivedPullback

end
