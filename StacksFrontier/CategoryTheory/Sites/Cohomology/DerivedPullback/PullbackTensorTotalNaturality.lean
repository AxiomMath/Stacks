module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-! # The comparison of total tensor complexes is natural in the pair of complexes

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi and let `K`, `L` be cochain
complexes of `O'`-modules. The comparison

`f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`,

whose component on the summand of bidegree `(p, q)` is the comparison of **Stacks 03EL**, is
natural in `K` and in `L`: for morphisms `a : K ⟶ K'` and `b : L ⟶ L'` the square formed with
the total tensor product of `a` and `b` commutes.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_hom_naturality`: the naturality square
  of the comparison of total tensor complexes.

## Implementation notes

The square is proved on the degreewise summands rather than at the level of bicomplexes. Both
sides are morphisms out of `f^*Tot(K ⊗_{O'} L)` in a fixed total degree, and pullback preserves
the coproduct decomposition of a total complex, so `hom_ext_pullbackTotal` reduces the square to
its restriction along the `f^*`-image of each summand inclusion. There the comparison acts by
Stacks 03EL in the bidegree, which is `ι_pullbackTensorTotalIso_hom`, and the summand inclusions
intertwine with the total tensor product of `a` and `b` by
`HomologicalComplex.ι_mapBifunctorMap`; what remains is exactly the naturality of Stacks 03EL in
both modules at once.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

namespace Stacks.Sheaves.DerivedPullback

open Stacks.SheafOfModules

private lemma map_square_naturality
    {Source Target : Type*} [Category Source] [Category Target] (functor : Source ⥤ Target)
    {sourceTerm sourceTerm' sourceTotal sourceTotal' : Source}
    {targetTerm targetTerm' targetTotal targetTotal' : Target}
    {sourceInclusion : sourceTerm ⟶ sourceTotal}
    {sourceInclusion' : sourceTerm' ⟶ sourceTotal'}
    {sourceMap : sourceTotal ⟶ sourceTotal'} {sourceTermMap : sourceTerm ⟶ sourceTerm'}
    {targetInclusion : targetTerm ⟶ targetTotal}
    {targetInclusion' : targetTerm' ⟶ targetTotal'}
    {targetMap : targetTotal ⟶ targetTotal'} {targetTermMap : targetTerm ⟶ targetTerm'}
    {comparison : functor.obj sourceTotal ⟶ targetTotal}
    {comparison' : functor.obj sourceTotal' ⟶ targetTotal'}
    {termComparison : functor.obj sourceTerm ⟶ targetTerm}
    {termComparison' : functor.obj sourceTerm' ⟶ targetTerm'}
    (sourceSquare : sourceInclusion ≫ sourceMap = sourceTermMap ≫ sourceInclusion')
    (targetSquare : targetInclusion ≫ targetMap = targetTermMap ≫ targetInclusion')
    (comparisonSquare : functor.map sourceInclusion ≫ comparison =
      termComparison ≫ targetInclusion)
    (comparisonSquare' : functor.map sourceInclusion' ≫ comparison' =
      termComparison' ≫ targetInclusion')
    (naturality : functor.map sourceTermMap ≫ termComparison' =
      termComparison ≫ targetTermMap) :
    functor.map sourceInclusion ≫ functor.map sourceMap ≫ comparison' =
      functor.map sourceInclusion ≫ comparison ≫ targetMap := by
  rw [← Category.assoc, ← functor.map_comp, sourceSquare, functor.map_comp,
    Category.assoc, comparisonSquare', ← Category.assoc, naturality, Category.assoc,
    ← targetSquare, ← Category.assoc, ← comparisonSquare, Category.assoc]

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
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)]

/-- **The comparison of total tensor complexes is natural in the pair of complexes.** For
morphisms `a : K ⟶ K'` and `b : L ⟶ L'` of cochain complexes of `O'`-modules, the comparison
`f^*Tot(- ⊗_{O'} -) ≅ Tot(f^*- ⊗_O f^*-)` commutes with the total tensor product of `a` and
`b`. -/
lemma pullbackTensorTotalIso_hom_naturality
    {K K' L L' :
      CochainComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (pullbackComplexFunctor f).map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'} Y.O) (ComplexShape.up ℤ)) ≫
        (pullbackTensorTotalIso f K' L').hom =
      (pullbackTensorTotalIso f K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((pullbackComplexFunctor f).map a)
          ((pullbackComplexFunctor f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine hom_ext_pullbackTotal f K L n (fun p q hpq => ?_)
  exact map_square_naturality (f.pullbackModules)
    (by rw [HomologicalComplex.ι_mapBifunctorMap]; exact (Category.assoc _ _ _).symm)
    (by rw [HomologicalComplex.ι_mapBifunctorMap]; exact (Category.assoc _ _ _).symm)
    (ι_pullbackTensorTotalIso_hom f K L p q n hpq)
    (ι_pullbackTensorTotalIso_hom f K' L' p q n hpq)
    (pullbackTensorIso_hom_naturality_map f (a.f p) (b.f q))

end Stacks.Sheaves.DerivedPullback

end
