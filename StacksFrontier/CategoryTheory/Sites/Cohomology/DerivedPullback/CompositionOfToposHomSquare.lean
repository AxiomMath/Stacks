module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# Derived pullbacks around a square of morphisms of ringed topoi, on complexes

For morphisms of ringed topoi `f : X ⟶ Y`, `g : Y ⟶ Z`, `f' : X ⟶ Y'`, `g' : Y' ⟶ Z` and an
isomorphism `e : (g ∘ f)^* ≅ (g' ∘ f')^*` of pullbacks of modules, Stacks 0D6D gives the
isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ L(g' ∘ f')^* ≅ Lg'^* ⋙ Lf'^*`. This file computes it on
a complex: after the comparisons with degreewise pullback it is degreewise pullback of `e`,
conjugated by the compositors of pullbacks of modules.

## Main results

In the namespace `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`:

* `pullbackMapHomotopySquareIso`
* `derivedPullbackSquareIso_hom_app_comparison`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v₁ u₁ w₁ v'' u'' w''

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Y' : RingedTopos.{v₁, u₁, w₁}} {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Y'.J.HasSheafCompose (forget RingCat.{w₁})] [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y'.J AddCommGrpCat.{w₁}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Y'.J (Type w₁)]
  [HasSheafify Z.J (Type w'')]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (f' : RingedToposHom X Y')
  (g' : RingedToposHom Y' Z)

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-- The degreewise counterpart of the isomorphism of Stacks 0D6D around a square: the
compositors of degreewise pullbacks and degreewise pullback of `e`. -/
def pullbackMapHomotopySquareIso
    (e : (g.comp f).toModulesHom.pullbackModules ≅ (g'.comp f').toModulesHom.pullbackModules) :
    DerivedPushforward.pullbackMapHomotopy g ⋙ DerivedPushforward.pullbackMapHomotopy f ≅
      DerivedPushforward.pullbackMapHomotopy g' ⋙ DerivedPushforward.pullbackMapHomotopy f' :=
  pullbackMapHomotopyCompIso f g ≪≫
    Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ) ≪≫
    (pullbackMapHomotopyCompIso f' g').symm

/-- **The derived pullbacks around a square agree with the degreewise ones on complexes.** The
isomorphism `Lg^* ⋙ Lf^* ≅ Lg'^* ⋙ Lf'^*` of Stacks 0D6D attached to
`e : (g ∘ f)^* ≅ (g' ∘ f')^*`, followed by the comparisons of `Lg'^*` and `Lf'^*`, is the
comparisons of `Lg^*` and `Lf^*` followed by degreewise pullback of `e` between the compositors. -/
theorem derivedPullbackSquareIso_hom_app_comparison
    (e : (g.comp f).toModulesHom.pullbackModules ≅ (g'.comp f').toModulesHom.pullbackModules)
    (K : HomotopyCategory
      (SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompIso f g ≪≫ derivedPullbackIsoOfPullbackModulesIso e ≪≫
          (derivedPullbackCompIso f' g').symm).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullback f').map ((derivedPullbackComparison g').app K) ≫
        (derivedPullbackComparison f').app
          ((DerivedPushforward.pullbackMapHomotopy g').obj K) =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopySquareIso f g f' g' e).hom.app K) := by
  unfold pullbackMapHomotopySquareIso
  have h' := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f' g' K
  have hinv : (derivedPullbackCompIso f' g').inv.app (DerivedCategory.Qh.obj K) ≫
      (derivedPullback f').map ((derivedPullbackComparison g').app K) ≫
      (derivedPullbackComparison f').app ((DerivedPushforward.pullbackMapHomotopy g').obj K) =
      (derivedPullbackComparison (g'.comp f')).app K ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f' g').inv.app K) := by
    rw [← cancel_epi ((derivedPullbackCompIso f' g').hom.app (DerivedCategory.Qh.obj K)),
      Iso.hom_inv_id_app_assoc, derivedPullbackCompIso_hom, ← Category.assoc, h']
    simp [← Functor.map_comp]
  have h := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app f g e K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, hinv]
  rw [derivedPullbackCompIso_hom, ← Category.assoc
    ((derivedPullbackIsoOfPullbackModulesIso e).hom.app _), ← Category.assoc, h]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
