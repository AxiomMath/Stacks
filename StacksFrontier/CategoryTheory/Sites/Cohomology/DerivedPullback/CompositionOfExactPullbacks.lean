module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedIsoMapDerivedCategoryOfIsoComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# Derived pullbacks along morphisms with exact pullbacks, and composition

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` be morphisms of ringed topoi with
`e : (g ∘ f)^* ≅ h^*`, and suppose the pullbacks of modules are isomorphic to exact functors
`G_g`, `G_f`, `G_h` compatibly with `G_g ⋙ G_f ≅ G_h`. Then the identifications
`Lφ^* ≅ D(G_φ)` carry the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lh^*` of Stacks
0D6D to the composition isomorphism `D(G_g) ⋙ D(G_f) ≅ D(G_h)`.

## Main results

* `derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategoryOfIso`: the identifications
  `Lφ^* ≅ D(G_φ)` intertwine the two composition isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-- **Derived pullbacks along morphisms with exact pullbacks compose as the exact functors.** -/
theorem derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategoryOfIso
    {h : RingedToposHom X Z}
    (e : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    (G₁ : SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
    (G₂ : SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⥤
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (G₃ : SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⥤
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    [G₁.Additive] [G₂.Additive] [G₃.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
    (e₁ : g.toModulesHom.pullbackModules ≅ G₁) (e₂ : f.toModulesHom.pullbackModules ≅ G₂)
    (e₃ : h.toModulesHom.pullbackModules ≅ G₃) (v : G₁ ⋙ G₂ ≅ G₃)
    (hmod : ((RingedToposHom.pullbackModulesCompIso f g).symm ≪≫ e).hom ≫ e₃.hom =
      Functor.whiskerRight e₁.hom (f.toModulesHom.pullbackModules) ≫
        Functor.whiskerLeft G₁ e₂.hom ≫ v.hom) :
    (derivedPullbackCompIso f g ≪≫ derivedPullbackIsoOfPullbackModulesIso e).hom ≫
        (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ G₃ (derivedPullback h)
          (derivedPullbackComparison h) e₃).hom =
      Functor.whiskerRight (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ G₁
          (derivedPullback g) (derivedPullbackComparison g) e₁).hom (derivedPullback f) ≫
        Functor.whiskerLeft G₁.mapDerivedCategory
          (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso _ G₂
            (derivedPullback f) (derivedPullbackComparison f) e₂).hom ≫
        (Stacks.Homology.mapDerivedCategoryCompIso G₁ G₂ G₃ v).hom :=
  Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_comp_of_trans _ G₁ _ G₂ _ _ G₃
    (derivedPullback g) (derivedPullbackComparison g) (derivedPullback f)
    (derivedPullbackComparison f) (derivedPullback h) (derivedPullbackComparison h) e₁ e₂ e₃
    (RingedToposHom.pullbackModulesCompIso f g).symm e v hmod _ fun K => by
      rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc, derivedPullbackCompIso_hom]
      exact derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app f g e K

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
