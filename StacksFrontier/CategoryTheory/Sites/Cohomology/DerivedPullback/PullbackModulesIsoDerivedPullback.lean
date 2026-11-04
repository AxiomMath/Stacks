module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# The action of an isomorphism of pullbacks of modules on derived pullbacks

An isomorphism `φ^* ≅ ψ^*` between the pullbacks of modules along two morphisms of ringed topoi
`X ⟶ Y` (for instance a 2-isomorphism of morphisms of ringed topoi) induces `Lφ^* ≅ Lψ^*`, by the
universal property of the two left derived functors (Stacks 06YY). This file constructs it and
records its compatibility with the comparison of Stacks 0D6D for a composite.

## Main definitions

* `derivedPullbackIsoOfPullbackModulesIso`: the isomorphism `Lφ^* ≅ Lψ^*` induced by
  `φ^* ≅ ψ^*`.

## Main results

* `derivedPullbackIsoOfPullbackModulesIso_hom_app`: it is compatible with the two comparisons
  and with the isomorphism of pullbacks.
* `derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app`: the
  comparison of Stacks 0D6D followed by it is induced by the underived compositor.

All names are in the namespace `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Cohomology.DerivedPullbackOfToposHom

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Comparison

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
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

/-- **Isomorphic degreewise pullbacks have isomorphic derived pullbacks.**  An isomorphism
`φ^* ≅ ψ^*` between the pullbacks of modules along two morphisms of ringed topoi `X ⟶ Y` induces
`Lφ^* ≅ Lψ^*`, by the universal property of the two left derived functors.  This is how a
2-isomorphism of morphisms of ringed topoi acts on derived pullbacks. -/
def derivedPullbackIsoOfPullbackModulesIso {φ ψ : RingedToposHom X Y}
    [(pullbackOnHomotopy φ).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
    [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
    (e : φ.toModulesHom.pullbackModules ≅ ψ.toModulesHom.pullbackModules) :
    derivedPullback φ ≅ derivedPullback ψ :=
  Functor.leftDerivedNatIso (derivedPullback φ) (derivedPullback ψ)
    (derivedPullbackComparison φ) (derivedPullbackComparison ψ) (quasiIsoTarget (Y := Y))
    (Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The isomorphism `derivedPullbackIsoOfPullbackModulesIso` is compatible with the two
comparisons of Stacks 06YY and with `e`, which characterizes it. -/
theorem derivedPullbackIsoOfPullbackModulesIso_hom_app {φ ψ : RingedToposHom X Y}
    [(pullbackOnHomotopy φ).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
    [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
    (e : φ.toModulesHom.pullbackModules ≅ ψ.toModulesHom.pullbackModules)
    (K : HomotopyCategory
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))
      (ComplexShape.up ℤ)) :
    (derivedPullbackIsoOfPullbackModulesIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison ψ).app K =
      (derivedPullbackComparison φ).app K ≫
        DerivedCategory.Qh.map
          ((Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app K) :=
  Functor.leftDerivedNatTrans_app (derivedPullback φ) (derivedPullback ψ)
    (derivedPullbackComparison φ) (derivedPullbackComparison ψ) (quasiIsoTarget (Y := Y)) _ K

section Counit

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor (quasiIsoTarget (Y := Z))]

section Lift

variable [(pullbackOnHomotopy (g.comp f)).HasLeftDerivedFunctor (quasiIsoTarget (Y := Z))]

/-- **The comparison of Stacks 0D6D, followed by a 2-isomorphism, is induced by the underived
compositor.**  For a morphism of ringed topoi `h : X ⟶ Z` and an isomorphism
`e : (g ∘ f)^* ≅ h^*` of pullbacks of modules, the comparison `Lg^* ⋙ Lf^* ⟶ L(g ∘ f)^*`
followed by the action of `e` and by the comparison `Lh^* ⟶ h^*` is the comparison for `Lg^*`,
then the one for `Lf^*`, then `Q` of the underived compositor followed by `e`. -/
theorem derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    {h : RingedToposHom X Z}
    [(pullbackOnHomotopy h).HasLeftDerivedFunctor (quasiIsoTarget (Y := Z))]
    (e : (g.comp f).toModulesHom.pullbackModules ≅ h.toModulesHom.pullbackModules)
    (K : HomotopyCategory
      (SheafOfModules.{w''} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)))
      (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparison f g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackIsoOfPullbackModulesIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison h).app K =
      (derivedPullback f).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso f g ≪≫
          Stacks.Homology.mapHomotopyCategoryIso e (ComplexShape.up ℤ)).hom.app K) := by
  rw [derivedPullbackIsoOfPullbackModulesIso_hom_app, ← Category.assoc,
    derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

end Lift

end Counit

end Comparison

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
