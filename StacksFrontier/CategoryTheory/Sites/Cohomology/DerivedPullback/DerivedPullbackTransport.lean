module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom

/-!
# Transporting the derived pullback along an isomorphism of underived pullbacks

Let `h₁ h₂ : (Sh(C), O) ⟶ (Sh(C'), O')` be two morphisms of ringed topoi and let
`e : h₁^* ≅ h₂^*` be an isomorphism of the degreewise pullbacks of sheaves of modules. Both
derived pullbacks `Lh₁^*` and `Lh₂^*` of Tag 06YY are total left derived functors, and the
underived functors they derive are isomorphic through `e`, so the universal property gives a
canonical isomorphism `Lh₁^* ≅ Lh₂^*`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopyIsoOfIso`: the isomorphism of
  the degreewise pullbacks followed by localization.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoOfIso`: the induced isomorphism
  of derived pullbacks.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackIsoOfIso_hom_comparison`: the
  isomorphism is compatible with the two comparisons `Lhᵢ^* ⟶ hᵢ^*`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

open AlgebraicGeometry AlgebraicGeometry.RingedToposHom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (h₁ h₂ : RingedToposHom X Y)
  (e : h₁.toModulesHom.pullbackModules ≅ h₂.toModulesHom.pullbackModules)

/-- An isomorphism of degreewise pullbacks of sheaves of modules, read on the unbounded homotopy
categories and followed by localization. -/
def pullbackOnHomotopyIsoOfIso : pullbackOnHomotopy h₁ ≅ pullbackOnHomotopy h₂ :=
  Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
    DerivedCategory.Qh

omit [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The component of `pullbackOnHomotopyIsoOfIso` at a complex `K` is the localization of the
component at `K` of `e.hom` applied degreewise. -/
@[simp]
theorem pullbackOnHomotopyIsoOfIso_hom_app
    (K : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (pullbackOnHomotopyIsoOfIso h₁ h₂ e).hom.app K =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) :=
  rfl

variable [(pullbackOnHomotopy h₁).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]
  [(pullbackOnHomotopy h₂).HasLeftDerivedFunctor (quasiIsoTarget (Y := Y))]

/-- The isomorphism `Lh₁^* ≅ Lh₂^*` of derived pullbacks induced by an isomorphism `e` of the
underived pullbacks, given by the universal property of the total left derived functor. -/
def derivedPullbackIsoOfIso : derivedPullback h₁ ≅ derivedPullback h₂ :=
  Functor.leftDerivedNatIso (derivedPullback h₁) (derivedPullback h₂)
    (derivedPullbackComparison h₁) (derivedPullbackComparison h₂) (quasiIsoTarget (Y := Y))
    (pullbackOnHomotopyIsoOfIso h₁ h₂ e)

/-- The isomorphism `derivedPullbackIsoOfIso` is compatible with the comparisons
`derivedPullbackComparison h₁` and `derivedPullbackComparison h₂` and with the given isomorphism
of underived pullbacks. -/
@[reassoc]
theorem derivedPullbackIsoOfIso_hom_comparison
    (K : HomotopyCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackIsoOfIso h₁ h₂ e).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison h₂).app K =
      (derivedPullbackComparison h₁).app K ≫ (pullbackOnHomotopyIsoOfIso h₁ h₂ e).hom.app K :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (quasiIsoTarget (Y := Y)) _ K

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
