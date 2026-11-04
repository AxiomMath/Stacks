module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizes

/-!
# Derived pullback along an identity transition, without flatness

This file identifies the derived pullback along the transition of an identity simplex map with
the identity functor, without any flatness of the transitions.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIdIsoOfKFlat`: derived pullback
  along the transition of an identity simplex map is the identity functor, with no flatness
  hypothesis (the base's `derivedTransitionPullbackIdIso` assumes flatness). Hence `Lf_𝟙^*` is
  faithful.

## References

* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- Degreewise pullback along the transition of an identity simplex map, followed by
localization, is the localization functor: the pullback of sheaves of modules along that
transition is the identity functor (Stacks 09WF). -/
def pullbackOnHomotopyTransitionIdIso (n : SimplexCategory) :
    DerivedCategory.Qh ⋙ 𝟭 _ ≅
      pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O (𝟙 n)) := by
  let e := S.transitionPullbackModulesIdToposIso O n
  let eK : (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules.mapHomotopyCategory
      (ComplexShape.up ℤ) ≅ (𝟭 ((S.componentRingedTopos O n).Modules)).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id] }
  exact Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      rintro ⟨K⟩ ⟨L⟩ ⟨f : K ⟶ L⟩
      exact (Category.comp_id _).trans (Category.id_comp _).symm) :
        (𝟭 ((S.componentRingedTopos O n).Modules)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
          𝟭 _).symm _ ≪≫
    Functor.isoWhiskerRight eK.symm _

/-- **Derived pullback along the transition of an identity simplex map is the identity
functor**, with no flatness hypothesis. Both are left derived functors of degreewise pullback
along that transition: `Lf_𝟙^*` by definition, and the identity functor because that degreewise
pullback is isomorphic to the localization functor. -/
def derivedTransitionPullbackIdIsoOfKFlat (n : SimplexCategory) :
    S.derivedTransitionPullback O (𝟙 n) ≅
      𝟭 (DerivedCategory (S.componentRingedTopos O n).Modules) :=
  haveI : (𝟭 (DerivedCategory (S.componentRingedTopos O n).Modules)).IsLeftDerivedFunctor
      (S.pullbackOnHomotopyTransitionIdIso O n).hom
      (targetQuasiIso (S.componentRingedTopos O n)) :=
    isLeftDerivedFunctor_of_inverts _ _ (S.pullbackOnHomotopyTransitionIdIso O n)
  leftDerivedNatIso _ _ (S.derivedTransitionComparison O (𝟙 n))
    (S.pullbackOnHomotopyTransitionIdIso O n).hom
    (targetQuasiIso (S.componentRingedTopos O n)) (Iso.refl _)

end CategoryTheory.SimplicialSiteSituation

end
