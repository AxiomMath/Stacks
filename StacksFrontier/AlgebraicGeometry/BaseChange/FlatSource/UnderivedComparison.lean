module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.UnderivedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapUnderived
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The underived base change map of a square of schemes

The underived base change map `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of a commutative square of ringed
spaces on sheaves of modules, its mate, and its relation with the underived base change map on
homotopy categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

variable {X' X S' S : RingedSpace.{u, u}}

/-- For `a = b`, the conjugate of the transport `a^* = b^*` of pullbacks under the
pullback--pushforward adjunctions is the transport `b_* = a_*` of pushforwards. -/
theorem conjugateEquiv_eqToHom_modulePullback {a b : X ⟶ S} (h : a = b) :
    conjugateEquiv (modulePullbackPushforwardAdjunction b) (modulePullbackPushforwardAdjunction a)
      (eqToHom (congrArg modulePullback h)) =
      eqToHom (congrArg modulePushforward h.symm) := by
  subst h
  simp

/-- The conjugate of the inverse of the composition isomorphism `b^* ⋙ a^* ≅ (a ≫ b)^*` of
pullbacks is the composition isomorphism `a_* ⋙ b_* ≅ (a ≫ b)_*` of pushforwards. -/
theorem conjugateEquiv_modulePullbackComp_inv {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) :
    conjugateEquiv ((modulePullbackPushforwardAdjunction b).comp
        (modulePullbackPushforwardAdjunction a)) (modulePullbackPushforwardAdjunction (a ≫ b))
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b).inv =
        (modulePushforwardComp a b).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv (modulePullbackPushforwardAdjunction b)
    (modulePullbackPushforwardAdjunction a) (modulePullbackPushforwardAdjunction (a ≫ b))
    (modulePushforwardComp a b)

/-- The conjugate of the composition isomorphism `b^* ⋙ a^* ≅ (a ≫ b)^*` of pullbacks is the
inverse of the composition isomorphism `a_* ⋙ b_* ≅ (a ≫ b)_*` of pushforwards. -/
theorem conjugateEquiv_modulePullbackComp_hom {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y)
    (b : Y ⟶ Z) :
    conjugateEquiv (modulePullbackPushforwardAdjunction (a ≫ b))
        ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction a))
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom = (modulePushforwardComp a
          b).inv := by
  have h := conjugateEquiv_comm ((modulePullbackPushforwardAdjunction b).comp
    (modulePullbackPushforwardAdjunction a)) (modulePullbackPushforwardAdjunction (a ≫ b))
    (α := (Stacks.DerivedPullback.Composition.modulePullbackComp a b).inv) (β :=
        (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom) (by simp)
  rw [conjugateEquiv_modulePullbackComp_inv] at h
  rw [← cancel_epi (modulePushforwardComp a b).hom, h, Iso.hom_inv_id]

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The comparison `g^* ⋙ f'^* ⟶ f^* ⋙ g'^*` of the two composites of degreewise pullbacks
around a commutative square of ringed spaces. -/
def pullbackCompSquare :
    TwoSquare (modulePullback g) (modulePullback f) (modulePullback f') (modulePullback g') :=
  TwoSquare.mk _ _ _ _ ((Stacks.DerivedPullback.Composition.modulePullbackComp f' g).hom ≫
    eqToHom (congrArg modulePullback
        sq.symm) ≫ (Stacks.DerivedPullback.Composition.modulePullbackComp g' f).inv)

/-- **The underived base change map** `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` on sheaves of modules: the mate
of `pullbackCompSquare` under the two pullback--pushforward adjunctions. -/
def moduleBaseChangeSquare :
    TwoSquare (modulePushforward f) (modulePullback g') (modulePullback g) (modulePushforward f') :=
  mateEquiv (modulePullbackPushforwardAdjunction f) (modulePullbackPushforwardAdjunction f')
    (pullbackCompSquare g' f' f g sq)

/-- The mate of `moduleBaseChangeSquare` under the pullback--pushforward adjunctions of the
horizontal morphisms is the composite of the composition isomorphisms of pushforwards. -/
@[sga "4 Vbis 3.2.2" "special case"]
theorem mateEquiv_moduleBaseChangeSquare :
    (mateEquiv (modulePullbackPushforwardAdjunction g') (modulePullbackPushforwardAdjunction g)
      (moduleBaseChangeSquare g' f' f g sq)).natTrans =
      (modulePushforwardComp g' f).hom ≫ eqToHom (congrArg modulePushforward sq) ≫
        (modulePushforwardComp f' g).inv := by
  rw [moduleBaseChangeSquare, iterated_mateEquiv_conjugateEquiv, pullbackCompSquare]
  show conjugateEquiv _ _ ((Stacks.DerivedPullback.Composition.modulePullbackComp f' g).hom ≫
    (eqToHom (congrArg modulePullback sq.symm) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp g' f).inv)) = _
  rw [← conjugateEquiv_comp _ (modulePullbackPushforwardAdjunction (f' ≫ g)),
    ← conjugateEquiv_comp _ (modulePullbackPushforwardAdjunction (g' ≫ f)),
    conjugateEquiv_modulePullbackComp_inv, conjugateEquiv_eqToHom_modulePullback sq.symm,
    conjugateEquiv_modulePullbackComp_hom, Category.assoc]

/-- The transport along an equality of morphisms of the functor induced on homotopy categories
by the pullback, at the class of a complex. -/
theorem eqToHom_mapHomotopyCategory_modulePullback_app {a b : X' ⟶ S} (e : a = b)
    (h : (modulePullback a).mapHomotopyCategory (ComplexShape.up ℤ) =
      (modulePullback b).mapHomotopyCategory (ComplexShape.up ℤ))
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (eqToHom h).app K =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (eqToHom (congrArg modulePullback e))
          (ComplexShape.up ℤ)).app K.as) := by
  subst e
  simp only [eqToHom_refl, NatTrans.id_app, NatTrans.mapHomologicalComplex_id,
    CategoryTheory.Functor.map_id]
  rfl

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange in
/-- **The underived base change map on homotopy categories, at the class of a complex, is the
class of the underived base change map of sheaves of modules applied termwise.** -/
theorem underivedBaseChangeSquare_app_quotient
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (underivedBaseChangeSquare g' f' f g sq).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (moduleBaseChangeSquare g' f' f g sq).natTrans
          (ComplexShape.up ℤ)).app K) := by
  have hunit : ∀ (a : X' ⟶ S') (Y : HomotopyCategory _ (ComplexShape.up ℤ)),
      (homotopyPullbackPushforwardAdjunction a).unit.app Y =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction a)
            (ComplexShape.up ℤ)).unit.app Y.as) := fun _ _ => rfl
  have hcounit : ∀ (a : X ⟶ S) (Y : HomotopyCategory _ (ComplexShape.up ℤ)),
      (homotopyPullbackPushforwardAdjunction a).counit.app Y =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction a)
            (ComplexShape.up ℤ)).counit.app Y.as) := fun _ _ => rfl
  have hcomp : ∀ {A B : RingedSpace.{u, u}} (a : X' ⟶ A) (b : A ⟶ B)
      (Y : HomotopyCategory _ (ComplexShape.up ℤ)),
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a b).hom.app Y =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (Stacks.DerivedPullback.Composition.modulePullbackComp a b).hom
            (ComplexShape.up ℤ)).app Y.as) := fun _ _ _ => rfl
  have hcomp' : ∀ {A B : RingedSpace.{u, u}} (a : X' ⟶ A) (b : A ⟶ B)
      (Y : HomotopyCategory _ (ComplexShape.up ℤ)),
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a b).inv.app Y =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (Stacks.DerivedPullback.Composition.modulePullbackComp a b).inv
            (ComplexShape.up ℤ)).app Y.as) := fun _ _ _ => rfl
  rw [underivedBaseChangeSquare, moduleBaseChangeSquare, pullbackCompSquare,
    pullbackOnHomotopyCompIsoLeft_eq]
  simp only [mateEquiv_apply, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
    Iso.trans_hom, eqToIso.hom, hunit, hcounit, hcomp, hcomp', Functor.comp_map,
    eqToHom_mapHomotopyCategory_modulePullback_app sq.symm, Functor.mapHomotopyCategory_map,
    Functor.comp_obj, Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as,
    ← Functor.map_comp]
  congr 1

section Scheme

variable {X' X S' S : Scheme.{u}}

/-- `Scheme.Modules.pushforwardCongr` is the transport along the equality of the underlying
morphisms of ringed spaces. -/
theorem pushforwardCongr_hom_eq_eqToHom {a b : X ⟶ S} (h : a = b)
    (h' : a.toLRSHom.toShHom = b.toLRSHom.toShHom) :
    (Scheme.Modules.pushforwardCongr h).hom = eqToHom (congrArg modulePushforward h') := by
  subst h
  ext M U x
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id, eqToHom_refl]
  rfl

/-- `Scheme.Modules.pushforwardComp` is `modulePushforwardComp` of the underlying morphisms of
ringed spaces. -/
theorem pushforwardComp_hom_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Scheme.Modules.pushforwardComp a b).hom =
      (modulePushforwardComp a.toLRSHom.toShHom b.toLRSHom.toShHom).hom := by
  ext M U x
  rfl

/-- `Scheme.Modules.pushforwardComp` is `modulePushforwardComp` of the underlying morphisms of
ringed spaces. -/
theorem pushforwardComp_inv_eq {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Scheme.Modules.pushforwardComp a b).inv =
      (modulePushforwardComp a.toLRSHom.toShHom b.toLRSHom.toShHom).inv := by
  ext M U x
  rfl

/-- **The underived base change map of a commutative square of schemes is the base-change
morphism of [Stacks, Tag 02KG].**  The mate of the comparison of the two composites of
pullbacks is the mate, across the other pair of adjunctions, of the comparison of the two
composites of pushforwards. -/
theorem moduleBaseChangeSquare_eq_baseChangeNatTrans {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) :
    (moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom sq).natTrans = ModuleBaseChange.baseChangeNatTrans w := by
  have h := mateEquiv_moduleBaseChangeSquare g'.toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom g.toLRSHom.toShHom sq
  rw [ModuleBaseChange.baseChangeNatTrans, AffinePushforward.baseChangeNatTrans,
    pushforwardComp_hom_eq, pushforwardComp_inv_eq, pushforwardCongr_hom_eq_eqToHom w sq]
  exact (Equiv.eq_symm_apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g))).2 h

end Scheme

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
