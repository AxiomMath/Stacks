module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplex

/-!
# The canonical map of de Rham complexes attached to a commutative square

For a commutative square of schemes this file constructs the canonical maps
`Ω^p_{X/S} ⟶ (g')_*Ω^p_{X'/S'}` of `f^{-1}𝒪_S`-modules, the map of de Rham complexes
`Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`, and its adjoint `g₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`, where
`g₀` is the induced morphism of inverse-image ringed spaces.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The ring-sheaf components of the two composites of the square
`toInverseImageBase_comp_inverseImageBaseMap` agree. -/
theorem toRingCatSheafHom_square :
    toRingCatSheafHom (toInverseImageBase f' ≫ inverseImageBaseMap g' f' f g w) =
      toRingCatSheafHom (g'.toLRSHom.toShHom ≫ toInverseImageBase f) := by
  have h := congrArg (fun m => m.hom) (toInverseImageBase_comp_inverseImageBaseMap g' f' f g w)
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  show (forget₂ CommRingCat RingCat).map
      ((toInverseImageBase f' ≫ inverseImageBaseMap g' f' f g w).hom.c.app U) =
    (forget₂ CommRingCat RingCat).map ((g'.toLRSHom.toShHom ≫ toInverseImageBase f).hom.c.app U)
  rw [PresheafedSpace.congr_app h U]
  exact congrArg (forget₂ CommRingCat RingCat).map
    ((congrArg (fun t => (g'.toLRSHom.toShHom ≫ toInverseImageBase f).hom.c.app U ≫
      X'.toRingedSpace.presheaf.map t) (eqToHom_refl _ rfl)).trans
      ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)))

/-- The identification of the two composite pushforward functors of the square
`toInverseImageBase_comp_inverseImageBaseMap`. -/
def pushforwardSquareIso :
    _root_.pushforward (toInverseImageBase f') ⋙
        _root_.pushforward (inverseImageBaseMap g' f' f g w) ≅
      _root_.pushforward g'.toLRSHom.toShHom ⋙ _root_.pushforward (toInverseImageBase f) :=
  (_root_.pushforwardComp (toInverseImageBase f') (inverseImageBaseMap g' f' f g w)).symm ≪≫
    SheafOfModules.pushforwardCongr (toRingCatSheafHom_square g' f' f g w) ≪≫
      _root_.pushforwardComp g'.toLRSHom.toShHom (toInverseImageBase f)

/-- The identification of the two composite pushforwards is the identity on sections. -/
theorem pushforwardSquareIso_inv_val_app (M : Modules X'.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ)
    (x : (((_root_.pushforward g'.toLRSHom.toShHom ⋙
      _root_.pushforward (toInverseImageBase f)).obj M)).val.obj U) :
    ((pushforwardSquareIso g' f' f g w).inv.app M).val.app U x = x :=
  rfl

/-- The adjoint `Ω^p_{X/S} ⟶ (g')_*Ω^p_{X'/S'}` of the canonical map
`(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` of Stacks 07HX. -/
def formsAdjoint (p : ℕ) :
    Scheme.Hom.relativeDifferentialForms f (p : ℤ) ⟶
      (Scheme.Modules.pushforward g').obj (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app _ ≫
    (Scheme.Modules.pushforward g').map (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p)

/-- On sections the adjoint of the canonical map is the pullback of differential forms. -/
theorem formsAdjoint_app (p : ℕ) (U : X.Opens)
    (ω : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U)) :
    (formsAdjoint g' f' f g w p).val.app (op U) ω =
      Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U ω :=
  rfl

/-- The degreewise maps `Ω^p_{X/S} ⟶ (g₀)_*Ω^p_{X'/S'}` of `f^{-1}𝒪_S`-modules. -/
def formsPushforward (p : ℕ) :
    (Scheme.Hom.deRhamComplex f).X p ⟶
      (_root_.pushforward (inverseImageBaseMap g' f' f g w)).obj
        ((Scheme.Hom.deRhamComplex f').X p) :=
  (_root_.pushforward (toInverseImageBase f)).map (formsAdjoint g' f' f g w p) ≫
    (pushforwardSquareIso g' f' f g w).inv.app (Scheme.Hom.relativeDifferentialForms f' (p : ℤ))

/-- **The canonical map of de Rham complexes `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`** of a commutative
square, as a morphism of complexes of `f^{-1}𝒪_S`-modules. -/
def deRhamPushforwardChain :
    Scheme.Hom.deRhamComplex f ⟶
      ((_root_.pushforward (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Scheme.Hom.deRhamComplex f') where
  f := formsPushforward g' f' f g w
  comm' := by
    rintro n m rfl
    ext U x
    change ((Scheme.Hom.deRhamComplex f').d n (n + 1)).val.app
          ((opensMap g'.toLRSHom.toShHom).op.obj U)
          (((pushforwardSquareIso g' f' f g w).inv.app
              (Scheme.Hom.relativeDifferentialForms f' (n : ℤ))).val.app U
            ((formsAdjoint g' f' f g w n).val.app U x)) =
        ((pushforwardSquareIso g' f' f g w).inv.app
            (Scheme.Hom.relativeDifferentialForms f' ((n + 1 : ℕ) : ℤ))).val.app U
          ((formsAdjoint g' f' f g w (n + 1)).val.app U
            (((Scheme.Hom.deRhamComplex f).d n (n + 1)).val.app U x))
    refine Eq.trans (congrArg (fun z => (((Scheme.Hom.deRhamComplex f').d n (n + 1)).val.app
        ((opensMap g'.toLRSHom.toShHom).op.obj U)) z)
      (pushforwardSquareIso_inv_val_app g' f' f g w
        (Scheme.Hom.relativeDifferentialForms f' (n : ℤ)) U
        ((formsAdjoint g' f' f g w n).val.app U x))) ?_
    exact (Scheme.Hom.deRhamComplex_d_relativeDifferentialFormsPullback g' f f' g w n U.unop
      x).trans (pushforwardSquareIso_inv_val_app g' f' f g w
        (Scheme.Hom.relativeDifferentialForms f' ((n + 1 : ℕ) : ℤ)) U
        ((formsAdjoint g' f' f g w (n + 1)).val.app U
          (((Scheme.Hom.deRhamComplex f).d n (n + 1)).val.app U x))).symm

/-- **The canonical morphism of complexes `g₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`** of
`f'^{-1}𝒪_{S'}`-modules attached to a commutative square, adjoint to
`deRhamPushforwardChain`. -/
def deRhamPullbackChain :
    ((_root_.pullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (Scheme.Hom.deRhamComplex f) ⟶
      Scheme.Hom.deRhamComplex f' :=
  (((_root_.pullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _).symm (deRhamPushforwardChain g' f' f g w)

end Stacks.DeRhamBaseChange

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The transport of pushforwards along the commutativity of the square
`toInverseImageBase_comp_inverseImageBaseMap` is the identity on sections. -/
theorem eqToHom_square_app_val_app (M : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj (op ((opensMap g'.toLRSHom.toShHom).obj U.unop))) :
    ((eqToHom (congrArg modulePushforward
        (toInverseImageBase_comp_inverseImageBaseMap g' f' f g
            w).symm)).app M).val.app U x = x := by
  have h := Stacks.DeRhamPullback.eqToIso_pushforward_inv_app_val_app
    (toInverseImageBase_comp_inverseImageBaseMap g' f' f g w) M U x
  exact eq_of_heq h

end Stacks.DeRhamBaseChange
