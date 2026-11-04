module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamComplexBaseChange

/-!
# The degreewise components of the canonical map of de Rham complexes

The degree-`p` component of the canonical map `g₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` is the underived
base change map of the square of structural morphisms at `Ω^p_{X/S}` followed by the canonical
map `(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage
open Stacks.AlgebraicGeometry.FlatSourceBaseChange

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The commutativity of the square of the structural morphisms, in the orientation of a base
change square. -/
theorem toShHom_comp_toInverseImageBase :
    g'.toLRSHom.toShHom ≫ toInverseImageBase f =
      toInverseImageBase f' ≫ inverseImageBaseMap g' f' f g w :=
  (toInverseImageBase_comp_inverseImageBaseMap g' f' f g w).symm

/-- The underived base change map `(g₀)^*ι_* ⟶ ι'_*(g')^*` of the square of structural
morphisms. -/
abbrev structuralBaseChange :=
  (moduleBaseChangeSquare g'.toLRSHom.toShHom (toInverseImageBase f') (toInverseImageBase f)
    (inverseImageBaseMap g' f' f g w) (toShHom_comp_toInverseImageBase g' f' f g w)).natTrans

/-- The two identifications of the composite pushforwards of the square of structural
morphisms agree. -/
theorem pushforwardSquareIso_inv_app_eq (M : SheafOfModules.{u} (structureSheafRing
    X'.toRingedSpace)) :
    (pushforwardSquareIso g' f' f g w).inv.app M =
      ((modulePushforwardComp g'.toLRSHom.toShHom (toInverseImageBase f)).hom ≫
        eqToHom (congrArg modulePushforward (toShHom_comp_toInverseImageBase g' f' f g w)) ≫
        (modulePushforwardComp (toInverseImageBase f')
          (inverseImageBaseMap g' f' f g w)).inv).app M := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact (pushforwardSquareIso_inv_val_app g' f' f g w M U x).trans
    (eqToHom_square_app_val_app g' f' f g w M U x).symm

/-- The adjoint of the canonical map on differential forms, in the ringed-space spelling. -/
theorem formsAdjoint_eq (p : ℕ) :
    formsAdjoint g' f' f g w p =
      (modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom).unit.app
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
        (modulePushforward g'.toLRSHom.toShHom).map
          (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p) :=
  rfl

/-- The degreewise component of the canonical map of de Rham complexes, in the ringed-space
spelling. -/
theorem formsPushforward_eq (p : ℕ) :
    formsPushforward g' f' f g w p =
      (modulePushforward (toInverseImageBase f)).map (formsAdjoint g' f' f g w p) ≫
        (pushforwardSquareIso g' f' f g w).inv.app
          (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) :=
  rfl

/-- An abstract rearrangement: a component of a natural transformation followed by the image of
a morphism is the image of the morphism followed by the other component. -/
theorem comp_app_comp_map_eq {𝒜 𝒞 : Type*} [Category* 𝒜] [Category* 𝒞] {P Q : 𝒜 ⥤ 𝒞}
    (α : P ⟶ Q) {A B : 𝒜} (φ : A ⟶ B) {Z : 𝒞} (v : Z ⟶ P.obj A) (M : P.obj A ⟶ Q.obj A)
    (hM : M = α.app A) (β : P.obj B ⟶ Q.obj B) (hβ : α.app B = β) :
    (v ≫ M) ≫ Q.map φ = v ≫ P.map φ ≫ β := by
  subst hM hβ
  rw [Category.assoc, α.naturality]

/-- **The transpose of the degreewise component of the canonical map of de Rham complexes**:
under `g₀^* ⊣ (g₀)_*`, the composite of the underived base change map of the square of
structural morphisms with the canonical map on differential forms is `formsPushforward`. -/
theorem homEquiv_structuralBaseChange_comp (p : ℕ) :
    (modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
        ((structuralBaseChange g' f' f g w).app (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
          (modulePushforward (toInverseImageBase f')).map
            (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p)) =
      formsPushforward g' f' f g w p := by
  have hu := unit_mateEquiv (modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom)
    (modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w))
    (moduleBaseChangeSquare g'.toLRSHom.toShHom (toInverseImageBase f') (toInverseImageBase f)
      (inverseImageBaseMap g' f' f g w) (toShHom_comp_toInverseImageBase g' f' f g w))
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ))
  have hα := mateEquiv_moduleBaseChangeSquare g'.toLRSHom.toShHom (toInverseImageBase f')
    (toInverseImageBase f) (inverseImageBaseMap g' f' f g w)
    (toShHom_comp_toInverseImageBase g' f' f g w)
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  refine (congrArg (· ≫ (modulePushforward (inverseImageBaseMap g' f' f g w)).map
    ((modulePushforward (toInverseImageBase f')).map
      (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p))) hu.symm).trans ?_
  let α := (modulePushforwardComp g'.toLRSHom.toShHom (toInverseImageBase f)).hom ≫
    eqToHom (congrArg modulePushforward (toShHom_comp_toInverseImageBase g' f' f g w)) ≫
    (modulePushforwardComp (toInverseImageBase f') (inverseImageBaseMap g' f' f g w)).inv
  have hM : ((mateEquiv (modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)))
        (moduleBaseChangeSquare g'.toLRSHom.toShHom (toInverseImageBase f') (toInverseImageBase f)
          (inverseImageBaseMap g' f' f g w) (toShHom_comp_toInverseImageBase g' f' f g w))).app
        ((modulePullback g'.toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))
      = α.app ((modulePullback g'.toLRSHom.toShHom).obj
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) :=
    congrArg (fun t => NatTrans.app t ((modulePullback g'.toLRSHom.toShHom).obj
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))) hα
  have hsq := pushforwardSquareIso_inv_app_eq g' f' f g w
    (Scheme.Hom.relativeDifferentialForms f' (p : ℤ))
  refine (comp_app_comp_map_eq α (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p) _ _ hM
    _ hsq.symm).trans ?_
  rw [formsPushforward_eq, formsAdjoint_eq]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (· ≫ (pushforwardSquareIso g' f' f g w).inv.app
    (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)))
    ((modulePushforward (toInverseImageBase f)).map_comp
      ((modulePullbackPushforwardAdjunction g'.toLRSHom.toShHom).unit.app
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))
      ((modulePushforward g'.toLRSHom.toShHom).map
        (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p))).symm

end Stacks.DeRhamBaseChange
