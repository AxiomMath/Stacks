module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedAlongEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePushforward

/-!
# Derived direct images on algebraic spaces under relocalization

Let `g : T ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a morphism of algebraic spaces
over `T`, with lower-shriek extension `Λ f : Λ X ⟶ Λ Y` over `S`. The derived direct image
commutes with the equivalences of derived categories induced by relocalization:
`ρ_Y ∘ Rf_* ≅ R(Λ f)_* ∘ ρ_X`. Both sides are right derived functors of the same functor,
by `AlgebraicGeometry.Space.relocalizeModulePushforwardIso` on modules.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeModulePushforwardFunctorIso`:
  `f_* ⋙ E_Y ≅ E_X ⋙ (Λ f)_*` on modules.
* `AlgebraicGeometry.Space.relocalizeDerivedPushforwardIso`: `Rf_* ⋙ ρ_Y ≅ ρ_X ⋙ R(Λ f)_*`.
* `AlgebraicGeometry.Space.relocalizeDerivedPushforwardObjIso`: the same on one object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)

/-- The direct image of modules along the lower-shriek extension `Λ f` is additive. -/
instance modulePushforward_relocalizeHom_additive :
    (modulePushforward B S hS (relocalizeHom B hT hS g f)).Additive :=
  modulePushforward_additive B S hS _

/-- The derived direct image `R(Λ f)_*` along the lower-shriek extension `Λ f` is a right derived
functor of `(Λ f)_*` with respect to the quasi-isomorphisms. -/
instance isRightDerivedFunctor_derivedModulePushforward_relocalizeHom :
    (derivedModulePushforward B S hS (relocalizeHom B hT hS g f)).IsRightDerivedFunctor
      (derivedModulePushforwardUnit B S hS (relocalizeHom B hT hS g f))
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS (relocalizeSpace B hT hS g X).1
        (relocalizeSpace B hT hS g X).2) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_derivedModulePushforward B S hS _

/-- **The direct image of modules commutes with relocalization**, in the direction of the
functors of the equivalences: `E_Y ∘ f_* ≅ (Λ f)_* ∘ E_X`. -/
def relocalizeModulePushforwardFunctorIso :
    modulePushforward B T hT f ⋙ (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).functor ≅
      (relocalizeModulesEquivalence B hT hS g X.1 X.2).functor ⋙
        modulePushforward B S hS (relocalizeHom B hT hS g f) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (relocalizeModulesEquivalence B hT hS g X.1 X.2).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (relocalizeModulePushforwardIso B hT hS g f).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).counitIso ≪≫
      Functor.rightUnitor _)

/-- **The derived direct image commutes with relocalization**: for an arbitrary morphism
`f : X ⟶ Y` of algebraic spaces over `T`, `ρ_Y ∘ Rf_* ≅ R(Λ f)_* ∘ ρ_X` as functors
`D(𝒪_X) ⥤ D(𝒪_{Λ Y})`, where `ρ` is the equivalence of derived categories of
`AlgebraicGeometry.Space.relocalizeDerivedFunctor`. -/
def relocalizeDerivedPushforwardIso :
    derivedModulePushforward B T hT f ⋙ relocalizeDerivedFunctor B hT hS g Y.1 Y.2 ≅
      relocalizeDerivedFunctor B hT hS g X.1 X.2 ⋙
        derivedModulePushforward B S hS (relocalizeHom B hT hS g f) :=
  Stacks.DerivedFunctor.rightDerivedCompMapDerivedCategoryIso (modulePushforward B T hT f)
    (modulePushforward B S hS (relocalizeHom B hT hS g f))
    (relocalizeModulesEquivalence B hT hS g X.1 X.2).functor
    (relocalizeModulesEquivalence B hT hS g Y.1 Y.2).functor
    (relocalizeModulePushforwardFunctorIso B hT hS g f)
    (derivedModulePushforward B T hT f) (derivedModulePushforwardUnit B T hT f)
    (derivedModulePushforward B S hS (relocalizeHom B hT hS g f))
    (derivedModulePushforwardUnit B S hS (relocalizeHom B hT hS g f))

/-- **The derived direct image commutes with relocalization**, on one object:
`ρ_Y (Rf_* K) ≅ R(Λ f)_* (ρ_X K)`. -/
def relocalizeDerivedPushforwardObjIso (K : DerivedCategory (Modules.{u, u} B T hT X.1 X.2)) :
    (relocalizeDerivedFunctor B hT hS g Y.1 Y.2).obj ((derivedModulePushforward B T hT f).obj K) ≅
      (derivedModulePushforward B S hS (relocalizeHom B hT hS g f)).obj
        ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj K) :=
  (relocalizeDerivedPushforwardIso B hT hS g f).app K

end AlgebraicGeometry.Space

end
