module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `Rf_*` be the derived direct image
`Stacks.Cohomology.DerivedPushforward.derivedPushforward` of the morphism of small étale ringed
topoi of `f`.  If `f` is quasi-compact and quasi-separated, `Rf_*` carries `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)` (Stacks 08FA, part (1)), and so restricts to an exact functor
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.Space.derivedModulePushforward`: `Rf_*`, read on the derived categories of
  `AlgebraicGeometry.Space.Modules`, with its shift and triangulated structure, and
  `AlgebraicGeometry.Space.derivedModulePushforwardUnit`, its unit as a right derived functor of
  `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPushforward`: the restriction
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, with its shift and triangulated structure.

## Main results

* `AlgebraicGeometry.Space.isRightDerivedFunctor_derivedModulePushforward`: `Rf_*` is a right
  derived functor of `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.nonempty_derivedPushforward_obj_iso_of_isKInjective`: a K-injective
  complex computes `Rf_*`.
* `AlgebraicGeometry.Space.qcohDerived_derivedModulePushforward_obj`: for `f` quasi-compact and
  quasi-separated, `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` (Stacks 08FA, part (1)).

## References

* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
-/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- A K-injective complex computes the derived direct image of a morphism of algebraic spaces:
`Rf_*(Q I) ≅ Q(f_* I)`, with `f_*` the direct image of the morphism of small étale ringed topoi. -/
theorem nonempty_derivedPushforward_obj_iso_of_isKInjective_aux (f : X ⟶ Y)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective) :
    Nonempty ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
        (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((RingedToposHom.pushforwardModules
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) := by
  have h := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
    (RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (Functor.totalRightDerivedUnit _ _ _)
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) I hI
  let φ := smallEtaleRingedToposHom B S hS f
  let P := RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) φ
  let R := derivedPushforward (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) φ
  let e₁ : R.obj (DerivedCategory.Q.obj I) ≅
      R.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) :=
    R.mapIso ((DerivedCategory.quotientCompQhIso _).app I).symm
  let e₂ : R.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) ≅
      DerivedCategory.Qh.obj ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I)) := (@asIso _ _ _ _ _ h).symm
  let e₃ : DerivedCategory.Qh.obj ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I)) ≅
      DerivedCategory.Q.obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    DerivedCategory.Qh.mapIso ((P.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩


end AlgebraicGeometry.Space

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

section

attribute [local instance 5000] SheafOfModules.instAbelian

/-- A K-injective complex computes the derived direct image of a morphism of algebraic spaces:
`Rf_*(Q I) ≅ Q(f_* I)`, with `f_*` the direct image of the morphism of small étale ringed topoi. -/
alias nonempty_derivedPushforward_obj_iso_of_isKInjective := nonempty_derivedPushforward_obj_iso_of_isKInjective_aux

end

/-- The derived direct image `Rf_*` of a morphism of algebraic spaces, read on the derived
categories of `AlgebraicGeometry.Space.Modules`: it is
`Stacks.Cohomology.DerivedPushforward.derivedPushforward` of the morphism of small étale ringed
topoi of `f`, the right adjoint of `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
abbrev derivedModulePushforward (f : X ⟶ Y) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
  derivedPushforward (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)

/-- The degreewise direct images of the morphism of small étale ringed topoi and of
`AlgebraicGeometry.Space.modulePushforward` induce the same functor to the derived category. -/
theorem mapHomotopyCategory_modulePushforward_comp_Qh_eq (f : X ⟶ Y) :
    (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (DerivedCategory.Qh (C := Modules.{u, u} B S hS Y.1 Y.2)) =
    (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) :
        HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤
          DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) := by
  have key : ∀ (G : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
      (_ : RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) = G)
      [G.Additive],
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh (C := Modules.{u, u} B S hS Y.1 Y.2)) =
      (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) :
          HomotopyCategory (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤
            DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) := by
    rintro G rfl _
    rfl
  exact key _ (pushforwardModules_eq_modulePushforward B S hS f)

/-- Precomposing the unit of a right derived functor with `eqToHom` of an equality of functors
gives a right derived functor. -/
theorem isRightDerivedFunctor_eqToHom_comp {K D H : Type*} [Category K] [Category D] [Category H]
    {F F' : K ⥤ H}
    (h : F = F') {L : K ⥤ D} {RF : D ⥤ H} (α : F' ⟶ L ⋙ RF) (W : MorphismProperty K)
    [L.IsLocalization W] [RF.IsRightDerivedFunctor α W] :
    RF.IsRightDerivedFunctor (eqToHom h ≫ α) W := by
  subst h
  simpa using (inferInstance : RF.IsRightDerivedFunctor α W)

/-- The unit exhibiting `Rf_*` as a right derived functor of the direct image of modules
`AlgebraicGeometry.Space.modulePushforward`: the canonical unit of the total right derived functor,
precomposed with the identification of the two spellings of the direct image. -/
noncomputable def derivedModulePushforwardUnit (f : X ⟶ Y) :
    (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedModulePushforward B S hS f :=
  eqToHom (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS f) ≫
    (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
            (ComplexShape.up ℤ))

/-- `Rf_*` is a right derived functor of the direct image of modules
`AlgebraicGeometry.Space.modulePushforward`, with unit
`AlgebraicGeometry.Space.derivedModulePushforwardUnit`. -/
instance isRightDerivedFunctor_derivedModulePushforward (f : X ⟶ Y) :
    (derivedModulePushforward B S hS f).IsRightDerivedFunctor
      (derivedModulePushforwardUnit B S hS f)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  @isRightDerivedFunctor_eqToHom_comp _ _ _ _ _ _ _ _
    (mapHomotopyCategory_modulePushforward_comp_Qh_eq B S hS f) _ _ _ _ _
    (inferInstance : (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).IsRightDerivedFunctor
      ((pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit
          DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
            (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
            (ComplexShape.up ℤ)))
/-- The shift structure of `Rf_*`. -/
instance derivedModulePushforward_commShift (f : X ⟶ Y) :
    (derivedModulePushforward B S hS f).CommShift ℤ :=
  (inferInstance : (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).CommShift ℤ)

/-- `Rf_*` is a triangulated functor. -/
instance derivedModulePushforward_isTriangulated (f : X ⟶ Y) :
    (derivedModulePushforward B S hS f).IsTriangulated :=
  Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
    (RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)) _
    (Functor.totalRightDerivedUnit _ _ _)


/-- Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism
of algebraic spaces over `S`.  Then the derived direct image `Rf_*` carries `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)`. -/
theorem qcohDerived_derivedModulePushforward_obj (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) :
    QcohDerived B S hS Y ((derivedModulePushforward B S hS f).obj E) :=
  @qcohDerived_obj_of_isKInjective_iso B S hS X Y f hfqc hfqs
    (RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (pushforwardModules_eq_modulePushforward B S hS f)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
      (additive_smallEtaleRingedToposHom_pushforwardModules B S hS f)) _
    (fun I hI => nonempty_derivedPushforward_obj_iso_of_isKInjective B S hS f I hI) E hE

/-- The derived direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of a quasi-compact
quasi-separated morphism of algebraic spaces: the restriction of
`AlgebraicGeometry.Space.derivedModulePushforward` to `D_QCoh`. -/
def quasicoherentDerivedPushforward (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ derivedModulePushforward B S hS f)
    (fun E => qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E.obj E.property)

/-- The restricted derived direct image followed by the inclusion of `D_QCoh(𝒪_Y)` is the
derived direct image on `D_QCoh(𝒪_X)`. -/
def quasicoherentDerivedPushforwardCompιIso (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ derivedModulePushforward B S hS f :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restricted derived direct image commutes with the shift. -/
instance commShift_quasicoherentDerivedPushforward (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (quasicoherentDerivedPushforward B S hS f hfqc hfqs).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _ _ _).CommShift ℤ)

/-- The restricted derived direct image is exact: it is a triangulated functor
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
instance isTriangulated_quasicoherentDerivedPushforward (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (quasicoherentDerivedPushforward B S hS f hfqc hfqs).IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _ _ _).IsTriangulated

end AlgebraicGeometry.Space

end

