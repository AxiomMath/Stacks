module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackToSmallZariski
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.Cotangent.SchemeCotangentComplex

/-!
# Modules along a morphism of schemes read as a morphism of Zariski ringed topoi

For a morphism of schemes `f : X ⟶ Y`, `AlgebraicGeometry.Scheme.Hom.zariskiRingedToposHom f` is
`f` read as a morphism of ringed topoi `(X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)`.  The direct image and the
pullback of sheaves of modules of Stacks 03D6 along it are Mathlib's
`Scheme.Modules.pushforward f` and `Scheme.Modules.pullback f`.  The morphism of ringed topoi of
the morphism of Zariski ringed sites `AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom f` is
`zariskiRingedToposHom f` by definition.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.zariskiPushforwardModulesIsoSchemeModules`: `f_*` of Stacks 03D6 is
  `Scheme.Modules.pushforward f`.
* `AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIsoSchemeModules`: `f^*` of Stacks 03D6 is
  `Scheme.Modules.pullback f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The morphism of ringed topoi of `zariskiRingedSiteHom f` is `zariskiRingedToposHom f`. -/
theorem zariskiRingedSiteHom_toRingedToposHom :
    (zariskiRingedSiteHom f).toRingedToposHom = f.zariskiRingedToposHom :=
  rfl

/-- The direct image of sheaves of modules along `zariskiRingedSiteHom f`, presented by the
functor of sites, is `Scheme.Modules.pushforward f`. -/
def zariskiPushforwardToposIso :
    (zariskiRingedSiteHom f).toRingedToposSiteHom.pushforwardTopos ≅
      Scheme.Modules.pushforward.{u} f :=
  Iso.refl _

/-- **The direct image of modules along `f` read as a morphism of Zariski ringed topoi is
`Scheme.Modules.pushforward f`.** -/
def zariskiPushforwardModulesIsoSchemeModules :
    f.zariskiRingedToposHom.pushforwardModules ≅
      Scheme.Modules.pushforward.{u} f :=
  (zariskiRingedSiteHom f).pushforwardToposIsoGeneral ≪≫ zariskiPushforwardToposIso f

/-- **The pullback of modules along `f` read as a morphism of Zariski ringed topoi is
`Scheme.Modules.pullback f`**: both are left adjoint to the direct image, and the two direct
images agree by `zariskiPushforwardModulesIsoSchemeModules`. -/
def zariskiPullbackModulesIsoSchemeModules :
    f.zariskiRingedToposHom.toModulesHom.pullbackModules ≅ Scheme.Modules.pullback.{u} f :=
  (f.zariskiRingedToposHom.pullbackAdjPushforwardModules.ofNatIsoRight
      (zariskiPushforwardModulesIsoSchemeModules f)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction.{u} f)

end AlgebraicGeometry.Scheme.Hom
