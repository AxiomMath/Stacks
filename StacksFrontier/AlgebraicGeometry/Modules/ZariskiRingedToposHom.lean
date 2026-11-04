module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackToSmallZariski
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.TopologicalComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardSections
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoTransposeCharacterization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison

/-!
# The Zariski morphism of ringed topoi of a morphism of schemes

A morphism of schemes `g : X ⟶ Y` is a morphism of ringed sites
`(X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)`: the functor is `V ↦ g⁻¹V`, a morphism of sites by Stacks 00X2,
and the structure map is `g^♯`. This file records it in the four-field form of the modules
development (`Stacks.Sheaves.RingedToposModules.RingedToposHom`), so that Stacks 03D6, 03D7 and
03EL of that development apply to it, and identifies its pushforward and pullback of modules with
the ringed-space ones.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.zariskiRingedToposModulesHom`: the four-field morphism of ringed
  topoi of the morphism of ringed sites `AlgebraicGeometry.Scheme.Hom.zariskiRingedSiteHom`.
* `AlgebraicGeometry.Scheme.Hom.zariskiPushforwardModulesIso`: its pushforward of modules is the
  ringed-space pushforward (the identity on sections,
  `zariskiPushforwardModulesIso_hom_app_val_app`).
* `AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIso`: its pullback of modules is the
  ringed-space pullback, by uniqueness of left adjoints.

## Main results

* `AlgebraicGeometry.Scheme.Hom.zariskiPushforwardModulesIso_transpose` and
  `zariskiPullbackAdjunction_transpose_val_app`: the four-field transpose of a morphism out of a
  pullback is the ringed-space transpose of the morphism precomposed with the comparison of the
  pullbacks.
* `AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIso_inv_app_unit`: the comparison of the
  pullbacks carries the ringed-space unit image of a section to its four-field unit image.

## References

* [Stacks Project, Tag 00X2](https://stacks.math.columbia.edu/tag/00X2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open scoped TensorProduct
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The morphism of ringed topoi `(Sh(X_Zar), 𝒪_X) ⟶ (Sh(Y_Zar), 𝒪_Y)` of a morphism of schemes,
in the four-field form over which the modules development builds Stacks 03D6 and 03EL. -/
abbrev zariskiRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom X.zariskiRingedSite.toRingedTopos
      Y.zariskiRingedSite.toRingedTopos :=
  g.zariskiRingedSiteHom.toRingedToposHom.toRingedToposModulesHom

/-- The pushforward of modules along the Zariski morphism of ringed topoi of `g` is the
ringed-space pushforward. -/
def zariskiPushforwardModulesIso :
    pushforwardModules.{u, u, u, u, u, u} g.zariskiRingedToposModulesHom ≅
      Stacks.RingedSpace.pushforwardFunctor g.toLRSHom.toShHom :=
  g.zariskiRingedSiteHom.pushforwardModulesToposIsoGeneral

/-- The pullback of modules along the Zariski morphism of ringed topoi of `g` is the ringed-space
pullback. -/
def zariskiPullbackModulesIso :
    g.zariskiRingedToposModulesHom.pullbackModules ≅
      Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom :=
  Adjunction.leftAdjointUniq
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).ofNatIsoRight
      g.zariskiPushforwardModulesIso)
    (Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom)

/-- The transpose of a morphism out of the four-field pullback, read through the two
identifications, is the transpose for the ringed-space adjunction. -/
theorem zariskiPushforwardModulesIso_transpose (M : Y.Modules)
    (N : X.Modules) (k : g.zariskiRingedToposModulesHom.pullbackModules.obj M ⟶ N) :
    (pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app M ≫
        (pushforwardModules g.zariskiRingedToposModulesHom).map k ≫
          g.zariskiPushforwardModulesIso.hom.app N =
      ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv M N)
        (g.zariskiPullbackModulesIso.inv.app M ≫ k) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ g.zariskiPushforwardModulesIso.hom.app N)
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).homEquiv_unit M N k).symm).trans
      ?_
  exact Stacks.SheafOfModules.homEquiv_comp_hom_app_eq_homEquiv_leftAdjointUniq_inv
    (pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom) g.zariskiPushforwardModulesIso
    (Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom) M N k

/-- The identification of the two pushforwards is the identity on sections. -/
theorem zariskiPushforwardModulesIso_hom_app_val_app (N : X.Modules) (V : Y.Opensᵒᵖ)
    (z : ((pushforwardModules g.zariskiRingedToposModulesHom).obj N).val.obj V) :
    (g.zariskiPushforwardModulesIso.hom.app N).val.app V z =
      (show N.val.obj ((Opens.map g.base).op.obj V) from z) :=
  g.zariskiRingedSiteHom.pushforwardModulesToposIsoGeneral_hom_app_val_app N V z

/-- The unit of the four-field adjunction, carried to the ringed-space pushforward, is the
ringed-space unit followed by the comparison of the two pullbacks. -/
theorem zariskiPullbackAdjunction_unit_app_comp (M : Y.Modules) :
    (pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app M ≫
        g.zariskiPushforwardModulesIso.hom.app
          (g.zariskiRingedToposModulesHom.pullbackModules.obj M) =
      (Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app M ≫
        (Stacks.RingedSpace.pushforwardFunctor g.toLRSHom.toShHom).map
          (g.zariskiPullbackModulesIso.inv.app M) :=
  Stacks.SheafOfModules.unit_app_comp_hom_app_eq_unit_app_comp_map_leftAdjointUniq_inv
    (pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom) g.zariskiPushforwardModulesIso
    (Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom) M

/-- Morphisms into the four-field pushforward agree on sections with their composite with the
identification of the two pushforwards. -/
private theorem val_app_eq_of_comp_pushforwardModulesIso_hom_app {N : X.Modules} {P : Y.Modules}
    (f : P ⟶ (pushforwardModules g.zariskiRingedToposModulesHom).obj N)
    (ψ : P ⟶ (Stacks.RingedSpace.pushforwardFunctor g.toLRSHom.toShHom).obj N)
    (h : f ≫ g.zariskiPushforwardModulesIso.hom.app N = ψ) (V : Y.Opensᵒᵖ) (x : P.val.obj V) :
    f.val.app V x = ψ.val.app V x := by
  exact (g.zariskiPushforwardModulesIso_hom_app_val_app N V (f.val.app V x)).symm.trans
    (congrArg (fun φ => φ.val.app V x) h)

/-- **The comparison of the two pullbacks carries the ringed-space unit image of a section to
its four-field unit image.** -/
theorem zariskiPullbackModulesIso_inv_app_unit (M : Y.Modules) (V : Y.Opensᵒᵖ) (x : M.val.obj V) :
    (g.zariskiPullbackModulesIso.inv.app M).val.app ((Opens.map g.base).op.obj V)
        (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app M).val.app V x) =
      ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app M).val.app V x := by
  exact (g.val_app_eq_of_comp_pushforwardModulesIso_hom_app _ _
    (g.zariskiPullbackAdjunction_unit_app_comp M) V x).symm

/-- **The four-field transpose of a morphism out of a pullback, on sections**, is the
ringed-space transpose of the morphism precomposed with the comparison of the two pullbacks. -/
theorem zariskiPullbackAdjunction_transpose_val_app (M : Y.Modules) (N : X.Modules)
    (k : g.zariskiRingedToposModulesHom.pullbackModules.obj M ⟶ N) (V : Y.Opensᵒᵖ)
    (z : M.val.obj V) :
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app M ≫
        (pushforwardModules g.zariskiRingedToposModulesHom).map k).val.app V z =
      (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv M N)
        (g.zariskiPullbackModulesIso.inv.app M ≫ k)).val.app V z := by
  refine g.val_app_eq_of_comp_pushforwardModulesIso_hom_app _ _ ?_ V z
  exact g.zariskiPushforwardModulesIso_transpose M N k

end AlgebraicGeometry.Scheme.Hom

end
