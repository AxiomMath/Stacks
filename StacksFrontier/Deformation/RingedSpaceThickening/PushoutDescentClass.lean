module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPushoutDescent
public import StacksFrontier.Deformation.RingedSpaceThickening.TrivializedFunctoriality
import StacksCore.Tactic.StacksAttribute

/-!
# The extension class of the extension that Tag 08LC produces (Stacks 08LD)

Let `(X, 𝒪_X)` be a ringed space, let `i : X ⟶ X'` be a first order thickening with ideal `ℐ₁`,
and let `S` present a second first order thickening on the space of `X'`, with comorphism
`h^♯ : 𝒪'₂ ⟶ 𝒪_{X'}` and ideal `ℐ₂`; the morphism of thickenings it presents is
`SecondThickening.spaceHom`, and `i ≫ spaceHom = S.hom` holds on the nose. Fix the data `ℱ`,
`(𝒦₁, c₁)`, `(𝒦₂, c₂)`, `κ : 𝒦₂ ⟶ 𝒦₁` of `PushoutDescentData` and an extension `ℱ'₂` over the
second thickening whose canonical map of Tag 08L4 is `c₂`.

Tag 08LC carries `ℱ'₂` to the extension `PushoutDescentData.extensionOne` over the first
thickening, whose middle term is the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁` with the `𝒪_{X'}`-module structure
descended along `q : T = 𝒪'₂ ⋉ ℐ₁ ⟶ 𝒪_{X'}`. Tag 08LD asserts that, once both thickenings are
trivialized compatibly, the class `ξ` of Tag 08LB of that extension is the image of the class of
`ℱ'₂` under functoriality of `Ext¹_{𝒪_X}(ℱ, -)` along `κ`.

This file supplies the map `φ` that identifies the output of Tag 08LC as the pushed extension of
Tag 08LD, and concludes the square of Tag 08LD for it.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.middleSection`: a local section of
  the pushout, read as a local section of the middle term through the comparison `middleIso`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.pushoutToMiddle`: the map `φ` from
  the pushout to `h_* ℱ'₁`, the comparison `middleIso` read as a map of `𝒪'₂`-modules.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.pushedExtensionOne`: the datum
  `AlgebraicGeometry.RingedSpaceThickening.PushedExtension` exhibiting the extension of
  Tag 08LC as the pushed extension of `ℱ'₂` along `κ`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.middleSection_smul`: the
  comparison with the pushout is `𝒪'₂`-semilinear, the action on the middle term being taken
  through `h^♯`. This is what makes `φ` a morphism of `𝒪'₂`-modules.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.f_comp_pushoutToMiddle` and
  `.pushoutToMiddle_comp_g`: the two squares of `φ`, over the inclusion of `𝒦₁` and over the
  surjection onto `ℱ`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData`
  `.underlyingExtensionClass_extensionOne`: **Stacks 08LD** for the extension of Tag 08LC — the
  class of `PushoutDescentData.extensionOne` is the image of the class of `ℱ'₂` under `κ`.

## Implementation notes

The three changes of acting sheaf of rings that `φ` crosses are handled as follows. The `𝒪'₂`-
action on the pushout is the twisted `T`-action of the section `(a, 0)`, since the twisting term
of the zero section of `ℐ₁` vanishes (`PushoutDescentData.twistedSmul_mk_zero`); `q` carries
`(a, 0)` to `h^♯(a)` (`SecondThickening.sqZeroProj_mk_zero`); and `h` is the identity on the
underlying space, so `h_*` neither moves opens nor changes sections and the `𝒪'₂`-action on
`h_* ℱ'₁` is the `𝒪_{X'}`-action through `h^♯` definitionally. So `middleSection_smul` is
exactly the `T`-linearity of `middleIso.inv` at `(a, 0)`, and `φ` is `middleIso.inv` with its
semilinearity restated; `PushoutDescentData.pushoutToMiddle_app` is `rfl`.

For the same reason the comparison
`AlgebraicGeometry.RingedSpaceThickening.thickeningPushforwardComp` and the functor `h_*` are
the identity on sections here, so the two squares of `φ` are the local-section descriptions
`PushoutDescentData.extInclOne_app` and `PushoutDescentData.extQuotOne_app` of the two maps of
the extension of Tag 08LC, together with `PushoutDescentData.middleIso_hom_inv`.

## References

* [Stacks Project, Tag 08LD](https://stacks.math.columbia.edu/tag/08LD)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Thickenings

universe e u

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

attribute [local implicit_reducible] CategoryTheory.ConcreteCategory.hom
  CategoryTheory.sheafCompose SheafOfModules.unit PresheafOfModules.unit
  SheafOfModules.forget SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' : RingedSpace.{u, u}}

attribute [local instance] sectionsModuleOverSpace sectionsModuleOverBase

namespace SecondThickening

variable {i : X ⟶ X'} (S : SecondThickening i)

/-- The image under `q` of a section of `T` with zero ideal component is the image of its ring
component under `h^♯`. -/
theorem sqZeroProj_mk_zero (hi : IsFirstOrderThickening i) (V : Opens X'.carrier)
    (a : S.O.obj (op V)) :
    (S.sqZeroProj hi).hom.app (op V) (S.sqMk V a 0) = S.hSharpApp V a := by
  rw [S.sqZeroProj_hom_app, S.sqFst_mk, S.sqSnd_mk, idealIncl_zero, sub_zero]

end SecondThickening

namespace PushoutDescentData

variable {i : X ⟶ X'} {S : SecondThickening i} (dat : PushoutDescentData S)
  (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.hom).obj dat.F)
    ((modulePushforward S.hom).obj dat.K₂) 0)
  (hi : IsFirstOrderThickening i)
  (hE₂ : (firstOrderExtensionAction S.hom dat.F dat.K₂ S.firstOrder E₂).val = dat.c₂)

attribute [local instance] sectionsModuleOverSpace sectionsModuleOverBase
  SecondThickening.sectionsModuleOverTwo SecondThickening.sectionsModuleOverTwoSpace
  SecondThickening.sectionsModuleOverSq

/-- The comparison with the pushout, read in the other direction, is bijective on local
sections. -/
theorem middleIso_hom_inv (V : Opens X'.carrier)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    (dat.middleIso E₂ hi hE₂).hom.val.app (op V)
        ((dat.middleIso E₂ hi hE₂).inv.val.app (op V) p) = p :=
  congrArg (fun z : dat.twistedSheaf E₂ ⟶ dat.twistedSheaf E₂ => z.val.app (op V) p)
    (dat.middleIso E₂ hi hE₂).inv_hom_id

/-- The twisted action of a section of `T` with zero ideal component is the untwisted action of
its ring component: the twisting term vanishes. -/
theorem twistedSmul_mk_zero (V : Opens X'.carrier) (a : S.O.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.twistedSmul E₂ V (S.sqMk V a 0) p = a • p := by
  rw [dat.twistedSmul_eq, S.sqFst_mk, S.sqSnd_mk, dat.twist_zero_left, sub_zero]

/-- A local section of the pushout, read as a local section of the middle term through the
comparison `middleIso`. The type is named so that the `𝒪_{X'}`-action on the middle term is the
one the statements below are about. -/
noncomputable def middleSection (V : Opens X'.carrier)
    (p : (dat.pushoutMod E₂).val.obj (op V)) : (dat.middle E₂ hi hE₂).val.obj (op V) :=
  (dat.middleIso E₂ hi hE₂).inv.val.app (op V) p

/-- **The comparison with the pushout is `𝒪'₂`-semilinear.** The section `(a, 0)` of
`T = 𝒪'₂ ⋉ ℐ₁` acts on the twisted module as `a` does untwisted, and `q` carries it to
`h^♯(a)`; so the inverse comparison carries the `𝒪'₂`-action on the pushout to the
`𝒪_{X'}`-action on the middle term through `h^♯`. -/
theorem middleSection_smul (V : Opens X'.carrier) (a : S.O.obj (op V))
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    dat.middleSection E₂ hi hE₂ V (a • p) =
      S.hSharpApp V a • dat.middleSection E₂ hi hE₂ V p := by
  have linear : ∀ (r : S.sqSections V) (z : (dat.twistedSheaf E₂).val.obj (op V)),
      (dat.middleIso E₂ hi hE₂).inv.val.app (op V) (r • z) =
        r • (dat.middleIso E₂ hi hE₂).inv.val.app (op V) z :=
    fun r z => map_smul ((dat.middleIso E₂ hi hE₂).inv.val.app (op V)).hom r z
  calc dat.middleSection E₂ hi hE₂ V (a • p)
      = dat.middleSection E₂ hi hE₂ V (dat.twistedSmul E₂ V (S.sqMk V a 0) p) :=
        congrArg (dat.middleSection E₂ hi hE₂ V) (dat.twistedSmul_mk_zero E₂ V a p).symm
    _ = (S.sqZeroProj hi).hom.app (op V) (S.sqMk V a 0) • dat.middleSection E₂ hi hE₂ V p :=
        linear (S.sqMk V a 0) p
    _ = S.hSharpApp V a • dat.middleSection E₂ hi hE₂ V p :=
        congrArg (fun z : X'.presheaf.obj (op V) => z • dat.middleSection E₂ hi hE₂ V p)
          (S.sqZeroProj_mk_zero hi V a)

/-- **The map `φ` out of the pushout.** The comparison `middleIso`, read as a map from the
pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁` — an `𝒪'₂`-module — to the direct image along `h` of the middle term
of the extension that Tag 08LC produces. -/
noncomputable def pushoutToMiddle :
    dat.pushoutMod E₂ ⟶ (modulePushforward S.spaceHom).obj (dat.middle E₂ hi hE₂) :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf S.sqZeroRing.obj).map (dat.middleIso E₂ hi hE₂).inv.val)
    (fun U a p => dat.middleSection_smul E₂ hi hE₂ U.unop a p)⟩

/-- The map `φ` on local sections. -/
theorem pushoutToMiddle_app (V : Opens X'.carrier)
    (p : (dat.pushoutMod E₂).val.obj (op V)) :
    (dat.pushoutToMiddle E₂ hi hE₂).val.app (op V) p = dat.middleSection E₂ hi hE₂ V p := rfl

/-- `φ` carries the inclusion of `𝒦₁` into the pushout to the inclusion of `𝒦₁` into the middle
term of the extension of Tag 08LC. -/
theorem f_comp_pushoutToMiddle :
    (pushoutExtension S.hom dat.F dat.K₁ dat.K₂ dat.kernelMap E₂).f ≫
        dat.pushoutToMiddle E₂ hi hE₂ =
      (thickeningPushforwardComp i S.hom S.spaceHom S.comp_spaceHom).inv.app dat.K₁ ≫
        (modulePushforward S.spaceHom).map (dat.extensionOne E₂ hi hE₂).f :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext <|
    LinearMap.ext fun k => (dat.extInclOne_app E₂ hi hE₂ U.unop k).symm

/-- `φ` is compatible with the two surjections onto `ℱ`. -/
theorem pushoutToMiddle_comp_g :
    dat.pushoutToMiddle E₂ hi hE₂ ≫
        (modulePushforward S.spaceHom).map (dat.extensionOne E₂ hi hE₂).g =
      (pushoutExtension S.hom dat.F dat.K₁ dat.K₂ dat.kernelMap E₂).g ≫
        (thickeningPushforwardComp i S.hom S.spaceHom S.comp_spaceHom).inv.app dat.F :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext <|
    LinearMap.ext fun p =>
      (dat.extQuotOne_app E₂ hi hE₂ U.unop (dat.middleSection E₂ hi hE₂ U.unop p)).trans
        (congrArg (fun z => S.ofSecond dat.F U.unop (dat.quotSection E₂ U.unop z))
          (dat.middleIso_hom_inv E₂ hi hE₂ U.unop p))

/-- **The extension of Tag 08LC is the pushed extension of Tag 08LD.** The map `φ` and its two
squares turn the extension that Tag 08LC produces into the datum
`AlgebraicGeometry.RingedSpaceThickening.PushedExtension` over which the square of Tag 08LD is
stated: `h_* ℱ'₁` receives the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁` compatibly with `κ` and with `𝟙 ℱ`. -/
noncomputable def pushedExtensionOne :
    PushedExtension i S.hom S.spaceHom S.comp_spaceHom dat.F dat.K₁ dat.K₂ dat.kernelMap E₂
      (dat.extensionOne E₂ hi hE₂) :=
  PushedExtension.ofPushoutMap i S.hom S.spaceHom S.comp_spaceHom dat.F dat.K₁ dat.K₂
    dat.kernelMap (dat.pushoutToMiddle E₂ hi hE₂) (dat.f_comp_pushoutToMiddle E₂ hi hE₂)
    (dat.pushoutToMiddle_comp_g E₂ hi hE₂)

/-- **Stacks Project, Tag 08LD.** The square of the remark commutes for the extension that
Tag 08LC produces: let `h = SecondThickening.spaceHom` be the morphism of first order
thickenings of `(X, 𝒪_X)` that `h^♯` presents, let both thickenings be trivialized by `π₁` and
`π₂` with `π₁ = h ≫ π₂`, so that `h` is a morphism of *trivialized* thickenings, and let the
square relating `c₁`, `c₂`, `κ` and `ℐ₂ ⟶ ℐ₁` commute. If `ℱ'₂` is an extension as in Tag 08L4
whose canonical map is `c₂`, then the class `ξ` of Tag 08LB of the extension
`AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.extensionOne` that Tag 08LC produces
from it is the image of `ξ_{ℱ'₂}` under functoriality of `Ext¹_{𝒪_X}(ℱ, -)` along `κ`.

Both extensions are members of the two sets the square relates: `hE₂` says that the canonical
map of `ℱ'₂` is `c₂`, and `PushoutDescentData.extensionOne_action` says that the canonical map
of the extension produced from it is `c₁`.

The hypothesis `hc` is the remark's commuting square, written with the induced map of ideals
`AlgebraicGeometry.RingedSpaceThickening.thickeningIdealMap`. The field
`AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.comm` of `dat` is the same square of
the same remark, written on local pure tensors, which is the form the construction of Tag 08LC
consumes; no cross-thickening comparison of the two canonical maps is available to pass between
the two forms, so the square is assumed in both. -/
@[stacks 08LD "the square commutes for the extension Tag 08LC produces"]
theorem underlyingExtensionClass_extensionOne
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))]
    (π₁ : SplitMono i) (π₂ : SplitMono S.hom)
    (hπ : π₁.retraction = S.spaceHom ≫ π₂.retraction)
    (hc : dat.c₂ ≫ dat.kernelMap =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        ((thickeningIdealMap i S.hom S.spaceHom S.comp_spaceHom, 𝟙 dat.F) : (_, _) ⟶ (_, _)) ≫
          dat.c₁) :
    underlyingExtensionClass i π₁ hi.1.1 dat.F dat.K₁ (dat.extensionOne E₂ hi hE₂) =
      (underlyingExtensionClass S.hom π₂ S.firstOrder.1.1 dat.F dat.K₂ E₂).comp
        (CategoryTheory.Abelian.Ext.mk₀ dat.kernelMap) (add_zero 1) :=
  underlyingExtensionClass_eq_of_pushedExtension i S.hom S.spaceHom S.comp_spaceHom hi
    S.firstOrder π₁ π₂ hπ dat.F dat.K₁ dat.K₂ dat.kernelMap dat.c₁ dat.c₂ hc E₂ hE₂
    (dat.extensionOne E₂ hi hE₂) (dat.extensionOne_action E₂ hi hE₂)
    (dat.pushedExtensionOne E₂ hi hE₂)

end PushoutDescentData

end AlgebraicGeometry.RingedSpaceThickening

end
