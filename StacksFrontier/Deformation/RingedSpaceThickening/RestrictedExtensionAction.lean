module

public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningComplexBoundary
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassification
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPushoutDescent
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of an extension read across a morphism of thickenings, and Stacks 08LF

Let `h : (X'₂, 𝒪_{X'₂}) ⟶ (X'₃, 𝒪_{X'₃})` be a morphism of first order thickenings of a ringed
space `(X, 𝒪_X)`, so that `i₂ ≫ h = i₃`. An extension `0 ⟶ (i₂)_* 𝒦 ⟶ ℱ' ⟶ (i₂)_* ℱ ⟶ 0` as in
**Stacks 08L4** over `X'₂` is also one over `X'₃`, by direct image along `h`
(`AlgebraicGeometry.RingedSpaceThickening.restrictedExtension`): this is the source's "the same
module, viewed as an `𝒪_{X'₃}`-module via `𝒪_{X'₃} ⟶ 𝒪_{X'₂}`". The first result of this file
computes its canonical map of Tag 08L4: it is the canonical map of `ℱ'` precomposed with
`ℐ₃ ⊗ ℱ ⟶ ℐ₂ ⊗ ℱ`, where `ℐ₃ ⟶ ℐ₂` is the map induced by `h^♯`
(`AlgebraicGeometry.RingedSpaceThickening.thickeningIdealMap`). This is the computation the proof
of **Stacks 08LF** makes when it asserts `c_{ℰ'₃} = j ∘ c₃`.

With it, and with the observation that a map of extensions inducing the identity on `ℱ` exhibits
its target as a pushout, the claim of **Stacks 08LF** holds with no hypothesis beyond those of the
source:
`AlgebraicGeometry.RingedSpaceThickening.boundary_underlyingExtensionClass_eq_obstructionClass`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.FirstOrderThickeningSequence.trivialization`: the
  canonical splitting `π : X'₁ ⟶ X` of a complex of first order thickenings, **Stacks 08LE**.
* `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.toSpace` and
  `AlgebraicGeometry.RingedSpaceThickening.SecondThickening.thickeningSequence`: the morphism of
  thickenings of the presentation of Tag 08LC, and the sequence of thickenings it starts.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.extensionTensorComparison_app_tmul`: the comparison
  `ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` of Tag 08L4 on a local pure tensor `a ⊗ t`: it is
  the pure tensor of the pullback-unit image of `a` with `t`.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningIdealMap_unit`: the map `ℐ₃ ⟶ ℐ₂` on the
  pullback-unit image of a local section `a` of `ℐ₃` is the pullback-unit image of the section of
  `ℐ₂` that `h^♯` carries `a` to.
* `AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_restrictedExtension`: the
  canonical map of an extension read across `h`.
* `AlgebraicGeometry.RingedSpaceThickening.PushedExtension.isPushout`: a map of extensions as in
  Tag 08LC exhibits the direct image of its target as the pushout of its source.
* `AlgebraicGeometry.RingedSpaceThickening.boundary_underlyingExtensionClass_eq_obstructionClass`:
  **Stacks 08LF**, for every extension `ℱ'₁` receiving a map of extensions from `ℱ'₂`.
* `AlgebraicGeometry.RingedSpaceThickening.PushoutDescentData.pushedExtension`: the extension of
  Tag 08LC receives such a map, and
  `boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass`:
  **Stacks 08LF** for `ℱ'₁` the extension of Tag 08LC.

## Implementation notes

The canonical map is characterised by its local lifting formula
(`AlgebraicGeometry.RingedSpaceThickening.eq_firstOrderExtensionAction_of_comp`), so the
computation is done on local pure tensors `a ⊗ s'` with `a` a section of `ℐ₃` over `V` and `s'`
a section of `ℱ'` over `h⁻¹ V`. Three section-level facts are combined: the comparison of
Tag 08L4 on a pure tensor, which is the canonicality clause of **Stacks 01CD**
(`Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul`) followed by a triangle identity of
`i^* ⊣ i_*`; the map `ℐ₃ ⟶ ℐ₂` on a pullback-unit image, which is
`Stacks.ClosedImmersion.unit_comp_pushforward_homEquiv_conormalSheafMap` read on sections once
the unit of `(𝟙 X)^* ⊣ (𝟙 X)_*` is identified with `RingedSpaceModuleAdjunction.modulePullbackId`;
and the image of that section of `ℐ₂` in `𝒪_{X'₂}`, which is `h^♯` of the image of `a`
(`Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι`). The morphism `i₃` is
substituted by `i₂ ≫ h`, after which every open of `X` in sight is literally
`(i₂ ≫ h)⁻¹ V = i₂⁻¹ (h⁻¹ V)` and no transport between opens is needed.

The extension `ℱ'₁` of the remark is the one the functoriality of **Stacks 08LC** produces from
`ℱ'₂`: an extension over `X'₁` with canonical map `c₁` receiving a map of extensions from `ℱ'₂`
which is `𝒦₂ ⟶ 𝒦₁` on kernels and the identity on `ℱ`
(`AlgebraicGeometry.RingedSpaceThickening.PushedExtension`), exactly as in Tag 08LD.

## References

* [Stacks Project, Tag 08LF](https://stacks.math.columbia.edu/tag/08LF)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08L8](https://stacks.math.columbia.edu/tag/08L8)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' X₂ X₃ : RingedSpace.{u, u}}

/-- **The comparison of Stacks 08L4 on a local pure tensor.** For a section `a` of the ideal `ℐ`
of `i : X ⟶ X'` and a section `t` of `i_* ℱ` over an open `V` of `X'`, the comparison
`ℐ ⊗_{𝒪_{X'}} i_* ℱ ⟶ i_*(i^* ℐ ⊗_{𝒪_X} ℱ)` carries `a ⊗ t` to the pure tensor of the
pullback-unit image of `a` with `t`, over `i⁻¹ V`. -/
theorem extensionTensorComparison_app_tmul (i : X ⟶ X')
    (F : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X'.carrier)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op V))
    (t : ((modulePushforward i).obj F).val.obj (op V)) :
    ((extensionTensorComparison i F).val.app (op V)).hom
        (toTensorSheafSection X' (AlgebraicGeometry.SheafOfModules.idealSheaf i)
          ((modulePushforward i).obj F) (op V) (a ⊗ₜ[X'.presheaf.obj (op V)] t)) =
      toTensorSheafSection X (idealSheafPullback i) F ((opensMap i).op.obj (op V))
        ((((modulePullbackPushforwardAdjunction i).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i)).val.app (op V)).hom a ⊗ₜ[
            X.presheaf.obj ((opensMap i).op.obj (op V))]
          (show F.val.obj ((opensMap i).op.obj (op V)) from t)) := by
  have h01 := Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul i
    (AlgebraicGeometry.SheafOfModules.idealSheaf i) ((modulePushforward i).obj F) (op V) a t
  have hε : (((modulePullbackPushforwardAdjunction i).counit.app F).val.app
      ((opensMap i).op.obj (op V))).hom
        ((((modulePullbackPushforwardAdjunction i).unit.app ((modulePushforward i).obj F)).val.app
          (op V)).hom t) = t :=
    congrArg (fun φ => (φ.val.app (op V)).hom t)
      ((modulePullbackPushforwardAdjunction i).right_triangle_components F)
  have hT := tensorSheafMap_app_toTensorSheafSection X (idealSheafPullback i)
    ((modulePullback i).obj ((modulePushforward i).obj F)) (idealSheafPullback i) F
    (𝟙 _) ((modulePullbackPushforwardAdjunction i).counit.app F) ((opensMap i).obj V)
    ((((modulePullbackPushforwardAdjunction i).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i)).val.app (op V)).hom a)
    ((((modulePullbackPushforwardAdjunction i).unit.app ((modulePushforward i).obj F)).val.app
          (op V)).hom t)
  refine (congrArg (fun z => (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
      (((𝟙 (idealSheafPullback i)), ((modulePullbackPushforwardAdjunction i).counit.app F)) :
        (idealSheafPullback i, (modulePullback i).obj ((modulePushforward i).obj F)) ⟶
          (idealSheafPullback i, F))).val.app ((opensMap i).op.obj (op V))).hom z) h01).trans ?_
  refine hT.trans ?_
  exact congrArg (fun z => toTensorSheafSection X (idealSheafPullback i) F
    ((opensMap i).op.obj (op V))
      ((((modulePullbackPushforwardAdjunction i).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i)).val.app (op V)).hom a ⊗ₜ z)) hε

/-- The unit of `(𝟙 X)^* ⊣ (𝟙 X)_*` is the inverse of the identification
`RingedSpaceModuleAdjunction.modulePullbackId`: both are mates of the identity of `(𝟙 X)_* = 𝟭`. -/
theorem modulePullbackPushforwardAdjunction_id_unit_app
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M =
      (modulePullbackId X).inv.app M := by
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (modulePullbackPushforwardAdjunction (𝟙 X)) (modulePullbackId X).hom M
  have hc : CategoryTheory.conjugateEquiv Adjunction.id
      (modulePullbackPushforwardAdjunction (𝟙 X)) (modulePullbackId X).hom =
      (SheafOfModules.pushforwardId (structureSheafRing X)).inv :=
    SheafOfModules.conjugateEquiv_pullbackId_hom (structureSheafRing X)
  rw [hc] at h
  have h' : (modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
      (modulePullbackId X).hom.app M = 𝟙 M := h.symm
  exact ((modulePullbackId X).app M).comp_hom_eq_id.1 h'

/-- **The map `ℐ₃ ⟶ ℐ₂` induced by `h^♯`, on sections.** For a morphism `h : X'₂ ⟶ X'₃` of
thickenings of `X`, with `i₃ = i₂ ≫ h`, the map `thickeningIdealMap` carries the pullback-unit
image of a local section `a` of `ℐ₃` to the pullback-unit image of the section of `ℐ₂` that the
ideal-sheaf map of the square produces from `a`. -/
theorem thickeningIdealMap_unit (i₂ : X ⟶ X₂) (h : X₂ ⟶ X₃) (V : Opens X₃.carrier)
    (m : (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h)).val.obj (op V)) :
    ((thickeningIdealMap i₂ (i₂ ≫ h) h rfl).val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom
        ((((modulePullbackPushforwardAdjunction (i₂ ≫ h)).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))).val.app (op V)).hom m) =
      ((((modulePullbackPushforwardAdjunction i₂).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)).val.app
            ((opensMap h).op.obj (op V))).hom
        (((Stacks.ClosedImmersion.idealSheafMap
            (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h))).val.app
              ((opensMap h).op.obj (op V))).hom
          ((((modulePullbackPushforwardAdjunction h).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))).val.app (op V)).hom m))) := by
  have hC := Stacks.ClosedImmersion.unit_comp_pushforward_homEquiv_conormalSheafMap
    (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h))
  have key := congrArg (fun φ => (φ.val.app (op V)).hom m) hC
  simp only [Adjunction.homEquiv_unit, modulePullbackPushforwardAdjunction_id_unit_app] at key
  refine key.trans ?_
  refine (RingedSpaceModuleAdjunction.modulePushforwardSquareIso_hom_val_app (𝟙 X) h i₂ (i₂ ≫ h)
    (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h)) (Stacks.ClosedImmersion.conormalSheaf i₂) V
      _).trans ?_
  refine ((Stacks.ClosedImmersion.conormalSheaf i₂).val.congr_map_apply
      (Subsingleton.elim _ (𝟙 _)) _).trans ?_
  simp only [PresheafOfModules.map_id]
  rfl

/-- The map `ℐ₃ ⊗ ℱ ⟶ ℐ₂ ⊗ ℱ` carries the pure tensor of the pullback-unit image of a section `a`
of `ℐ₃` with `t` to the pure tensor of the pullback-unit image of the section of `ℐ₂` that `h^♯`
produces from `a`, with `t`. -/
private theorem thickeningIdealMap_toTensorSheafSection_unit (i₂ : X ⟶ X₂) (h : X₂ ⟶ X₃)
    (F : SheafOfModules.{u} (structureSheafRing X)) (V : Opens X₃.carrier)
    (a : (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h)).val.obj (op V))
    (t : F.val.obj ((opensMap (i₂ ≫ h)).op.obj (op V))) :
    (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
      (((thickeningIdealMap i₂ (i₂ ≫ h) h rfl), (𝟙 F)) : (_, _) ⟶ (_, _))).val.app
        ((opensMap (i₂ ≫ h)).op.obj (op V))).hom
      (toTensorSheafSection X (idealSheafPullback (i₂ ≫ h)) F ((opensMap (i₂ ≫ h)).op.obj (op V))
        ((((modulePullbackPushforwardAdjunction (i₂ ≫ h)).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))).val.app (op V)).hom a ⊗ₜ t)) =
      toTensorSheafSection X (idealSheafPullback i₂) F ((opensMap (i₂ ≫ h)).op.obj (op V))
        (((((modulePullbackPushforwardAdjunction i₂).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)).val.app
            ((opensMap h).op.obj (op V))).hom
          (((Stacks.ClosedImmersion.idealSheafMap
            (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h))).val.app
              ((opensMap h).op.obj (op V))).hom
            ((((modulePullbackPushforwardAdjunction h).unit.app
              (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))).val.app
                (op V)).hom a))) ⊗ₜ t) :=
  (tensorSheafMap_app_toTensorSheafSection X (idealSheafPullback (i₂ ≫ h)) F
    (idealSheafPullback i₂) F (thickeningIdealMap i₂ (i₂ ≫ h) h rfl) (𝟙 F)
    ((opensMap (i₂ ≫ h)).obj V) _ t).trans
    (congrArg (fun z => toTensorSheafSection X (idealSheafPullback i₂) F
      ((opensMap (i₂ ≫ h)).op.obj (op V)) (z ⊗ₜ t)) (thickeningIdealMap_unit i₂ h V a))

/-- **The canonical map of an extension read across a morphism of thickenings.** Let
`h : X'₂ ⟶ X'₃` be a morphism of first order thickenings of `X` and let `ℱ'` be an extension as in
Tag 08L4 over `X'₂`. Read over `X'₃` through `h_*`, its canonical map of Tag 08L4 is
`ℐ₃ ⊗ ℱ ⟶ ℐ₂ ⊗ ℱ ⟶ 𝒦`, the map induced by `h^♯` followed by the canonical map of `ℱ'`.

This is the step `c_{ℰ'₃} = j ∘ c₃` of the proof of **Stacks 08LF**, and the module-structure half
of the comparison of extensions across a morphism of thickenings. -/
theorem firstOrderExtensionAction_restrictedExtension (i₂ : X ⟶ X₂) (i₃ : X ⟶ X₃)
    (h : X₂ ⟶ X₃) (comm : i₂ ≫ h = i₃) (hi₂ : IsFirstOrderThickening i₂)
    (hi₃ : IsFirstOrderThickening i₃) (F K : SheafOfModules.{u} (structureSheafRing X))
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K) 0) (hb : IsIso h.hom.base) :
    (firstOrderExtensionAction i₃ F K hi₃ (restrictedExtension i₂ i₃ h comm F K E hb)).val =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((thickeningIdealMap i₂ i₃ h comm), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫
        (firstOrderExtensionAction i₂ F K hi₂ E).val := by
  subst comm
  refine (eq_firstOrderExtensionAction_of_comp (i₂ ≫ h) F K hi₃ _ _ ?_).symm
  refine tensorSheaf_hom_ext fun V a s' => ?_
  -- the section `b` of `ℐ₂` over `h⁻¹ V` produced from `a`
  let b : (AlgebraicGeometry.SheafOfModules.idealSheaf i₂).val.obj ((opensMap h).op.obj (op V)) :=
    ((Stacks.ClosedImmersion.idealSheafMap
        (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h))).val.app ((opensMap h).op.obj (op V))).hom
      ((((modulePullbackPushforwardAdjunction h).unit.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))).val.app (op V)).hom a)
  let t : F.val.obj ((opensMap (i₂ ≫ h)).op.obj (op V)) :=
    (E.g.val.app ((opensMap h).op.obj (op V))).hom s'
  have hT1 := tensorSheafMap_app_toTensorSheafSection X₃
    (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))
    (restrictedExtension i₂ (i₂ ≫ h) h rfl F K E hb).Z.left
    (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h)) ((modulePushforward (i₂ ≫ h)).obj F)
    (𝟙 _) (restrictedExtension i₂ (i₂ ≫ h) h rfl F K E hb).g V a s'
  have hL3 := extensionTensorComparison_app_tmul (i₂ ≫ h) F V a t
  have hU := thickeningIdealMap_toTensorSheafSection_unit i₂ h F V a t
  have hL2 := extensionTensorComparison_app_tmul i₂ F ((opensMap h).obj V) b t
  have hP := (firstOrderExtensionAction i₂ F K hi₂ E).property ((opensMap h).obj V) b t s' rfl
  have hA := idealAction_app_tmul (i₂ ≫ h) (restrictedExtension i₂ (i₂ ≫ h) h rfl F K E hb).Z.left
    V a s'
  have hS := congrArg (fun φ => (φ.val.app (op V)).hom a)
    (Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι
      (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h)))
  let Tm := (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
    (((thickeningIdealMap i₂ (i₂ ≫ h) h rfl), (𝟙 F)) : (_, _) ⟶ (_, _))
  let c := (firstOrderExtensionAction i₂ F K hi₂ E).val
  let Ef := fun z => ((restrictedExtension i₂ (i₂ ≫ h) h rfl F K E hb).f.val.app (op V)).hom z
  refine (congrArg (fun z => Ef (((c.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom
      ((Tm.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom
        (((extensionTensorComparison (i₂ ≫ h) F).val.app (op V)).hom z))))) hT1).trans ?_
  refine (congrArg (fun z => Ef (((c.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom
      ((Tm.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom z)))) hL3).trans ?_
  refine (congrArg (fun z => Ef ((c.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom z))
    hU).trans ?_
  refine (congrArg (fun z => Ef ((c.val.app ((opensMap (i₂ ≫ h)).op.obj (op V))).hom z))
    hL2.symm).trans ?_
  refine hP.trans ?_
  refine Eq.trans ?_ hA.symm
  exact congrArg (fun r : (structureSheafRing X₂).obj.obj ((opensMap h).op.obj (op V)) =>
    r • (show E.Z.left.val.obj ((opensMap h).op.obj (op V)) from s')) hS

variable {X₁ : RingedSpace.{u, u}} in
/-- **A map of extensions as in Tag 08LC is a pushout.** If `ℱ'₂ ⟶ h_* ℱ'₁` is a map of extensions,
over a morphism `h : X'₁ ⟶ X'₂` of thickenings of `X`, inducing `k : 𝒦₂ ⟶ 𝒦₁` on the kernels and
the identity on `ℱ`, then the square formed with the two kernel inclusions is a pushout: `h_*` is
exact, since the base map of `h` is a homeomorphism, and a map of short exact sequences which is
the identity on the quotient exhibits its target as the pushout. -/
theorem PushedExtension.isPushout (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (hb : IsIso h.hom.base)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X))
    (k : K₂ ⟶ K₁)
    {E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0}
    {E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0}
    (w : PushedExtension i₁ i₂ h comm F K₁ K₂ k E₂ E₁) :
    IsPushout E₂.f ((modulePushforward i₂).map k ≫
        (thickeningPushforwardComp i₁ i₂ h comm).inv.app K₁) w.hom
        ((modulePushforward h).map E₁.f) := by
  have := hb
  have hMap := (CategoryTheory.Abelian.YonedaExtension.shortExact E₁).map_of_exact
    (modulePushforward h)
  have hz : (modulePushforward h).map E₁.f ≫
      ((modulePushforward h).map E₁.g ≫ (thickeningPushforwardComp i₁ i₂ h comm).hom.app F) =
        0 := by
    rw [← Category.assoc, ← Functor.map_comp,
      CategoryTheory.Abelian.YonedaExtension.comp_eq_zero E₁, Functor.map_zero, zero_comp]
  have h' : (ShortComplex.mk ((modulePushforward h).map E₁.f)
      ((modulePushforward h).map E₁.g ≫ (thickeningPushforwardComp i₁ i₂ h comm).hom.app F)
      hz).ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_ hMap
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      ((thickeningPushforwardComp i₁ i₂ h comm).app F) (by simp) (by simp)
  refine CategoryTheory.Abelian.isPushout_of_shortExact
    (CategoryTheory.Abelian.YonedaExtension.shortExact E₂) h' _ w.hom ?_ ?_
  · rw [w.kernel_commutes, Category.assoc]
  · rw [← Category.assoc, w.quotient_commutes, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id]

namespace FirstOrderThickeningSequence

variable (S : FirstOrderThickeningSequence.{u}) (hS : IsComplex S)

/-- **Stacks 08LE.** The canonical splitting `π : X'₁ ⟶ X` of the first thickening of a complex of
first order thickenings: the unique retraction of `i₁` with `π ≫ i₃ = f₁₂ ≫ f₂₃`
(`FirstOrderThickeningSequence.existsUnique_trivialization_of_isComplex`). -/
noncomputable def trivialization : SplitMono S.i₁ where
  retraction := (S.existsUnique_trivialization_of_isComplex hS).choose
  id := (S.existsUnique_trivialization_of_isComplex hS).choose_spec.1.1

/-- The canonical splitting satisfies `π ≫ i₃ = f₁₂ ≫ f₂₃`. -/
theorem trivialization_retraction_comp :
    (S.trivialization hS).retraction ≫ S.i₃ = S.f₁₂ ≫ S.f₂₃ :=
  (S.existsUnique_trivialization_of_isComplex hS).choose_spec.1.2

end FirstOrderThickeningSequence

/-- **Stacks Project, Tag 08LF.** Let `(X, 𝒪_X)` be a ringed space, `ℱ` an `𝒪_X`-module and
`X'₁ ⟶ X'₂ ⟶ X'₃` a complex of first order thickenings of `(X, 𝒪_X)` (Tag 08LE), with ideals
`ℐᵢ`. Let `cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ` be maps and `0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` a short exact sequence of
`𝒪_X`-modules for which the two squares of the remark commute. Let `ℱ'₂` be an extension
`0 ⟶ 𝒦₂ ⟶ ℱ'₂ ⟶ ℱ ⟶ 0` as in Tag 08L4 over `X'₂` with `c_{ℱ'₂} = c₂`, and let `ℱ'₁` be the
extension over `X'₁` that the functoriality of Tag 08LC produces from it. That functoriality
carries `ℱ'₂` to an extension as in Tag 08L4 over `X'₁` together with a map of extensions `w`
from `ℱ'₂`, which is `𝒦₂ ⟶ 𝒦₁` on kernels and the identity on `ℱ`; the statement is made for
every extension `ℱ'₁` over `X'₁` receiving such a map, so in particular for the one of Tag 08LC
(which in addition has `c_{ℱ'₁} = c₁`, a property the identity of classes does not use).

Then the boundary map `∂ : Ext¹_{𝒪_X}(ℱ, 𝒦₁) ⟶ Ext²_{𝒪_X}(ℱ, 𝒦₃)` of
`0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` — Yoneda composition with the class of that sequence — sends the class
`ξ_{ℱ'₁}` of Tag 08LB, formed with the canonical splitting `π` of Tag 08LE, to the obstruction
class `o(ℱ, 𝒦₃, c₃)` of Tag 08L8.

The first compatibility square of the remark, relating `c₂`, `c₁` and `𝒦₂ ⟶ 𝒦₁`, is what makes
Tag 08LC applicable; once `ℱ'₁` and `w` are given it is not needed for the identity of classes,
so it is not a hypothesis here. It is a hypothesis of the version for the extension that Tag 08LC
constructs, `boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass`, where it is the
input of that construction; the map `c₁` enters only through that square, so it does not appear
here either. -/
@[stacks 08LF]
theorem boundary_underlyingExtensionClass_eq_obstructionClass
    (S : FirstOrderThickeningSequence.{u})
    [HasExt (SheafOfModules.{u} (structureSheafRing S.X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))]
    (hS : IsComplex S) (F K₁ K₂ K₃ : SheafOfModules.{u} (structureSheafRing S.X))
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).obj
      (idealSheafPullback S.i₂)).obj F) ⟶ K₂)
    (c₃ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).obj
      (idealSheafPullback S.i₃)).obj F) ⟶ K₃)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩)).map
        (((thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₂).obj F)
      ((modulePushforward S.i₂).obj K₂) 0)
    (hE₂ : (firstOrderExtensionAction S.i₂ F K₂ S.firstOrder₂ E₂).val = c₂)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward S.i₁).obj F)
      ((modulePushforward S.i₁).obj K₁) 0)
    (w : PushedExtension S.i₁ S.i₂ S.f₁₂ S.comm₁₂ F K₁ K₂ k₂₁ E₂ E₁) :
    (underlyingExtensionClass S.i₁ (S.trivialization hS) S.firstOrder₁.1.1 F K₁ E₁).comp
        hK.extClass (by decide) =
      obstructionClass S.i₃ S.firstOrder₃ F K₃ c₃ := by
  have hw := PushedExtension.isPushout S.i₁ S.i₂ S.f₁₂ S.comm₁₂
    (isIso_base_of_thickeningMap S.i₁ S.i₂ S.f₁₂ S.comm₁₂ S.firstOrder₁.1.1 S.firstOrder₂.1.1)
    F K₁ K₂ k₂₁ w
  have hrestrict := firstOrderExtensionAction_restrictedExtension S.i₂ S.i₃ S.f₂₃ S.comm₂₃
    S.firstOrder₂ S.firstOrder₃ F K₂ E₂
    (isIso_base_of_thickeningMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃ S.firstOrder₂.1.1 S.firstOrder₃.1.1)
  rw [hE₂] at hrestrict
  have hjm : Mono (Injective.ι K₃) := Injective.ι_mono K₃
  have hKJ : (ShortComplex.mk (Injective.ι K₃) (cokernel.π (Injective.ι K₃))
      (cokernel.condition (Injective.ι K₃))).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      hjm inferInstance
  have hk₃₂ : Mono k₃₂ := hK.mono_f
  exact boundary_underlyingExtensionClass_of_injective S (S.trivialization hS)
    (S.trivialization_retraction_comp hS) F K₁ K₂ K₃ (Injective.under K₃)
    (cokernel (Injective.ι K₃)) (Injective.injective_under K₃) (Injective.ι K₃)
    (cokernel.π (Injective.ι K₃)) (cokernel.condition (Injective.ι K₃)) hKJ
    (Injective.factorThru (Injective.ι K₃) k₃₂) k₃₂ k₂₁ hk hK
    (Injective.comp_factorThru _ _) c₂ c₃ hc₃₂ E₂ E₁ w hw hrestrict

namespace SecondThickening

variable {X₁ : RingedSpace.{u, u}} {i : X ⟶ X₁} (ST : SecondThickening i)

/-- The morphism of thickenings `h : X'₁ ⟶ X'₂` of a second thickening presented on the space of
the first: the identity on the underlying space, with comorphism `h^♯ : 𝒪'₂ ⟶ 𝒪_{X'₁}`. -/
noncomputable def toSpace : X₁ ⟶ ST.space :=
  InducedCategory.homMk
    ({ base := 𝟙 X₁.carrier, c := ST.hSharp } :
      X₁.toPresheafedSpace ⟶ ST.space.toPresheafedSpace)

/-- `h` is a morphism of thickenings of `X`: `i ≫ h` is the second thickening. -/
theorem comp_toSpace : i ≫ ST.toSpace = ST.hom := rfl

end SecondThickening

section Square

variable {X₁ : RingedSpace.{u, u}} {i : X ⟶ X₁} (ST : SecondThickening i)
  (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X))
  (c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
    (idealSheafPullback i)).obj F) ⟶ K₁)
  (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
    (idealSheafPullback ST.hom)).obj F) ⟶ K₂) (k : K₂ ⟶ K₁)
  (hc : c₂ ≫ k = ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
      (((thickeningIdealMap i ST.hom ST.toSpace ST.comp_toSpace), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₁)

include hc in
/-- **The square of Tag 08LC, read on local pure tensors.** If `c₂ ≫ k = (ℐ₂ ⟶ ℐ₁ ⊗ 1) ≫ c₁`,
with `ℐ₂ ⟶ ℐ₁` the map induced by `h^♯`, then for a section `b` of `ℐ₂` and a section `m` of `ℐ₁`
with the same image in `𝒪_{X'₁}` the two descended actions agree on `b ⊗ y` and `m ⊗ y`. This is
the form `PushoutDescentData.comm` in which the construction of Tag 08LC takes the square. -/
theorem SecondThickening.comm_of_thickeningIdealMap (V : Opens X₁.carrier)
    (b : ST.ideal.val.obj (op V)) (m : (Stacks.ClosedImmersion.idealSheaf i).val.obj (op V))
    (hm : idealIncl i V m = ST.hSharpApp V (ST.inclTwo V b))
    (y : ((modulePushforward ST.hom).obj F).val.obj (op V)) :
    (descendedActionOfMap ST.hom F K₁ (c₂ ≫ k)).val.app (op V)
        (toTensorSheafSection ST.space (Stacks.ClosedImmersion.idealSheaf ST.hom)
          ((modulePushforward ST.hom).obj F) (op V)
          (b ⊗ₜ[ST.space.presheaf.obj (op V)] y)) =
      ST.toSecond K₁ V ((descendedActionOfMap i F K₁ c₁).val.app (op V)
        (toTensorSheafSection X₁ (Stacks.ClosedImmersion.idealSheaf i)
          ((modulePushforward i).obj F) (op V)
          (m ⊗ₜ[X₁.presheaf.obj (op V)] ST.ofSecond F V y))) := by
  -- the section of `ℐ₁` that the square produces from `b` is `m`
  have hb : ((Stacks.ClosedImmersion.idealSheafMap
        (comp_eq_id_comp (rfl : i ≫ ST.toSpace = i ≫ ST.toSpace))).val.app
          ((opensMap ST.toSpace).op.obj (op V))).hom
        ((((modulePullbackPushforwardAdjunction ST.toSpace).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf (i ≫ ST.toSpace))).val.app (op V)).hom b) =
      m := by
    refine idealIncl_injective i V ?_
    refine Eq.trans ?_ hm.symm
    exact congrArg (fun φ => (φ.val.app (op V)).hom b)
      (Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι
        (comp_eq_id_comp (rfl : i ≫ ST.toSpace = i ≫ ST.toSpace)))
  have hL := extensionTensorComparison_app_tmul ST.hom F V b y
  have hR := extensionTensorComparison_app_tmul i F V m (ST.ofSecond F V y)
  have hU := thickeningIdealMap_toTensorSheafSection_unit i ST.toSpace F V b y
  rw [hb] at hU
  have hcV := congrArg (fun φ => (φ.val.app ((opensMap ST.hom).op.obj (op V))).hom
    (toTensorSheafSection X (idealSheafPullback ST.hom) F ((opensMap ST.hom).op.obj (op V))
      ((((modulePullbackPushforwardAdjunction ST.hom).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf ST.hom)).val.app (op V)).hom b ⊗ₜ y))) hc
  refine (congrArg (fun z => ((c₂ ≫ k).val.app ((opensMap ST.hom).op.obj (op V))).hom z)
    hL).trans ?_
  refine hcV.trans ?_
  refine (congrArg (fun z => (c₁.val.app ((opensMap ST.hom).op.obj (op V))).hom z) hU).trans ?_
  exact (congrArg (fun z => (c₁.val.app ((opensMap i).op.obj (op V))).hom z) hR).symm

/-- The data of Tag 08LC from the commutative square of the remark, stated with the induced map
`ℐ₂ ⟶ ℐ₁` of `thickeningIdealMap`. -/
noncomputable def PushoutDescentData.ofSquare : PushoutDescentData ST where
  F := F
  K₁ := K₁
  K₂ := K₂
  c₁ := c₁
  c₂ := c₂
  kernelMap := k
  comm V b m hm y := ST.comm_of_thickeningIdealMap F K₁ K₂ c₁ c₂ k hc V b m hm y

end Square

namespace PushoutDescentData

attribute [local instance] sectionsModuleOverSpace

variable {X₁ : RingedSpace.{u, u}} {i : X ⟶ X₁} {ST : SecondThickening i}
  (dat : PushoutDescentData ST)
  (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward ST.hom).obj dat.F)
    ((modulePushforward ST.hom).obj dat.K₂) 0)
  (hi : IsFirstOrderThickening i)
  (hE₂ : (firstOrderExtensionAction ST.hom dat.F dat.K₂ ST.firstOrder E₂).val = dat.c₂)

/-- The map from `ℱ'₂` to the middle term of the extension `ℱ'₁` of Tag 08LC, read over `X'₂`:
the pushout inclusion `ℱ'₂ ⟶ ℱ'₂ ⊔_{𝒦₂} 𝒦₁` followed by the identification of the pushout with
the middle term. It is `𝒪'₂`-linear because the twisted action of `(a, 0) ∈ 𝒪'₂ ⋉ ℐ₁` is the
action of `a`, and `q(a, 0) = h^♯ a`. -/
noncomputable def toMiddle :
    E₂.Z.left ⟶ (modulePushforward ST.toSpace).obj (dat.middle E₂ hi hE₂) :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf _).map
        (pushoutCompatibleMap ST.hom dat.F dat.K₁ dat.K₂ ST.firstOrder dat.kernelMap E₂).hom.val ≫
      (PresheafOfModules.toPresheaf ST.sqZeroRing.obj).map (dat.middleIso E₂ hi hE₂).inv.val)
    (fun U r x => by
      let inl := (pushoutCompatibleMap ST.hom dat.F dat.K₁ dat.K₂ ST.firstOrder dat.kernelMap
        E₂).hom
      change ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom ((inl.val.app U).hom (r • x)) =
        ST.hSharpApp U.unop r • (show (dat.middle E₂ hi hE₂).val.obj (op U.unop) from
          ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom ((inl.val.app U).hom x))
      let p : (dat.pushoutMod E₂).val.obj (op U.unop) := (inl.val.app U).hom x
      have key := (dat.twistedSmul_eq E₂ U.unop (ST.sqMk U.unop r 0) p).trans
        ((congrArg (fun z => _ - z) (dat.twist_zero_left E₂ U.unop p)).trans (sub_zero _))
      refine (congrArg ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom
        ((inl.val.app U).hom.map_smul r x)).trans ?_
      refine (congrArg ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom key.symm).trans ?_
      refine (((dat.middleIso E₂ hi hE₂).inv.val.app U).hom.map_smul
        (ST.sqMk U.unop r 0) p).trans ?_
      have hq : (ST.sqZeroProj hi).hom.app (op U.unop) (ST.sqMk U.unop r 0) =
          ST.hSharpApp U.unop r :=
        (ST.sqZeroProj_hom_app hi U.unop (ST.sqMk U.unop r 0)).trans
          ((congrArg (fun z => ST.hSharpApp U.unop r - z) (idealIncl_zero i U.unop)).trans
            (sub_zero _))
      exact congrArg (fun z : X₁.presheaf.obj (op U.unop) =>
        z • (show (dat.middle E₂ hi hE₂).val.obj (op U.unop) from
          ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom p)) hq)⟩

/-- **The map of extensions of Tag 08LC.** The extension `ℱ'₁ = extensionOne` that Tag 08LC
produces from `ℱ'₂` receives a map of extensions from `ℱ'₂` over the morphism of thickenings
`h = SecondThickening.toSpace`, inducing `κ : 𝒦₂ ⟶ 𝒦₁` on kernels and the identity on `ℱ`. -/
noncomputable def pushedExtension :
    PushedExtension i ST.hom ST.toSpace ST.comp_toSpace dat.F dat.K₁ dat.K₂ dat.kernelMap E₂
      (dat.extensionOne E₂ hi hE₂) where
  hom := dat.toMiddle E₂ hi hE₂
  kernel_commutes := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    have hk := congrArg (fun φ => (φ.val.app U).hom x)
      (pushoutCompatibleMap ST.hom dat.F dat.K₁ dat.K₂ ST.firstOrder dat.kernelMap
        E₂).kernel_commutes
    refine (congrArg ((dat.middleIso E₂ hi hE₂).inv.val.app U).hom hk).trans ?_
    exact (dat.extInclOne_app E₂ hi hE₂ U.unop _).symm
  quotient_commutes := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    have hq := congrArg (fun φ => (φ.val.app U).hom x)
      (pushoutCompatibleMap ST.hom dat.F dat.K₁ dat.K₂ ST.firstOrder dat.kernelMap
        E₂).quotient_commutes
    refine (dat.extQuotOne_app E₂ hi hE₂ U.unop _).trans ?_
    have hhi := congrArg (fun φ => (φ.val.app U).hom
        (((pushoutCompatibleMap ST.hom dat.F dat.K₁ dat.K₂ ST.firstOrder dat.kernelMap
          E₂).hom.val.app
          U).hom x))
      (dat.middleIso E₂ hi hE₂).inv_hom_id
    exact (congrArg (fun z => ST.ofSecond dat.F U.unop (dat.quotSection E₂ U.unop z)) hhi).trans hq

end PushoutDescentData

namespace SecondThickening

variable {X₁ : RingedSpace.{u, u}} {i : X ⟶ X₁} (ST : SecondThickening i)

/-- The sequence of first order thickenings `X'₁ ⟶ X'₂ ⟶ X'₃` whose first morphism is the
morphism of thickenings `h` of a second thickening presented on the space of the first, the
presentation in which Tag 08LC is constructed. -/
noncomputable def thickeningSequence (hi : IsFirstOrderThickening i) (i₃ : X ⟶ X₃)
    (hi₃ : IsFirstOrderThickening i₃) (f₂₃ : ST.space ⟶ X₃) (comm₂₃ : ST.hom ≫ f₂₃ = i₃)
    (idealMap₂₁ : (modulePullback ST.hom).obj (AlgebraicGeometry.SheafOfModules.idealSheaf ST.hom) ⟶
      (modulePullback i).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i))
    (idealMap₃₂ : (modulePullback i₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₃) ⟶
      (modulePullback ST.hom).obj (AlgebraicGeometry.SheafOfModules.idealSheaf ST.hom)) :
    FirstOrderThickeningSequence.{u} where
  X := X
  X₁ := X₁
  X₂ := ST.space
  X₃ := X₃
  i₁ := i
  i₂ := ST.hom
  i₃ := i₃
  firstOrder₁ := hi
  firstOrder₂ := ST.firstOrder
  firstOrder₃ := hi₃
  f₁₂ := ST.toSpace
  f₂₃ := f₂₃
  comm₁₂ := ST.comp_toSpace
  comm₂₃ := comm₂₃
  idealMap₂₁ := idealMap₂₁
  idealMap₃₂ := idealMap₃₂

end SecondThickening

/-- **Stacks Project, Tag 08LF**, for the extension `ℱ'₁` that Tag 08LC constructs. Let
`X'₁ ⟶ X'₂ ⟶ X'₃` be a complex of first order thickenings of `(X, 𝒪_X)` (Tag 08LE), with
`X'₂` presented on the space of `X'₁` as in Tag 08LC, and let `(𝒦ᵢ, cᵢ)`, a short exact sequence
`0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` and the two commutative squares be as in the remark. For an extension
`ℱ'₂` over `X'₂` as in Tag 08L4 with `c_{ℱ'₂} = c₂`, let `ℱ'₁` be the extension over `X'₁` that the
functoriality of Tag 08LC produces (`PushoutDescentData.extensionOne`). Then the boundary map
`Ext¹_{𝒪_X}(ℱ, 𝒦₁) ⟶ Ext²_{𝒪_X}(ℱ, 𝒦₃)` sends `ξ_{ℱ'₁}`, formed with the canonical splitting of
Tag 08LE, to the obstruction class `o(ℱ, 𝒦₃, c₃)` of Tag 08L8. -/
@[stacks 08LF]
theorem boundary_underlyingExtensionClass_extensionOne_eq_obstructionClass
    {X₁ : RingedSpace.{u, u}} {i : X ⟶ X₁} (hi : IsFirstOrderThickening i)
    (ST : SecondThickening i) (i₃ : X ⟶ X₃) (hi₃ : IsFirstOrderThickening i₃)
    (f₂₃ : ST.space ⟶ X₃) (comm₂₃ : ST.hom ≫ f₂₃ = i₃)
    (idealMap₂₁ : (modulePullback ST.hom).obj (AlgebraicGeometry.SheafOfModules.idealSheaf ST.hom) ⟶
      (modulePullback i).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i))
    (idealMap₃₂ : (modulePullback i₃).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₃) ⟶
      (modulePullback ST.hom).obj (AlgebraicGeometry.SheafOfModules.idealSheaf ST.hom))
    [HasExt (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
    (hS : IsComplex (ST.thickeningSequence hi i₃ hi₃ f₂₃ comm₂₃ idealMap₂₁ idealMap₃₂))
    (F K₁ K₂ K₃ : SheafOfModules.{u} (structureSheafRing X))
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁) (hk : k₃₂ ≫ k₂₁ = 0)
    (hK : (ShortComplex.mk k₃₂ k₂₁ hk).ShortExact)
    (c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (idealSheafPullback i)).obj F) ⟶ K₁)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (idealSheafPullback ST.hom)).obj F) ⟶ K₂)
    (c₃ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (idealSheafPullback i₃)).obj F) ⟶ K₃)
    (hc₂₁ : c₂ ≫ k₂₁ =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        (((thickeningIdealMap i ST.hom ST.toSpace ST.comp_toSpace), (𝟙 F)) :
          (_, _) ⟶ (_, _))) ≫ c₁)
    (hc₃₂ : c₃ ≫ k₃₂ =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        (((thickeningIdealMap ST.hom i₃ f₂₃ comm₂₃), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₂)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward ST.hom).obj F)
      ((modulePushforward ST.hom).obj K₂) 0)
    (hE₂ : (firstOrderExtensionAction ST.hom F K₂ ST.firstOrder E₂).val = c₂) :
    (underlyingExtensionClass i
        ((ST.thickeningSequence hi i₃ hi₃ f₂₃ comm₂₃ idealMap₂₁ idealMap₃₂).trivialization hS)
        hi.1.1 F K₁
        ((PushoutDescentData.ofSquare ST F K₁ K₂ c₁ c₂ k₂₁ hc₂₁).extensionOne E₂ hi hE₂)).comp
        hK.extClass (by decide) =
      obstructionClass i₃ hi₃ F K₃ c₃ := by
  let : HasExt (SheafOfModules.{u} (structureSheafRing
      (ST.thickeningSequence hi i₃ hi₃ f₂₃ comm₂₃ idealMap₂₁ idealMap₃₂).X)) :=
    ‹HasExt (SheafOfModules.{u} (structureSheafRing X))›
  let : HasDerivedCategory (SheafOfModules.{u} (structureSheafRing
      (ST.thickeningSequence hi i₃ hi₃ f₂₃ comm₂₃ idealMap₂₁ idealMap₃₂).X)) :=
    ‹HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))›
  exact boundary_underlyingExtensionClass_eq_obstructionClass
    (ST.thickeningSequence hi i₃ hi₃ f₂₃ comm₂₃ idealMap₂₁ idealMap₃₂) hS F K₁ K₂ K₃
    k₃₂ k₂₁ hk hK c₂ c₃ hc₃₂ E₂ hE₂
    ((PushoutDescentData.ofSquare ST F K₁ K₂ c₁ c₂ k₂₁ hc₂₁).extensionOne E₂ hi hE₂)
    ((PushoutDescentData.ofSquare ST F K₁ K₂ c₁ c₂ k₂₁ hc₂₁).pushedExtension E₂ hi hE₂)

end AlgebraicGeometry.RingedSpaceThickening

end
