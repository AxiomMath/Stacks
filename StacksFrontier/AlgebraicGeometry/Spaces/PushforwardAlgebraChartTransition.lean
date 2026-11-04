module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageRingSectionsChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentAlgebraColimitModules
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardIdealImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAlgebraFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit

/-!
# Maps of direct-image algebras read on base-changed charts

Let `Z ⟶ X` be a representable morphism of algebraic spaces.  The direct image `π_* 𝒪_Z` occurs
in two spellings.  As a sheaf of `𝒪_X`-algebras it is `AlgebraicGeometry.Space.pushforwardAlgebra`,
the spelling of the anti-equivalence of Stacks 081V and of the limit presentation of Stacks 07VR
(`AlgebraicGeometry.Space.exists_affineOver_limit_pushforwardColimit_of_isFinite`), whose
transition maps are morphisms of algebra sheaves.  As an `𝒪_X`-module whose sections over an
étale chart `V` of `X` are the regular functions on `V ×_X Z` it is
`AlgebraicGeometry.Space.chartBaseChangeStructureModule`, the spelling in which ideals of `𝒪_Z`
are pushed forward (`AlgebraicGeometry.Space.pushforwardSubmodule`) and in which
`Space.exists_ideal_pushforwardSubmodule_eq_imageSubmodule_of_isLocallySurjective` is stated.

This file compares the two by an explicit isomorphism, and reads a morphism of direct-image
algebras as a morphism of the chart modules which is multiplicative on sections, and locally
surjective when the morphism of algebras is.  It also transports a colimit of direct-image
algebras to the chart modules.

## Main definitions and results

* `AlgebraicGeometry.Space.pushforwardAlgebraModuleIso`: the underlying module of
  `π_* 𝒪_Z` is the chart module; on sections it is the ring isomorphism
  `AlgebraicGeometry.Space.directImageRingSectionsRingEquiv`
  (`AlgebraicGeometry.Space.pushforwardAlgebraModuleIso_hom_val_app`), so it is multiplicative
  (`AlgebraicGeometry.Space.pushforwardAlgebraModuleIso_hom_val_app_mul`).
* `AlgebraicGeometry.Space.pushforwardAlgebraChartMap`: a morphism of direct-image algebras,
  conjugated to the chart modules.  It is multiplicative
  (`AlgebraicGeometry.Space.pushforwardAlgebraChartMap_val_app_mul`) and locally surjective when
  the morphism of algebras is
  (`AlgebraicGeometry.Space.exists_pushforwardAlgebraChartMap_val_app_eq_map`).
* `AlgebraicGeometry.Space.exists_ideal_pushforwardSubmodule_eq_image_pushforwardAlgebraChartMap`:
  the image of the direct image of an ideal under such a map is the direct image of an ideal.
* `AlgebraicGeometry.Space.pushforwardAlgebraChartMap_pushforwardAlgebraMap_val_app_eq_appTop`:
  the map induced by a morphism `f : Z₁ ⟶ Z₂` over `X` is pullback of regular functions along any
  morphism of base-changed charts `Z₁ ×_X Q ⟶ Z₂ ×_X Q` over `f`.
* `AlgebraicGeometry.Space.chartStructureModuleDiagram` and
  `AlgebraicGeometry.Space.nonempty_isColimit_chartStructureModuleCocone`: a diagram of spaces
  affine over `X` whose direct-image algebras form a colimit gives a colimit of chart modules.

## Implementation notes

The underlying module of `pushforwardAlgebra Z` is the direct image of modules of Stacks 03D6
attached to the morphism of ringed topoi; it is identified with
`AlgebraicGeometry.Space.modulePushforward` by
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`, which is the identity on
sections, and then with the chart module by `AlgebraicGeometry.Space.modulePushforwardChartIso`.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-! ### The comparison isomorphism -/

/-- **The direct-image algebra, as a module, is the chart module.**  For `Z` over `X` with
representable structure morphism, the underlying `𝒪_X`-module of `π_* 𝒪_Z` is the module whose
sections over an étale chart `V` of `X` are the regular functions on `V ×_X Z`. -/
def pushforwardAlgebraModuleIso (Z : Over X) (hZ : yoneda.relativelyRepresentable Z.hom.hom) :
    (pushforwardAlgebra B S hS Z).underlyingModule ≅
      chartBaseChangeStructureModule B S hS Z.hom hZ :=
  (pushforwardModulesIsoModulePushforward B S hS Z.hom).app
      (SheafOfModules.unit (structureRingSheaf B S hS Z.left)) ≪≫
    (modulePushforwardChartIso B S hS Z.hom hZ).app _

/-- The chart comparison of `modulePushforward` on the unit is the ring isomorphism of sections. -/
private theorem modulePushforwardChartIso_hom_app_unit_val_app (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (n : ((modulePushforward B S hS Z.hom).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Z.left))).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS Z.hom hZ).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS Z.left))).val.app (op V) n =
      directImageRingSectionsRingEquiv B S hS Z.hom hZ (structureRingSheaf B S hS Z.left) V n :=
  (modulePushforwardChartIso_hom_app_val_app B S hS Z.hom hZ _ V n).trans rfl

/-- The comparison is the composite of its two steps on sections. -/
private theorem pushforwardAlgebraModuleIso_hom_val_app_eq_comp (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (n : ((pushforwardAlgebra B S hS Z).underlyingModule).val.obj (op V)) :
    ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V)) n =
      ((modulePushforwardChartIso B S hS Z.hom hZ).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS Z.left))).val.app (op V)
        (((pushforwardModulesIsoModulePushforward B S hS Z.hom).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS Z.left))).val.app (op V) n) :=
  rfl

/-- **On sections over a chart `V`, the comparison is the ring isomorphism
`AlgebraicGeometry.Space.directImageRingSectionsRingEquiv`** from the sections of `π_* 𝒪_Z` over
`V` to the regular functions on `V ×_X Z`. -/
theorem pushforwardAlgebraModuleIso_hom_val_app (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (n : ((pushforwardAlgebra B S hS Z).underlyingModule).val.obj (op V)) :
    ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V)) n =
      directImageRingSectionsRingEquiv B S hS Z.hom hZ (structureRingSheaf B S hS Z.left) V n :=
  (pushforwardAlgebraModuleIso_hom_val_app_eq_comp B S hS Z hZ V n).trans
    (modulePushforwardChartIso_hom_app_unit_val_app B S hS Z hZ V _)

/-- **The comparison is multiplicative on sections**: the product of two sections of the algebra
`π_* 𝒪_Z` goes to the product of regular functions on `V ×_X Z`. -/
theorem pushforwardAlgebraModuleIso_hom_val_app_mul (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (a b : (pushforwardAlgebra B S hS Z).right.obj.obj (op V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) (a * b) =
      @HMul.hMul (chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V))
        (chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V))
        (chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V)) instHMul
        ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) a)
        ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) b) :=
  (pushforwardAlgebraModuleIso_hom_val_app B S hS Z hZ V _).trans
    ((map_mul (directImageRingSectionsRingEquiv B S hS Z.hom hZ
      (structureRingSheaf B S hS Z.left) V) a b).trans
      (congrArg₂ _ (pushforwardAlgebraModuleIso_hom_val_app B S hS Z hZ V a).symm
        (pushforwardAlgebraModuleIso_hom_val_app B S hS Z hZ V b).symm))

private theorem pushforwardAlgebraModuleIso_hom_inv_val_app (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (x : chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V)
      ((pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V) x) = x :=
  congrArg (fun φ => φ.val.app (op V) x) (pushforwardAlgebraModuleIso B S hS Z hZ).inv_hom_id

private theorem pushforwardAlgebraModuleIso_inv_hom_val_app (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (x : (pushforwardAlgebra B S hS Z).right.obj.obj (op V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V)
      ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) x) = x :=
  congrArg (fun φ => φ.val.app (op V) x) (pushforwardAlgebraModuleIso B S hS Z hZ).hom_inv_id

/-- The comparison is injective on sections. -/
private theorem pushforwardAlgebraModuleIso_hom_val_app_injective (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    Function.Injective ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V)) :=
  Function.LeftInverse.injective (pushforwardAlgebraModuleIso_inv_hom_val_app B S hS Z hZ V)

/-- The inverse comparison is multiplicative too. -/
private theorem pushforwardAlgebraModuleIso_inv_val_app_mul (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (a b : chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V) (a * b) =
      @HMul.hMul ((pushforwardAlgebra B S hS Z).right.obj.obj (op V))
        ((pushforwardAlgebra B S hS Z).right.obj.obj (op V))
        ((pushforwardAlgebra B S hS Z).right.obj.obj (op V)) instHMul
        ((pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V) a)
        ((pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V) b) := by
  refine pushforwardAlgebraModuleIso_hom_val_app_injective B S hS Z hZ V
    ((pushforwardAlgebraModuleIso_hom_inv_val_app B S hS Z hZ V _).trans ?_)
  refine Eq.trans ?_ (pushforwardAlgebraModuleIso_hom_val_app_mul B S hS Z hZ V _ _).symm
  exact (congrArg₂ _ (pushforwardAlgebraModuleIso_hom_inv_val_app B S hS Z hZ V a)
    (pushforwardAlgebraModuleIso_hom_inv_val_app B S hS Z hZ V b)).symm

/-- The comparison commutes with restriction along a morphism of charts of `X`. -/
private theorem pushforwardAlgebraModuleIso_hom_val_app_map (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) {V W : SmallEtale B S hS X.1} (h : W ⟶ V)
    (x : ((pushforwardAlgebra B S hS Z).underlyingModule).val.obj (op V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op W)
      (((pushforwardAlgebra B S hS Z).underlyingModule).val.map h.op x) =
      (chartBaseChangeStructureModule B S hS Z.hom hZ).val.map h.op
        ((pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) x) :=
  PresheafOfModules.naturality_apply (X := op V) (Y := op W)
    (pushforwardAlgebraModuleIso B S hS Z hZ).hom.val h.op x

/-! ### Morphisms of direct-image algebras on the chart modules -/

/-- **A morphism of direct-image algebras, read on the chart modules.**  For `Z₁, Z₂` over `X`
with representable structure morphisms and a morphism of `𝒪_X`-algebras
`α : π_{2,*} 𝒪_{Z₂} ⟶ π_{1,*} 𝒪_{Z₁}`, the morphism of chart modules conjugate to the underlying
morphism of modules of `α` under `AlgebraicGeometry.Space.pushforwardAlgebraModuleIso`. -/
def pushforwardAlgebraChartMap {Z₁ Z₂ : Over X}
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁) :
    chartBaseChangeStructureModule B S hS Z₂.hom hZ₂ ⟶
      chartBaseChangeStructureModule B S hS Z₁.hom hZ₁ :=
  (pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv ≫ AlgebraSheaf.underlyingModuleMap α ≫
    (pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom

/-- On sections, the morphism of chart modules is `α` conjugated by the comparisons. -/
theorem pushforwardAlgebraChartMap_val_app {Z₁ Z₂ : Over X}
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁) (V : SmallEtale B S hS X.1)
    (x : chartSectionsRing B S hS Z₂.left ((smallBaseChange B S hS Z₂.hom hZ₂).obj V)) :
    (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α).val.app (op V) x =
      (pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom.val.app (op V)
        (α.right.hom.app (op V)
          ((pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv.val.app (op V) x)) :=
  rfl

/-- **A morphism of direct-image algebras is multiplicative on the chart modules.** -/
theorem pushforwardAlgebraChartMap_val_app_mul {Z₁ Z₂ : Over X}
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁)
    (Q : SmallEtale B S hS X.1)
    (a b : chartSectionsRing B S hS Z₂.left ((smallBaseChange B S hS Z₂.hom hZ₂).obj Q)) :
    (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α).val.app (op Q) (a * b) =
      @HMul.hMul (chartSectionsRing B S hS Z₁.left ((smallBaseChange B S hS Z₁.hom hZ₁).obj Q))
        (chartSectionsRing B S hS Z₁.left ((smallBaseChange B S hS Z₁.hom hZ₁).obj Q))
        (chartSectionsRing B S hS Z₁.left ((smallBaseChange B S hS Z₁.hom hZ₁).obj Q)) instHMul
        ((pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α).val.app (op Q) a)
        ((pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α).val.app (op Q) b) := by
  refine (pushforwardAlgebraChartMap_val_app B S hS hZ₁ hZ₂ α Q _).trans ?_
  refine (congrArg (fun y => (pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom.val.app (op Q)
      (α.right.hom.app (op Q) y))
    (pushforwardAlgebraModuleIso_inv_val_app_mul B S hS Z₂ hZ₂ Q a b)).trans ?_
  refine (congrArg ((pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom.val.app (op Q))
    (RingHom.map_mul (α.right.hom.app (op Q)).hom
      ((pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv.val.app (op Q) a :
        (pushforwardAlgebra B S hS Z₂).right.obj.obj (op Q))
      ((pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv.val.app (op Q) b :
        (pushforwardAlgebra B S hS Z₂).right.obj.obj (op Q)))).trans ?_
  refine (pushforwardAlgebraModuleIso_hom_val_app_mul B S hS Z₁ hZ₁ Q
    (α.right.hom.app (op Q) ((pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv.val.app (op Q) a))
    (α.right.hom.app (op Q)
      ((pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).inv.val.app (op Q) b))).trans ?_
  exact congrArg₂ _ (pushforwardAlgebraChartMap_val_app B S hS hZ₁ hZ₂ α Q a).symm
    (pushforwardAlgebraChartMap_val_app B S hS hZ₁ hZ₂ α Q b).symm

/-- **A locally surjective morphism of direct-image algebras is locally surjective on the chart
modules.** -/
theorem exists_pushforwardAlgebraChartMap_val_app_eq_map {Z₁ Z₂ : Over X}
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁)
    (hα : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) α.right.hom)
    (Q : SmallEtale B S hS X.1)
    (b : chartSectionsRing B S hS Z₁.left ((smallBaseChange B S hS Z₁.hom hZ₁).obj Q)) :
    ∃ R : Sieve Q, R ∈ SmallEtale.topology B S hS X.1 Q ∧ ∀ ⦃W : SmallEtale B S hS X.1⦄
      (h : W ⟶ Q), R h → ∃ a, (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α).val.app (op W) a =
        (chartBaseChangeStructureModule B S hS Z₁.hom hZ₁).val.map h.op b := by
  refine ⟨Presheaf.imageSieve α.right.hom
    ((pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).inv.val.app (op Q) b),
    Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1) α.right.hom _, ?_⟩
  rintro W h ⟨a', ha'⟩
  refine ⟨(pushforwardAlgebraModuleIso B S hS Z₂ hZ₂).hom.val.app (op W) a', ?_⟩
  refine (congrArg (fun y => (pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom.val.app (op W)
      (α.right.hom.app (op W) y))
    (pushforwardAlgebraModuleIso_inv_hom_val_app B S hS Z₂ hZ₂ W a')).trans ?_
  refine (congrArg ((pushforwardAlgebraModuleIso B S hS Z₁ hZ₁).hom.val.app (op W)) ha').trans ?_
  refine (pushforwardAlgebraModuleIso_hom_val_app_map B S hS Z₁ hZ₁ h _).trans ?_
  exact congrArg ((chartBaseChangeStructureModule B S hS Z₁.hom hZ₁).val.map h.op)
    (pushforwardAlgebraModuleIso_hom_inv_val_app B S hS Z₁ hZ₁ Q b)

/-- **The image of the direct image of an ideal under a locally surjective morphism of
direct-image algebras is the direct image of an ideal.**  Let `Z₁ ⟶ X` be affine and `Z₂ ⟶ X`
representable, `α : π_{2,*} 𝒪_{Z₂} ⟶ π_{1,*} 𝒪_{Z₁}` a locally surjective morphism of
`𝒪_X`-algebras and `𝒥 ⊆ 𝒪_{Z₂}` a sheaf of ideals.  If the image of `π_{2,*} 𝒥` in
`π_{1,*} 𝒪_{Z₁}` is quasi-coherent, it is `π_{1,*} ℐ` for a quasi-coherent sheaf of ideals
`ℐ ⊆ 𝒪_{Z₁}`, of finite type when the image is. -/
theorem exists_ideal_pushforwardSubmodule_eq_image_pushforwardAlgebraChartMap
    {Z₁ Z₂ : Over X}
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom) (haff : IsAffineHom B S hS Z₁.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁)
    (hα : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1) α.right.hom)
    (J : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z₂.left.1 Z₂.left.2)).Submodule)
    (hM : (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      ((pushforwardSubmodule B S hS Z₂.hom hZ₂ _ J).ι ≫
        pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α)).toSheafOfModules.IsQuasicoherentOnSite) :
    ∃ I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z₁.left.1 Z₁.left.2)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite ∧
      (SheafOfModules.IsFiniteTypeOnSite
          ((Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
            ((pushforwardSubmodule B S hS Z₂.hom hZ₂ _ J).ι ≫
              pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α)).toSheafOfModules :
            Modules.{u, u} B S hS X.1 X.2) →
        SheafOfModules.IsFiniteTypeOnSite
          (I.toSheafOfModules : Modules.{u, u} B S hS Z₁.left.1 Z₁.left.2)) ∧
      pushforwardSubmodule B S hS Z₁.hom hZ₁ _ I =
        Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
          ((pushforwardSubmodule B S hS Z₂.hom hZ₂ _ J).ι ≫
            pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α) :=
  exists_ideal_pushforwardSubmodule_eq_imageSubmodule_of_isLocallySurjective
    (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α) J haff
    (pushforwardAlgebraChartMap_val_app_mul B S hS hZ₁ hZ₂ α)
    (exists_pushforwardAlgebraChartMap_val_app_eq_map B S hS hZ₁ hZ₂ α hα) hM

/-! ### Morphisms over `X`: pullback of functions along the base-changed charts -/

/-- **The comparison is the identification of sections of Stacks 03G8.**  On sections over a
chart `V`, `AlgebraicGeometry.Space.pushforwardAlgebraModuleIso` is
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`: both are the projection of the limit
defining the direct image to the base-changed chart `V ×_X Z`. -/
theorem pushforwardAlgebraModuleIso_hom_val_app_eq_sectionsIso (Z : Over X)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (a : (pushforwardAlgebra B S hS Z).right.obj.obj (op V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).hom.val.app (op V) a =
      (pushforwardAlgebraSectionsIso B S hS Z hZ V).hom a := by
  have := isContinuous_smallBaseChange B S hS Z.hom hZ
  refine (pushforwardAlgebraModuleIso_hom_val_app B S hS Z hZ V a).trans ?_
  refine Eq.trans ?_ ((Sheaf.hom_congr_app_apply
    (smallEtaleRingedToposHom_representableRing_forget B S hS Z.hom hZ
      (smallEtaleRingedTopos B S hS Z.left).O) (op V) a).trans
    (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS Z.hom hZ
      (structureSetSheaf B S hS Z.left) V a)).symm
  rfl

/-- The inverse comparison is the inverse identification of sections of Stacks 03G8. -/
private theorem pushforwardAlgebraModuleIso_inv_val_app_eq_sectionsIso
    (Z : Over X) (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1)
    (a : chartSectionsRing B S hS Z.left ((smallBaseChange B S hS Z.hom hZ).obj V)) :
    (pushforwardAlgebraModuleIso B S hS Z hZ).inv.val.app (op V) a =
      (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv a := by
  have h := pushforwardAlgebraModuleIso_hom_val_app_eq_sectionsIso B S hS Z hZ V
    ((pushforwardAlgebraSectionsIso B S hS Z hZ V).inv a)
  have h' : (pushforwardAlgebraSectionsIso B S hS Z hZ V).hom
      ((pushforwardAlgebraSectionsIso B S hS Z hZ V).inv a) = a :=
    ConcreteCategory.congr_hom (pushforwardAlgebraSectionsIso B S hS Z hZ V).inv_hom_id a
  exact pushforwardAlgebraModuleIso_hom_val_app_injective B S hS Z hZ V
    ((pushforwardAlgebraModuleIso_hom_inv_val_app B S hS Z hZ V a).trans (h.trans h').symm)

/-- **The direct-image algebra map of a morphism over `X` is, on the chart modules, pullback of
regular functions along the base-changed morphism** `Z₁ ×_X Q ⟶ Z₂ ×_X Q` of
`AlgebraicGeometry.Space.smallBaseChangeOverMap`. -/
theorem pushforwardAlgebraChartMap_pushforwardAlgebraMap_val_app {Z₁ Z₂ : Over X} (f : Z₁ ⟶ Z₂)
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom) (Q : SmallEtale B S hS X.1)
    (a : chartSectionsRing B S hS Z₂.left ((smallBaseChange B S hS Z₂.hom hZ₂).obj Q)) :
    (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ (pushforwardAlgebraMap B S hS f)).val.app (op Q) a =
      ((BigFppfOver.toScheme B S hS).map
        (smallBaseChangeOverMap B S hS f hZ₁ hZ₂ Q)).appTop.hom a := by
  refine (pushforwardAlgebraChartMap_val_app B S hS hZ₁ hZ₂ _ Q a).trans ?_
  refine (pushforwardAlgebraModuleIso_hom_val_app_eq_sectionsIso B S hS Z₁ hZ₁ Q
    _).trans ?_
  refine (congrArg (fun y => (pushforwardAlgebraSectionsIso B S hS Z₁ hZ₁ Q).hom
    ((pushforwardRingMap B S hS f).hom.app (op Q) y))
    (pushforwardAlgebraModuleIso_inv_val_app_eq_sectionsIso B S hS Z₂ hZ₂ Q
      a)).trans ?_
  have h := ConcreteCategory.congr_hom (pushforwardRingMap_app_eq B S hS f hZ₁ hZ₂ Q) a
  exact h

/-- **The direct-image algebra map of a morphism `f : Z₁ ⟶ Z₂` over `X` is pullback of regular
functions along any morphism of base-changed charts over `f`.**  For every étale chart `Q` of `X`
and every morphism `c : Z₁ ×_X Q ⟶ Z₂ ×_X Q` over `Q` covering `f`, the morphism of chart modules
is pullback of functions along `c`. -/
theorem pushforwardAlgebraChartMap_pushforwardAlgebraMap_val_app_eq_appTop {Z₁ Z₂ : Over X}
    (f : Z₁ ⟶ Z₂) (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom) (Q : SmallEtale B S hS X.1)
    (c : hZ₁.pullback Q.1.hom ⟶ hZ₂.pullback Q.1.hom)
    (hsnd : c ≫ hZ₂.snd Q.1.hom = hZ₁.snd Q.1.hom)
    (hfst : yoneda.map c ≫ hZ₂.fst Q.1.hom = hZ₁.fst Q.1.hom ≫ f.left.hom)
    (a : chartSectionsRing B S hS Z₂.left ((smallBaseChange B S hS Z₂.hom hZ₂).obj Q)) :
    (pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ (pushforwardAlgebraMap B S hS f)).val.app (op Q) a =
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom a := by
  rw [eq_smallBaseChangeOverMap B S hS f hZ₁ hZ₂ Q c hfst hsnd]
  exact pushforwardAlgebraChartMap_pushforwardAlgebraMap_val_app B S hS f hZ₁ hZ₂ Q a

/-! ### Diagrams of direct-image algebras on the chart modules -/

/-- The identity of a direct-image algebra is the identity on the chart module. -/
theorem pushforwardAlgebraChartMap_id {Z : Over X}
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) :
    pushforwardAlgebraChartMap B S hS hZ hZ (𝟙 (pushforwardAlgebra B S hS Z)) = 𝟙 _ := by
  have h : AlgebraSheaf.underlyingModuleMap (𝟙 (pushforwardAlgebra B S hS Z)) = 𝟙 _ :=
    AlgebraSheaf.underlyingModuleFunctor.{u, u}.map_id _
  rw [pushforwardAlgebraChartMap, h]
  simp

/-- Composition of direct-image algebra maps is composition on the chart modules. -/
theorem pushforwardAlgebraChartMap_comp {Z₀ Z₁ Z₂ : Over X}
    (hZ₀ : yoneda.relativelyRepresentable Z₀.hom.hom)
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁)
    (β : pushforwardAlgebra B S hS Z₁ ⟶ pushforwardAlgebra B S hS Z₀) :
    pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α ≫ pushforwardAlgebraChartMap B S hS hZ₀ hZ₁ β =
      pushforwardAlgebraChartMap B S hS hZ₀ hZ₂ (α ≫ β) := by
  have h : AlgebraSheaf.underlyingModuleMap (α ≫ β) =
      AlgebraSheaf.underlyingModuleMap α ≫ AlgebraSheaf.underlyingModuleMap β :=
    AlgebraSheaf.underlyingModuleFunctor.{u, u}.map_comp α β
  simp only [pushforwardAlgebraChartMap, h, Category.assoc, Iso.hom_inv_id_assoc]

/-- Composition of direct-image algebra maps: if `α ≫ β = γ`, the composite of the maps of chart
modules of `α` and `β` is the map of chart modules of `γ`. -/
theorem pushforwardAlgebraChartMap_comp_of_comp_eq {Z₀ Z₁ Z₂ : Over X}
    (hZ₀ : yoneda.relativelyRepresentable Z₀.hom.hom)
    (hZ₁ : yoneda.relativelyRepresentable Z₁.hom.hom)
    (hZ₂ : yoneda.relativelyRepresentable Z₂.hom.hom)
    (α : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₁)
    (β : pushforwardAlgebra B S hS Z₁ ⟶ pushforwardAlgebra B S hS Z₀)
    (γ : pushforwardAlgebra B S hS Z₂ ⟶ pushforwardAlgebra B S hS Z₀) (h : α ≫ β = γ) :
    pushforwardAlgebraChartMap B S hS hZ₁ hZ₂ α ≫ pushforwardAlgebraChartMap B S hS hZ₀ hZ₁ β =
      pushforwardAlgebraChartMap B S hS hZ₀ hZ₂ γ :=
  (pushforwardAlgebraChartMap_comp B S hS hZ₀ hZ₁ hZ₂ α β).trans
    (congrArg (pushforwardAlgebraChartMap B S hS hZ₀ hZ₂) h)

/-- **A diagram of spaces affine over `X`, read on the chart modules.**  For a diagram
`D : K ⥤ (AffineOver X)ᵒᵖ`, the diagram of chart modules `k ↦ π_{k,*} 𝒪_{Y_k}` whose maps are
the direct-image algebra maps conjugated by `AlgebraicGeometry.Space.pushforwardAlgebraModuleIso`
(`AlgebraicGeometry.Space.chartStructureModuleDiagram_map`). -/
def chartStructureModuleDiagram {K : Type w} [Category.{v} K]
    (D : K ⥤ (AffineOver B S hS X)ᵒᵖ) : K ⥤ Modules.{u, u} B S hS X.1 X.2 where
  obj k := chartBaseChangeStructureModule B S hS (D.obj k).unop.obj.hom
    (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom (D.obj k).unop.property)
  map {k l} f := pushforwardAlgebraChartMap B S hS (Z₁ := (D.obj l).unop.obj)
    (Z₂ := (D.obj k).unop.obj)
    (relativelyRepresentable_of_isAffineHom B S hS (D.obj l).unop.obj.hom (D.obj l).unop.property)
    (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom (D.obj k).unop.property)
    ((affinePushforwardAlgebraFunctor B S hS X).map (D.map f))
  map_id k := by
    have h : (affinePushforwardAlgebraFunctor B S hS X).map (D.map (𝟙 k)) =
        𝟙 (pushforwardAlgebra B S hS (D.obj k).unop.obj) := by
      rw [D.map_id]
      exact (affinePushforwardAlgebraFunctor B S hS X).map_id _
    exact (congrArg (pushforwardAlgebraChartMap B S hS (Z₁ := (D.obj k).unop.obj)
      (Z₂ := (D.obj k).unop.obj)
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)) h).trans
      (pushforwardAlgebraChartMap_id B S hS
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property))
  map_comp {k l m} f g := by
    have h : (affinePushforwardAlgebraFunctor B S hS X).map (D.map (f ≫ g)) =
        (affinePushforwardAlgebraFunctor B S hS X).map (D.map f) ≫
          (affinePushforwardAlgebraFunctor B S hS X).map (D.map g) := by
      rw [D.map_comp, CategoryTheory.Functor.map_comp]
    exact (congrArg (pushforwardAlgebraChartMap B S hS (Z₁ := (D.obj m).unop.obj)
      (Z₂ := (D.obj k).unop.obj)
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj m).unop.obj.hom
        (D.obj m).unop.property)
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)) h).trans
      (pushforwardAlgebraChartMap_comp B S hS (Z₀ := (D.obj m).unop.obj)
        (Z₁ := (D.obj l).unop.obj) (Z₂ := (D.obj k).unop.obj)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj m).unop.obj.hom
        (D.obj m).unop.property)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj l).unop.obj.hom
        (D.obj l).unop.property)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
        ((affinePushforwardAlgebraFunctor B S hS X).map (D.map f))
        ((affinePushforwardAlgebraFunctor B S hS X).map (D.map g))).symm

/-- The maps of the chart diagram are the direct-image algebra maps read on the chart modules. -/
theorem chartStructureModuleDiagram_map {K : Type w} [Category.{v} K]
    (D : K ⥤ (AffineOver B S hS X)ᵒᵖ) {k l : K} (f : k ⟶ l) :
    (chartStructureModuleDiagram B S hS D).map f =
      pushforwardAlgebraChartMap B S hS (Z₁ := (D.obj l).unop.obj) (Z₂ := (D.obj k).unop.obj)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj l).unop.obj.hom
        (D.obj l).unop.property)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
        ((affinePushforwardAlgebraFunctor B S hS X).map (D.map f)) := by
  delta chartStructureModuleDiagram
  rfl

/-- **The cocone of chart modules of a cocone of spaces affine over `X`.**  Its point is the
chart module of the cocone point, and its legs are the direct-image algebra maps of the legs read
on the chart modules (`AlgebraicGeometry.Space.chartStructureModuleCocone_ι_app`). -/
def chartStructureModuleCocone {K : Type w} [Category.{v} K] {D : K ⥤ (AffineOver B S hS X)ᵒᵖ}
    (c : Cocone D) : Cocone (chartStructureModuleDiagram B S hS D) where
  pt := chartBaseChangeStructureModule B S hS c.pt.unop.obj.hom
    (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)
  ι :=
    { app k := pushforwardAlgebraChartMap B S hS (Z₁ := c.pt.unop.obj)
        (Z₂ := (D.obj k).unop.obj)
        (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
        ((affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app k))
      naturality k l f := by
        have h : (affinePushforwardAlgebraFunctor B S hS X).map (D.map f) ≫
            (affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app l) =
            (affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app k) :=
          ((affinePushforwardAlgebraFunctor B S hS X).map_comp _ _).symm.trans
            (congrArg (affinePushforwardAlgebraFunctor B S hS X).map (c.w f))
        refine Eq.trans ?_ (Category.comp_id _).symm
        rw [chartStructureModuleDiagram_map]
        exact pushforwardAlgebraChartMap_comp_of_comp_eq B S hS (Z₀ := c.pt.unop.obj)
          (Z₁ := (D.obj l).unop.obj) (Z₂ := (D.obj k).unop.obj)
          (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)
          (relativelyRepresentable_of_isAffineHom B S hS (D.obj l).unop.obj.hom
        (D.obj l).unop.property)
          (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
          ((affinePushforwardAlgebraFunctor B S hS X).map (D.map f))
          ((affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app l))
          ((affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app k)) h }

/-- The legs of the cocone of chart modules are the direct-image algebra maps of the legs read on
the chart modules. -/
theorem chartStructureModuleCocone_ι_app {K : Type w} [Category.{v} K]
    {D : K ⥤ (AffineOver B S hS X)ᵒᵖ} (c : Cocone D) (k : K) :
    (chartStructureModuleCocone B S hS c).ι.app k =
      pushforwardAlgebraChartMap B S hS (Z₁ := c.pt.unop.obj) (Z₂ := (D.obj k).unop.obj)
        (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)
        (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)
        ((affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app k)) := by
  delta chartStructureModuleCocone
  rfl

/-- The comparison of the diagram of underlying modules with the diagram of chart modules. -/
private def underlyingModuleDiagramChartIso {K : Type w} [Category.{v} K]
    (D : K ⥤ (AffineOver B S hS X)ᵒᵖ) :
    D ⋙ affinePushforwardAlgebraFunctor B S hS X ⋙ AlgebraSheaf.underlyingModuleFunctor.{u, u} ≅
      chartStructureModuleDiagram B S hS D :=
  NatIso.ofComponents (fun k => pushforwardAlgebraModuleIso B S hS (D.obj k).unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)) (fun {k l} f => by
    rw [chartStructureModuleDiagram_map]
    change _ = _ ≫ (pushforwardAlgebraModuleIso B S hS (D.obj k).unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)).inv ≫ _
    exact (Iso.hom_inv_id_assoc (pushforwardAlgebraModuleIso B S hS (D.obj k).unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)) _).symm)

/-- **A colimit of direct-image algebras is a colimit of chart modules.**  For a filtered diagram
`D` of spaces affine over `X` and a cocone `c` whose image under the direct-image functor of
Stacks 081V is a colimit of quasi-coherent `𝒪_X`-algebras, the cocone of chart modules is a
colimit of `𝒪_X`-modules. -/
theorem nonempty_isColimit_chartStructureModuleCocone {K : Type u} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ (AffineOver B S hS X)ᵒᵖ} {c : Cocone D}
    (hc : IsColimit ((quasicoherentPushforwardAlgebraFunctor B S hS X).mapCocone c)) :
    Nonempty (IsColimit (chartStructureModuleCocone B S hS c)) := by
  obtain ⟨hc'⟩ := nonempty_isColimit_underlyingModule_of_isColimit hc
  have hc'' : IsColimit ((affinePushforwardAlgebraFunctor B S hS X ⋙
      AlgebraSheaf.underlyingModuleFunctor.{u, u}).mapCocone c) := hc'
  have h1 := (IsColimit.precomposeInvEquiv (underlyingModuleDiagramChartIso B S hS D) _).symm hc''
  refine ⟨IsColimit.ofIsoColimit h1 (Cocone.ext (pushforwardAlgebraModuleIso B S hS c.pt.unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)) fun k => ?_)⟩
  rw [chartStructureModuleCocone_ι_app]
  exact Category.assoc (pushforwardAlgebraModuleIso B S hS (D.obj k).unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (D.obj k).unop.obj.hom
        (D.obj k).unop.property)).inv
    (AlgebraSheaf.underlyingModuleMap ((affinePushforwardAlgebraFunctor B S hS X).map (c.ι.app k)))
    (pushforwardAlgebraModuleIso B S hS c.pt.unop.obj
      (relativelyRepresentable_of_isAffineHom B S hS (c.pt).unop.obj.hom
        (c.pt).unop.property)).hom

end AlgebraicGeometry.Space

end
