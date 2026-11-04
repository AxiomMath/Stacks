module

public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.Deformation.RingedSpaceThickening.ExistenceObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.LiftingObstruction
import StacksCore.Tactic.StacksAttribute

/-!
# Pushing an extension out along a morphism of first order thickenings

Let `(X, 𝒪_X)` be a ringed space with two first order thickenings `i₁ : X ⟶ X'₁` and
`i₂ : X ⟶ X'₂`, with ideals `ℐ₁` and `ℐ₂`, and let `h : X'₁ ⟶ X'₂` be a morphism of thickenings
over `(X, 𝒪_X)`, so `i₁ ≫ h = i₂`. The comorphism `h^♯ : 𝒪_{X'₂} ⟶ 𝒪_{X'₁}` carries `ℐ₂` into
`ℐ₁` and so induces an `𝒪_X`-module map `ℐ₂ ⟶ ℐ₁`.

Fix an `𝒪_X`-module `ℱ` and pairs `(𝒦₁, c₁)`, `(𝒦₂, c₂)` with `cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ`,
together with a map `k : 𝒦₂ ⟶ 𝒦₁` making the square

    ℐ₂ ⊗ ℱ --c₂--> 𝒦₂
       |            |
       |            k
       v            v
    ℐ₁ ⊗ ℱ --c₁--> 𝒦₁

commute, the left vertical map being induced by `ℐ₂ ⟶ ℐ₁`. Given an extension
`0 ⟶ i₂_* 𝒦₂ ⟶ ℱ'₂ ⟶ i₂_* ℱ ⟶ 0` as in Tag 08L4 whose canonical map is `c₂`, this file forms
the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`, which sits in a morphism of short exact sequences

    0 ⟶ i₂_* 𝒦₂ ⟶ ℱ'₂ ⟶ i₂_* ℱ ⟶ 0
            |         |        ‖
            k         |        ‖
            v         v        ‖
    0 ⟶ i₂_* 𝒦₁ ⟶ ℱ'   ⟶ i₂_* ℱ ⟶ 0

that is the identity on `ℱ`, and whose canonical map of Tag 08L4 is `c₂ ≫ k`, hence — by the
commuting square above — the map prescribed by `c₁` and `ℐ₂ ⟶ ℐ₁`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.thickeningIdealMap`: the `𝒪_X`-linear map
  `ℐ₂ ⟶ ℐ₁` induced by the comorphism of a morphism of thickenings over `(X, 𝒪_X)`.
* `AlgebraicGeometry.RingedSpaceThickening.pushoutExtension`: the extension as in Tag 08L4
  obtained by pushing an extension out along a map `k : 𝒦₂ ⟶ 𝒦₁` of its kernel module.
* `AlgebraicGeometry.RingedSpaceThickening.pushoutExtensionInl`: the injection of the given
  extension into its pushout.
* `AlgebraicGeometry.RingedSpaceThickening.pushoutCompatibleMap`: the resulting map of
  extensions, as the data of Tag 08L5 with `𝟙 ℱ` on the quotient module and `k` on the kernel
  module.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isPushout_pushoutExtension`: the middle term of the
  pushout extension is the pushout of the middle term of the given extension and of `i₂_* 𝒦₁`
  over `i₂_* 𝒦₂`.
* `AlgebraicGeometry.RingedSpaceThickening.firstOrderExtensionAction_pushoutExtension`: the
  canonical map of Tag 08L4 of the pushout extension is `c₂ ≫ k`.
* `AlgebraicGeometry.RingedSpaceThickening`
  `.firstOrderExtensionAction_pushoutExtension_eq_of_compatible`: consequently, when the square
  relating `c₁` and `c₂` commutes, the canonical map of the pushout extension is the one
  prescribed by `c₁` through `ℐ₂ ⟶ ℐ₁`.

## Implementation notes

The pushout of a short exact sequence along a map of its kernel object is not built here: it is
`CategoryTheory.Abelian.pushoutShortComplex` of
`StacksFrontier.Deformation.RingedSpaceThickening.ExistenceObstruction`, which takes the pushout of
`CategoryTheory.Limits.pushout` and so gets its universal property from
`CategoryTheory.Limits.IsPushout.of_hasPushout`. Everything below is stated through that
interface — `CategoryTheory.Abelian.pushoutShortComplex_shortExact`,
`CategoryTheory.Abelian.f_comp_pushout_inl`,
`CategoryTheory.Abelian.inl_pushoutShortComplex_g` and
`CategoryTheory.Abelian.isPushout_pushoutShortComplex`.

The map `ℐ₂ ⟶ ℐ₁` is the conormal sheaf map
`Stacks.ClosedImmersion.conormalSheafMap` of the commuting square `i₁ ≫ h = 𝟙 X ≫ i₂`, read
through `RingedSpaceModuleAdjunction.modulePullbackId`; no thickening hypothesis is
needed to form it, and it is the `f = 𝟙 X` case of
`AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.baseToSourceIdeal` with the
hypotheses dropped.

## References

* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X₁ X₂ : RingedSpace.{u, u}}

/-- A morphism of thickenings of `(X, 𝒪_X)`, `i₁ ≫ h = i₂`, read as the commutative square
`i₁ ≫ h = 𝟙 X ≫ i₂` of ringed spaces. -/
theorem comp_eq_id_comp {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {h : X₁ ⟶ X₂} (comm : i₁ ≫ h = i₂) :
    i₁ ≫ h = 𝟙 X ≫ i₂ := by
  rw [Category.id_comp]; exact comm

/-- The `𝒪_X`-module map `ℐ₂ ⟶ ℐ₁` induced by a morphism `h : X'₁ ⟶ X'₂` of thickenings of
`(X, 𝒪_X)`: the comorphism `h^♯` carries `ℐ₂` into `ℐ₁`, and the resulting map is read on `X` by
pullback along `i₁`.

It is the conormal sheaf map of the commuting square `i₁ ≫ h = 𝟙 X ≫ i₂`, whose
characterisation is `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`; no thickening
hypothesis is needed to form it. -/
noncomputable def thickeningIdealMap (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) :
    idealSheafPullback i₂ ⟶ idealSheafPullback i₁ :=
  (RingedSpaceModuleAdjunction.modulePullbackId X).inv.app (idealSheafPullback i₂) ≫
    Stacks.ClosedImmersion.conormalSheafMap (comp_eq_id_comp comm)

/-- The map `ℐ₂ ⟶ ℐ₁` is the one induced by the comorphism of `h`: after mapping both ideals
into `i₁^* 𝒪_{X'₁}` it becomes the pullback of the inclusion `ℐ₂ ⟶ 𝒪_{X'₂}` followed by the
transpose `h^* 𝒪_{X'₂} ⟶ 𝒪_{X'₁}` of the comorphism. -/
theorem thickeningIdealMap_comp_pullback_idealSheafι (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) :
    thickeningIdealMap i₁ i₂ h comm ≫
        (modulePullback i₁).map (Stacks.ClosedImmersion.idealSheafι i₁) =
      (RingedSpaceModuleAdjunction.modulePullbackId X).inv.app
          (idealSheafPullback i₂) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (comp_eq_id_comp comm)
            (Stacks.ClosedImmersion.idealSheaf i₂)).hom ≫
          (modulePullback i₁).map ((modulePullback h).map
            (Stacks.ClosedImmersion.idealSheafι i₂) ≫
              RingedSpaceModuleAdjunction.modulePullbackUnitToUnit h) := by
  rw [thickeningIdealMap]
  exact (Category.assoc _ _ _).trans (congrArg
    (fun z => (RingedSpaceModuleAdjunction.modulePullbackId X).inv.app (idealSheafPullback i₂) ≫ z)
    (Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι (comp_eq_id_comp comm)))

/-- The extension as in Tag 08L4 obtained from `0 ⟶ i_* 𝒦₂ ⟶ ℱ' ⟶ i_* ℱ ⟶ 0` by pushing its
middle term out along a map `k : 𝒦₂ ⟶ 𝒦₁` of kernel modules: the short exact sequence
`0 ⟶ i_* 𝒦₁ ⟶ ℱ' ⊔_{i_* 𝒦₂} i_* 𝒦₁ ⟶ i_* ℱ ⟶ 0`. -/
noncomputable def pushoutExtension (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X))
    (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₁) 0 :=
  Abelian.shortExactYonedaExtension
    (Abelian.pushoutShortComplex_shortExact (Abelian.YonedaExtension.shortExact E)
      ((modulePushforward i).map k))

/-- The injection of the middle term of an extension into the middle term of its pushout along
`k : 𝒦₂ ⟶ 𝒦₁`. -/
noncomputable def pushoutExtensionInl (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    E.Z.left ⟶ (pushoutExtension i F K₁ K₂ k E).Z.left :=
  pushout.inl E.f ((modulePushforward i).map k)

/-- The defining square of the pushout: the inclusion of `𝒦₂` followed by the injection is `k`
followed by the inclusion of `𝒦₁`. -/
theorem f_comp_pushoutExtensionInl (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    E.f ≫ pushoutExtensionInl i F K₁ K₂ k E =
      (modulePushforward i).map k ≫ (pushoutExtension i F K₁ K₂ k E).f :=
  pushout.condition

/-- The injection into the pushout is compatible with the surjections onto `ℱ`. -/
theorem pushoutExtensionInl_comp_g (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    pushoutExtensionInl i F K₁ K₂ k E ≫ (pushoutExtension i F K₁ K₂ k E).g = E.g :=
  Abelian.inl_pushoutShortComplex_g
    (ShortComplex.mk E.f E.g (Abelian.YonedaExtension.comp_eq_zero E))
    ((modulePushforward i).map k)

/-- The data of Tag 08L5 relating an extension to its pushout along `k : 𝒦₂ ⟶ 𝒦₁`: the same
thickening and quotient module `ℱ`, the two kernel modules `𝒦₂` and `𝒦₁`, the identity on `ℱ`
and `k` on the kernels. -/
noncomputable def pushoutExtensionPair (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (hi : IsFirstOrderThickening i)
    (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    ExtensionPair.{u} where
  X := X
  X' := X₂
  i := i
  firstOrder := hi
  F := F
  K := K₂
  G := F
  L := K₁
  firstExtension := E
  secondExtension := pushoutExtension i F K₁ K₂ k E
  quotientMap := 𝟙 F
  kernelMap := k

/-- The map from an extension to its pushout, as a compatible map of Tag 08L5: it induces `k`
on the kernel modules and the identity on the quotient module `ℱ`. -/
noncomputable def pushoutCompatibleMap (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (hi : IsFirstOrderThickening i)
    (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    ExtensionPair.CompatibleMap (pushoutExtensionPair i F K₁ K₂ hi k E) where
  hom := pushout.inl E.f ((modulePushforward i).map k)
  kernel_commutes := Abelian.f_comp_pushout_inl
    (ShortComplex.mk E.f E.g (Abelian.YonedaExtension.comp_eq_zero E))
    ((modulePushforward i).map k)
  quotient_commutes :=
    (Abelian.inl_pushoutShortComplex_g
        (ShortComplex.mk E.f E.g (Abelian.YonedaExtension.comp_eq_zero E))
        ((modulePushforward i).map k)).trans
      (show E.g = E.g ≫ (modulePushforward i).map (𝟙 F) by
        rw [(modulePushforward i).map_id, Category.comp_id])

/-- **The pushout square.** The middle term of the pushout extension is the pushout of the
middle term of the given extension and of `i_* 𝒦₁` over `i_* 𝒦₂`. -/
theorem isPushout_pushoutExtension (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (hi : IsFirstOrderThickening i)
    (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    IsPushout E.f ((modulePushforward i).map k)
      (pushoutCompatibleMap i F K₁ K₂ hi k E).hom (pushoutExtension i F K₁ K₂ k E).f :=
  Abelian.isPushout_pushoutShortComplex
    (ShortComplex.mk E.f E.g (Abelian.YonedaExtension.comp_eq_zero E))
    ((modulePushforward i).map k)

/-- The canonical map of Tag 08L4 of the pushout extension is the canonical map of the given
extension followed by `k`. This is part (1) of Tag 08L5 for the map of extensions
`pushoutCompatibleMap`, which induces `𝟙 ℱ` and `k`. -/
theorem firstOrderExtensionAction_pushoutExtension (i : X ⟶ X₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (hi : IsFirstOrderThickening i)
    (k : K₂ ⟶ K₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K₂) 0) :
    (firstOrderExtensionAction i F K₁ hi (pushoutExtension i F K₁ K₂ k E)).val =
      (firstOrderExtensionAction i F K₂ hi E).val ≫ k := by
  have h : (firstOrderExtensionAction i F K₂ hi E).val ≫ k =
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
            (((𝟙 (idealSheafPullback i)), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫
        (firstOrderExtensionAction i F K₁ hi (pushoutExtension i F K₁ K₂ k E)).val :=
    ExtensionPair.extensionAction_naturality (pushoutExtensionPair i F K₁ K₂ hi k E)
      (pushoutCompatibleMap i F K₁ K₂ hi k E)
  exact (h.trans ((congrArg
    (fun z => z ≫ (firstOrderExtensionAction i F K₁ hi (pushoutExtension i F K₁ K₂ k E)).val)
    (tensorSheafMap_id_id X (idealSheafPullback i) F)).trans (Category.id_comp _))).symm

/-- The canonical map of the pushout extension is the one prescribed by `c₁` and the induced map
`ℐ₂ ⟶ ℐ₁`, as soon as the square relating `c₁` and `c₂` commutes. -/
theorem firstOrderExtensionAction_pushoutExtension_eq_of_compatible
    (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (hi₂ : IsFirstOrderThickening i₂) (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X))
    (c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i₁))).obj (F)) ⟶ K₁)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i₂))).obj (F)) ⟶ K₂) (k : K₂ ⟶ K₁)
    (compatible :
      c₂ ≫ k = ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((thickeningIdealMap i₁ i₂ h comm), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₁)
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0)
    (hE : (firstOrderExtensionAction i₂ F K₂ hi₂ E).val = c₂) :
    (firstOrderExtensionAction i₂ F K₁ hi₂ (pushoutExtension i₂ F K₁ K₂ k E)).val =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
          (((thickeningIdealMap i₁ i₂ h comm), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₁ := by
  rw [firstOrderExtensionAction_pushoutExtension, hE, compatible]

end AlgebraicGeometry.RingedSpaceThickening

end
