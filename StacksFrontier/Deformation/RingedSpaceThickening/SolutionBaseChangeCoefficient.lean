module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChangeIdealMap
public import StacksFrontier.Deformation.RingedSpaceThickening.SchemeDeformationExtClassNaturality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushing a square-zero extension out along a map of coefficient modules

Let `g : (X, 𝒪_X) ⟶ (T, 𝒪_T)` be a morphism of ringed spaces and
`0 ⟶ 𝒢₁ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` a square-zero extension of `g⁻¹𝒪_T`-algebras. For a map
`ν : 𝒢₁ ⟶ 𝒢₂` of `𝒪_X`-modules the square-zero pushout `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂ = (𝒪_{X'} ⋉ 𝒢₂)/J` of
`Stacks.Sites.SqZeroPushout` is a square-zero extension `0 ⟶ 𝒢₂ ⟶ 𝒪'' ⟶ 𝒪_X ⟶ 0` of
`g⁻¹𝒪_T`-algebras, and the inclusion `𝒪_{X'} ⟶ 𝒪''` is a morphism of extensions inducing `ν`
on ideals. Its class is the class of `𝒪_{X'}` pushed forward along `ν`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.coeffPushoutData`: the
  map `ν ∘ (ideal of 𝒪_{X'})`, as square-zero pushout data.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.pushCoeff`: the extension
  `𝒪''` by `𝒢₂`.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.pushCoeffInl`: the
  morphism of extensions `𝒪_{X'} ⟶ 𝒪''`.

## Main results

* `AlgebraSquareZeroExtension.pushCoeff_ideal_pushCoeffInl`: the morphism induces `ν` on ideals.
* `AlgebraSquareZeroExtension.pushCoeff_idealBijective`: the ideal of `𝒪''` is identified with
  `𝒢₂` bijectively.
* `AlgebraSquareZeroExtension.extClass_pushCoeff`: the class of `𝒪''` is the class of `𝒪_{X'}`
  followed by `ν`.

## References

* [Stacks Project, Tag 08UA](https://stacks.math.columbia.edu/tag/08UA)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq
  presentationScalar)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

namespace AlgebraSquareZeroExtension

variable {X T : RingedSpace.{u, u}} {g : X ⟶ T}
  {G₁ G₂ : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- The map `ν ∘ (ideal of 𝒪_{X'})` from the kernel of the reduction of `𝒪_{X'}` to `𝒢₂`, as
square-zero pushout data. -/
@[ega "0 18.2.8" "Annihilation of L′"]
def coeffPushoutData (P : AlgebraSquareZeroExtension g G₁) (ν : G₁ ⟶ G₂) :
    PushoutData.{u} P.reduction (restrictAlong.{u} P.reduction G₂) where
  app U := (ν.val.app U).hom.toAddMonoidHom.comp (P.ideal.app U)
  app_smul U r y := by
    change ν.val.app U (P.ideal.app U (r • y)) = presentationScalar P.reduction U r •
      ν.val.app U (P.ideal.app U y)
    rw [P.ideal.app_smul]
    exact (ν.val.app U).hom.map_smul _ _
  app_map {U V} i y := by
    change ν.val.app V (P.ideal.app V _) = G₂.val.map i (ν.val.app U (P.ideal.app U y))
    rw [P.ideal.app_map]
    exact congrArg (fun k => k.hom (P.ideal.app U y)) (ν.val.naturality i)
  smul_eq_zero U y m := by
    have h0 : presentationScalar P.reduction U (y : ↥(P.sheaf.obj.obj U)) = 0 := y.2
    have key : ∀ n : ↥(G₂.val.obj U),
        presentationScalar P.reduction U (y : ↥(P.sheaf.obj.obj U)) • n = 0 := by
      intro n
      rw [h0, zero_smul]
    exact key m

variable (P : AlgebraSquareZeroExtension g G₁) (ν : G₁ ⟶ G₂)

/-- **The square-zero extension `𝒪_{X'} ⊔_{𝒢₁} 𝒢₂` of `𝒪_X` by `𝒢₂`**: the square-zero pushout
of `𝒪_{X'}` along `ν`, a `g⁻¹𝒪_T`-algebra through `𝒪_{X'}`. -/
@[ega "0 18.2.8"]
def pushCoeff : AlgebraSquareZeroExtension g G₂ where
  sheaf := pushoutSheaf.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν)
  base := P.base ≫ pushoutInl.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
      (coeffPushoutData P ν)
  reduction := pushoutProj.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
      (coeffPushoutData P ν)
  base_comp_reduction := (Category.assoc _ _ _).trans
      ((congrArg (P.base ≫ ·) (pushoutInl_comp_pushoutProj.{u} _ _ _)).trans P.base_comp_reduction)
  reduction_surjective :=
      haveI := P.reduction_surjective
      isLocallySurjective_pushoutProj.{u} _ _ _
  ideal := Stacks.Sites.SqZeroPushout.idealRestriction.{u} P.reduction G₂ (coeffPushoutData P ν)

/-- The inclusion `𝒪_{X'} ⟶ 𝒪_{X'} ⊔_{𝒢₁} 𝒢₂`, `r ↦ [(r, 0)]`. -/
abbrev pushCoeffInl : P.sheaf ⟶ (pushCoeff P ν).sheaf :=
  pushoutInl.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν)

/-- The inclusion is compatible with the algebra structures. -/
theorem base_comp_pushCoeffInl : P.base ≫ pushCoeffInl P ν = (pushCoeff P ν).base :=
  rfl

/-- The inclusion is compatible with the reductions. -/
theorem pushCoeffInl_comp_reduction :
    pushCoeffInl P ν ≫ (pushCoeff P ν).reduction = P.reduction :=
  pushoutInl_comp_pushoutProj.{u} _ _ _

/-- **The inclusion induces `ν` on the square-zero ideals.** -/
theorem pushCoeff_ideal_pushCoeffInl (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal P.reduction.hom V)) :
    (pushCoeff P ν).ideal.app V ⟨(pushCoeffInl P ν).hom.app V y,
        kernelIdeal_le_comap P.reduction.hom (pushCoeff P ν).reduction.hom
          (pushCoeffInl P ν).hom (hom_of_comp_eq (pushCoeffInl_comp_reduction P ν)) V y.2⟩ =
      ν.val.app V (P.ideal.app V y) :=
  idealRestriction_app_eq_of_val.{u} P.reduction G₂ (coeffPushoutData P ν) V _ _
    (pushoutInl_app_kernel.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
      (coeffPushoutData P ν) V y)

/-- A local section of the ideal of the pushout is the image of its value in `𝒢₂`. -/
theorem pushCoeff_ideal_app_eq (U : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal (pushCoeff P ν).reduction.hom U)) :
    (y : (pushCoeff P ν).sheaf.obj.obj U) =
      pushoutInr.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν) U
        ((pushCoeff P ν).ideal.app U y) := by
  have := P.reduction_surjective
  obtain ⟨n, hn⟩ := (pushoutProj_app_eq_zero_iff.{u} P.reduction
    (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν) U y.1).1 y.2
  have h : (pushCoeff P ν).ideal.app U y = n :=
    idealRestriction_app_eq_of_val.{u} P.reduction G₂ (coeffPushoutData P ν) U y n hn.symm
  rw [h]
  exact hn.symm

/-- **The pushout identifies its ideal with `𝒢₂` bijectively.** -/
@[ega "0 18.2.8" "Exactness 0→L′→H→B"]
theorem pushCoeff_idealBijective : (pushCoeff P ν).IdealBijective := by
  intro U
  refine ⟨fun y₁ y₂ h => Subtype.ext ?_, fun n => ?_⟩
  · rw [pushCoeff_ideal_app_eq P ν U y₁, pushCoeff_ideal_app_eq P ν U y₂, h]
  · exact ⟨⟨pushoutInr.{u} P.reduction (restrictAlong.{u} P.reduction G₂) (coeffPushoutData P ν)
        U n, pushoutProj_pushoutInr.{u} P.reduction (restrictAlong.{u} P.reduction G₂)
          (coeffPushoutData P ν) U n⟩,
      idealRestriction_app_pushoutInr.{u} P.reduction G₂ (coeffPushoutData P ν) U n⟩

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The class of the pushout is the class of `𝒪_{X'}` pushed forward along `ν`.** -/
theorem extClass_pushCoeff :
    P.toPresented.extClass ≫ ((DerivedCategory.singleFunctor _ 0).map ν)⟦(1 : ℤ)⟧' =
      (pushCoeff P ν).toPresented.extClass :=
  extClass_comp_eq_extClass_of_hom P (pushCoeff P ν) ν (pushCoeffInl P ν)
    (base_comp_pushCoeffInl P ν) (pushCoeffInl_comp_reduction P ν)
    (pushCoeff_ideal_pushCoeffInl P ν)

end Derived

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
