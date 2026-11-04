module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChange
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesFibre
public import StacksFrontier.Deformation.ToposThickening.SquareZeroDerivedObstruction
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionNaiveExt
import StacksCore.Tactic.StacksAttribute

/-!
# The class of the base thickening (the element `ξ` of Stacks 0GQ9)

In the situation (08UF) of **Stacks 08UF** the base is a first order thickening
`t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` with ideal `𝒥 = Ker(t^♯)`. **Stacks 0GQ9** uses the
element `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` which the bijection of **Stacks 0GQ5**, applied to
`t` and the `𝒪_ℬ`-module `𝒥`, attaches to the extension `0 ⟶ 𝒥 ⟶ 𝒪_{ℬ'} ⟶ 𝒪_ℬ ⟶ 0`. This file
constructs `t`, `𝒥`, that extension and `ξ` from a problem
`S : RingedToposExtensionProblem X B`, whose base thickening is the pair
`(S.baseExtension, S.baseReduction)` on the site of `ℬ` (the underlying topoi of `ℬ` and `ℬ'` are
identified, as in the source).

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.baseThickening`: the morphism of
  ringed topoi `t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ), 𝒪_{ℬ'})`, the identity on topoi with structure map
  `t^♯ = S.baseReduction`.
* `.baseIdeal`: `𝒥 = Ker(t^♯)` as a sheaf of `𝒪_ℬ`-modules, and `.baseIdealInclusion`, its
  inclusion into `𝒪_{ℬ'}`.
* `.baseThickeningSolution`: `𝒪_{ℬ'}` as an extension of `t⁻¹𝒪_{ℬ'}`-algebras of `𝒪_ℬ` by `𝒥`,
  i.e. a solution of the problem `ofTrivialBase t 𝒥` of **Stacks 0GQ5**.
* `.baseThickeningClass`: the class `ξ` of that extension.

## Implementation notes

`𝒥` is `Deformation.ComplexLift.squareZeroIdeal`: the kernel of `t^♯` is a sheaf of
`𝒪_{ℬ'}`-modules killed by the kernel, so it descends to `𝒪_ℬ`. That the inclusion identifies `𝒥`
with the whole kernel, section by section, is proved here
(`existsUnique_baseIdealInclusion`). The derived category is
`CategoryTheory.HasDerivedCategory.standard`, installed locally at high priority, as in the
modules of the derived pullback this class is fed into.

## References

* [Stacks Project, Tag 0GQ9](https://stacks.math.columbia.edu/tag/0GQ9)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X B : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (S : RingedToposExtensionProblem X B)

/-- The first order thickening `t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ), 𝒪_{ℬ'})` of the base. -/
def baseThickening : RingedToposHom B S.thickenedBase :=
  RingedToposHom.coefficientMorphism B.J S.baseReduction

/-- The underlying morphism of topoi of `t` is the identity of `Sh(ℬ)`. -/
theorem baseThickening_toToposHom :
    S.baseThickening.toToposHom = MorphismOfTopoi.id (Sheaf B.J (Type u)) := rfl

/-- The inverse-image form of the structure map of `t` is `t^♯ = S.baseReduction`, read through
the identification of the inverse image along the identity with the identity. -/
theorem baseThickening_fSharpInverseImage :
    S.baseThickening.fSharpInverseImage =
      (pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension ≫ S.baseReduction :=
  RingedToposHom.coefficientMorphism_fSharpInverseImage B.J S.baseReduction

/-- The ideal of the base thickening has square zero, section by section. -/
theorem baseReduction_mul_eq_zero (U : B.Cᵒᵖ) (a b : S.baseExtension.obj.obj U)
    (ha : S.baseReduction.hom.app U a = 0) (hb : S.baseReduction.hom.app U b = 0) :
    a * b = 0 := by
  have h : a * b ∈ RingHom.ker (S.baseReduction.hom.app U).hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rwa [S.baseSquareZero U] at h

variable [HasSheafify B.J AddCommGrpCat.{u}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `𝒥 = Ker(t^♯)` as a sheaf of `𝒪_ℬ`-modules. -/
def baseIdeal : SheafOfModules.{u}
    ((sheafCompose B.J (forget₂ CommRingCat.{u} RingCat.{u})).obj B.O) :=
  Deformation.ComplexLift.squareZeroIdeal S.baseReduction S.baseLocallySurjective
    S.baseReduction_mul_eq_zero

/-- The inclusion `𝒥 ⟶ 𝒪_{ℬ'}`. -/
def baseIdealInclusion :
    (SheafOfModules.restrictScalars
      ((sheafCompose B.J (forget₂ CommRingCat.{u} RingCat.{u})).map S.baseReduction)).obj
        S.baseIdeal ⟶
      SheafOfModules.unit
        ((sheafCompose B.J (forget₂ CommRingCat.{u} RingCat.{u})).obj S.baseExtension) :=
  Deformation.ComplexLift.squareZeroIdealInclusion S.baseReduction S.baseLocallySurjective
    S.baseReduction_mul_eq_zero

/-- On sections, the inclusion `𝒥 ⟶ 𝒪_{ℬ'}` is the inclusion of the kernel of `t^♯`. -/
theorem baseIdealInclusion_val_app (U : B.Cᵒᵖ) (a : S.baseIdeal.val.obj U) :
    S.baseIdealInclusion.val.app U a =
      ((Deformation.ComplexLift.restrictSquareZeroIdealIso S.baseReduction
        S.baseLocallySurjective S.baseReduction_mul_eq_zero).hom.val.app U a).val :=
  rfl

/-- The inclusion `𝒥 ⟶ 𝒪_{ℬ'}` lands in the kernel of `t^♯`. -/
theorem baseReduction_baseIdealInclusion (U : B.Cᵒᵖ) (a : S.baseIdeal.val.obj U) :
    S.baseReduction.hom.app U
      (show S.baseExtension.obj.obj U from S.baseIdealInclusion.val.app U a) = 0 := by
  rw [S.baseIdealInclusion_val_app]
  have h := (SheafOfModules.mem_kerSubmodule _ U _).1
    ((Deformation.ComplexLift.restrictSquareZeroIdealIso S.baseReduction
        S.baseLocallySurjective S.baseReduction_mul_eq_zero).hom.val.app U a).2
  exact (Deformation.ComplexLift.structureModuleMap_val_app S.baseReduction U _).symm.trans h

/-- The inclusion `𝒥 ⟶ 𝒪_{ℬ'}` identifies `𝒥` with the kernel of `t^♯`, section by section. -/
theorem existsUnique_baseIdealInclusion (U : B.Cᵒᵖ) (a : S.baseExtension.obj.obj U)
    (ha : S.baseReduction.hom.app U a = 0) :
    ∃! g : S.baseIdeal.val.obj U,
      (show S.baseExtension.obj.obj U from S.baseIdealInclusion.val.app U g) = a := by
  let e := (SheafOfModules.evaluation _ U).mapIso
    (Deformation.ComplexLift.restrictSquareZeroIdealIso S.baseReduction
      S.baseLocallySurjective S.baseReduction_mul_eq_zero)
  have hmem : a ∈ (SheafOfModules.kerSubmodule
      (Deformation.ComplexLift.structureModuleMap S.baseReduction)).obj U :=
    (SheafOfModules.mem_kerSubmodule
      (Deformation.ComplexLift.structureModuleMap S.baseReduction) U a).2
      ((Deformation.ComplexLift.structureModuleMap_val_app S.baseReduction U a).trans ha)
  refine ⟨e.inv ⟨a, hmem⟩, ?_, fun g hg => ?_⟩
  · exact congrArg Subtype.val (e.inv_hom_id_apply ⟨a, hmem⟩)
  · exact (e.hom_inv_id_apply g).symm.trans (congrArg e.inv (Subtype.ext hg :
      e.hom g = ⟨a, hmem⟩))

/-- **The extension `𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥`**, as an extension of `t⁻¹𝒪_{ℬ'}`-algebras: a
solution of the problem `ofTrivialBase t 𝒥` of **Stacks 0GQ5**. -/
def baseThickeningSolution :
    (ofTrivialBase S.baseThickening S.baseIdeal).CompatibleFirstOrderThickening where
  extension := S.baseExtension
  reduction := S.baseReduction
  locallySurjective := S.baseLocallySurjective
  squareZero := S.baseSquareZero
  baseMap := (pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension
  baseMap_reduction := by
    change _ = (inverseImageCommRingFunctor S.baseThickening.toToposHom).map
        (𝟙 S.baseExtension) ≫ S.baseThickening.fSharpInverseImage
    rw [CategoryTheory.Functor.map_id, Category.id_comp, S.baseThickening_fSharpInverseImage]
    rfl
  kernelInclusion := S.baseIdealInclusion
  kernelZero := S.baseReduction_baseIdealInclusion
  kernelUniversal := S.existsUnique_baseIdealInclusion
  baseMap_ideal := fun U a => by
    have h : IsIso (ofTrivialBase S.baseThickening S.baseIdeal).baseReduction := inferInstance
    rw [(ofTrivialBase S.baseThickening S.baseIdeal).idealInclusion_val_app_eq_zero h U a,
      (ofTrivialBase S.baseThickening S.baseIdeal).c_val_app_eq_zero h U a, map_zero]
    exact (map_zero _).symm

section Class

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The class `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` of the base thickening**: the element that
the bijection of **Stacks 0GQ5** for `t` and `𝒥` attaches to the extension `𝒪_{ℬ'}` of `𝒪_ℬ`
by `𝒥`. -/
def baseThickeningClass :
    Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u} B.J
      ((inverseImageCommRingFunctor S.baseThickening.toToposHom).obj S.baseExtension) B.O
      S.baseThickening.fSharpInverseImage S.baseIdeal 1 :=
  squareZeroExtensionClassesEquiv S.baseThickening S.baseIdeal
    (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) S.baseThickeningSolution)

end Class

end Deformation.ToposThickening.RingedToposExtensionProblem

end
