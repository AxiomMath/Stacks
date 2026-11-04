module

public import StacksFrontier.Deformation.AlgebraExtension.Basic
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem

/-!
# The extension problem over a base thickening presented as an algebra extension

Let `f : (Sh(C), 𝒪_X) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and let
`0 → ℳ → 𝒪' → 𝒪_D → 0` be a square-zero extension of sheaves of rings on `D`, the kernel
`ℳ` being identified with an `𝒪_D`-module (a `Deformation.AlgebraExtension`). Pulling the
extension back along `f` gives the lower row of a square-zero extension problem
(`Deformation.ToposThickening.RingedToposExtensionProblem`): the thickened base is `𝒪'`, its
reduction is `𝒪' → 𝒪_D`, and the inverse image of the base ideal is `f⁻¹ℳ`, a module over
`f⁻¹𝒪_D`, which is section by section exactly the kernel of `f⁻¹𝒪' → f⁻¹𝒪_D` because the inverse
image of sheaves of sets is left exact.

This is how the problem of the body of the proof of [Stacks Project, Tag 0D3X] is set up: the
base thickening `Y₀ ⊂ Spec(lim Rₙ)` is the extension of `𝒪_{Y₀}` by its conormal module.

## Main definitions

* `Deformation.ToposThickening.inverseImageExtensionIdeal`: `f⁻¹ℳ`, a module over `f⁻¹𝒪_D`.
* `Deformation.ToposThickening.inverseImageExtensionIdealIncl`: its inclusion into `f⁻¹𝒪'`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.ofBaseAlgebraExtension`: the problem
  with lower row the inverse image of the extension, for a given module `𝒢` and map `f⁻¹ℳ ⟶ 𝒢`.

## Main results

* `Deformation.AlgebraExtension.isPullback_kernelInclusion`: the kernel of an algebra extension,
  as a pullback square of sheaves of sets.
* `Deformation.ToposThickening.existsUnique_inverseImageExtensionIdeal_section`: `f⁻¹ℳ` is the
  kernel of `f⁻¹𝒪' → f⁻¹𝒪_D`, section by section.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPullback (pullbackModuleObj pullbackRingSheafMap
  pullbackModuleUnitIso isPullback_terminal_of_sections existsUnique_sections_of_isPullback
  sections_comp_eq_zero_of_isPullback)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sheaves.RingedToposModules (inverseImageModules pullbackModuleObjRestrictScalarsIso)

universe v u v' u' w w'

namespace Deformation

section Kernel

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w'})] [J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  {A O : Sheaf J CommRingCat.{w'}} {a : A ⟶ O}
  {M : SheafOfModules.{w'} ((sheafCompose J (forget₂ CommRingCat.{w'} RingCat.{w'})).obj O)}

/-- **The inclusion of the kernel of an algebra extension, on underlying sheaves of sets.** -/
noncomputable def AlgebraExtension.inclSheafSets (E : AlgebraExtension a M) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)
        ((SheafOfModules.restrictScalars ((sheafCompose J
          (forget₂ CommRingCat.{w'} RingCat.{w'})).map E.reduction)).obj M) ⟶
      Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf E.extension) :=
  (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)).map
    E.kernelInclusion

/-- **The kernel module of an algebra extension is the kernel of its reduction**, as a pullback
square of sheaves of sets: the fibre of the reduction over the zero section. -/
theorem AlgebraExtension.isPullback_kernelInclusion (E : AlgebraExtension a M) :
    IsPullback E.inclSheafSets (terminal.from _)
      ((sheafCompose J (forget RingCat.{w'})).map
        ((Stacks.forgetCommRingSheaf J).map E.reduction))
      (Sheaf.ringZeroHom (Stacks.SheafOfModules.Tensor.ringSheaf O)) := by
  refine isPullback_terminal_of_sections _ _ _ ?_ (fun U b b' h ↦ E.incl_injective h)
    fun U x hx ↦ E.exists_incl x hx
  refine hom_ext_sections fun U b ↦ ?_
  rw [(Sheaf.sectionsFunctor J U).map_comp_apply]
  exact E.kernelZero U b

end Kernel

end Deformation

namespace Deformation.ToposThickening

section InverseImage

variable {X : RingedTopos.{v, u, w}} {D : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [D.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X D) {A : Sheaf D.J CommRingCat.{w'}} {a : A ⟶ D.O}
  {M : SheafOfModules.{w'} ((sheafCompose D.J (forget₂ CommRingCat.{w'} RingCat.{w'})).obj D.O)}
  (E : AlgebraExtension a M)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The inverse image of the reduction of an algebra extension, in the spelling the inverse image
of sheaves of rings produces it in. -/
theorem ringMap_inverseImage_reduction :
    (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor f.toToposHom).map E.reduction) =
      pullbackRingSheafMap X.J f.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf D.J).map E.reduction) :=
  Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap X.J
    f.toToposHom.inverseImage E.reduction

/-- **`f⁻¹ℳ`**, the inverse image of the kernel module of an algebra extension, as a module over
`f⁻¹𝒪_D`. -/
noncomputable abbrev inverseImageExtensionIdeal :
    SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor f.toToposHom).obj D.O)) :=
  pullbackModuleObj X.J f.toToposHom.inverseImage
    (Stacks.SheafOfModules.Tensor.ringSheaf D.O) M

/-- **The inclusion `f⁻¹ℳ ⟶ f⁻¹𝒪'`**: the inverse image of the kernel inclusion, read through
the comparison of the inverse image of a restriction of scalars with the restriction of scalars
of the inverse image, and through the identification of the inverse image of a unit module with
the unit module of the inverse-image sheaf of rings. -/
noncomputable def inverseImageExtensionIdealIncl :
    (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map
            ((inverseImageCommRingFunctor f.toToposHom).map E.reduction))).obj
        (inverseImageExtensionIdeal f (M := M)) ⟶
      SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        ((inverseImageCommRingFunctor f.toToposHom).obj E.extension)) :=
  eqToHom (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj
      (inverseImageExtensionIdeal f (M := M))) (ringMap_inverseImage_reduction f E)) ≫
    (pullbackModuleObjRestrictScalarsIso X.J f.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf D.J).map E.reduction) M).hom ≫
      (inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)).map E.kernelInclusion ≫
        (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)).inv

/-- The inclusion of `f⁻¹ℳ` is, on sections, the inverse image of the kernel inclusion of sheaves
of sets. -/
theorem inverseImageExtensionIdealIncl_val_app (U : X.Cᵒᵖ)
    (m : (inverseImageExtensionIdeal f (M := M)).val.obj U) :
    (inverseImageExtensionIdealIncl f E).val.app U m =
      (Sheaf.sectionsFunctor X.J U).map
        (f.toToposHom.inverseImage.map E.inclSheafSets) m :=
  congrArg (fun y ↦ (((pullbackModuleObjRestrictScalarsIso X.J f.toToposHom.inverseImage
      ((Stacks.forgetCommRingSheaf D.J).map E.reduction) M).hom ≫
      (inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)).map E.kernelInclusion ≫
        (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf E.extension)).inv).val.app U) y)
    (restrictScalars_eqToHom_val_app (ringMap_inverseImage_reduction f E)
      (inverseImageExtensionIdeal f (M := M)) U m)

/-- **The inclusion of `f⁻¹ℳ` is killed by the inverse image of the reduction.** -/
theorem inverseImage_reduction_inverseImageExtensionIdealIncl (U : X.Cᵒᵖ)
    (m : (inverseImageExtensionIdeal f (M := M)).val.obj U) :
    ((inverseImageCommRingFunctor f.toToposHom).map E.reduction).hom.app U
        (show ((inverseImageCommRingFunctor f.toToposHom).obj E.extension).obj.obj U from
          (inverseImageExtensionIdealIncl f E).val.app U m) = 0 := by
  rw [inverseImageExtensionIdealIncl_val_app]
  have h := sections_comp_eq_zero_of_isPullback X.J f.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf D.J).map E.reduction) _ E.isPullback_kernelInclusion U m
  rw [← ringMap_inverseImage_reduction f E] at h
  exact h

/-- **A section of `f⁻¹𝒪'` killed by the inverse image of the reduction is the image of exactly
one section of `f⁻¹ℳ`**: the inverse image of sheaves of sets is left exact. -/
theorem existsUnique_inverseImageExtensionIdeal_section (U : X.Cᵒᵖ)
    (x : ((inverseImageCommRingFunctor f.toToposHom).obj E.extension).obj.obj U)
    (hx : ((inverseImageCommRingFunctor f.toToposHom).map E.reduction).hom.app U x = 0) :
    ∃! m : (inverseImageExtensionIdeal f (M := M)).val.obj U,
      (show ((inverseImageCommRingFunctor f.toToposHom).obj E.extension).obj.obj U from
        (inverseImageExtensionIdealIncl f E).val.app U m) = x := by
  have hx' : (Sheaf.sectionsFunctor X.J U).map ((sheafCompose X.J (forget RingCat.{w})).map
      (pullbackRingSheafMap X.J f.toToposHom.inverseImage
        ((Stacks.forgetCommRingSheaf D.J).map E.reduction))) x = 0 := by
    rw [← ringMap_inverseImage_reduction f E]
    exact hx
  obtain ⟨m, hm, huniq⟩ := existsUnique_sections_of_isPullback X.J f.toToposHom.inverseImage
    ((Stacks.forgetCommRingSheaf D.J).map E.reduction) _ E.isPullback_kernelInclusion U x hx'
  exact ⟨m, (inverseImageExtensionIdealIncl_val_app f E U m).trans hm,
    fun b hb ↦ huniq b ((inverseImageExtensionIdealIncl_val_app f E U b).symm.trans hb)⟩

/-- **The square-zero extension problem whose lower row is the inverse image of an algebra
extension of the base** (Stacks 08UF set up over a base thickening `0 → ℳ → 𝒪' → 𝒪_D → 0`): the
thickened base is `𝒪'` with its reduction, the inverse image of the base ideal is `f⁻¹ℳ`, and
`c : f⁻¹ℳ ⟶ 𝒢` is the prescribed map to the given `𝒪_X`-module. -/
noncomputable def RingedToposExtensionProblem.ofBaseAlgebraExtension
    (G : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O))
    (c : inverseImageExtensionIdeal f (M := M) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f.fSharpInverseImage)).obj G) :
    RingedToposExtensionProblem X D where
  f := f
  baseExtension := E.extension
  baseReduction := E.reduction
  baseLocallySurjective := E.locallySurjective
  baseSquareZero := E.squareZero
  I := inverseImageExtensionIdeal f (M := M)
  G := G
  idealInclusion := inverseImageExtensionIdealIncl f E
  c := c
  idealZero := inverseImage_reduction_inverseImageExtensionIdealIncl f E
  idealUniversal := existsUnique_inverseImageExtensionIdeal_section f E

end InverseImage

end Deformation.ToposThickening
