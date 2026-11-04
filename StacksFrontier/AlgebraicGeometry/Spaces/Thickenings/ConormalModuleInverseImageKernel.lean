module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# The conormal module of a first-order thickening is the kernel of the reduction

Let `Z ⊆ X` be a first-order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`.  On the small étale site of `Z` the inverse image `i^{-1}𝒪_X` of the structure
sheaf of the ambient space carries the inverse-image form `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the
structure map of [Stacks Project, Tag 03G8]. This file identifies the conormal module

`𝒞_{Z/X} ≅ ker(i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z)`

and shows that this kernel has square zero.

## Main definitions

* `AlgebraicGeometry.Space.thickeningTransport`: the direct image of sheaves of
  `i^{-1}𝒪_X`-modules along `i`, read as `𝒪_X`-modules through the unit.
* `AlgebraicGeometry.Space.conormalDirectImageIso`: the defining ideal of a first-order
  thickening, identified with the direct image of the conormal module in that presentation.
* `AlgebraicGeometry.Space.conormalInverseImageι`: the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X`, a
  morphism of sheaves of `i^{-1}𝒪_X`-modules.
* `AlgebraicGeometry.Space.conormalInverseImageKernelIso`: the isomorphism
  `𝒞_{Z/X} ≅ ker(i^♯)`.

## Main results

* `AlgebraicGeometry.Space.app_conormalInverseImageι_eq_zero` and
  `AlgebraicGeometry.Space.exists_conormalInverseImageι_eq`: the image of the inclusion over an
  object of the small étale site of `Z` is exactly the kernel of `i^♯` there.
* `AlgebraicGeometry.Space.conormalInverseImageι_injective`: the inclusion is injective on
  sections.
* `AlgebraicGeometry.Space.conormalInverseImageι_val_app_map`: it commutes with restriction.
* `AlgebraicGeometry.Space.conormalInverseImageKernelIso_hom_comp_ι`: the isomorphism composed
  with the inclusion of the kernel ideal is the inclusion.
* `AlgebraicGeometry.Space.mul_eq_zero_of_structureSharpRingInverseImage_app_eq_zero` and
  `AlgebraicGeometry.Space.mul_app_conormalInverseImageι_eq_zero`: the kernel of
  `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` has square zero, stated of two sections it kills and of the images of
  two sections of the conormal module.

## Implementation notes

The inclusion is a morphism of sheaves of `i^{-1}𝒪_X`-modules, the conormal module being one by
restriction of scalars along `i^♯`. On sections restriction of scalars changes nothing, so the
sectionwise statements are statements about the sections of `𝒞_{Z/X}` itself.

The invertibility of the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` is supplied by name, as `hηiso`, from
`AlgebraicGeometry.Space.isIso_thickeningRingUnit`: instance resolution for
`CategoryTheory.IsIso` at a morphism of sheaves of rings on the small étale site does not
terminate within the default budget.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ), part (3).
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The direct image of modules over the inverse-image structure sheaf -/

/-- The morphism of small étale topoi of the inclusion of a closed subspace. -/
abbrev thickeningToposHom :=
  (smallEtaleRingedToposModulesHom B S hS (subspaceInclusion B S hS X Z)).toToposHom

/-- The direct image of sheaves of sets along the inclusion of a closed subspace is full. -/
instance full_thickeningToposHom_pushforward :
    (thickeningToposHom B S hS Z).pushforward.Full :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).full

/-- The direct image of sheaves of sets along the inclusion of a closed subspace is faithful. -/
instance faithful_thickeningToposHom_pushforward :
    (thickeningToposHom B S hS Z).pushforward.Faithful :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).faithful

/-- The unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` of the inclusion of a closed subspace, as a morphism of
sheaves of rings. -/
abbrev thickeningRingUnit :=
  ringUnit (thickeningToposHom B S hS Z) (structureRingSheaf B S hS X)

/-- **The direct image of sheaves of `i^{-1}𝒪_X`-modules along the inclusion of a closed
subspace**, read as sheaves of `𝒪_X`-modules through the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`. -/
abbrev thickeningTransport :=
  Stacks.SheafOfModules.IdealTransport.transport (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward (thickeningRingUnit B S hS Z)

/-- Restriction of scalars along the inverse-image form of the structure map, followed by the
direct image above, is the direct image of sheaves of modules of [Stacks Project, Tag 03D6],
part (1) attached to the morphism of small étale ringed topoi. -/
theorem restrictScalars_comp_thickeningTransport :
    SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) ⋙
      thickeningTransport B S hS Z =
    pushforwardModules (smallEtaleRingedToposModulesHom B S hS
      (subspaceInclusion B S hS X Z)) :=
  congrArg (fun φ ↦ SheafOfModules.restrictScalars φ ⋙ thickeningTransport B S hS Z)
    (fSharpInverseImage_eq_structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).symm

/-- **The comparison with `AlgebraicGeometry.Space.modulePushforward`.** The direct image of
`𝒪_Z`-modules taken in the inverse-image presentation, restriction of scalars along
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` followed by `AlgebraicGeometry.Space.thickeningTransport`, is the
direct image of Stacks 03LU, which takes the direct image first and restricts along
`i^♯ : 𝒪_X ⟶ i_*𝒪_Z` after. -/
def thickeningTransportIso :
    SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) ⋙
        thickeningTransport B S hS Z ≅
      modulePushforward B S hS (subspaceInclusion B S hS X Z) :=
  eqToIso (restrictScalars_comp_thickeningTransport B S hS Z) ≪≫
    modulePushforwardIso B S hS (subspaceInclusion B S hS X Z)

/-- **The two forms of the structure map are adjunct.** -/
theorem thickeningRingUnit_comp_pullbackRingSheafMap :
    thickeningRingUnit B S hS Z ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
          (thickeningToposHom B S hS Z).pushforward
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharp B S hS (subspaceInclusion B S hS X Z) :=
  ringUnit_comp_map_structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z)

/-- The unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` is an isomorphism for the inclusion of a thickening. -/
theorem isIso_thickeningRingUnit (hZ : IsThickening B S hS X Z.1) :
    IsIso (thickeningRingUnit B S hS Z) :=
  isIso_ringUnit_of_isThickening B S hS Z hZ (structureRingSheaf B S hS X)

/-! ### The conormal module as the kernel of the reduction -/

/-- **The defining ideal of a first-order thickening is the direct image of the conormal
module**, `𝓘 ≅ i_*𝒞_{Z/X}`, in the inverse-image presentation of the direct image. -/
def conormalDirectImageIso (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (SheafOfModules.kerIdeal
        (structureSharp B S hS (subspaceInclusion B S hS X Z))).toSheafOfModules ≅
      (thickeningTransport B S hS Z).obj
        ((SheafOfModules.restrictScalars
            (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)) :=
  firstOrderConormalModuleIso B S hS Z hZ ≪≫
    ((thickeningTransportIso B S hS Z).app (conormalModule B S hS X Z)).symm

/-- **The inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` of the conormal module of a first-order thickening
into the inverse image of the structure sheaf of the ambient space**, as a morphism of sheaves
of `i^{-1}𝒪_X`-modules on the small étale site of `Z`. -/
def conormalInverseImageι (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z) ⟶
      SheafOfModules.unit
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  Stacks.SheafOfModules.IdealTransport.idealι
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
    (thickeningRingUnit B S hS Z)
    (structureSharp B S hS (subspaceInclusion B S hS X Z))
    (conormalDirectImageIso B S hS Z hZ)

/-- **The inclusion lands in the kernel of the reduction**, on sections. -/
theorem app_conormalInverseImageι_eq_zero (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    ((structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z)).hom.app V)
        ((conormalInverseImageι B S hS Z hZ).val.app V m) = 0 :=
  Stacks.SheafOfModules.IdealTransport.app_idealι_eq_zero
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z) V m

/-- **Every section of `i^{-1}𝒪_X` killed by the reduction comes from the conormal module.** -/
theorem exists_conormalInverseImageι_eq (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (s : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V)
    (hs : ((structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app V) s = 0) :
    ∃ m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V,
      (conormalInverseImageι B S hS Z hZ).val.app V m = s :=
  Stacks.SheafOfModules.IdealTransport.exists_idealι_eq
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z) V s hs

/-- **The direct image of the inclusion, on sections over the small étale site of `X`, is the
unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` of a local section of the defining ideal.** -/
theorem exists_structureSharp_eq_zero_map_conormalInverseImageι_val_app
    (hZ : IsFirstOrderThickening B S hS X Z.1) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ((thickeningTransport B S hS Z).obj
      ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z))).val.obj U) :
    ∃ r : (structureRingSheaf B S hS X).obj.obj U,
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U) r = 0 ∧
        ((thickeningTransport B S hS Z).map
            (conormalInverseImageι B S hS Z hZ)).val.app U t =
          ((thickeningRingUnit B S hS Z).hom.app U) r :=
  Stacks.SheafOfModules.IdealTransport.exists_mem_kerIdeal_map_idealι_val_app
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _
    (conormalDirectImageIso B S hS Z hZ) U t

/-- **The inclusion is injective on sections.** -/
theorem conormalInverseImageι_injective (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ) :
    Function.Injective ((conormalInverseImageι B S hS Z hZ).val.app V) :=
  Stacks.SheafOfModules.IdealTransport.idealι_injective
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _
    (conormalDirectImageIso B S hS Z hZ) V

/-- **The conormal module of a first-order thickening is the kernel of the reduction
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`**, as sheaves of `i^{-1}𝒪_X`-modules on the small étale site of `Z`. -/
def conormalInverseImageKernelIso (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (SheafOfModules.restrictScalars
          (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z) ≅
      (SheafOfModules.kerIdeal
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).toSheafOfModules :=
  Stacks.SheafOfModules.IdealTransport.idealKernelIso
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z)

/-- The isomorphism with the kernel, composed with the inclusion of the kernel ideal into
`i^{-1}𝒪_X`, is `AlgebraicGeometry.Space.conormalInverseImageι`. -/
theorem conormalInverseImageKernelIso_hom_comp_ι (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (conormalInverseImageKernelIso B S hS Z hZ).hom ≫
        (SheafOfModules.kerIdeal
          (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))).ι =
      conormalInverseImageι B S hS Z hZ :=
  Stacks.SheafOfModules.IdealTransport.idealKernelIso_hom_comp_ι
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z)

/-- **The kernel of the reduction `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of a first-order thickening has
square zero.** Read on the small étale site of `Z`: two sections of `i^{-1}𝒪_X` over the same
object which the reduction kills have vanishing product. -/
theorem mul_eq_zero_of_structureSharpRingInverseImage_app_eq_zero
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m m' : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj V)
    (hm : ((structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app V) m = 0)
    (hm' : ((structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app V) m' = 0) :
    m * m' = 0 :=
  Stacks.SheafOfModules.IdealTransport.mul_eq_zero_of_app_eq_zero
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z) V m m' hm hm'

/-- **The inclusion commutes with restriction**, read on sections. -/
theorem conormalInverseImageι_val_app_map (hZ : IsFirstOrderThickening B S hS X Z.1)
    {V W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (h : V ⟶ W)
    (m : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    (conormalInverseImageι B S hS Z hZ).val.app W
        (((SheafOfModules.restrictScalars
            (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))).obj
          (conormalModule B S hS X Z)).val.map h m) =
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)).obj.map h
        (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
          (conormalInverseImageι B S hS Z hZ).val.app V m) :=
  PresheafOfModules.naturality_apply (conormalInverseImageι B S hS Z hZ).val h m

/-- **The image of the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` has square zero**: the product of the
images of two sections of the conormal module over the same object of the small étale site of
`Z` vanishes. -/
theorem mul_app_conormalInverseImageι_eq_zero (hZ : IsFirstOrderThickening B S hS X Z.1)
    (V : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m m' : ((SheafOfModules.restrictScalars
        (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS X Z))).obj (conormalModule B S hS X Z)).val.obj V) :
    (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V m) *
      (show ToType ((structureRingSheafInverseImage B S hS
            (subspaceInclusion B S hS X Z)).obj.obj V) from
        (conormalInverseImageι B S hS Z hZ).val.app V m') = 0 :=
  Stacks.SheafOfModules.IdealTransport.mul_app_idealι_eq_zero
    (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
    (SmallEtale.topology B S hS X.1)
    (thickeningToposHom B S hS Z).pushforward _ _ _ (conormalDirectImageIso B S hS Z hZ)
    (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z) V m m'

end AlgebraicGeometry.Space

end
