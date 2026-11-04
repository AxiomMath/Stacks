module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsInclusion
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom

/-!
# The inclusion of the forms with no pole into the forms with a logarithmic pole

Let `f : X ⟶ S` be a morphism of schemes and let `I` cut out a closed subscheme `Y ⊆ X` with
ideal sheaf `ℐ`. A relative `p`-form `ω` with no pole along `Y` determines a logarithmic form,
namely the `𝒪_X`-linear map `a ↦ a · ω` from `ℐ` to the sheaf `𝒦^p` of forms vanishing on `Y`.
This file constructs that morphism

`Ω^p_{X/S} ⟶ Ω^p_{X/S}(log Y) = SheafHom_{𝒪_X}(ℐ, 𝒦^p)`,

the first map of the short exact sequence of [Stacks, Tag 0FMW].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.negativeTwistAction`: the multiplication `ℱ ⊗_{𝒪_X} ℐ ⟶ ℱ` by
  the ideal sheaf, on an arbitrary sheaf of modules.
* `AlgebraicGeometry.Scheme.Hom.idealFormProduct`: that multiplication on the relative
  `p`-forms, read as a morphism into the subsheaf `𝒦^p` of forms vanishing on the divisor.
* `AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion`: the canonical inclusion
  `Ω^p_{X/S} ⟶ Ω^p_{X/S}(log Y)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.negativeTwistAction_tmul`: the multiplication carries a local
  pure tensor `m ⊗ a` to `a · m`. This pins the multiplication down.
* `AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion_app_apply`: the logarithmic form
  attached to `ω` carries a local section `a` of the ideal sheaf to `a · ω`. This pins the
  inclusion down.

## Implementation notes

The multiplication is the whiskered ideal inclusion followed by the right unitor,
`ℱ ⊗ ℐ ⟶ ℱ ⊗ 𝒪_X ⟶ ℱ`, for the monoidal structure
`Stacks.SheafOfModules.OnSpace.monoidal` of [Stacks, Tag 01CA], whose tensor product is the
sheafification of the objectwise tensor product and whose
unit is the structure sheaf, both on the nose. That is the only one of the several spellings of
the tensor product of sheaves of modules in which both halves of the construction are
available: the structural morphisms are evaluated on local pure tensors by
`Stacks.SheafOfModules.OnSpace.rightUnitor_tmul`, and the currying bijection of
[Stacks, Tag 01CN] that turns the multiplication into a map into the sheaf-hom is
`Stacks.SheafOfModules.tensorHomEquiv`. No bridge between spellings of the tensor product is
needed anywhere below.

That monoidal structure lives on the sheaves of modules over the ringed-space spelling
`structureSheafRing` of the structure sheaf, while the sheaves of differential forms are typed
over `AlgebraicGeometry.Scheme.ringCatSheaf`. The two are equal by `rfl`, so a *term* crosses
between them freely, but instance search does not: a type ascription does not change the type
an elaborated term reports, so `ℱ ⊗ ℐ` written at a sheaf of forms looks for its monoidal
instance at `X.Modules` and fails. Hence the multiplication, its value on pure tensors, and the
vanishing criterion for a composite out of it are all stated for *variable* modules typed at
`structureSheafRing`, and the sheaves of forms are substituted in afterwards; the same device
supplies the zero morphism, whose `Zero` instance is likewise invisible at the mixed spelling.

That the multiplication lands in `𝒦^p` is proved at the level of morphisms, as the vanishing of
its composite with the restriction to the divisor, and only then read on sections. It has to be
done in that order: a morphism out of a sheafified tensor product is determined by its values on
local pure tensors (`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`), where
`AlgebraicGeometry.Scheme.Hom.negativeTwistSection_smul_mem_formRestrictionKernel` applies, but
the hypothesis of `SheafOfModules.Submodule.factorThru` is about *every* local section, and a
general local section of the sheafified tensor product is not a pure tensor.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open Stacks.SheafOfModules.OnSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

section Action

variable (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- **The multiplication `ℱ ⊗_{𝒪_X} ℐ ⟶ ℱ`** by the ideal sheaf of the closed subscheme cut out
by `I`: the inclusion `ℐ ⟶ 𝒪_X` whiskered with `ℱ`, followed by the right unitor. -/
def negativeTwistAction :
    F ⊗ Stacks.Divisors.negativeTwist I ⟶ F :=
  (F ◁ Stacks.Divisors.idealInclusion I) ≫ (ρ_ F).hom

/-- The multiplication by the ideal sheaf, on a local pure tensor: the section of the ideal
sheaf is pushed into `𝒪_X` and the right unitor then multiplies by it. The scalar is taken as a
variable together with the equation naming it, so that a caller can supply its own spelling of
the section of `𝒪_X` and of the scalar action. -/
theorem negativeTwistAction_tmul (U : X.Opens) (m : F.val.obj (op U))
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op U))
    (r : X.toRingedSpace.presheaf.obj (op U))
    (hr : ((Stacks.Divisors.idealInclusion I).val.app (op U)).hom a = r) :
    ((negativeTwistAction I F).val.app (op U)).hom
        (tensorObjTmul X.toRingedSpace F (Stacks.Divisors.negativeTwist I) (op U) m a) =
      r • m :=
  (congrArg (fun t => ((ρ_ F).hom.val.app (op U)).hom t)
      (whiskerLeft_tmul X.toRingedSpace F (Stacks.Divisors.idealInclusion I) (op U) m a)).trans
    ((rightUnitor_tmul X.toRingedSpace F (op U) m
        (((Stacks.Divisors.idealInclusion I).val.app (op U)).hom a)).trans
      (congrArg (fun s : X.toRingedSpace.presheaf.obj (op U) => s • m) hr))

/-- A morphism out of the multiplication by the ideal sheaf vanishes as soon as it vanishes on
every local pure tensor: a morphism out of a sheafified tensor product is determined by its
values on local pure tensors. -/
theorem negativeTwistAction_comp_eq_zero
    {G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (φ : F ⟶ G)
    (h : ∀ (U : (X.Opens)ᵒᵖ) (m : F.val.obj U)
      (a : (Stacks.Divisors.negativeTwist I).val.obj U),
      (φ.val.app U).hom (((negativeTwistAction I F).val.app U).hom
        (tensorObjTmul X.toRingedSpace F (Stacks.Divisors.negativeTwist I) U m a)) = 0) :
    negativeTwistAction I F ≫ φ = 0 := by
  refine tensor_hom_ext (X := X.toRingedSpace) (A := F)
    (B := Stacks.Divisors.negativeTwist I) ?_
  intro U m a
  exact (sheaf_comp_app_apply X.toRingedSpace (negativeTwistAction I F) φ U
      (tensorObjTmul X.toRingedSpace F (Stacks.Divisors.negativeTwist I) U m a)).trans
    ((h U m a).trans (map_zero (ConcreteCategory.hom
      ((0 : F ⊗ Stacks.Divisors.negativeTwist I ⟶ G).val.app
        U))).symm)

end Action

/-- Every local section of `Ω^p_{X/S} ⊗_{𝒪_X} ℐ` is carried into the subsheaf `𝒦^p` of forms
vanishing on the divisor. -/
theorem negativeTwistAction_app_mem (p : ℕ) (U : (X.Opens)ᵒᵖ)
    (x : (id (α := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (relativeDifferentialForms f (p : ℤ)) ⊗
      Stacks.Divisors.negativeTwist I).val.obj U) :
    PresheafOfModules.Hom.app
        (negativeTwistAction I (relativeDifferentialForms f (p : ℤ))).val U x ∈
      (formRestrictionKernel f I p).obj U := by
  refine (mem_formRestrictionKernel f I p U _).2 (Eq.trans
    (congrArg (fun q => PresheafOfModules.Hom.app (_root_.SheafOfModules.Hom.val q) U x)
      (negativeTwistAction_comp_eq_zero I (relativeDifferentialForms f (p : ℤ))
        (formRestriction I.subschemeι f (p : ℤ)) ?_)) ?_)
  · intro W ω a
    obtain ⟨V⟩ := W
    exact (congrArg (fun t => ((formRestriction I.subschemeι f (p : ℤ)).val.app (op V)).hom t)
        (negativeTwistAction_tmul I (relativeDifferentialForms f (p : ℤ)) V ω a
          (negativeTwistSection I V a) rfl)).trans
      ((mem_formRestrictionKernel f I p (op V) _).1
        (negativeTwistSection_smul_mem_formRestrictionKernel f I p V a ω))
  · rfl

/-- The multiplication `Ω^p_{X/S} ⊗_{𝒪_X} ℐ ⟶ 𝒦^p` of the relative `p`-forms by the ideal
sheaf, read as a morphism into the subsheaf of forms vanishing on the divisor. -/
def idealFormProduct (p : ℕ) :
    id (α := SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (relativeDifferentialForms f (p : ℤ)) ⊗
        Stacks.Divisors.negativeTwist I ⟶
      formRestrictionKernelSheaf f I p :=
  (formRestrictionKernel f I p).factorThru
    (negativeTwistAction I (relativeDifferentialForms f (p : ℤ)))
    (negativeTwistAction_app_mem f I p)

/-- **The canonical inclusion `Ω^p_{X/S} ⟶ Ω^p_{X/S}(log Y)`** of the relative `p`-forms with
no pole into the relative `p`-forms with a logarithmic pole along the divisor `Y` cut out by
`I`: the form `ω` goes to the `𝒪_X`-linear map `a ↦ a · ω` from the ideal sheaf of `Y` to the
sheaf `𝒦^p` of forms vanishing on `Y`.

This is the first map of the short exact sequence of [Stacks, Tag 0FMW]. -/
def logPolesFormsInclusion (p : ℕ) :
    relativeDifferentialForms f (p : ℤ) ⟶ logPolesForms f I p :=
  Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace
    (relativeDifferentialForms f (p : ℤ)) (Stacks.Divisors.negativeTwist I)
    (formRestrictionKernelSheaf f I p) (idealFormProduct f I p)

/-- **The inclusion of the forms with no pole, on local sections**: the logarithmic form
attached to `ω` carries a local section `a` of the ideal sheaf to `a · ω`, read in `Ω^p_{X/S}`
through the inclusion of `𝒦^p`. -/
theorem logPolesFormsInclusion_app_apply (p : ℕ) (U : X.Opens)
    (ω : (relativeDifferentialForms f (p : ℤ)).val.obj (op U))
    (a : (Stacks.Divisors.negativeTwist I).val.obj (op U)) :
    PresheafOfModules.Hom.app (formRestrictionKernel f I p).ι.val (op U)
        ((((logPolesFormsInclusion f I p).val.app (op U) ω).app
          (op (Over.mk (𝟙 U)))).hom a) =
      negativeTwistSection I U a • ω :=
  (congrArg (fun z => PresheafOfModules.Hom.app (formRestrictionKernel f I p).ι.val (op U) z)
      (Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry X.toRingedSpace
        (idealFormProduct f I p) U ω a)).trans
    ((congrArg (fun q => PresheafOfModules.Hom.app (_root_.SheafOfModules.Hom.val q) (op U)
          (tensorObjTmul X.toRingedSpace (relativeDifferentialForms f (p : ℤ))
            (Stacks.Divisors.negativeTwist I) (op U) ω a))
        ((formRestrictionKernel f I p).factorThru_ι
          (negativeTwistAction I (relativeDifferentialForms f (p : ℤ)))
          (negativeTwistAction_app_mem f I p))).trans
      (negativeTwistAction_tmul I (relativeDifferentialForms f (p : ℤ)) U ω a
        (negativeTwistSection I U a) rfl))

end AlgebraicGeometry.Scheme.Hom

end
