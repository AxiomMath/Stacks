module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.RingTheory.TensorProduct.IdealSmulKernel

/-!
# The kernel of `J ⊗ F ⟶ J F` is killed by `J`

Let `X` be a scheme, `J ⊆ 𝒪_X` an ideal of the structure sheaf and `F` an `𝒪_X`-module. The
multiplication morphism `Stacks.Algebraization.idealAction J F : J ⊗ F ⟶ F` corestricts, by
`Stacks.Algebraization.idealActionLift`, to the surjection of the sheafified tensor product onto
the ideal multiple `J F`. This file proves that the kernel of that surjection is annihilated by
`J`: a section of `J ⊗ F` over an open `U` whose product vanishes is killed by every section of
`J` over `U`.

With `J = 𝓘 ^ n` this is the vanishing `𝓘 ^ n 𝓚 = 0`, for `𝓚` the kernel of
`𝓘 ^ n ⊗ 𝓖 ⟶ 𝓘 ^ n 𝓖`, which the proof of [Stacks, Tag 01YB] uses to descend a morphism defined
on `𝓘 ^ n ⊗ 𝓖` to a morphism defined on a further ideal multiple of `𝓖`. No hypothesis is placed
on `X`, `J` or `F`; in particular neither Noetherian-ness nor coherence is used, and the exponent
that kills the kernel is `1` rather than one produced by Artin–Rees.

## Main definitions

* `Stacks.Algebraization.idealSections`: the sections of `J` over an open, as an ideal of
  `Γ(X, U)`; its `Submodule.subtype` is the inclusion into `Γ(X, U)`.

## Main results

* `Stacks.Algebraization.idealActionPresheaf_app_eq_smulMap`: before sheafification the
  multiplication on sections over an open is the module-level multiplication map
  `Stacks.IdealTensor.smulMap` of that inclusion.
* `Stacks.Algebraization.smul_eq_zero_of_idealActionPresheaf_eq_zero`: the presheaf-level form of
  the vanishing, immediate from `Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero`.
* `Stacks.Algebraization.smul_eq_zero_of_idealAction_eq_zero`: **the kernel of
  `Stacks.Algebraization.idealAction` is killed by `J`**, the sheafified statement.
* `Stacks.Algebraization.idealSections_smul_ker_idealAction_app_eq_bot`: the same as an equality
  of submodules of the sections over an open, which is the shape
  `AlgebraicGeometry.exists_idealPow_smul_inf_eq_bot` consumes.
* `Stacks.Algebraization.smul_eq_zero_of_idealActionLift_eq_zero`: the same for the
  corestriction `Stacks.Algebraization.idealActionLift` of the action to a submodule containing
  all the products — for the ideal multiple itself, that is the surjection whose kernel
  [Stacks, Tag 01YB] names.

## Implementation notes

The module-level input is elementary and carries no finiteness hypothesis — see
`StacksFrontier.RingTheory.TensorProduct.IdealSmulKernel` — so the only work here is the passage
from the presheaf tensor product to its sheafification. It is done by stalks, which is where the
sheafification is under control: `Stacks.SheafOfModules.TensorStalkRingedSpace` proves
[Stacks, Tag 01CB], and in particular
`Stacks.SheafOfModules.TensorStalkRingedSpace.exists_tensorSheafStalkIso`, the statement that the
stalk of the sheafified tensor product is the stalk of the presheaf tensor product with the germ
of a presheaf section going to the germ of its image. Given a section `z` of `J ⊗ F` over `U` and
a point `x` of `U`, that isomorphism produces a presheaf-tensor section whose image agrees with
`z` near `x`; the module-level lemma kills it there, and `TopCat.Presheaf.section_ext` assembles
the local vanishings.

Three spelling points. The scalar action on the sections of a presheaf of modules over the
structure sheaf is declared over
`(Stacks.SheafOfModules.TensorStalkRingedSpace.O X.toRingedSpace).obj U`, which instance search
does not recognise as `Γ(X, U)`; `sectionsModuleO` restates it, exactly as the local instances of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent` do for the
other spelling. And the ideal of sections of `J` is reached through the named
`idealSections` rather than an ascription inside a statement: an ascribed subterm survives
into the goal as a `have`, which is not type-correct at the transparency `rw` builds its motive
at, so every rewrite touching it fails.

The third point concerns the sheafified tensor product, whose sections are a module over
`(Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj U` for `R` the structure sheaf of `X`.
`Stacks.SheafOfModules.Tensor.ringSheafSectionModule` is the instance that recovers `Γ(X, U)` as
the scalar ring, and it is the canonical provider's, so no instance is declared here. It is not
*findable*, however: its conclusion names the scalar ring as `R.obj.obj U` for a variable `R`, so
instance search would have to solve `?R.obj =?= X.presheaf`, a projection applied to a
metavariable. Every statement below that multiplies a section of the sheafified tensor product
therefore names that instance in a `letI`, which inlines it, leaving the statement itself the
proposition it would have been had search succeeded.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- The module structure on the sections of a presheaf of modules over the structure sheaf
written as `Stacks.SheafOfModules.TensorStalkRingedSpace.O`, restated with `Γ(X, U)` as the
scalar ring. -/
local instance sectionsModuleO (M : PresheafOfModules.{u} (O X.toRingedSpace))
    (U : (Opens X)ᵒᵖ) : Module (X.presheaf.obj U) (M.obj U) :=
  inferInstanceAs (Module ((O X.toRingedSpace).obj U) (M.obj U))

/-- The module structure on the sections of a presheaf of modules over the structure sheaf
written as `X.ringCatSheaf.obj`, restated with `Γ(X, U)` as the scalar ring. -/
local instance sectionsModuleRingCat (M : PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : (Opens X)ᵒᵖ) : Module (X.presheaf.obj U) (M.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.obj U))

/-- The sections over an open of an ideal `J` of the structure sheaf, as an ideal of `Γ(X, U)`.

Its `Submodule.subtype` is the inclusion into `Γ(X, U)`, and is the linear map to which the
module-level `Stacks.IdealTensor.smulMap` is applied below. The ideal is given a name rather than
written as an ascription inside a statement because an ascribed subterm survives into the goal as
a `have`, which is not type-correct at the transparency `rw` builds its motive at. -/
def idealSections (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (U : (Opens X)ᵒᵖ) :
    Ideal (X.presheaf.obj U) :=
  J.toSubmodule.obj U

/-- The inclusion of the sections of an ideal of the structure sheaf is compatible with
restriction. -/
lemma subtype_idealSections_map (J : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (a : J.toSheafOfModules.val.obj U) :
    (idealSections J V).subtype (J.toSheafOfModules.val.map i a) =
      X.presheaf.map i ((idealSections J U).subtype a) :=
  rfl

/-- Over an open, the multiplication of `Stacks.Algebraization.idealActionPresheaf` is the
module-level multiplication map `Stacks.IdealTensor.smulMap` attached to the inclusion of the
ideal of sections of `J`. Both send a pure tensor `a ⊗ m` to `a • m`. -/
lemma idealActionPresheaf_app_eq_smulMap
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (U : (Opens X)ᵒᵖ)
    (t : ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
      (J.toSheafOfModules.val) (F.val))).obj U) :
    ((idealActionPresheaf J F).app U).hom t =
      Stacks.IdealTensor.smulMap (idealSections J U).subtype t := by
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a m => rfl
  | add t s ht hs =>
      exact (map_add _ t s).trans ((congrArg₂ (· + ·) ht hs).trans (map_add _ t s).symm)

/-- **The presheaf-level form of the vanishing.** A section of the presheaf tensor product of `J`
with `F` over an open `U` whose product in `F` vanishes is killed by every section of `J` over
`U`.

This is `Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero` for the ideal of sections of `J`
over `U`. -/
lemma smul_eq_zero_of_idealActionPresheaf_eq_zero
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U)
    (t : ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
      (J.toSheafOfModules.val) (F.val))).obj U)
    (ht : ((idealActionPresheaf J F).app U).hom t = 0) :
    (idealSections J U).subtype a • t = 0 := by
  rw [idealActionPresheaf_app_eq_smulMap] at ht
  exact Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero (idealSections J U).subtype
    (Ideal.smul_comm_subtype (idealSections J U)) a ht

/-- The multiplication on sections of the sheafified tensor product, evaluated on the image of a
section of the presheaf tensor product, is the presheaf-level multiplication.

This is `Stacks.Algebraization.idealAction_tmul` for an arbitrary section of the presheaf tensor
product rather than a pure tensor: both sides are the two readings of the adjunction isomorphism
that defines `Stacks.Algebraization.idealAction`. -/
lemma idealAction_app_sheafifyUnit
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (U : (Opens X)ᵒᵖ)
    (t : ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
      (J.toSheafOfModules.val) (F.val))).obj U) :
    (idealAction J F).val.app U
        ((sheafifyUnit X.toRingedSpace
          ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
            (J.toSheafOfModules.val) (F.val)))).app U t) =
      ((idealActionPresheaf J F).app U).hom t :=
  congrArg (fun k ↦ (PresheafOfModules.Hom.app k U).hom t)
    ((PresheafOfModules.sheafificationHomEquiv (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).apply_symm_apply (idealActionPresheaf J F))

/-- **The kernel of `Stacks.Algebraization.idealAction` is killed by `J`.** Let `X` be a scheme,
`J` an ideal of its structure sheaf and `F` an `𝒪_X`-module. If a section `z` of the sheafified
tensor product `J ⊗ F` over an open `U` has vanishing product in `F`, then `a • z = 0` for every
section `a` of `J` over `U`.

With `J = 𝓘 ^ n` this is the vanishing `𝓘 ^ n 𝓚 = 0` for `𝓚` the kernel of the surjection
`𝓘 ^ n ⊗ 𝓖 ⟶ 𝓘 ^ n 𝓖` in the proof of [Stacks, Tag 01YB]. Nothing is assumed of `X`, `J` or `F`.

The proof is local. The module-level statement
`Stacks.IdealTensor.smul_eq_zero_of_smulMap_eq_zero` kills a section of the *presheaf* tensor
product, and by [Stacks, Tag 01CB] the germ of `z` at any point of `U` is the germ of the image
of such a section, which therefore agrees with `z` on a neighbourhood. So `a • z` vanishes near
every point of `U`, hence vanishes. -/
theorem smul_eq_zero_of_idealAction_eq_zero
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules)
    (U : Opens X) (a : J.toSheafOfModules.val.obj (op U))
    (z : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.obj (op U))
    (hz : (idealAction J F).val.app (op U) z = 0) :
    letI : ∀ V : (Opens X)ᵒᵖ, Module (X.presheaf.obj V)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            J.toSheafOfModules).obj F).val.obj V) :=
      fun V ↦ Stacks.SheafOfModules.Tensor.ringSheafSectionModule
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ V _
    (idealSections J (op U)).subtype a • z = 0 := by
  let : ∀ V : (Opens X)ᵒᵖ, Module (X.presheaf.obj V)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.obj V) :=
    fun V ↦ Stacks.SheafOfModules.Tensor.ringSheafSectionModule
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ V _
  set P := PresheafOfModules.tensorObj.{u, u, u, u, u}
    (O := X.toRingedSpace.presheaf) J.toSheafOfModules.val F.val
  refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u})
    ⟨(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.presheaf,
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).isSheaf⟩ U
    ((idealSections J (op U)).subtype a • z) 0 fun x hxU ↦ ?_
  -- Tag 01CB: the germ of `z` at `x` is the germ of the image of a presheaf-tensor section.
  obtain ⟨θ, hθ⟩ := exists_tensorSheafStalkIso X.toRingedSpace x J.toSheafOfModules F
  obtain ⟨V, hxV, w, hw⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    P.presheaf (θ (grpGerm X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val x U hxU z))
  have hw' : grpGerm X.toRingedSpace P x V hxV w =
      θ (grpGerm X.toRingedSpace
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val x U hxU z) := hw
  have hgerm : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.presheaf U x hxU) z =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.presheaf V x hxV)
        ((sheafifyUnit X.toRingedSpace P).app (op V) w) :=
    (θ.injective ((hθ V hxV w).trans hw')).symm
  -- So `z` and that image agree on some neighbourhood `W` of `x` inside `U`.
  obtain ⟨W, hxW, iU, iV, hWeq⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.presheaf x hxU hxV z _ hgerm
  -- Restricting the presheaf-tensor section to `W`, its image is the restriction of `z`.
  have hres : (sheafifyUnit X.toRingedSpace P).app (op W) (P.map iV.op w) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.map iU.op z :=
    (PresheafOfModules.naturality_apply (sheafifyUnit X.toRingedSpace P) iV.op w).trans hWeq.symm
  -- Its product vanishes, because the product of `z` does.
  have hzero : ((idealActionPresheaf J F).app (op W)).hom (P.map iV.op w) = 0 :=
    (idealAction_app_sheafifyUnit J F (op W) (P.map iV.op w)).symm.trans
      ((congrArg _ hres).trans
        ((PresheafOfModules.naturality_apply (idealAction J F).val iU.op z).trans
          ((congrArg _ hz).trans (map_zero _))))
  -- The module-level lemma kills it on `W`.
  have hkill : X.presheaf.map iU.op ((idealSections J (op U)).subtype a) • P.map iV.op w = 0 :=
    smul_eq_zero_of_idealActionPresheaf_eq_zero J F (op W)
      (J.toSheafOfModules.val.map iU.op a) _ hzero
  -- Hence `a • z` restricts to zero on `W`, so its germ at `x` vanishes.
  refine TopCat.Presheaf.germ_ext (C := AddCommGrpCat.{u})
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.presheaf W hxW iU iU ?_
  have elin : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.map iU.op
        ((idealSections J (op U)).subtype a • z) =
      X.presheaf.map iU.op ((idealSections J (op U)).subtype a) •
        (sheafifyUnit X.toRingedSpace P).app (op W) (P.map iV.op w) := by
    rw [hres]
    exact PresheafOfModules.map_smul
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val iU.op _ z
  have eunit : X.presheaf.map iU.op ((idealSections J (op U)).subtype a) •
        (sheafifyUnit X.toRingedSpace P).app (op W) (P.map iV.op w) =
      (sheafifyUnit X.toRingedSpace P).app (op W)
        (X.presheaf.map iU.op ((idealSections J (op U)).subtype a) • P.map iV.op w) :=
    (map_smul ((sheafifyUnit X.toRingedSpace P).app (op W)).hom _ _).symm
  refine Eq.trans ?_ (map_zero _).symm
  exact elin.trans (eunit.trans ((congrArg _ hkill).trans (map_zero _)))

/-- **The kernel of the ideal multiplication, as a submodule of the sections over an open, is
annihilated by the ideal of sections.** This is
`Stacks.Algebraization.smul_eq_zero_of_idealAction_eq_zero` read as an equality of submodules,
which is the shape in which `AlgebraicGeometry.exists_idealPow_smul_inf_eq_bot` — the Artin–Rees
separation step of [Stacks, Tag 01YB] — asks for the annihilation of its torsion subsheaf. -/
theorem idealSections_smul_ker_idealAction_app_eq_bot
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules) (U : Opens X) :
    letI : ∀ V : (Opens X)ᵒᵖ, Module (X.presheaf.obj V)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            J.toSheafOfModules).obj F).val.obj V) :=
      fun V ↦ Stacks.SheafOfModules.Tensor.ringSheafSectionModule
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ V _
    idealSections J (op U) •
        (LinearMap.ker ((idealAction J F).val.app (op U)).hom :
          Submodule (X.presheaf.obj (op U))
            (((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                (J.toSheafOfModules)).obj (F))).val.obj (op U))) = ⊥ :=
  let : ∀ V : (Opens X)ᵒᵖ, Module (X.presheaf.obj V)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          J.toSheafOfModules).obj F).val.obj V) :=
    fun V ↦ Stacks.SheafOfModules.Tensor.ringSheafSectionModule
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ V _
  le_antisymm
    (Submodule.smul_le.2 fun c hc z hz ↦
      (smul_eq_zero_of_idealAction_eq_zero J F U ⟨c, hc⟩ z hz) ▸ Submodule.zero_mem _)
    bot_le

/-- **The kernel of the surjection `J ⊗ F ⟶ J F` is killed by `J`.** The corestriction
`Stacks.Algebraization.idealActionLift` of the multiplication to a submodule `N` of `F`
containing every product — for `N` the ideal multiple `J F` this is the surjection of
[Stacks, Tag 01YB] — has the same sectionwise kernel as the multiplication itself, because the
inclusion of `N` is injective on sections. So that kernel too is killed by `J`. -/
theorem smul_eq_zero_of_idealActionLift_eq_zero
    (J : (SheafOfModules.unit X.ringCatSheaf).Submodule) (F : X.Modules) (N : F.Submodule)
    (h : ∀ (V : (Opens X)ᵒᵖ) (b : J.toSheafOfModules.val.obj V) (m : F.val.obj V),
      (show X.presheaf.obj V from b.1) • m ∈ N.toSubmodule.obj V)
    (U : Opens X) (a : J.toSheafOfModules.val.obj (op U))
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        (J.toSheafOfModules)).obj (F))).val.obj (op U))
    (hz : (idealActionLift J F N h).val.app (op U) z = 0) :
    letI : ∀ V : (Opens X)ᵒᵖ, Module (X.presheaf.obj V)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            J.toSheafOfModules).obj F).val.obj V) :=
      fun V ↦ Stacks.SheafOfModules.Tensor.ringSheafSectionModule
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ V _
    (idealSections J (op U)).subtype a • z = 0 := by
  refine smul_eq_zero_of_idealAction_eq_zero J F U a z ?_
  have hfac := congrArg
    (fun g ↦ (PresheafOfModules.Hom.app (SheafOfModules.Hom.val g) (op U)).hom z)
    (idealActionLift_fac J F N h)
  refine hfac.symm.trans ?_
  show (N.ι.val.app (op U)).hom ((idealActionLift J F N h).val.app (op U) z) = 0
  rw [hz, map_zero]

end Stacks.Algebraization

end

end
