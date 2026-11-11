module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.Blowup.AlmostExactness
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf

/-!
# Twisting down on a blowup and the modules supported on a thickening of the exceptional divisor

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `b : B → X` the blowup of
`X` in `ℐ`, with exceptional divisor `Y`, an effective Cartier divisor whose ideal sheaf is
`ℐ𝒪_B`. The twists of the structure sheaf of the blowup satisfy `𝒪_B(-1) = 𝒪_B(Y)`, so
`𝒪_B(c)` is the ideal sheaf of the `c`-fold thickening `Y_c = cY`, which is `(ℐ𝒪_B)^c`.
Twisting a module down by `c` is therefore multiplication by that ideal sheaf: the canonical map
`𝓕(c) = 𝓕 ⊗ (ℐ𝒪_B)^c ⟶ 𝓕` induced by the inclusion of `(ℐ𝒪_B)^c` into `𝒪_B`.

This file constructs that map and proves that it vanishes exactly when `𝓕` is scheme
theoretically supported on `Y_c`.

## Main definitions

* `AlgebraicGeometry.exceptionalTwistInclusion` — the inclusion `𝒪_B(c) ⟶ 𝒪_B` of the ideal
  sheaf of the `c`-fold thickening of the exceptional divisor into the structure sheaf.
* `AlgebraicGeometry.exceptionalTwistContraction` — the canonical map `𝓕(c) ⟶ 𝓕` obtained from
  it by tensoring with `𝓕`.

## Main results

* `AlgebraicGeometry.exceptionalTwistContraction_app_tmul` — on a local pure tensor the
  canonical map is multiplication by the image of the twisting factor in `𝒪_B`.
* `AlgebraicGeometry.schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero` — a
  quasi-coherent module of finite type on the blowup is scheme theoretically supported on `Y_c`
  if and only if the map `𝓕 ⊗ (ℐ𝒪_B)^c ⟶ 𝓕` is zero; the form of [Stacks, Tag 0GA9] with the
  Serre twist itself is in `StacksFrontier/AlgebraicGeometry/Blowup/TwistExceptionalIdealPow.lean`.

## Implementation notes

What is written `𝒪_B(c)` here is the ideal sheaf `(ℐ𝒪_B)^c` of `Y_c`, realized as the degree-`c`
piece `Stacks.Blowup.idealPowerKernel` of the Rees algebra of the exceptional ideal sheaf. The
twists themselves exist: the graded twists of a relative `Proj`, [Stacks, Tag 01NR], are
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, and the twist
`𝒪_B(n)` on the blowup itself is `AlgebraicGeometry.blowUpTwist`, which is invertible in every
degree. The identification `𝒪_B(c) ≅ (ℐ𝒪_B)^c` is
`AlgebraicGeometry.blowUpTwistIsoExceptionalIdealPow` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwistExceptionalIdealPow.lean`, which imports this file and
carries the statement over to `AlgebraicGeometry.blowUpTwist`; nothing in this file depends on
it. In particular the map `𝓕 ⟶ 𝓕(c)` of the Stacks statement is read
in the direction in which the map exists: `(ℐ𝒪_B)^c` is an ideal sheaf, so it maps to `𝒪_B` and
not conversely, and the Stacks proof uses exactly that map, which it describes as vanishing
along `Y`.

Scheme theoretic support is recorded by `AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport`
of [Stacks, Tag 05JU]; for a quasi-coherent module of finite type it is the annihilator ideal
sheaf, which is the form the proof uses. The hypothesis on the annihilator ideal sheaf is carried
only by the affine opens, while the vanishing of the canonical map is a statement about every
open, so the two are matched up by the sheaf property of `𝓕` over an affine cover.

The monoidal structure on `X.Modules` is `Stacks.SheafOfModules.OnSpace.monoidal`, whose tensor
product is the sheafified tensor product and whose unit is the structure sheaf, both on the
nose, and whose structural morphisms are evaluated on local pure tensors. It is activated as a
local instance, since a global monoidal instance on sheaves of modules is not wanted.

## References

* [Stacks Project, Tag 0GA9](https://stacks.math.columbia.edu/tag/0GA9)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open Stacks.Blowup Stacks.SheafOfModules.OnSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

universe u

/-- The sheaves of modules on a scheme with the sheafified tensor product: the tensor product is
the sheafified tensor product and the unit is the structure sheaf. -/
@[sga "4 IV 12.7" "special case"]
local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData) (c : ℕ)

/-- The inclusion `𝒪_B(c) ⟶ 𝒪_B` of the ideal sheaf of the `c`-fold thickening of the
exceptional divisor of a blowup into the structure sheaf. -/
def exceptionalTwistInclusion : idealPowerKernel (exceptionalIdeal ℐ) c ⟶
    SheafOfModules.unit (blowUp ℐ).ringCatSheaf :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    ((exceptionalIdeal ℐ ^ c).subschemeι.toRingCatSheafHom))

/-- The canonical map `𝓕(c) ⟶ 𝓕` on the blowup of a scheme in a quasi-coherent sheaf of
ideals: the inclusion of the ideal sheaf of the `c`-fold thickening of the exceptional divisor
into `𝒪_B`, tensored with `𝓕`. -/
def exceptionalTwistContraction (F : (blowUp ℐ).Modules) :
    F ⊗ idealPowerKernel (exceptionalIdeal ℐ) c ⟶ F :=
  (F ◁ exceptionalTwistInclusion ℐ c) ≫ (ρ_ F).hom

/-- The canonical map `𝓕(c) ⟶ 𝓕` on a local pure tensor: the twisting factor is pushed into
`𝒪_B` and the right unitor then multiplies by it. -/
theorem exceptionalTwistContraction_app_tmul (F : (blowUp ℐ).Modules) (U : (blowUp ℐ).Opens)
    (s : F.val.obj (op U)) (x : (idealPowerKernel (exceptionalIdeal ℐ) c).val.obj (op U)) :
    ((exceptionalTwistContraction ℐ c F).val.app (op U)).hom
        (tensorObjTmul (blowUp ℐ).toRingedSpace F
          (idealPowerKernel (exceptionalIdeal ℐ) c) (op U) s x) =
      ((ρ_ F).hom.val.app (op U)).hom
        (tensorObjTmul (blowUp ℐ).toRingedSpace F
          (SheafOfModules.unit (blowUp ℐ).ringCatSheaf) (op U) s
          (((exceptionalTwistInclusion ℐ c).val.app (op U)).hom x)) :=
  congrArg (fun t => ((ρ_ F).hom.val.app (op U)).hom t)
    (whiskerLeft_tmul (blowUp ℐ).toRingedSpace F (exceptionalTwistInclusion ℐ c) (op U) s x)

/-- The canonical map `𝓕(c) ⟶ 𝓕` on a local pure tensor is the scalar multiplication by the image
of the twisting factor in `𝒪_B`. -/
private theorem exceptionalTwistContraction_app_tmul_eq_smul (F : (blowUp ℐ).Modules)
    (U : (blowUp ℐ).Opens) (s : F.val.obj (op U))
    (x : (idealPowerKernel (exceptionalIdeal ℐ) c).val.obj (op U)) :
    ((exceptionalTwistContraction ℐ c F).val.app (op U)).hom
        (tensorObjTmul (blowUp ℐ).toRingedSpace F
          (idealPowerKernel (exceptionalIdeal ℐ) c) (op U) s x) =
      (show (blowUp ℐ).ringCatSheaf.obj.obj (op U) from
        ((exceptionalTwistInclusion ℐ c).val.app (op U)).hom x) • s :=
  (exceptionalTwistContraction_app_tmul ℐ c F U s x).trans
    (rightUnitor_tmul (blowUp ℐ).toRingedSpace F (op U) s _)

/-- A section of the ideal sheaf of `Y_c` kills every local section of a module whose
annihilator ideal sheaf contains that ideal sheaf. The hypothesis is carried by the affine
opens only; vanishing of a section is a local condition, which is what extends it to every
open. -/
private theorem twistSection_smul_eq_zero (F : (blowUp ℐ).Modules)
    (h : exceptionalIdeal ℐ ^ c ≤ Scheme.Modules.annihilatorIdeal F) (U : (blowUp ℐ).Opens)
    (x : (idealPowerKernel (exceptionalIdeal ℐ) c).val.obj (op U))
    (a : (blowUp ℐ).ringCatSheaf.obj.obj (op U))
    (ha : ((exceptionalTwistInclusion ℐ c).val.app (op U)).hom x = a)
    (s : F.val.obj (op U)) : a • s = 0 := by
  have haff : ∀ V : (blowUp ℐ).affineOpens,
      (exceptionalIdeal ℐ).ideal V ^ c ≤ Module.annihilator Γ(blowUp ℐ, V.1) Γ(F, V.1) := by
    intro V
    have hle := Scheme.IdealSheafData.le_ofIdeals_iff.1 h V
    rwa [Scheme.IdealSheafData.ideal_pow] at hle
  apply TopCat.Presheaf.IsSheaf.section_ext (X := (blowUp ℐ).toTopCat)
    (A := AddCommGrpCat.{u}) (F := F.val.presheaf) (U := op U) (s := a • s) (t := 0) F.isSheaf
  intro z hz
  obtain ⟨V, ⟨V₀, hV₀, rfl⟩, hzV, hVU⟩ :=
    (blowUp ℐ).isBasis_affineOpens.exists_subset_of_mem_open hz U.2
  refine ⟨V₀, hVU, hzV, ?_⟩
  have hamb : reesPieceAmbient (exceptionalIdeal ℐ) (c : ℤ) V₀
        (ConcreteCategory.hom
          ((reesPiece (exceptionalIdeal ℐ) (c : ℤ)).val.map (homOfLE hVU).op) x) =
      (blowUp ℐ).presheaf.map (homOfLE hVU).op
        (reesPieceAmbient (exceptionalIdeal ℐ) (c : ℤ) U x) :=
    reesPieceAmbient_restrict (exceptionalIdeal ℐ) (c : ℤ) V₀ U hVU x
  have hmem : reesPieceAmbient (exceptionalIdeal ℐ) (c : ℤ) V₀
      (ConcreteCategory.hom
        ((reesPiece (exceptionalIdeal ℐ) (c : ℤ)).val.map (homOfLE hVU).op) x) ∈
      (exceptionalIdeal ℐ).ideal ⟨V₀, hV₀⟩ ^ c :=
    reesPieceAmbient_mem_affine (exceptionalIdeal ℐ) (c : ℤ) (Int.natCast_nonneg c)
      ⟨V₀, hV₀⟩ _
  have hmem' : (blowUp ℐ).ringCatSheaf.obj.map (homOfLE hVU).op a ∈
      (exceptionalIdeal ℐ).ideal ⟨V₀, hV₀⟩ ^ c := by
    have hrw : (blowUp ℐ).ringCatSheaf.obj.map (homOfLE hVU).op a =
        reesPieceAmbient (exceptionalIdeal ℐ) (c : ℤ) V₀
          (ConcreteCategory.hom
            ((reesPiece (exceptionalIdeal ℐ) (c : ℤ)).val.map (homOfLE hVU).op) x) :=
      (hamb.trans (congrArg (fun t => (blowUp ℐ).presheaf.map (homOfLE hVU).op t) ha)).symm
    exact hrw ▸ hmem
  have hkill : ((blowUp ℐ).ringCatSheaf.obj.map (homOfLE hVU).op a) •
      F.val.map (homOfLE hVU).op s = 0 :=
    Module.mem_annihilator.1 (haff ⟨V₀, hV₀⟩ hmem') _
  have hstep : F.val.map (homOfLE hVU).op (a • s) =
      ((blowUp ℐ).ringCatSheaf.obj.map (homOfLE hVU).op a) •
        F.val.map (homOfLE hVU).op s := F.val.map_smul _ _ _
  exact hstep.trans (hkill.trans (map_zero
    (ConcreteCategory.hom (F.val.presheaf.map (homOfLE hVU).op))).symm)

/-- The canonical map `𝓕(c) ⟶ 𝓕` vanishes as soon as the annihilator ideal sheaf of `𝓕`
contains the ideal sheaf of `Y_c`. -/
private theorem exceptionalTwistContraction_eq_zero_of_le_annihilatorIdeal (F : (blowUp ℐ).Modules)
    (h : exceptionalIdeal ℐ ^ c ≤ Scheme.Modules.annihilatorIdeal F) :
    exceptionalTwistContraction ℐ c F = 0 := by
  refine tensor_hom_ext (X := (blowUp ℐ).toRingedSpace) (A := F)
    (B := idealPowerKernel (exceptionalIdeal ℐ) c) fun U a b => ?_
  have hzero : ((exceptionalTwistContraction ℐ c F).val.app U).hom
      (tensorObjTmul (blowUp ℐ).toRingedSpace F
        (idealPowerKernel (exceptionalIdeal ℐ) c) U a b) = 0 :=
    (exceptionalTwistContraction_app_tmul_eq_smul ℐ c F U.unop a b).trans
      (twistSection_smul_eq_zero ℐ c F h U.unop b _ rfl a)
  exact hzero.trans (map_zero (ConcreteCategory.hom
    ((0 : F ⊗ idealPowerKernel (exceptionalIdeal ℐ) c ⟶ F).val.app U))).symm

/-- If the canonical map `𝓕(c) ⟶ 𝓕` vanishes, the annihilator ideal sheaf of `𝓕` contains
the ideal sheaf of `Y_c`. -/
private theorem le_annihilatorIdeal_of_exceptionalTwistContraction_eq_zero (F : (blowUp ℐ).Modules)
    (h : exceptionalTwistContraction ℐ c F = 0) :
    exceptionalIdeal ℐ ^ c ≤ Scheme.Modules.annihilatorIdeal F := by
  rw [Scheme.Modules.annihilatorIdeal, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U
  rw [Scheme.IdealSheafData.ideal_pow]
  intro a ha
  rw [Module.mem_annihilator]
  intro s
  set x : (idealPowerKernel (exceptionalIdeal ℐ) c).val.obj (op U.1) :=
    (reesPieceAffineEquiv (exceptionalIdeal ℐ) (c : ℤ) (Int.natCast_nonneg c) U).symm
      ⟨a, ha⟩ with hxdef
  have hx : ((exceptionalTwistInclusion ℐ c).val.app (op U.1)).hom x = a := by
    have hco := reesPieceAffineEquiv_coe (exceptionalIdeal ℐ) (c : ℤ)
      (Int.natCast_nonneg c) U x
    rw [hxdef, AddEquiv.apply_symm_apply] at hco
    exact hco.symm
  have hval := exceptionalTwistContraction_app_tmul_eq_smul ℐ c F U.1 s x
  have hzero : ((exceptionalTwistContraction ℐ c F).val.app (op U.1)).hom
      (tensorObjTmul (blowUp ℐ).toRingedSpace F
        (idealPowerKernel (exceptionalIdeal ℐ) c) (op U.1) s x) = 0 := by
    rw [h]
    exact map_zero (ConcreteCategory.hom
      ((0 : F ⊗ idealPowerKernel (exceptionalIdeal ℐ) c ⟶ F).val.app (op U.1)))
  rw [← hx]
  exact hval.symm.trans hzero

/-- **The ideal sheaf form of [Stacks, Tag 0GA9].** A quasi-coherent module of finite type on
the blowup of a scheme in a quasi-coherent sheaf of ideals is scheme theoretically supported on
the `c`-fold thickening `Y_c` of the exceptional divisor if and only if the map
`𝓕 ⊗ (ℐ𝒪_B)^c ⟶ 𝓕` induced by the inclusion of the ideal sheaf of `Y_c` vanishes.

The tag itself, stated for the Serre twist `𝓕(c) = 𝓕 ⊗ 𝒪_B(c)` and the canonical map
`𝒪_B(c) ⟶ 𝒪_B`, is `AlgebraicGeometry.schemeTheoreticSupport_iff_blowUpTwistContraction_eq_zero`
in `StacksFrontier/AlgebraicGeometry/Blowup/TwistExceptionalIdealPow.lean`, which deduces it from
this statement through the identification `𝒪_B(c) ≅ (ℐ𝒪_B)^c`. -/
theorem schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero
    (F : (blowUp ℐ).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    exceptionalIdeal ℐ ^ c ≤ Scheme.Modules.schemeTheoreticSupport F ↔
      exceptionalTwistContraction ℐ c F = 0 := by
  rw [← Scheme.Modules.annihilatorIdeal_eq_schemeTheoreticSupport F]
  exact ⟨exceptionalTwistContraction_eq_zero_of_le_annihilatorIdeal ℐ c F,
    le_annihilatorIdeal_of_exceptionalTwistContraction_eq_zero ℐ c F⟩

end AlgebraicGeometry

end
