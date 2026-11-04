module

public import StacksFrontier.AlgebraicGeometry.DeRham.MixedTensorBaseChangeUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetMixedTensor

/-!
# The identity of [Stacks, Tag 08DE] at the binders of Section 0FMK, on pure tensors

`Stacks.DeRhamSmooth.gradedSourceMixedTensorIso` identifies, for a sheaf `F` of `𝒪_X`-modules,

`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|_{f^{-1}𝒪_Y}  ≅  (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|_{f^{-1}𝒪_Y}`.

**This file computes it on the image of a pure tensor**: `y ⊗ a ↦ c(y) ⊗ a`, with
`c : f^{-1}Ω^k_{Y/S} ⟶ (f^*Ω^k_{Y/S})|_{f^{-1}𝒪_Y}` the comparison
`Stacks.DeRhamSmooth.targetFormsToPullback`. That is what lets a morphism which is linear over
`f^{-1}𝒪_Y` but not over `𝒪_X` — the relative de Rham differential of `f` — be carried across
the identity, which its naturality (`Stacks.DeRhamSmooth.gradedSourceMixedTensorIso_naturality`,
for `𝒪_X`-linear maps only) cannot do.

## Main definitions

* `Stacks.DeRhamSmooth.targetFormsToPullback`: the comparison `f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S}`
  through which the identity acts.

## Main results

* `Stacks.FlatChangeOfRings.sheafTensorSymmIso_hom_val_app_toSheafifyVal`: the symmetry of the
  tensor product on the image of a pure tensor.
* `Stacks.DeRhamSmooth.gradedSourceMixedTensorIso_hom_val_app_toSheafifyVal`: **the identity of
  [Stacks, Tag 08DE] on the image of a pure tensor.**
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.MixedDerivedTensor
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace
open StacksPullbackFactorization

universe u v w

namespace Stacks.FlatChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

open scoped TensorProduct in
/-- **The symmetry of the tensor product sheaf on the image of a pure tensor**: `b ⊗ a ↦ a ⊗ b`.
It is the sheafification of the objectwise symmetry, and sheafification carries the image of a
section to the image of its value. -/
theorem sheafTensorSymmIso_hom_val_app_toSheafifyVal (O : Sheaf J CommRingCat.{w})
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (b : B.val.obj U) (a : A.val.obj U) :
    ((sheafTensorSymmIso O A B).hom.val.app U).hom
        ((toSheafifyVal (tensorObj B.val A.val)).app U (b ⊗ₜ[O.obj.obj U] a)) =
      (toSheafifyVal (tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b) :=
  moduleSheafification_map_val_app_toSheafifyVal (O := O) (tensorObjCommOf O B.val A.val).hom U _

end Stacks.FlatChangeOfRings

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The comparison `f^{-1}Ω^k_{Y/S} ⟶ (f^*Ω^k_{Y/S})|_{f^{-1}𝒪_Y}`** through which the identity
of [Stacks, Tag 08DE] acts on the forms of the target: the unit of the extension of scalars along
`f^{-1}𝒪_Y ⟶ 𝒪_X`, followed by the identification of that extension with `f^*`. It is
`Stacks.Cohomology.MixedDerivedTensor.inverseImageToPullbackTopos` at the topos presentation of
`f`, whose spellings are those of Section 50.12 by `rfl`. -/
def targetFormsToPullback (k : ℕ) :
    pulledBackTargetForms f g k ⟶
      (pushforward (toInverseImageBase f)).obj ((Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) :=
  inverseImageToPullbackTopos (ringedToposSiteHom f.toLRSHom.toShHom)
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))

open scoped TensorProduct in
/-- **`Stacks.DeRhamSmooth.targetFormsMixedTensorIso` on the image of a pure tensor**:
`a ⊗ y ↦ a ⊗ c(y)`. This is
`underivedTensorInverseImageLinearIso_hom_app_val_app_toSheafifyVal`
at the topos presentation of `f`. -/
theorem targetFormsMixedTensorIso_hom_val_app_toSheafifyVal (k : ℕ) (F : Modules X.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ) (a : F.val.obj U) (y : (pulledBackTargetForms f g k).val.obj U) :
    ((targetFormsMixedTensorIso f g k F).hom.val.app U).hom
        ((toSheafifyVal (tensorObj ((pushforward (toInverseImageBase f)).obj F).val
          (pulledBackTargetForms f g k).val)).app U
            (a ⊗ₜ[(inverseImageBase f).sheaf.obj.obj U] y)) =
      (toSheafifyVal (tensorObj F.val ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val)).app U
        (a ⊗ₜ[X.sheaf.obj.obj U] ((targetFormsToPullback f g k).val.app U).hom y) :=
  underivedTensorInverseImageLinearIso_hom_app_val_app_toSheafifyVal
    (ringedToposSiteHom f.toLRSHom.toShHom)
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) F U a y

open scoped TensorProduct in
/-- **[Stacks, Tag 08DE] at the binders of Section 0FMK, on the image of a pure tensor**: for a
section `y` of `f^{-1}Ω^k_{Y/S}` and a section `a` of a sheaf `F` of `𝒪_X`-modules,

`y ⊗_{f^{-1}𝒪_Y} a  ↦  c(y) ⊗_{𝒪_X} a`,

`c` the comparison `Stacks.DeRhamSmooth.targetFormsToPullback`. The identity is the symmetry of
the tensor product on either side of
`Stacks.DeRhamSmooth.targetFormsMixedTensorIso`, and all three act on the image of a pure tensor
through its entries. -/
theorem gradedSourceMixedTensorIso_hom_val_app_toSheafifyVal (k : ℕ) (F : Modules X.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ) (y : (pulledBackTargetForms f g k).val.obj U) (a : F.val.obj U) :
    ((gradedSourceMixedTensorIso f g k F).hom.val.app U).hom
        ((toSheafifyVal (tensorObj (pulledBackTargetForms f g k).val
          ((pushforward (toInverseImageBase f)).obj F).val)).app U
            (y ⊗ₜ[(inverseImageBase f).sheaf.obj.obj U] a)) =
      (toSheafifyVal (tensorObj ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val F.val)).app U
        (((targetFormsToPullback f g k).val.app U).hom y ⊗ₜ[X.sheaf.obj.obj U] a) := by
  refine Eq.trans (congrArg (fun z =>
      (((pushforward (toInverseImageBase f)).map (pullbackFormsTensorSymmIso f g k F).hom).val.app
        U).hom (((targetFormsMixedTensorIso f g k F).hom.val.app U).hom z))
    (Stacks.FlatChangeOfRings.sheafTensorSymmIso_hom_val_app_toSheafifyVal
      (inverseImageBase f).sheaf ((pushforward (toInverseImageBase f)).obj F)
      (pulledBackTargetForms f g k) U y a)) ?_
  refine Eq.trans (congrArg (fun z =>
      (((pushforward (toInverseImageBase f)).map (pullbackFormsTensorSymmIso f g k F).hom).val.app
        U).hom z)
    (targetFormsMixedTensorIso_hom_val_app_toSheafifyVal f g k F U a y)) ?_
  exact Stacks.FlatChangeOfRings.sheafTensorSymmIso_hom_val_app_toSheafifyVal X.sheaf
    ((Scheme.Modules.pullback f).obj
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F U a _

end Stacks.DeRhamSmooth

end
