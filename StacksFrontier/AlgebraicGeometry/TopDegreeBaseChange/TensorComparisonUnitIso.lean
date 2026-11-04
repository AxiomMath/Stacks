module

public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonUnitValue

/-!
# The canonical map of Tag 0EX3 (b) is invertible at the structure sheaf of the base

`TensorComparisonUnitValue.lean` computes the canonical map of conclusion (b) of
[Stacks, Tag 0EX3] at `G = 𝒪_Y`: it is the right unitor followed by the `n`-th higher direct
image of `x ↦ x ⊗ η`, where `η` is the global section of `f^* 𝒪_Y` attached by the unit of
`f^* ⊣ f_*` to the unit section of `𝒪_Y`.  This file proves that map **invertible**.

The unitor is invertible by construction, so what has to be seen is that `x ↦ x ⊗ η` is.  That is
where the comparison `f^* 𝒪_Y ≅ 𝒪_X` enters, and with it the one fact about it that matters: it
carries `η` to the unit section of `𝒪_X`.  That fact is proved, as
`Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections` at the unit
section, where the structure morphism of `f` on global sections is a ring map and so sends `1` to
`1`.  Composing `x ↦ x ⊗ η` with `𝟙 ⊗ (f^* 𝒪_Y ≅ 𝒪_X)` therefore gives `x ↦ x ⊗ 1`, which is the
inverse unitor; the comparison in the second factor is invertible, so `x ↦ x ⊗ η` is too.

Nothing is assumed: `f` is an arbitrary morphism of schemes, `F` an arbitrary sheaf of modules on
`X` and `n` an arbitrary degree.  In particular the base `Y` is arbitrary, and this is the base
case the source's Eilenberg–Watts argument for conclusion (b) runs from.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `pullbackUnitIso_hom_unitGlobalSection`: **the comparison `f^* 𝒪_Y ≅ 𝒪_X` carries `η` to the
  unit section.**
* `tensorGlobalSection_unitGlobalSection`: `x ↦ x ⊗ η`, followed by the comparison in the second
  factor, is the inverse right unitor.
* `isIso_tensorGlobalSection_unitGlobalSection`: **`x ↦ x ⊗ η` is invertible**, as an instance.
* `isIso_unitValueMap`: so is its `n`-th higher direct image.
* `isIso_higherDirectImageTensorMap_unitModule`: **the canonical map of conclusion (b) of
  [Stacks, Tag 0EX3] is invertible at `G = 𝒪_Y`**, for an arbitrary morphism of schemes, an
  arbitrary module upstairs and an arbitrary degree.

## Implementation notes

The fact about the comparison is stated through
`Stacks.AlgebraicGeometry.PullbackSections.pullbackUnitSections`, which is the unit of
`f^* ⊣ f_*` read on sections; `unitGlobalSection` is that at the top open, so the two agree by
`rfl` and no bridge is needed.  The other spelling of the same comparison —
`Stacks.PullbackAlgebra.pullbackUnitIso` on a ringed space, where
`Stacks.PullbackAlgebra.pullbackUnitIso_inv_app_one` is the same statement — would need the
crossing between the ringed-space and the scheme module systems, so the scheme-level one is used.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (n : ℕ)

/-! ### The comparison `f^* 𝒪_Y ≅ 𝒪_X` on the unit section -/

/-- **The comparison `f^* 𝒪_Y ≅ 𝒪_X` carries the unit section of `f^* 𝒪_Y` to the unit section
of `𝒪_X`.** The library's statement of the comparison on sections is that it carries the
pullback-unit image of a global function to the image of that function under the structure
morphism of `f`, which is a ring map and so sends `1` to `1`. -/
theorem pullbackUnitIso_hom_unitGlobalSection :
    Scheme.Modules.Hom.app (Scheme.Modules.pullbackUnitIso f).hom ⊤
        (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))) =
      (1 : ↑(X.presheaf.obj (op ⊤))) :=
  (Stacks.AlgebraicGeometry.PicardBaseChange.pullbackUnitIso_hom_pullbackUnitSections f
      (1 : Γ(Y, ⊤))).trans
    (map_one (f.app ⊤).hom)

/-! ### Tensoring with the unit section is invertible -/

/-- **Tensoring with `η`, followed by the comparison `f^* 𝒪_Y ≅ 𝒪_X` in the second factor, is
the inverse right unitor.** -/
theorem tensorGlobalSection_unitGlobalSection :
    tensorGlobalSection F ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
          (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).map
          (Scheme.Modules.pullbackUnitIso f).hom) =
      tensorUnitInv F := by
  rw [tensorGlobalSection_naturality F
      ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
      (Scheme.Modules.pullbackUnitIso f).hom
      (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))),
    pullbackUnitIso_hom_unitGlobalSection f, tensorGlobalSection_unit F]

/-- **Tensoring with `η`, written as the inverse unitor followed by the comparison in the second
factor.** -/
theorem tensorGlobalSection_unitGlobalSection_eq :
    tensorGlobalSection F ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
        (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))) =
      tensorUnitInv F ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).map
          (Scheme.Modules.pullbackUnitIso f).inv) :=
  (Iso.eq_comp_inv (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).mapIso
      (Scheme.Modules.pullbackUnitIso f))).mpr
    (tensorGlobalSection_unitGlobalSection f F)

/-- **Tensoring with `η`, as an isomorphism `F ≅ F ⊗_{𝒪_X} f^* 𝒪_Y`.** -/
def tensorGlobalSectionUnitIso :
    F ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))) :=
  (tensorUnitIso F).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).mapIso
      (Scheme.Modules.pullbackUnitIso f).symm

/-- The isomorphism above is `x ↦ x ⊗ η`. -/
theorem tensorGlobalSectionUnitIso_hom :
    (tensorGlobalSectionUnitIso f F).hom =
      tensorGlobalSection F ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
        (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤)))) :=
  (tensorGlobalSection_unitGlobalSection_eq f F).symm

/-- **Tensoring with `η` is invertible.** -/
instance isIso_tensorGlobalSection_unitGlobalSection :
    IsIso (tensorGlobalSection F ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y))
      (unitGlobalSection f (Scheme.unitModule Y) (1 : ↑(Y.presheaf.obj (op ⊤))))) := by
  rw [← tensorGlobalSectionUnitIso_hom f F]
  exact Iso.isIso_hom _

/-! ### The canonical map at the structure sheaf of the base -/

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3] at `G = 𝒪_Y`, as an
isomorphism.** -/
def higherDirectImageTensorUnitIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (topDirectImage f F n)).obj
          (Scheme.unitModule Y)) ≅
      topDirectImageTensor f F (Scheme.unitModule Y) n :=
  tensorUnitIso (topDirectImage f F n) ≪≫
    ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).mapIso
      (tensorGlobalSectionUnitIso f F)

/-- The isomorphism above is the canonical map of conclusion (b) at `G = 𝒪_Y`. -/
theorem higherDirectImageTensorUnitIso_hom :
    (higherDirectImageTensorUnitIso f F n).hom =
      higherDirectImageTensorMap f F (Scheme.unitModule Y) n := by
  rw [higherDirectImageTensorMap_structureModule f F n]
  change tensorUnitHom (topDirectImage f F n) ≫
    ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
      (tensorGlobalSectionUnitIso f F).hom = _
  rw [tensorGlobalSectionUnitIso_hom f F]

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3] is invertible at
`G = 𝒪_Y`.** For an arbitrary morphism of schemes, an arbitrary sheaf of modules on the source
and an arbitrary degree,

`R^n f_* F ⊗_{𝒪_Y} 𝒪_Y ⟶ R^n f_*(F ⊗_{𝒪_X} f^* 𝒪_Y)`

is an isomorphism.  This is the base case of the source's Eilenberg-Watts argument for
conclusion (b), and it carries no hypothesis at all: the base `Y` is not assumed affine, `F` is
not assumed quasi-coherent and the degree is not assumed to be the top one. -/
instance isIso_higherDirectImageTensorMap_unitModule :
    IsIso (higherDirectImageTensorMap f F (Scheme.unitModule Y) n) := by
  rw [← higherDirectImageTensorUnitIso_hom f F n]
  exact Iso.isIso_hom _

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
