module

public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.LocalProduct

/-!
# Cancelling an invertible sheaf of modules out of a tensor product

An invertible `𝒪_X`-module can be cancelled from a tensor product: a morphism which becomes an
isomorphism after tensoring with an invertible module was one already, and a product of local
sections which does not vanish at a point has both factors non-vanishing there. This file proves
both statements.

## Main definitions

* `Stacks.InvertibleTensorCancel.tensorInvIsoLeft` and
  `Stacks.InvertibleTensorCancel.tensorInvIsoRight`: `P^{⊗ -1} ⊗ P ≅ 𝒪_X` and
  `P ⊗ P^{⊗ -1} ≅ 𝒪_X` for an invertible `P`.
* `Stacks.InvertibleTensorCancel.mulIso`: the multiplication isomorphism
  `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` in the monoidal category `X.Modules`.

## Main results

* `Stacks.InvertibleTensorCancel.isIso_of_isIso_whiskerLeft` and
  `Stacks.InvertibleTensorCancel.isIso_of_isIso_whiskerRight`: in a monoidal category, tensoring
  with an object that has a tensor inverse reflects isomorphisms.
* `Stacks.InvertibleTensorCancel.isIso_of_isIso_whiskerLeft_modules` and
  `Stacks.InvertibleTensorCancel.isIso_of_isIso_whiskerRight_modules`: tensoring with an
  invertible `𝒪_X`-module reflects isomorphisms.
* `Stacks.InvertibleTensorCancel.localMul_eq_tensorSection`: the product of two local sections of
  integer tensor powers is the image of their pure tensor under `mulIso`.
* `Stacks.InvertibleTensorCancel.nonvanishingLocusOn_localMul`: `U_{y · z} = U_y ∩ U_z` for two
  local sections of integer tensor powers over one open `U`.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open Stacks.SectionTensorFormula (tensorSection)
open Stacks.TensorPowerDivision (localMul)

universe u

namespace Stacks.InvertibleTensorCancel

/-! ### Cancelling a tensor-invertible object in a monoidal category -/

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Tensoring on the left with an object that has a tensor inverse reflects isomorphisms: if
`Q ⊗ P ≅ 𝟙_ C` and `P ◁ φ` is an isomorphism, then `φ` is one. -/
theorem isIso_of_isIso_whiskerLeft {P Q : C} (e : Q ⊗ P ≅ 𝟙_ C) {M N : C} (φ : M ⟶ N)
    (h : IsIso (P ◁ φ)) : IsIso φ := by
  have : IsIso ((Q ⊗ P) ◁ φ) := by rw [tensor_whiskerLeft]; infer_instance
  have : IsIso (𝟙_ C ◁ φ) := by
    have hy : inv (e.hom ▷ M) ≫ ((Q ⊗ P) ◁ φ ≫ e.hom ▷ N) = 𝟙_ C ◁ φ := by
      rw [whisker_exchange e.hom φ, IsIso.inv_hom_id_assoc]
    exact hy ▸ inferInstance
  exact (id_whiskerLeft_symm φ).symm ▸
    (inferInstance : IsIso ((λ_ M).inv ≫ 𝟙_ C ◁ φ ≫ (λ_ N).hom))

/-- Tensoring on the right with an object that has a tensor inverse reflects isomorphisms: if
`P ⊗ Q ≅ 𝟙_ C` and `φ ▷ P` is an isomorphism, then `φ` is one. -/
theorem isIso_of_isIso_whiskerRight {P Q : C} (e : P ⊗ Q ≅ 𝟙_ C) {M N : C} (φ : M ⟶ N)
    (h : IsIso (φ ▷ P)) : IsIso φ := by
  have : IsIso (φ ▷ (P ⊗ Q)) := by rw [whiskerRight_tensor]; infer_instance
  have : IsIso (φ ▷ 𝟙_ C) := by
    have hy : inv (M ◁ e.hom) ≫ (φ ▷ (P ⊗ Q) ≫ N ◁ e.hom) = φ ▷ 𝟙_ C := by
      rw [← whisker_exchange φ e.hom, IsIso.inv_hom_id_assoc]
    exact hy ▸ inferInstance
  exact (whiskerRight_id_symm φ).symm ▸
    (inferInstance : IsIso ((ρ_ M).inv ≫ φ ▷ 𝟙_ C ≫ (ρ_ N).hom))

/-! ### The tensor inverse of an invertible `𝒪_X`-module -/

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

/-- `P^{⊗ -1} ⊗ P ≅ 𝒪_X` for an invertible `𝒪_X`-module `P`. -/
def tensorInvIsoLeft {X : Scheme.{u}} (P : X.Modules) [Stacks.Ample.IsInvertibleModule X P] :
    Stacks.Ample.tensorPowModule X P (-1) ⊗ P ≅ 𝟙_ X.Modules :=
  whiskerLeftIso (Stacks.Ample.tensorPowModule X P (-1))
      (Stacks.Ample.tensorPowModuleOneIso X P).symm ≪≫
    Stacks.AmpleEventualGeneration.tensorPowAdd (by ring : (-1 : ℤ) + 1 = 0) ≪≫
    Stacks.Ample.tensorPowModuleZeroIso X P ≪≫ Stacks.Ample.unitModuleIsoTensorUnit X

/-- `P ⊗ P^{⊗ -1} ≅ 𝒪_X` for an invertible `𝒪_X`-module `P`. -/
def tensorInvIsoRight {X : Scheme.{u}} (P : X.Modules) [Stacks.Ample.IsInvertibleModule X P] :
    P ⊗ Stacks.Ample.tensorPowModule X P (-1) ≅ 𝟙_ X.Modules :=
  whiskerRightIso (Stacks.Ample.tensorPowModuleOneIso X P).symm
      (Stacks.Ample.tensorPowModule X P (-1)) ≪≫
    Stacks.AmpleEventualGeneration.tensorPowAdd (by ring : (1 : ℤ) + -1 = 0) ≪≫
    Stacks.Ample.tensorPowModuleZeroIso X P ≪≫ Stacks.Ample.unitModuleIsoTensorUnit X

/-- Tensoring on the left with an invertible `𝒪_X`-module reflects isomorphisms. -/
theorem isIso_of_isIso_whiskerLeft_modules {X : Scheme.{u}} (P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] {M N : X.Modules} (φ : M ⟶ N)
    (h : IsIso (P ◁ φ)) : IsIso φ :=
  isIso_of_isIso_whiskerLeft (tensorInvIsoLeft P) φ h

/-- Tensoring on the right with an invertible `𝒪_X`-module reflects isomorphisms. -/
theorem isIso_of_isIso_whiskerRight_modules {X : Scheme.{u}} (P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] {M N : X.Modules} (φ : M ⟶ N)
    (h : IsIso (φ ▷ P)) : IsIso φ :=
  isIso_of_isIso_whiskerRight (tensorInvIsoRight P) φ h

/-! ### Cancelling an invertible factor from a product of local sections -/

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- An invertible `𝒪_X`-module in the sense of `Stacks.Ample.IsInvertibleModule` is invertible
in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
local instance schemeStacksIsInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
  Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L

/-- An isomorphism of `𝒪_X`-modules is inverted on the sections over any open. -/
theorem app_inv_app {M N : X.Modules} (e : M ≅ N) (W : X.Opens) (s : Γ(M, W)) :
    e.inv.app W (e.hom.app W s) = s := by
  have h : e.hom.app W ≫ e.inv.app W = 𝟙 Γ(M, W) := by
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  exact ConcreteCategory.congr_hom h s

/-- The sheafified sectionwise tensor product `L^{⊗ n} ⊗ L^{⊗ m}`, as an object of
`X.Modules`. -/
abbrev sheafTensorPow (n m : ℤ) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).obj
      (tensorPowerModule X L n)).obj (tensorPowerModule X L m)

/-- The multiplication isomorphism `Stacks.SheafOfModules.TensorPower.coherentMulIso`, with
source `Stacks.InvertibleTensorCancel.sheafTensorPow`. -/
abbrev powMulIso (n m : ℤ) : sheafTensorPow L n m ≅ tensorPowerModule X L (n + m) :=
  Stacks.SheafOfModules.TensorPower.coherentMulIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n m

/-- `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` for `L^{⊗ n}` and `L^{⊗ m}`, with source
`Stacks.InvertibleTensorCancel.sheafTensorPow`. -/
abbrev powTensorIso (n m : ℤ) :
    sheafTensorPow L n m ≅ (tensorPowerModule X L n ⊗ tensorPowerModule X L m : X.Modules) :=
  Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (tensorPowerModule X L n) (tensorPowerModule X L m)

/-- The multiplication isomorphism `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` in the monoidal category
`X.Modules`. -/
def mulIso (n m : ℤ) :
    (tensorPowerModule X L n ⊗ tensorPowerModule X L m : X.Modules) ≅
      tensorPowerModule X L (n + m) :=
  (powTensorIso L n m).symm ≪≫ powMulIso L n m

/-- The image of the pure tensor `y ⊗ z` in the sheafified sectionwise tensor product. -/
def commonSection (n m : ℤ) {W : X.Opens} (y : Γ(tensorPowerModule X L n, W))
    (z : Γ(tensorPowerModule X L m, W)) : Γ(sheafTensorPow L n m, W) :=
  Stacks.SheafOfModules.tensorSectionsAt X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op W)
    (tensorPowerModule X L n) (tensorPowerModule X L m) y z

/-- The product of two local sections of integer tensor powers is the image of
`Stacks.InvertibleTensorCancel.commonSection` under the multiplication isomorphism. -/
theorem localMul_eq (n m : ℤ) {W : X.Opens} (y : Γ(tensorPowerModule X L n, W))
    (z : Γ(tensorPowerModule X L m, W)) :
    localMul L y z = (powMulIso L n m).hom.app W (commonSection L n m y z) :=
  rfl

/-- The pure tensor of two local sections is the image of `commonSection` under
`powTensorIso`. -/
theorem tensorSection_eq (n m : ℤ) {W : X.Opens} (y : Γ(tensorPowerModule X L n, W))
    (z : Γ(tensorPowerModule X L m, W)) :
    tensorSection (tensorPowerModule X L n) (tensorPowerModule X L m) y z =
      (powTensorIso L n m).hom.app W (commonSection L n m y z) :=
  rfl

/-- The product of two local sections of integer tensor powers is the image of their pure tensor
under the multiplication isomorphism `Stacks.InvertibleTensorCancel.mulIso`. -/
theorem localMul_eq_tensorSection (n m : ℤ) {W : X.Opens}
    (y : Γ(tensorPowerModule X L n, W)) (z : Γ(tensorPowerModule X L m, W)) :
    localMul L y z = (mulIso L n m).hom.app W
      (tensorSection (tensorPowerModule X L n) (tensorPowerModule X L m) y z) := by
  rw [tensorSection_eq L n m y z, localMul_eq L n m y z]
  show _ = (powMulIso L n m).hom.app W ((powTensorIso L n m).inv.app W
    ((powTensorIso L n m).hom.app W (commonSection L n m y z)))
  rw [app_inv_app]

/-- For two local sections `y` and `z` of integer tensor powers over one open, the nonvanishing
locus of their product is the intersection of the nonvanishing loci of `y` and of `z`. -/
theorem nonvanishingLocusOn_localMul (n m : ℤ) (W : X.Opens)
    (y : Γ(tensorPowerModule X L n, W)) (z : Γ(tensorPowerModule X L m, W)) :
    nonvanishingLocusOn (tensorPowerModule X L (n + m)) W (localMul L y z) =
      nonvanishingLocusOn (tensorPowerModule X L n) W y ∩
        nonvanishingLocusOn (tensorPowerModule X L m) W z := by
  rw [localMul_eq_tensorSection L n m y z,
    Stacks.SectionPowerOverOpen.nonvanishingLocusOn_congr,
    Stacks.SectionPowerOverOpen.nonvanishingLocusOn_tensorSection]

end Stacks.InvertibleTensorCancel

end
