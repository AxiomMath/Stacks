module

public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Integer
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.UnitShiftSectionTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections

/-!
# The product of two global sections of integer tensor powers is the Laurent multiplication

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. On global sections of the integer tensor
powers `Stacks.AmpleProjectiveImmersion.tensorPowerModule` of [Stacks, Tag 01CU], the product
`Stacks.TensorPowerDivision.intMulSections` (multiplication by the first factor, read as a
morphism `L ^⊗ n ⟶ L ^⊗ (k + n)` of `𝒪_X`-modules, applied to the second) is the multiplication
`Stacks.SheafOfModules.TensorPower.mulBilinear` of the Laurent algebra of [Stacks, Tag 01CU].

## Main results

* `Stacks.TensorPowerDivision.monoidalMulIso_whiskerRight_val_app`: the composite
  `L ^⊗ n ⟶ 𝟙 ⊗ L ^⊗ n ⟶ L ^⊗ k ⊗ L ^⊗ n ⟶ L ^⊗ (k + n)`, whose middle map is a global section
  of `L ^⊗ k` whiskered on the right, acts on a local section as the multiplication of the
  Laurent algebra against that global section.
* `Stacks.TensorPowerDivision.intMulMap_val_app`: the same for a scheme, with the composite named
  as `Stacks.TensorPowerDivision.intMulMap`.
* `Stacks.TensorPowerDivision.intMulSections_eq_mulBilinear`: the product of two global sections
  of integer tensor powers is the multiplication of the Laurent algebra of [Stacks, Tag 01CU] on
  those two sections.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (unitIso)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)
open Stacks.SheafOfModules.TensorPower (tensorPower mulBilinear mulBilinear_app monoidalMulIso
  coherentMulIso)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SectionProduct (globalSection)

universe v u w

namespace Stacks.TensorPowerDivision

/-! ### The site half: the whiskered global section, read on a local section -/

section Site

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]

/-- Multiplication by a global section of `L ^⊗ k`, read on a local section of `L ^⊗ n`, is the
multiplication of the Laurent algebra of [Stacks, Tag 01CU]. The composite on the left is the
left unitor, the global section `τ` whiskered on the right by `L ^⊗ n`, and the coherent
multiplication `Stacks.SheafOfModules.TensorPower.monoidalMulIso`; the product on the right is
`Stacks.SheafOfModules.TensorPower.mulBilinear`, against the local section `τ` names over `U`. -/
theorem monoidalMulIso_whiskerRight_val_app (k n : ℤ)
    (τ : 𝟙_ (SheafOfModules.{w} (structureSheaf O hO)) ⟶ tensorPower O hO L k)
    (U : Cᵒᵖ) (v : (tensorPower O hO L n).val.obj U) :
    ((λ_ (tensorPower O hO L n)).inv ≫ (τ ▷ tensorPower O hO L n) ≫
          (monoidalMulIso O hO L k n).hom).val.app U v
      = (mulBilinear O hO L k n).app U
          (((unitIso O hO).inv ≫ τ).val.app U (1 : O.obj U)) v :=
  have hsplit : (λ_ (tensorPower O hO L n)).inv ≫ (τ ▷ tensorPower O hO L n) ≫
        (monoidalMulIso O hO L k n).hom
      = ((λ_ (tensorPower O hO L n)).inv ≫ (τ ▷ tensorPower O hO L n) ≫
            (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L k)
              (tensorPower O hO L n)).hom) ≫
          (coherentMulIso O hO L k n).hom :=
    ((Category.assoc (λ_ (tensorPower O hO L n)).inv
            ((τ ▷ tensorPower O hO L n) ≫
              (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L k)
                (tensorPower O hO L n)).hom)
            (coherentMulIso O hO L k n).hom).trans
        (congrArg (fun φ => (λ_ (tensorPower O hO L n)).inv ≫ φ)
          (Category.assoc (τ ▷ tensorPower O hO L n)
            (Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L k)
              (tensorPower O hO L n)).hom
            (coherentMulIso O hO L k n).hom))).symm
  (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app U v) hsplit).trans
    ((Stacks.SheafOfModules.comp_val_app_apply _ _ U v).trans
      ((congrArg (fun z => (coherentMulIso O hO L k n).hom.val.app U z)
            (Stacks.SheafOfModules.tensorObjIso_hom_val_app_whiskerRight O hO
              (tensorPower O hO L k) (tensorPower O hO L n) τ U v)).trans
        (mulBilinear_app O hO L k n U _ v).symm))

end Site

/-! ### The scheme half: the product of two global sections -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The sheaf condition on the structure presheaf of rings of a scheme. -/
abbrev hStruct (X : Scheme.{u}) : Presheaf.IsSheaf (Opens.grothendieckTopology ↥X)
    (structureRingPresheaf X.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X

/-- An invertible module `L` on a scheme, in the sense of `Stacks.Ample.IsInvertibleModule`, is
invertible in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
local instance schemeStacksIsInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (hStruct X) L :=
  Stacks.PowerFamilyBridge.instIsInvertible X.presheaf (hStruct X) L

/-- `Stacks.TensorPowerDivision.intMulMap` acts on a local section as the multiplication of the
Laurent algebra of [Stacks, Tag 01CU]. -/
theorem intMulMap_val_app {k : ℤ} (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k) (n : ℤ)
    (U : (Opens ↥X)ᵒᵖ) (v : (tensorPowerModule X L n).val.obj U) :
    (intMulMap L τ n).val.app U v
      = (mulBilinear X.presheaf (hStruct X) L k n).app U
          (((unitIso X.presheaf (hStruct X)).inv ≫ τ).val.app U (1 : X.presheaf.obj U)) v :=
  monoidalMulIso_whiskerRight_val_app X.presheaf (hStruct X) L k n τ U v

/-- On global sections, `Stacks.TensorPowerDivision.intMulMap` is the multiplication of the
Laurent algebra against the global section `Stacks.SectionProduct.globalSection` of `τ`. -/
theorem intMulMap_app_globalSection {k : ℤ} (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k) (n : ℤ)
    (v : Γ(tensorPowerModule X L n, ⊤)) :
    (intMulMap L τ n).app ⊤ v
      = (mulBilinear X.presheaf (hStruct X) L k n).app (op ⊤)
          (globalSection X (tensorPowerModule X L k) τ) v :=
  intMulMap_val_app L τ n (op ⊤) v

/-- The product `Stacks.TensorPowerDivision.intMulSections` of two global sections of the integer
tensor powers of [Stacks, Tag 01CU] is their product
`Stacks.SheafOfModules.TensorPower.mulBilinear` in the Laurent algebra over the terminal open. -/
theorem intMulSections_eq_mulBilinear {k n : ℤ} (t : Γ(tensorPowerModule X L k, ⊤))
    (b : Γ(tensorPowerModule X L n, ⊤)) :
    intMulSections L t b
      = (mulBilinear X.presheaf (hStruct X) L k n).app (op ⊤) t b :=
  (intMulMap_app_globalSection L (intSecOf L t) n b).trans
    (congrArg (fun z => (mulBilinear X.presheaf (hStruct X) L k n).app (op ⊤) z b)
      (globalSection_intSecOf L t))

/-! ### Reindexing -/

/-- Reindexing twice along `Stacks.TensorPowerDivision.intPowReindex` is reindexing once. -/
theorem intPowReindex_trans {a b c : ℤ} (h : a = b) (h' : b = c)
    (v : Γ(tensorPowerModule X L a, ⊤)) :
    (intPowReindex L h').hom.app ⊤ ((intPowReindex L h).hom.app ⊤ v)
      = (intPowReindex L (h.trans h')).hom.app ⊤ v := by
  subst h h'; rfl

/-- The product of global sections commutes with reindexing the second factor. -/
theorem intMulSections_intPowReindex {k a b : ℤ} (t : Γ(tensorPowerModule X L k, ⊤))
    (h : a = b) (v : Γ(tensorPowerModule X L a, ⊤)) :
    intMulSections L t ((intPowReindex L h).hom.app ⊤ v)
      = (intPowReindex L (congrArg (fun z => k + z) h)).hom.app ⊤ (intMulSections L t v) := by
  subst h; rfl

end Scheme

end Stacks.TensorPowerDivision

end
