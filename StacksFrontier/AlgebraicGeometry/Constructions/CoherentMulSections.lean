module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.CoherentSectionMul

/-!
# The product of global sections of iterated tensor powers is the Laurent multiplication

Let `𝒪` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `𝒪`-modules.
There are two multiplications on the global sections of the tensor powers of `L`:

* `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`, the product of global sections of
  the iterated tensor products `Stacks.TensorPowers.natTensorPow`, read in the monoidal structure
  `Stacks.SheafInternalHom.monoidalCategory` of sheaves of modules;
* `Stacks.SheafOfModules.TensorPower.mulBilinear`, the multiplication of the Laurent algebra on
  local sections of the integer tensor powers `Stacks.SheafOfModules.TensorPower.tensorPower`.

This file proves that the comparison `L ^⊗ n ≅ L^{⊗ n}` carries the first to the second. The
iterated tensor powers are compared in the two localized monoidal structures
`Stacks.SheafOfModules.monoidalCategory` and `Stacks.SheafInternalHom.monoidalCategory`, which
differ only in the unit object.

## Main definitions

* `Stacks.SheafOfModules.Invertible.natTensorPowUnitShift`: the comparison of the iterated tensor
  powers read in the two localized monoidal structures on sheaves of modules.
* `Stacks.SheafOfModules.Invertible.unitShiftSection`: a global section of an iterated tensor
  power, read across that comparison.
* `Stacks.SheafOfModules.Invertible.tensorPowerCompare`: the comparison `L ^⊗ n ≅ L^{⊗ n}` of the
  iterated tensor products of `Stacks.SheafInternalHom.monoidalCategory` with the integer tensor
  powers.
* `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`: the same comparison for an
  invertible module on a scheme.

## Main results

* `Stacks.SheafOfModules.Invertible.unitShiftSection_mul`: the comparison of the two monoidal
  structures carries the product of two global sections to the product of their images.
* `Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare`: `tensorPowerCompare` is
  multiplicative for the Laurent multiplication, on local sections over any object of the site.
* `Stacks.AlgebraicGeometry.CoherentMulSections.mulBilinear_mulSections` and
  `Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear`: the same for a scheme,
  on global sections, in the two directions: the image of `mulSections` is the Laurent product,
  and the preimage of the Laurent product is `mulSections`.
* `Stacks.SheafOfModules.Invertible.tensorPowerCompareSection_id_app` and
  `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare_zero_globalSection_id`: the comparison
  carries the unit section of the zeroth iterated tensor power to the section `1` of the
  structure sheaf.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)
open Stacks.TensorPowers (natTensorPow)
open AlgebraicGeometry.SheafOfModules (IsInvertible unitIso)
open Stacks.GradedSections (powSections mulMap mul)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-! ### The two localized monoidal structures, and their iterated tensor powers -/

/-- The isomorphism between the iterated tensor powers of `L` in the two localized monoidal
structures on sheaves of `𝒪`-modules: in degree zero the comparison
`AlgebraicGeometry.SheafOfModules.unitIso` of the two unit objects, and in each successive degree
its whiskering by one more copy of `L`. -/
def natTensorPowUnitShift : (n : ℕ) →
    natTensorPow L n ≅ @natTensorPow _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n
  | 0 => unitIso 𝒪 h𝒪
  | n + 1 => MonoidalCategory.whiskerRightIso (natTensorPowUnitShift n) L

/-- A global section of an iterated tensor power, read in the other localized monoidal
structure: the comparison of the two units, followed by the section, followed by
`natTensorPowUnitShift`. -/
def unitShiftSection {n : ℕ} (s : powSections L n) :
    @powSections _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n :=
  (unitIso 𝒪 h𝒪).inv ≫ s ≫ (natTensorPowUnitShift 𝒪 h𝒪 L n).hom

/-- Multiplication by a global section is the same morphism in the two localized monoidal
structures, up to `natTensorPowUnitShift`. -/
theorem mulMap_natTensorPowUnitShift {n : ℕ} (s : powSections L n) : ∀ m : ℕ,
    (natTensorPowUnitShift 𝒪 h𝒪 L m).inv ≫ mulMap s m ≫
        (natTensorPowUnitShift 𝒪 h𝒪 L (n + m)).hom
      = @mulMap _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n
          (unitShiftSection 𝒪 h𝒪 L s) m
  | 0 => by
      change _ = (unitIso 𝒪 h𝒪).inv ≫ s ≫ (natTensorPowUnitShift 𝒪 h𝒪 L n).hom
      rfl
  | m + 1 => by
      change ((natTensorPowUnitShift 𝒪 h𝒪 L m).inv ▷ L) ≫ (mulMap s m ▷ L) ≫
          ((natTensorPowUnitShift 𝒪 h𝒪 L (n + m)).hom ▷ L)
        = (@mulMap _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n
            (unitShiftSection 𝒪 h𝒪 L s) m) ▷ L
      rw [← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.comp_whiskerRight,
        mulMap_natTensorPowUnitShift s m]

/-- The comparison of the two localized monoidal structures is multiplicative on global sections
of the iterated tensor powers. -/
theorem unitShiftSection_mul {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    unitShiftSection 𝒪 h𝒪 L (mul s t)
      = @mul _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n m
          (unitShiftSection 𝒪 h𝒪 L s) (unitShiftSection 𝒪 h𝒪 L t) := by
  change (unitIso 𝒪 h𝒪).inv ≫ (t ≫ mulMap s m) ≫ (natTensorPowUnitShift 𝒪 h𝒪 L (n + m)).hom
    = (unitShiftSection 𝒪 h𝒪 L t) ≫
        @mulMap _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L n
          (unitShiftSection 𝒪 h𝒪 L s) m
  rw [← mulMap_natTensorPowUnitShift 𝒪 h𝒪 L s m]
  change _ = ((unitIso 𝒪 h𝒪).inv ≫ t ≫ (natTensorPowUnitShift 𝒪 h𝒪 L m).hom) ≫ _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-! ### The comparison with the integer tensor powers -/

variable [IsInvertible 𝒪 h𝒪 L]

/-- The comparison of the iterated tensor products of `L`, read in
`Stacks.SheafInternalHom.monoidalCategory`, with the integer tensor powers in nonnegative degree:
`natTensorPowUnitShift` followed by `Stacks.SheafOfModules.Invertible.natTensorPowCompare`. -/
def tensorPowerCompare (n : ℕ) : natTensorPow L n ≅ tensorPower 𝒪 h𝒪 L (n : ℤ) :=
  natTensorPowUnitShift 𝒪 h𝒪 L n ≪≫ natTensorPowCompare 𝒪 h𝒪 L n

/-- A global section of an iterated tensor product, read as a global section of the integer
tensor power, as a morphism out of `SheafOfModules.unit`. -/
def tensorPowerCompareSection {n : ℕ} (s : powSections L n) :
    _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪) ⟶ tensorPower 𝒪 h𝒪 L (n : ℤ) :=
  (unitIso 𝒪 h𝒪).inv ≫ s ≫ (tensorPowerCompare 𝒪 h𝒪 L n).hom

/-- `tensorPowerCompareSection` splits as the comparison of the two monoidal structures followed
by `natTensorPowCompare`. -/
theorem tensorPowerCompareSection_eq {n : ℕ} (s : powSections L n) :
    tensorPowerCompareSection 𝒪 h𝒪 L s
      = unitShiftSection 𝒪 h𝒪 L s ≫ (natTensorPowCompare 𝒪 h𝒪 L n).hom := by
  change (unitIso 𝒪 h𝒪).inv ≫ s ≫ ((natTensorPowUnitShift 𝒪 h𝒪 L n).hom ≫
      (natTensorPowCompare 𝒪 h𝒪 L n).hom) = _
  change _ = ((unitIso 𝒪 h𝒪).inv ≫ s ≫ (natTensorPowUnitShift 𝒪 h𝒪 L n).hom) ≫ _
  simp only [Category.assoc]

/-- The comparison of the iterated tensor products of `Stacks.SheafInternalHom.monoidalCategory`
with the integer tensor powers is multiplicative for the multiplication of the Laurent algebra,
on local sections. -/
theorem mulBilinear_tensorPowerCompare (a b : ℕ) (U : Cᵒᵖ)
    (s : powSections L a) (t : powSections L b) :
    (Stacks.SheafOfModules.TensorPower.mulBilinear 𝒪 h𝒪 L (a : ℤ) (b : ℤ)).app U
        ((tensorPowerCompareSection 𝒪 h𝒪 L s).val.app U
          (1 : (structureSheaf 𝒪 h𝒪).obj.obj U))
        ((tensorPowerCompareSection 𝒪 h𝒪 L t).val.app U
          (1 : (structureSheaf 𝒪 h𝒪).obj.obj U))
      = (tensorPowerCompareSection 𝒪 h𝒪 L (mul s t)).val.app U
          (1 : (structureSheaf 𝒪 h𝒪).obj.obj U) := by
  rw [tensorPowerCompareSection_eq, tensorPowerCompareSection_eq, tensorPowerCompareSection_eq,
    unitShiftSection_mul]
  exact mulBilinear_natTensorPowCompare 𝒪 h𝒪 L a b U
    (unitShiftSection 𝒪 h𝒪 L s) (unitShiftSection 𝒪 h𝒪 L t)

/-! ### Degree zero: the two unit sections agree -/

/-- The comparison `natTensorPowCompare` of the iterated tensor powers with the integer tensor
powers is the identity in degree zero. -/
theorem natTensorPowCompare_zero_hom :
    (natTensorPowCompare 𝒪 h𝒪 L 0).hom = 𝟙 (tensorPower 𝒪 h𝒪 L ((0 : ℕ) : ℤ)) :=
  (Category.id_comp _).symm.trans ((natTensorPowCompare_sectionOne 𝒪 h𝒪 L).trans rfl)

/-- The comparison of the two localized monoidal structures carries the unit section of the
zeroth iterated tensor power to the identity. -/
theorem unitShiftSection_id :
    unitShiftSection 𝒪 h𝒪 L (𝟙 (natTensorPow L 0) : powSections L 0)
      = 𝟙 (tensorPower 𝒪 h𝒪 L ((0 : ℕ) : ℤ)) := by
  change (unitIso 𝒪 h𝒪).inv ≫ 𝟙 _ ≫ (natTensorPowUnitShift 𝒪 h𝒪 L 0).hom = _
  rw [Category.id_comp]
  exact (unitIso 𝒪 h𝒪).inv_hom_id

/-- The unit section of the zeroth iterated tensor power, read as a section of the zeroth integer
tensor power, is the identity of the tensor unit. -/
theorem tensorPowerCompareSection_id :
    tensorPowerCompareSection 𝒪 h𝒪 L (𝟙 (natTensorPow L 0) : powSections L 0)
      = 𝟙 (tensorPower 𝒪 h𝒪 L ((0 : ℕ) : ℤ)) := by
  rw [tensorPowerCompareSection_eq, unitShiftSection_id, natTensorPowCompare_zero_hom]
  exact Category.id_comp _

/-- The unit section of the zeroth iterated tensor power, read on the sections over any object of
the site through the comparison with the zeroth integer tensor power, is the section `1`. -/
theorem tensorPowerCompareSection_id_app (U : Cᵒᵖ) :
    (tensorPowerCompareSection 𝒪 h𝒪 L (𝟙 (natTensorPow L 0) : powSections L 0)).val.app U
        (1 : (structureSheaf 𝒪 h𝒪).obj.obj U)
      = (1 : (structureSheaf 𝒪 h𝒪).obj.obj U) := by
  rw [tensorPowerCompareSection_id]
  rfl

end Stacks.SheafOfModules.Invertible

namespace Stacks.AlgebraicGeometry.CoherentMulSections

open Stacks.SheafOfModules.Invertible (tensorPowerCompare tensorPowerCompareSection)
open Stacks.SheafOfModules.Invertible (tensorPower)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf mulSections)
open Stacks.SectionProduct (globalSection)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- The sheaf condition on the structure presheaf of rings of a scheme. -/
abbrev hStruct (Y : Scheme.{u}) : Presheaf.IsSheaf (Opens.grothendieckTopology ↥Y)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y

/-- The comparison `L ^⊗ n ≅ L^{⊗ n}` of the iterated tensor products of an invertible
`𝒪_Y`-module with its integer tensor powers, as an isomorphism of
`AlgebraicGeometry.Scheme.Modules`. -/
def powCompare (n : ℕ) :
    Stacks.TensorPowers.natTensorPow L n ≅ tensorPower Y.presheaf (hStruct Y) L (n : ℤ) :=
  tensorPowerCompare Y.presheaf (hStruct Y) L n

/-- The value of `powCompare` on the global section named by a morphism out of the monoidal unit
is the value of `Stacks.SheafOfModules.Invertible.tensorPowerCompareSection` on the section
`1`. -/
theorem tensorPowerCompareSection_app (n : ℕ) (s : Stacks.GradedSections.powSections L n) :
    (tensorPowerCompareSection Y.presheaf (hStruct Y) L s).val.app (op ⊤)
        (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
          (hStruct Y)).obj.obj (op ⊤))
      = (powCompare L n).hom.app ⊤ (globalSection Y _ s) := rfl

/-- `powCompare` carries the unit section of the zeroth iterated tensor power to the function
`1`. -/
theorem powCompare_zero_globalSection_id :
    (powCompare L 0).hom.app ⊤
        (globalSection Y (Stacks.TensorPowers.natTensorPow L 0) (𝟙 (𝟙_ Y.Modules)))
      = (1 : Γ(Y, ⊤)) :=
  (tensorPowerCompareSection_app L 0 (𝟙 (𝟙_ Y.Modules))).symm.trans
    (Stacks.SheafOfModules.Invertible.tensorPowerCompareSection_id_app Y.presheaf (hStruct Y) L
      (op ⊤))

/-- The comparison with the integer tensor powers is multiplicative for the Laurent
multiplication, on the global sections named by morphisms out of the monoidal unit. -/
theorem mulBilinear_globalSection (a b : ℕ) (s : Stacks.GradedSections.powSections L a)
    (t : Stacks.GradedSections.powSections L b) :
    (Stacks.SheafOfModules.TensorPower.mulBilinear Y.presheaf (hStruct Y) L
          (a : ℤ) (b : ℤ)).app (op ⊤)
        ((powCompare L a).hom.app ⊤ (globalSection Y (Stacks.TensorPowers.natTensorPow L a) s))
        ((powCompare L b).hom.app ⊤ (globalSection Y (Stacks.TensorPowers.natTensorPow L b) t))
      = (powCompare L (a + b)).hom.app ⊤
          (globalSection Y (Stacks.TensorPowers.natTensorPow L (a + b))
            (Stacks.GradedSections.mul s t)) := by
  have ha := tensorPowerCompareSection_app L a s
  have hb := tensorPowerCompareSection_app L b t
  have hab := tensorPowerCompareSection_app L (a + b) (Stacks.GradedSections.mul s t)
  rw [← ha, ← hb]
  exact (Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare Y.presheaf (hStruct Y) L
    a b (op ⊤) s t).trans hab

/-- The comparison with the integer tensor powers carries the product
`Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of two global sections of the iterated
tensor products to the multiplication of the Laurent algebra. -/
theorem mulBilinear_mulSections (a b : ℕ)
    (z : Γ(Stacks.TensorPowers.natTensorPow L a, ⊤))
    (w : Γ(Stacks.TensorPowers.natTensorPow L b, ⊤)) :
    (Stacks.SheafOfModules.TensorPower.mulBilinear Y.presheaf (hStruct Y) L
          (a : ℤ) (b : ℤ)).app (op ⊤)
        ((powCompare L a).hom.app ⊤ z) ((powCompare L b).hom.app ⊤ w)
      = (powCompare L (a + b)).hom.app ⊤ (mulSections L z w) := by
  have h := mulBilinear_globalSection L a b (secOf L z) (secOf L w)
  rw [← ProjChartFromRatios.mulSections_globalSection] at h
  simpa only [ProjChartFromRatios.globalSection_secOf] using h

/-- On global sections, the inverse of an isomorphism followed by it is the identity. -/
private theorem app_inv_hom_id_top {M N : Y.Modules} (e : M ≅ N) :
    e.inv.app (⊤ : Y.Opens) ≫ e.hom.app (⊤ : Y.Opens) = 𝟙 Γ(N, ⊤) :=
  (Scheme.Modules.Hom.comp_app e.inv e.hom).symm.trans
    ((congrArg (fun φ ↦ Scheme.Modules.Hom.app φ (⊤ : Y.Opens)) e.inv_hom_id).trans
      (Scheme.Modules.Hom.id_app _))

/-- On global sections, the inverse of `powCompare` followed by `powCompare` is the
identity. -/
theorem powCompare_app_inv_hom_id (n : ℕ) :
    (powCompare L n).inv.app (⊤ : Y.Opens) ≫ (powCompare L n).hom.app (⊤ : Y.Opens)
      = 𝟙 Γ((tensorPower Y.presheaf (hStruct Y) L (n : ℤ) : Y.Modules), ⊤) :=
  app_inv_hom_id_top (powCompare L n)

/-- On global sections, `powCompare` followed by its inverse is the identity. -/
theorem powCompare_app_hom_inv_id (n : ℕ) :
    (powCompare L n).hom.app (⊤ : Y.Opens) ≫ (powCompare L n).inv.app (⊤ : Y.Opens)
      = 𝟙 Γ(Stacks.TensorPowers.natTensorPow L n, ⊤) :=
  app_inv_hom_id_top (powCompare L n).symm

/-- Applying the inverse of the comparison and then the comparison to a global section of the
integer tensor power returns it. -/
theorem powCompare_hom_app_inv_app (n : ℕ)
    (u : Γ((tensorPower Y.presheaf (hStruct Y) L (n : ℤ) : Y.Modules), ⊤)) :
    (powCompare L n).hom.app ⊤ ((powCompare L n).inv.app ⊤ u) = u := by
  rw [← CategoryTheory.comp_apply, powCompare_app_inv_hom_id, CategoryTheory.id_apply]

/-- Applying the comparison and then its inverse to a global section of an iterated tensor
product returns it. -/
theorem powCompare_inv_app_hom_app (n : ℕ)
    (v : Γ(Stacks.TensorPowers.natTensorPow L n, ⊤)) :
    (powCompare L n).inv.app ⊤ ((powCompare L n).hom.app ⊤ v) = v := by
  rw [← CategoryTheory.comp_apply, powCompare_app_hom_inv_id, CategoryTheory.id_apply]

/-- The multiplication of the Laurent algebra, read on the iterated tensor products along the
inverse of the comparison, is `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`. -/
theorem mulSections_mulBilinear (a b : ℕ)
    (x : Γ((tensorPower Y.presheaf (hStruct Y) L (a : ℤ) : Y.Modules), ⊤))
    (y : Γ((tensorPower Y.presheaf (hStruct Y) L (b : ℤ) : Y.Modules), ⊤)) :
    mulSections L ((powCompare L a).inv.app ⊤ x) ((powCompare L b).inv.app ⊤ y)
      = (powCompare L (a + b)).inv.app ⊤
          ((Stacks.SheafOfModules.TensorPower.mulBilinear Y.presheaf (hStruct Y) L
            (a : ℤ) (b : ℤ)).app (op ⊤) x y) := by
  have h := mulBilinear_mulSections L a b ((powCompare L a).inv.app ⊤ x)
    ((powCompare L b).inv.app ⊤ y)
  rw [powCompare_hom_app_inv_app, powCompare_hom_app_inv_app] at h
  rw [h, powCompare_inv_app_hom_app]

end Stacks.AlgebraicGeometry.CoherentMulSections

end
