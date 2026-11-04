module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections

/-!
# The unitors of the re-seated tensor product are the unitors of the tensor product sheaf

On a ringed site `(C, J, 𝒪)` the monoidal structure `SheafOfModules.monoidalCategorySheafTensor`
has `Stacks.SheafOfModules.Tensor.sheafTensor` for its tensor product and `SheafOfModules.unit`
for its unit, but its unitors are inherited from the localized structure and so have no
description on local sections.  The unitors `ℱ ⊗_𝒪 𝒪 ≅ ℱ` and `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections` do have one, `x ⊗ r ↦ r • x`.
This file identifies the two.

## Main results

* `SheafOfModules.rightUnitor_sheafTensor_eq` and `SheafOfModules.leftUnitor_sheafTensor_eq`:
  **the unitors of the re-seated monoidal structure are
  `Stacks.SheafOfModules.tensorSheafUnitRightIso` and
  `Stacks.SheafOfModules.tensorSheafUnitLeftIso`.**
* `Stacks.RingedSpace.rightUnitor_sheafTensor_eq` and
  `Stacks.RingedSpace.leftUnitor_sheafTensor_eq`: the same on a ringed space, at the spelling of
  [Stacks, Tag 0GMW].
* `SheafOfModules.rightUnitor_sheafifyMod` and `SheafOfModules.leftUnitor_sheafifyMod`: the
  unitors of the localized structure at a sheafified presheaf of modules are the tensorator of
  sheafification followed by the sheafification of the presheaf unitor.

## Implementation notes

`Mod(𝒪)` carries the localized monoidal structure and the re-seated one at once, so the
re-seated one is named by `@`-application throughout and never left to instance synthesis.

The computation runs entirely inside the localized structure.  The unit comparison of
sheafification there is the identity — the localization is performed with `Iso.refl` as its
choice of unit — so the localized unitors at `ℱ^#` are the tensorator of sheafification followed
by `ℱ^#` of the presheaf unitor, and the re-seated unitors are those conjugated by
`SheafOfModules.sheafTensorIso` and the counit `SheafOfModules.unitIso` at the unit.  The counit
cancels against the counit inside `sheafTensorIso`, leaving the sheafified presheaf unitor, which
is the unitor of the tensor product sheaf by definition.  Nothing about the sections of the
sheafification is used.

Three spellings of the sheafified presheaf unit are in play: `𝟙_ (Mod(𝒪))` for the localized
structure, `(SheafOfModules.forget _).obj (SheafOfModules.unit _)`, and
`𝟙_ (Mod_{pre}(𝒪))`.  They agree by `rfl` and not syntactically, so a `rw` or a `simp` whose
pattern straddles two of them fails to unify; each lemma below therefore uses a single spelling
and the passages between them are left to the conversion check of a term-mode `Eq.trans`.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section



open CategoryTheory Limits MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal

universe v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v}) [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] monoidalCategory

/-! ### The localized unitors at a sheafified presheaf of modules -/

/-- The right unitor of the localized structure at `𝒫^#`: the unit comparison of sheafification
is the identity, so only the tensorator and the sheafified presheaf unitor are left. -/
theorem rightUnitor_sheafifyMod
    (P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (ρ_ ((PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P)).hom =
      μ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) P (𝟙_ _) ≫
        (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map (ρ_ P).hom :=
  (right_unitality _ P).trans
    (by rw [show _ ◁ ε _ = 𝟙 _ from MonoidalCategory.whiskerLeft_id _ _, Category.id_comp])

/-- `SheafOfModules.rightUnitor_sheafifyMod` with a morphism appended, in the bracketing a
rewrite inside a longer composite needs. -/
theorem rightUnitor_sheafifyMod_comp
    (P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {W : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (g : (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P ⟶ W) :
    (ρ_ ((PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P)).hom ≫ g =
      μ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) P (𝟙_ _) ≫
        (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map (ρ_ P).hom ≫ g :=
  by rw [rightUnitor_sheafifyMod, Category.assoc]

/-- The left unitor of the localized structure at `𝒫^#`, obtained the same way. -/
theorem leftUnitor_sheafifyMod
    (P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (λ_ ((PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P)).hom =
      μ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (𝟙_ _) P ≫
        (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map (λ_ P).hom :=
  (left_unitality _ P).trans
    (by rw [show ε _ ▷ _ = 𝟙 _ from MonoidalCategory.id_whiskerRight _ _, Category.id_comp])

/-- `SheafOfModules.leftUnitor_sheafifyMod` with a morphism appended. -/
theorem leftUnitor_sheafifyMod_comp
    (P : PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {W : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (g : (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P ⟶ W) :
    (λ_ ((PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj P)).hom ≫ g =
      μ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (𝟙_ _) P ≫
        (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map (λ_ P).hom ≫ g :=
  by rw [leftUnitor_sheafifyMod, Category.assoc]

/-! ### The comparison isomorphism at the unit -/

variable (A : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- `SheafOfModules.sheafTensorIso` at the unit in the second variable, written out: the two
counits whiskered one after the other, followed by the tensorator of sheafification. -/
theorem sheafTensorIso_unitRight_hom :
    (sheafTensorIso R A (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom =
      (counitIso R A).inv ▷ unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ≫
          (PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
              ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ◁ (unitIso R).inv ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A)
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) :=
  rfl

/-- `SheafOfModules.sheafTensorIso` at the unit in the first variable, written out. -/
theorem sheafTensorIso_unitLeft_hom :
    (sheafTensorIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) A).hom =
      (counitIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).inv ▷ A ≫
          (PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
              ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
                (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ◁ (counitIso R A).inv ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) :=
  rfl

/-- The counit at `ℱ`, whiskered with the unit and followed by the comparison isomorphism, is
the counit at the unit whiskered with `ℱ^#` followed by the tensorator: the two copies of the
counit at `ℱ` cancel. -/
theorem counit_whiskerRight_comp_sheafTensorIso :
    (counitIso R A).hom ▷ unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ≫
        (sheafTensorIso R A (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ◁ (unitIso R).inv ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A)
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) := by
  rw [sheafTensorIso_unitRight_hom, ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight,
    Category.id_comp]

/-- `SheafOfModules.counit_whiskerRight_comp_sheafTensorIso` with a morphism appended. -/
theorem counit_whiskerRight_comp_sheafTensorIso_comp
    {W : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (g : (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A ⊗
        (forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
          (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ⟶ W) :
    (counitIso R A).hom ▷ unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ≫
        (sheafTensorIso R A (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom ≫ g =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ◁ (unitIso R).inv ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A)
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
              (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ≫ g :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ g) (counit_whiskerRight_comp_sheafTensorIso R A)).trans (Category.assoc _ _ _))

/-- The left-handed counterpart of
`SheafOfModules.counit_whiskerRight_comp_sheafTensorIso`. -/
theorem counit_whiskerLeft_comp_sheafTensorIso :
    unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ◁ (counitIso R A).hom ≫
        (sheafTensorIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) A).hom =
      (counitIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).inv ▷
            (PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
              ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
            (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
          ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) := by
  rw [sheafTensorIso_unitLeft_hom, whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]

/-- `SheafOfModules.counit_whiskerLeft_comp_sheafTensorIso` with a morphism appended. -/
theorem counit_whiskerLeft_comp_sheafTensorIso_comp
    {W : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (g : (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
          (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ⊗
        (forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ⟶ W) :
    unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ◁ (counitIso R A).hom ≫
        (sheafTensorIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) A).hom ≫ g =
      (counitIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).inv ▷
            (PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
              ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
              (unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ≫ g :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ g) (counit_whiskerLeft_comp_sheafTensorIso R A)).trans (Category.assoc _ _ _))

/-! ### The re-seated unitors -/

/-- The localized right unitor at `ℱ`, precomposed with the counit, is the tensorator of
sheafification followed by the sheafified presheaf unitor and the counit. -/
theorem counit_whiskerRight_comp_rightUnitor :
    (counitIso R A).hom ▷ unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ≫
        (𝟙 A ⊗ₘ (unitIso R).inv) ≫ (ρ_ A).hom =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ◁ (unitIso R).inv ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) (𝟙_ _) ≫
          (PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
              (ρ_ ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A)).hom ≫
            (counitIso R A).hom := by
  rw [MonoidalCategory.id_tensorHom, ← whisker_exchange_assoc,
    MonoidalCategory.rightUnitor_naturality, rightUnitor_sheafifyMod_comp]

/-- The left-handed counterpart of
`SheafOfModules.counit_whiskerRight_comp_rightUnitor`. -/
theorem counit_whiskerLeft_comp_leftUnitor :
    unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ◁ (counitIso R A).hom ≫
        ((unitIso R).inv ⊗ₘ 𝟙 A) ≫ (λ_ A).hom =
      (unitIso R).inv ▷
            (PresheafOfModules.sheafification
                (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
                (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
              ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ≫
        μ (PresheafOfModules.sheafification
            (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
            (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (𝟙_ _)
            ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A) ≫
          (PresheafOfModules.sheafification
              (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
              (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
              (λ_ ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj A)).hom ≫
            (counitIso R A).hom := by
  rw [MonoidalCategory.tensorHom_id, whisker_exchange_assoc,
    MonoidalCategory.leftUnitor_naturality, leftUnitor_sheafifyMod_comp]

/-- **The right unitor of the re-seated monoidal structure is the right unitor
`ℱ ⊗_𝒪 𝒪 ≅ ℱ` of the tensor product sheaf**, whose action on local sections is `x ⊗ r ↦ r • x`. -/
theorem rightUnitor_sheafTensor_eq :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A).hom =
      (Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A).hom :=
  (Iso.inv_comp_eq _).mpr
    ((cancel_epi ((counitIso R A).hom ▷ unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).mp
      ((counit_whiskerRight_comp_rightUnitor R A).trans
        (counit_whiskerRight_comp_sheafTensorIso_comp R A _).symm))

/-- **The left unitor of the re-seated monoidal structure is the left unitor
`𝒪 ⊗_𝒪 ℱ ≅ ℱ` of the tensor product sheaf.** -/
theorem leftUnitor_sheafTensor_eq :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A).hom =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A).hom :=
  (Iso.inv_comp_eq _).mpr
    ((cancel_epi (unit (Stacks.SheafOfModules.Tensor.ringSheaf R) ◁ (counitIso R A).hom)).mp
      ((counit_whiskerLeft_comp_leftUnitor R A).trans
        (counit_whiskerLeft_comp_sheafTensorIso_comp R A _).symm))

/-- `SheafOfModules.rightUnitor_sheafTensor_eq`, as an equality of isomorphisms. -/
theorem rightUnitor_sheafTensor_eq_iso :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A) =
      Stacks.SheafOfModules.tensorSheafUnitRightIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A :=
  Iso.ext (rightUnitor_sheafTensor_eq R A)

/-- `SheafOfModules.leftUnitor_sheafTensor_eq`, as an equality of isomorphisms. -/
theorem leftUnitor_sheafTensor_eq_iso :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A) =
      Stacks.SheafOfModules.tensorSheafUnitLeftIso R.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf R).property A :=
  Iso.ext (leftUnitor_sheafTensor_eq R A)

end SheafOfModules

namespace Stacks.RingedSpace

open AlgebraicGeometry

universe w

variable (Z : RingedSpace.{w, w})
  (A : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Z.presheaf, Z.IsSheaf⟩))

/-- **On a ringed space, the right unitor of the re-seated monoidal structure is
`Stacks.RingedSpace.tensorSheafUnitRightIso`.** -/
theorem rightUnitor_sheafTensor_eq :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩).toMonoidalCategoryStruct
        A).hom =
      (tensorSheafUnitRightIso Z A).hom :=
  _root_.SheafOfModules.rightUnitor_sheafTensor_eq ⟨Z.presheaf, Z.IsSheaf⟩ A

/-- **On a ringed space, the left unitor of the re-seated monoidal structure is
`Stacks.RingedSpace.tensorSheafUnitLeftIso`.** -/
theorem leftUnitor_sheafTensor_eq :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor
          ⟨Z.presheaf, Z.IsSheaf⟩).toMonoidalCategoryStruct
        A).hom =
      (tensorSheafUnitLeftIso Z A).hom :=
  _root_.SheafOfModules.leftUnitor_sheafTensor_eq ⟨Z.presheaf, Z.IsSheaf⟩ A

end Stacks.RingedSpace

end
