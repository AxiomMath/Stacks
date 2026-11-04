module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Basic
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLinear

/-!
# Linearity of the tensor product of sheaves of modules

Let `(C, J)` be a site and `Λ` a commutative ring. The tensor product of sheaves of `Λ`-modules
and the derived tensor product on `D(C, Λ)` are `Λ`-linear in each variable: multiplication by
`a ∈ Λ` on one factor induces multiplication by `a` on the tensor product.

For sheaves, `F ⊗ G` is the sheafification of the objectwise tensor product, and sheafification
is a monoidal `Λ`-linear localization; objectwise the statement is that of `Λ`-modules. For the
derived tensor product it is transported along the localizations defining
`Stacks.ModuleSheaf.derivedMonoidal`, by
`CochainComplex.KFlatMonoidal.derived_smul_id_whiskerRight`.

## Main results

* `Stacks.ModuleSheaf.smul_id_whiskerRight`, `Stacks.ModuleSheaf.whiskerLeft_smul_id`: linearity
  of the tensor product of sheaves of `Λ`-modules.
* `Stacks.ModuleSheaf.monoidalLinear`: the monoidal category of sheaves of `Λ`-modules is
  `Λ`-linear, so tensoring with a fixed sheaf is a `Λ`-linear functor.
* `Stacks.ModuleSheaf.derived_smul_id_whiskerRight`,
  `Stacks.ModuleSheaf.derived_whiskerLeft_smul_id`: linearity of the derived tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ]

/-- Scalars act on a presheaf of `Λ`-modules through the unit presheaf. -/
theorem presheaf_smul_id_eq_leftUnitor (a : Λ) (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    a • 𝟙 P = (λ_ P).inv ≫ ((a • 𝟙 (𝟙_ (Cᵒᵖ ⥤ ModuleCat.{w} Λ))) ▷ P) ≫ (λ_ P).hom := by
  ext U : 2
  simp

variable [UnivLE.{max u v, w}]

/-- Scalars act on a sheaf of `Λ`-modules through the unit sheaf. -/
theorem smul_id_eq_leftUnitor (a : Λ) (X : Sheaf J (ModuleCat.{w} Λ)) :
    a • 𝟙 X = (λ_ X).inv ≫ ((a • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{w} Λ)))) ▷ X) ≫ (λ_ X).hom :=
  MonoidalCategory.smul_id_eq_leftUnitor_of_iso
    (asIso ((sheafificationAdjunction J _).counit.app X)) a
    (MonoidalCategory.smul_id_eq_leftUnitor_map (presheafToSheaf J (ModuleCat.{w} Λ)) a X.obj
      (presheaf_smul_id_eq_leftUnitor a X.obj))

/-- **The tensor product of sheaves of `Λ`-modules is `Λ`-linear in its left variable.** -/
theorem smul_id_whiskerRight (a : Λ) (X Y : Sheaf J (ModuleCat.{w} Λ)) :
    (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y) :=
  MonoidalCategory.smul_id_whiskerRight_of_forall Λ smul_id_eq_leftUnitor a X Y

/-- **The tensor product of sheaves of `Λ`-modules is `Λ`-linear in its right variable.** -/
theorem whiskerLeft_smul_id (a : Λ) (X Y : Sheaf J (ModuleCat.{w} Λ)) :
    X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y) :=
  MonoidalCategory.whiskerLeft_smul_id_of_forall smul_id_eq_leftUnitor a X Y

/-- **The monoidal category of sheaves of `Λ`-modules is `Λ`-linear**: whiskering commutes with
multiplication by scalars, as multiplication by `a` on a morphism factors through `a • 𝟙`. -/
instance monoidalLinear : MonoidalLinear Λ (Sheaf J (ModuleCat.{w} Λ)) where
  whiskerLeft_smul X Y Z a f := by
    rw [show a • f = (a • 𝟙 Y) ≫ f by rw [Linear.smul_comp, Category.id_comp],
      MonoidalCategory.whiskerLeft_comp, whiskerLeft_smul_id, Linear.smul_comp, Category.id_comp]
  smul_whiskerRight a Y Z f X := by
    rw [show a • f = (a • 𝟙 Y) ≫ f by rw [Linear.smul_comp, Category.id_comp],
      MonoidalCategory.comp_whiskerRight, smul_id_whiskerRight, Linear.smul_comp, Category.id_comp]

attribute [local instance] CochainComplex.braidedCategory derivedMonoidal derivedSymmetric

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- **The derived tensor product on `D(C, Λ)` is `Λ`-linear in its left variable.** -/
theorem derived_smul_id_whiskerRight (a : Λ)
    (X Y : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    (a • 𝟙 X) ▷ Y = a • 𝟙 (X ⊗ Y) :=
  let := CochainComplex.symmetricCategory (Sheaf J (ModuleCat.{w} Λ))
  CochainComplex.KFlatMonoidal.derived_smul_id_whiskerRight _ Λ _ smul_id_whiskerRight a X Y

/-- **The derived tensor product on `D(C, Λ)` is `Λ`-linear in its right variable.** -/
theorem derived_whiskerLeft_smul_id (a : Λ)
    (X Y : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y) :=
  let := CochainComplex.symmetricCategory (Sheaf J (ModuleCat.{w} Λ))
  CochainComplex.KFlatMonoidal.derived_whiskerLeft_smul_id _ Λ _ smul_id_whiskerRight a X Y

end Stacks.ModuleSheaf
