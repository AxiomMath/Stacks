module

public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# Further results on `UnitScalar`

Results about the endomorphisms of the monoidal unit of sheaves of modules on a ringed site and
on a scheme: they are identified with the sections of the structure sheaf over a terminal object,
additively and multiplicatively.
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification

universe u

universe v w

namespace Stacks.SectionRingGeometric

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory

/-- **A section of the structure sheaf, read as a section of the free rank-one sheaf of
modules.** The two types are definitionally equal. -/
def unitSecOnSite (T : C) (c : (structureSheaf 𝒪 h𝒪).obj.obj (op T)) :
    (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).val.obj (op T) :=
  c

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **Scaling the section `1` is the inclusion of the sections of the structure sheaf.** The
module structure on the sections of the free rank-one sheaf is the multiplication of the ring of
sections, so this is `mul_one`. -/
theorem smul_unitOne_onSite (T : C) (c : (structureSheaf 𝒪 h𝒪).obj.obj (op T)) :
    c • unitSecOnSite 𝒪 h𝒪 T 1 = unitSecOnSite 𝒪 h𝒪 T c :=
  mul_one c

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **A morphism of sheaves of modules is linear on sections.** Its value at an object of the
site is a morphism of `ModuleCat` over the ring of sections there. -/
theorem val_app_smul {M N : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (φ : M ⟶ N) (T : C)
    (r : (structureSheaf 𝒪 h𝒪).obj.obj (op T)) (x : M.val.obj (op T)) :
    ConcreteCategory.hom (φ.val.app (op T)) (r • x)
      = r • ConcreteCategory.hom (φ.val.app (op T)) x :=
  map_smul _ r x

/-- **The section of the structure sheaf attached to an endomorphism of the monoidal unit**: its
value at the section `1`, read through the comparison with the free rank-one sheaf. -/
def unitScalarOnSite (T : C) (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    (structureSheaf 𝒪 h𝒪).obj.obj (op T) :=
  ConcreteCategory.hom
    (((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫
      (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom).val.app (op T))
    (unitSecOnSite 𝒪 h𝒪 T 1)

/-- `unitScalarOnSite` read as a section of the free rank-one sheaf is the value at `1` itself. -/
theorem unitSec_unitScalar_onSite (T : C) (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    unitSecOnSite 𝒪 h𝒪 T (unitScalarOnSite 𝒪 h𝒪 T b)
      = ConcreteCategory.hom
          (((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫
            (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom).val.app (op T))
          (unitSecOnSite 𝒪 h𝒪 T 1) :=
  rfl

/-- **The endomorphisms of the monoidal unit are exactly the sections of the structure sheaf over
a terminal object.** Conjugating by `AlgebraicGeometry.SheafOfModules.unitIso` turns them into the
endomorphisms of the free rank-one sheaf, and those are its sections by
`SheafOfModules.unitHomEquiv`, which `sectionsEquivObj` reads at the terminal object. -/
def unitScalarEquivOnSite {T : C} (hT : IsTerminal T) :
    (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≃
      (structureSheaf 𝒪 h𝒪).obj.obj (op T) :=
  ((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).homCongr
      (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪)).trans
    ((SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).unitHomEquiv.trans
      (sectionsEquivObj hT (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)).val))

/-- The equivalence `unitScalarEquivOnSite` sends an endomorphism of the monoidal unit to its
scalar `unitScalarOnSite`. -/
@[simp] theorem unitScalarEquivOnSite_apply {T : C} (hT : IsTerminal T)
    (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    unitScalarEquivOnSite 𝒪 h𝒪 hT b = unitScalarOnSite 𝒪 h𝒪 T b :=
  rfl

/-- **The section of a morphism out of the monoidal unit is its value at `1`**, after the
comparison with the free rank-one sheaf. This unfolds
`Stacks.SectionRingGeometric.tensorUnitHomAddEquiv`. -/
theorem tensorUnitHomAddEquiv_apply {T : C} (hT : IsTerminal T)
    (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (f : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) :
    tensorUnitHomAddEquiv 𝒪 h𝒪 hT F f
      = ConcreteCategory.hom
          (((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ f).val.app (op T))
          (unitSecOnSite 𝒪 h𝒪 T 1) :=
  rfl

/-- Precomposing a morphism out of the monoidal unit with an endomorphism `b` of it multiplies its
value at `1` by the scalar of `b`. -/
private theorem unitIso_inv_comp_apply_one_smul (T : C)
    {F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))
    (t : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) :
    ConcreteCategory.hom
        (((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫ t).val.app (op T))
        (unitSecOnSite 𝒪 h𝒪 T 1)
      = unitScalarOnSite 𝒪 h𝒪 T b • ConcreteCategory.hom
        (((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ t).val.app (op T))
        (unitSecOnSite 𝒪 h𝒪 T 1) := by
  have hsplit : (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫ t
      = ((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫
          (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom)
        ≫ ((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ t) := by
    simp
  rw [hsplit, SheafOfModules.comp_val, PresheafOfModules.comp_app, CategoryTheory.comp_apply,
    ← unitSec_unitScalar_onSite, ← smul_unitOne_onSite, val_app_smul]

/-- **Composing with an endomorphism of the monoidal unit multiplies the section by its
scalar.** After conjugation the composite `b ≫ t` is a composite of two morphisms out of the free
rank-one sheaf; the first carries `1` to the scalar of `b`, which is that scalar times `1`, and the
second is linear. -/
theorem globalSection_unitComp_onSite {T : C} (hT : IsTerminal T)
    {F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))
    (t : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) :
    tensorUnitHomAddEquiv 𝒪 h𝒪 hT F (b ≫ t)
      = unitScalarOnSite 𝒪 h𝒪 T b • tensorUnitHomAddEquiv 𝒪 h𝒪 hT F t := by
  rw [tensorUnitHomAddEquiv_apply, tensorUnitHomAddEquiv_apply]
  exact unitIso_inv_comp_apply_one_smul 𝒪 h𝒪 T b t

/-- **The scalar of a sum is the sum of the scalars.** -/
theorem unitScalarOnSite_add (T : C) (b c : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    unitScalarOnSite 𝒪 h𝒪 T (b + c) = unitScalarOnSite 𝒪 h𝒪 T b + unitScalarOnSite 𝒪 h𝒪 T c := by
  have hsplit : (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ (b + c) ≫
        (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom
      = ((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ b ≫
          (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom)
        + ((AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ c ≫
          (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom) := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
  have h : unitSecOnSite 𝒪 h𝒪 T (unitScalarOnSite 𝒪 h𝒪 T (b + c))
      = unitSecOnSite 𝒪 h𝒪 T (unitScalarOnSite 𝒪 h𝒪 T b) +
        unitSecOnSite 𝒪 h𝒪 T (unitScalarOnSite 𝒪 h𝒪 T c) := by
    rw [unitSec_unitScalar_onSite, unitSec_unitScalar_onSite, unitSec_unitScalar_onSite, hsplit,
      SheafOfModules.add_val, PresheafOfModules.add_app]
    rfl
  exact h

/-- **The endomorphisms of the monoidal unit are the sections over a terminal object,
additively.** -/
def unitScalarAddEquivOnSite {T : C} (hT : IsTerminal T) :
    (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≃+
      (structureSheaf 𝒪 h𝒪).obj.obj (op T) where
  toEquiv := unitScalarEquivOnSite 𝒪 h𝒪 hT
  map_add' := unitScalarOnSite_add 𝒪 h𝒪 T

/-- The additive equivalence `unitScalarAddEquivOnSite` sends an endomorphism of the monoidal
unit to its scalar `unitScalarOnSite`. -/
@[simp] theorem unitScalarAddEquivOnSite_apply {T : C} (hT : IsTerminal T)
    (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    unitScalarAddEquivOnSite 𝒪 h𝒪 hT b = unitScalarOnSite 𝒪 h𝒪 T b :=
  rfl

/-- **The scalar of the identity is `1`.** -/
@[simp] theorem unitScalarOnSite_id (T : C) :
    unitScalarOnSite 𝒪 h𝒪 T (𝟙 (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))) = 1 := by
  have h : (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫
        𝟙 (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≫
          (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom
      = 𝟙 (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) := by
    simp
  rw [unitScalarOnSite, h]
  rfl

/-- **The scalar of a composite is the product of the scalars.** -/
theorem unitScalarOnSite_comp (T : C) (b c : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :
    unitScalarOnSite 𝒪 h𝒪 T (b ≫ c) = unitScalarOnSite 𝒪 h𝒪 T b * unitScalarOnSite 𝒪 h𝒪 T c := by
  have h := unitIso_inv_comp_apply_one_smul 𝒪 h𝒪 T b
    (c ≫ (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).hom)
  rw [← Category.assoc b] at h
  exact h

end Site

/-! ### Schemes -/

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

variable (X : Scheme.{u})

/-- **The global function attached to an endomorphism of the monoidal unit on a scheme**: the
instance of `Stacks.SectionRingGeometric.unitScalar` at the site of opens of `X` and its terminal
object `⊤`. -/
def schemeUnitScalar (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) : Γ(X, ⊤) :=
  unitScalarOnSite X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) ⊤ b

/-- **Composing with an endomorphism of the monoidal unit multiplies the global section by its
scalar**, on a scheme: the instance of `Stacks.SectionRingGeometric.globalSection_unitComp` at the
site of opens of `X` and its terminal object `⊤`. -/
theorem schemeGlobalSection_unitComp {F : X.Modules} (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (t : 𝟙_ X.Modules ⟶ F) :
    schemeGlobalSectionsAddEquiv X F (b ≫ t)
      = schemeUnitScalar X b • schemeGlobalSectionsAddEquiv X F t :=
  globalSection_unitComp_onSite X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    isTerminalTop b t

/-- **The scalar of a sum is the sum of the scalars**, on a scheme. -/
theorem schemeUnitScalar_add (b c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    schemeUnitScalar X (b + c) = schemeUnitScalar X b + schemeUnitScalar X c :=
  unitScalarOnSite_add X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) ⊤ b c

/-- **The scalar of the identity is `1`**, on a scheme. -/
@[simp] theorem schemeUnitScalar_id : schemeUnitScalar X (𝟙 (𝟙_ X.Modules)) = 1 :=
  unitScalarOnSite_id X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) ⊤

/-- **The scalar of a composite is the product of the scalars**, on a scheme. -/
theorem schemeUnitScalar_comp (b c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    schemeUnitScalar X (b ≫ c) = schemeUnitScalar X b * schemeUnitScalar X c :=
  unitScalarOnSite_comp X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) ⊤ b c

end Scheme

end Stacks.SectionRingGeometric

end
