module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# The monoidal structure on sheaves of modules over a ringed space

Let `(X, O_X)` be a ringed space.  The sheafified tensor product `tensorSheaf` of Stacks 01CA
makes the category of sheaves of `O_X`-modules monoidal.  This file builds that monoidal
structure and identifies all of its data with the canonical sheaf-theoretic maps.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.monoidal` is the monoidal structure on
  `SheafOfModules (structureSheafRing X)` whose tensor product is `tensorSheaf` and whose unit
  is `SheafOfModules.unit`.
* `Stacks.SheafOfModules.OnSpace.sheafModuleForget` is the forgetful functor to presheaves of
  modules and `Stacks.SheafOfModules.OnSpace.sheafModuleForgetLax` is its lax monoidal
  structure, coming from the sheafification adjunction.

## Main results

* `monoidal_tensorObj`, `monoidal_tensorUnit` and `monoidal_tensorHom` identify the tensor
  product, the unit and the functoriality of `monoidal` with `tensorSheaf`,
  `SheafOfModules.unit` and `tensorSheafMap`.
* `monoidal_forget_mu` and `monoidal_forget_epsilon` identify the lax monoidal structure maps
  of the forgetful functor with the sheafification unit and the identity.
* `tensorObjSection` and `tensorObjTmul` name the canonical sections of a tensor product; all
  of the section formulas are phrased with them, which is what lets them be chained.
* `tensorHom_tmul`, `whiskerRight_tmul`, `whiskerLeft_tmul`, `associator_tmul`,
  `associator_inv_tmul`, `leftUnitor_tmul`, `rightUnitor_tmul`, `leftUnitor_inv_apply` and
  `rightUnitor_inv_apply` evaluate the structural morphisms on local pure tensors, which
  determines them.
* `tensor_hom_ext` and `hom_ext_of_locally` are the two extensionality principles that make
  those evaluations sufficient: a morphism out of a tensor product is determined by its values
  on local pure tensors, and a morphism of sheaves is determined locally.

## Implementation notes

The monoidal structure is obtained by monoidal localization: sheafification
`PresheafOfModules (O X) ⥤ SheafOfModules (structureSheafRing X)` is the localization at the
local isomorphisms, that class is compatible with the monoidal structure of Stacks 05NA
(`sheafModuleLocalEquivalences_isMonoidal`), and `CategoryTheory.LocalizedMonoidal` therefore
produces a monoidal structure on the target.  Its tensor product is however only *isomorphic*
to `tensorSheaf`, not equal to it.  To make `monoidal_tensorObj` hold by `rfl` the structure is
transported once more: the tensor product is replaced by `tensorSheaf` on
`ULift (SheafOfModules _)` (the `ULift` only serves to keep the two competing monoidal
structures on distinguishable types), the comparison isomorphism
`sheafModuleTensorCompareIso` shows by `CategoryTheory.Monoidal.induced` that the replacement
is again monoidal, and the result is transported back along the `ULift` equivalence.

Consequently the structural morphisms of `monoidal` are not directly readable off the
localization data.  They are computed instead from the lax monoidal structure of the forgetful
functor `sheafModuleForget`, whose structure maps are the sheafification units
(`monoidal_forget_mu`, `monoidal_forget_epsilon`); the coherence axioms of a lax monoidal
functor then give each of the `*_tmul` lemmas.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace MonoidalCategory Opposite TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

attribute [local instance_reducible] TensorSheafification.structureSheaf
  CategoryTheory.Localization.Monoidal.toMonoidalCategory CategoryTheory.LocalizedMonoidal

attribute [local implicit_reducible] TensorSheafification.sheafify _root_.SheafOfModules.forget
  _root_.PresheafOfModules.restrictScalars

/-! ### The localized monoidal structure -/

/-- Presheaves of `O_X`-modules, the category that gets localized. -/
abbrev presheafModuleCategory := PresheafOfModules.{u} (structureSheafRing X).obj

/-- **Mathlib's monoidal structure on presheaves of `O_X`-modules, at the spelling of the
presheaf of rings used here.** `PresheafOfModules.monoidalCategory` is keyed on
`𝒪 ⋙ forget₂ CommRingCat RingCat`, whereas `(structureSheafRing X).obj` is a projection out of
a sheaf; only `@[reducible]` definitions are unfolded when a goal is keyed into the
discrimination tree that instance search uses, and `structureSheafRing` is
`@[instance_reducible]`, so Mathlib's instance is never retrieved at this spelling. The two
presheaves of rings are equal by `rfl`, so this is that same instance, named at a key search
does find.

It is `@[instance_reducible]`, as an instance should be, and is supplied to the proofs below as a
local instance (next line); the presheaves of rings themselves keep their reducibility. -/
@[instance_reducible]
noncomputable def presheafModuleMonoidalCategory :
    MonoidalCategory (presheafModuleCategory X) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})))

attribute [local instance] presheafModuleMonoidalCategory

/-- Sheafification of presheaves of `O_X`-modules; the localization functor. -/
noncomputable abbrev sheafModuleSheafification :=
  PresheafOfModules.sheafification (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)

/-- The local isomorphisms of presheaves of `O_X`-modules, i.e. the class of morphisms that
sheafification inverts. -/
abbrev sheafModuleLocalEquivalences :=
  (JX X).W.inverseImage (PresheafOfModules.toPresheaf (structureSheafRing X).obj)

/-- Sheafification inverts exactly the local isomorphisms. -/
theorem isIso_sheafification_map_iff {A B : presheafModuleCategory X} (f : A ⟶ B) :
    IsIso ((sheafModuleSheafification X).map f) ↔ sheafModuleLocalEquivalences X f := by
  rw [show IsIso ((sheafModuleSheafification X).map f) ↔
      MorphismProperty.isomorphisms (SheafOfModules.{u} (structureSheafRing X))
        ((sheafModuleSheafification X).map f) from (MorphismProperty.isomorphisms.iff _).symm,
    ← MorphismProperty.inverseImage_iff
      (MorphismProperty.isomorphisms (SheafOfModules.{u} (structureSheafRing X)))
      (sheafModuleSheafification X) f,
    ← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (structureSheafRing X).obj),
    MorphismProperty.inverseImage_iff]
  rfl

/-- The local isomorphisms are compatible with the monoidal structure on presheaves of
modules, which is what lets the monoidal structure descend to the localization. -/
theorem sheafModuleLocalEquivalences_isMonoidal :
    (sheafModuleLocalEquivalences X).IsMonoidal := by
  have hO : Presheaf.IsSheaf (JX X)
      (TensorSheafification.structureRingPresheaf X.presheaf) :=
    (Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)).mp X.IsSheaf
  have hLeft : ∀ {A B : presheafModuleCategory X} (f : A ⟶ B),
      sheafModuleLocalEquivalences X f →
      ∀ Y : presheafModuleCategory X, sheafModuleLocalEquivalences X (Y ◁ f) := by
    intro A B f hf Y
    exact (isIso_sheafification_map_iff X (Y ◁ f)).mp
      (TensorSheafification.isIso_sheafify_map_whiskerLeft X.presheaf hO Y f
        ((isIso_sheafification_map_iff X f).mpr hf))
  exact MorphismProperty.IsMonoidal.mk' _ (by
    intro A A' B B' f g hf hg
    rw [MonoidalCategory.tensorHom_def]
    exact MorphismProperty.comp_mem _ _ _
      (TensorSheafification.W_whiskerRight X.presheaf f B hf) (hLeft g hg A'))

attribute [local instance] sheafModuleLocalEquivalences_isMonoidal

/-- The chosen identification of the sheafification of the monoidal unit of presheaves of
modules with the structure sheaf, used as the preferred unit of the localized structure. -/
noncomputable def sheafModuleUnitIso :
    (sheafModuleSheafification X).obj (𝟙_ (presheafModuleCategory X)) ≅
      SheafOfModules.unit (structureSheafRing X) :=
  ((sheafModuleSheafification X).mapIso (eqToIso
      (show (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
            (SheafOfModules.unit (structureSheafRing X)) =
        𝟙_ (presheafModuleCategory X) from rfl))).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafRing X).obj)).counit.app (SheafOfModules.unit (structureSheafRing X)))

/-- The localized monoidal category of sheaves of `O_X`-modules, as a type synonym. -/
abbrev localizedSheafModules :=
  LocalizedMonoidal (sheafModuleSheafification X) (sheafModuleLocalEquivalences X)
    (sheafModuleUnitIso X)

/-- The monoidal structure transported from presheaves of modules to sheaves of modules by
monoidal localization.  Its tensor product is *not* `tensorSheaf` on the nose. -/
@[instance_reducible]
noncomputable def sheafModuleLocalizedMonoidal :
    MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  inferInstanceAs (MonoidalCategory (localizedSheafModules X))

/-- The forgetful functor from sheaves of `O_X`-modules to presheaves of `O_X`-modules. -/
noncomputable abbrev sheafModuleForget :=
  SheafOfModules.forget (structureSheafRing X) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)

/-- A copy of the category of sheaves of `O_X`-modules in a larger universe, used to carry the
candidate monoidal structure whose tensor product is `tensorSheaf` while the localized one is
still in scope on the original type. -/
abbrev sheafModuleTransportCategory :=
  ULift.{u} (SheafOfModules.{u} (structureSheafRing X))

/-- The category structure on the `ULift` copy. -/
@[instance_reducible]
noncomputable def sheafModuleULiftCategory :
    Category.{u, u + 1} (sheafModuleTransportCategory X) :=
  CategoryTheory.uliftCategory (SheafOfModules.{u} (structureSheafRing X))

attribute [local instance] sheafModuleULiftCategory

/-- A morphism of sheaves of modules, read as a morphism in the `ULift` copy. -/
def sheafModuleLiftHom {A B : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ B) :
    ULift.up.{u, u + 1} A ⟶ ULift.up.{u, u + 1} B := f

/-- A morphism in the `ULift` copy, read as a morphism of sheaves of modules. -/
def sheafModuleUnliftHom {A B : sheafModuleTransportCategory X} (f : A ⟶ B) :
    A.down ⟶ B.down := f

/-- An isomorphism of sheaves of modules, read as an isomorphism in the `ULift` copy. -/
def sheafModuleLiftIso {A B : SheafOfModules.{u} (structureSheafRing X)} (e : A ≅ B) :
    ULift.up.{u, u + 1} A ≅ ULift.up.{u, u + 1} B where
  hom := sheafModuleLiftHom X e.hom
  inv := sheafModuleLiftHom X e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-! ### Replacing the tensor product by `tensorSheaf` -/

section Localized

attribute [local instance] sheafModuleLocalizedMonoidal

/-- The localized tensor product of two sheaves of modules is canonically isomorphic to their
sheafified tensor product. -/
noncomputable def sheafModuleTensorCompareIso
    (A B : SheafOfModules.{u} (structureSheafRing X)) : A ⊗ B ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B)) :=
  ((asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).counit.app A)).symm ⊗ᵢ
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).counit.app B)).symm) ≪≫
    Localization.Monoidal.μ (sheafModuleSheafification X) (sheafModuleLocalEquivalences X)
      (sheafModuleUnitIso X) A.val B.val

/-- The candidate monoidal data on the `ULift` copy: the same as the localized one, except
that the tensor product of two objects is `tensorSheaf` on the nose. -/
@[instance_reducible]
noncomputable def sheafModuleTensorStruct :
    MonoidalCategoryStruct (sheafModuleTransportCategory X) where
  tensorObj A B := ULift.up ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A.down)).obj (B.down)))
  whiskerLeft A {B C} f :=
    sheafModuleLiftHom X ((sheafModuleTensorCompareIso X A.down B.down).inv ≫
      A.down ◁ sheafModuleUnliftHom X f ≫ (sheafModuleTensorCompareIso X A.down C.down).hom)
  whiskerRight {A B} f C :=
    sheafModuleLiftHom X ((sheafModuleTensorCompareIso X A.down C.down).inv ≫
      sheafModuleUnliftHom X f ▷ C.down ≫ (sheafModuleTensorCompareIso X B.down C.down).hom)
  tensorHom {A A' B B'} f g :=
    sheafModuleLiftHom X ((sheafModuleTensorCompareIso X A.down B.down).inv ≫
      (sheafModuleUnliftHom X f ⊗ₘ sheafModuleUnliftHom X g) ≫
      (sheafModuleTensorCompareIso X A'.down B'.down).hom)
  tensorUnit := ULift.up (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))
  associator A B C := sheafModuleLiftIso X <|
    ((sheafModuleTensorCompareIso X
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A.down)).obj
            (B.down))) C.down).symm ≪≫
        ((sheafModuleTensorCompareIso X A.down B.down).symm ⊗ᵢ Iso.refl C.down)) ≪≫
      α_ A.down B.down C.down ≪≫
      ((Iso.refl A.down ⊗ᵢ sheafModuleTensorCompareIso X B.down C.down) ≪≫
        sheafModuleTensorCompareIso X A.down
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (B.down)).obj
              (C.down))))
  leftUnitor A := sheafModuleLiftIso X <|
    ((sheafModuleTensorCompareIso X (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))
          A.down).symm ≪≫
        ((Iso.refl (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))).symm ⊗ᵢ
          Iso.refl A.down)) ≪≫ λ_ A.down
  rightUnitor A := sheafModuleLiftIso X <|
    ((sheafModuleTensorCompareIso X A.down
          (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))).symm ≪≫
        (Iso.refl A.down ⊗ᵢ
          (Iso.refl (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))).symm)) ≪≫ ρ_ A.down

attribute [local instance] sheafModuleTensorStruct

/-- The projection from the `ULift` copy. -/
noncomputable def sheafModuleDown :
    sheafModuleTransportCategory X ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  CategoryTheory.ULift.downFunctor

/-- The projection from the `ULift` copy is faithful. -/
theorem sheafModuleDown_faithful : (sheafModuleDown X).Faithful := ⟨fun h => h⟩

attribute [local instance] sheafModuleDown_faithful

/-- The witness that `sheafModuleTensorStruct` really is a monoidal structure: it is induced
from the localized one along the faithful projection `sheafModuleDown`. -/
noncomputable def sheafModuleInducingData :
    Monoidal.InducingFunctorData (sheafModuleDown X) where
  μIso A B := sheafModuleTensorCompareIso X A.down B.down
  εIso := Iso.refl (𝟙_ (SheafOfModules.{u} (structureSheafRing X)))
  whiskerLeft_eq := by intros; rfl
  whiskerRight_eq := by intros; rfl
  tensorHom_eq := by intros; rfl
  associator_eq := by intros; rfl
  leftUnitor_eq := by intros; rfl
  rightUnitor_eq := by intros; rfl

/-- The monoidal structure on the `ULift` copy whose tensor product is `tensorSheaf`. -/
@[instance_reducible]
noncomputable def sheafModuleLiftedMonoidal :
    MonoidalCategory (sheafModuleTransportCategory X) :=
  Monoidal.induced (sheafModuleDown X) (sheafModuleInducingData X)

attribute [local instance] sheafModuleLiftedMonoidal

/-- The projection from the `ULift` copy, read as a functor into the localized monoidal
category. -/
noncomputable def sheafModuleDownToLocalized :
    sheafModuleTransportCategory X ⥤ localizedSheafModules X :=
  sheafModuleDown X

/-- The projection from the `ULift` copy is a monoidal functor. -/
@[instance_reducible]
noncomputable def sheafModuleDownToLocalizedMonoidal :
    (sheafModuleDownToLocalized X).Monoidal :=
  Monoidal.fromInducedMonoidal (sheafModuleDown X) (sheafModuleInducingData X)

end Localized

attribute [local instance] sheafModuleDown_faithful sheafModuleLiftedMonoidal
  sheafModuleDownToLocalizedMonoidal

/-- **The monoidal structure on sheaves of `O_X`-modules** (Stacks 01CA): the tensor product
is the sheafified tensor product `tensorSheaf` and the unit is the structure sheaf, as recorded
by `monoidal_tensorObj` and `monoidal_tensorUnit`. -/
@[instance_reducible]
noncomputable def monoidal : MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  Monoidal.transport
    (CategoryTheory.ULift.equivalence (C := SheafOfModules.{u} (structureSheafRing X))).symm

attribute [local instance] monoidal

/-- The tensor product of `monoidal` is the sheafified tensor product. -/
theorem monoidal_tensorObj (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (A ⊗ B) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B)) := rfl

/-- The unit of `monoidal` is the structure sheaf. -/
theorem monoidal_tensorUnit :
    (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) =
      SheafOfModules.unit (structureSheafRing X) := rfl

/-- A local section of the structure sheaf, read as a section of the monoidal unit of
`monoidal`.  The ascription is what keeps the unitor formulas in the same spelling as the rest
of the section formulas; see `tensorObjSection`. -/
noncomputable abbrev unitSection (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U) :
    (𝟙_ (SheafOfModules.{u} (structureSheafRing X))).val.obj U := r

/-- The canonical map `A(U) ⊗_{O_X(U)} B(U) → (A ⊗ B)(U)` on local sections, with its target
written as the tensor product of `monoidal` rather than as `tensorSheaf`.  The two are equal
objects by `monoidal_tensorObj`, but the module structures on their sections are two *spellings*
of one structure, and a statement mixing the two is not type-correct at `implicit` transparency;
ascribing the target here keeps all of the section formulas below in a single spelling. -/
noncomputable abbrev tensorObjSection (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ)
    (t : TensorProduct (X.presheaf.obj U) (A.val.obj U) (B.val.obj U)) :
    (A ⊗ B).val.obj U :=
  toTensorSheafSection X A B U t

/-- The image of a pure tensor of local sections in `(A ⊗ B)(U)`.  Writing every section
formula with this abbreviation, rather than with `⊗ₜ` in place, is what makes them *chain*: the
module structures carried by the `⊗ₜ` are synthesized once here, for the variables `A`, `B`, `U`,
so that any two instantiations of any two of those formulas agree syntactically.  Synthesizing
them afresh at a concrete argument instead produces a different — definitionally equal, but not
cheaply so — spelling of the same structure. -/
noncomputable abbrev tensorObjTmul (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) : (A ⊗ B).val.obj U :=
  tensorObjSection X A B U (a ⊗ₜ[X.presheaf.obj U] b)

/-! ### The forgetful functor is lax monoidal -/

/-- The identity, read as a functor from sheaves of modules carrying `monoidal` to the
localized monoidal category. -/
noncomputable def sheafModuleToLocalized :
    SheafOfModules.{u} (structureSheafRing X) ⥤ localizedSheafModules X := 𝟭 _

/-- `sheafModuleToLocalized` is monoidal: it is the inverse of the `ULift` equivalence
followed by `sheafModuleDownToLocalized`. -/
@[instance_reducible]
noncomputable def sheafModuleToLocalizedMonoidal : (sheafModuleToLocalized X).Monoidal :=
  inferInstanceAs ((Monoidal.equivalenceTransported
      (CategoryTheory.ULift.equivalence
        (C := SheafOfModules.{u} (structureSheafRing X))).symm).inverse ⋙
    sheafModuleDownToLocalized X).Monoidal

attribute [local instance] sheafModuleToLocalizedMonoidal

/-- The forgetful functor, read as a functor out of the localized monoidal category. -/
noncomputable def localizedSheafModuleForget :
    localizedSheafModules X ⥤ presheafModuleCategory X := sheafModuleForget X

/-- The forgetful functor out of the localized monoidal category is lax monoidal, being right
adjoint to the (monoidal) localization functor. -/
@[instance_reducible]
noncomputable def localizedSheafModuleForgetLax :
    (localizedSheafModuleForget X).LaxMonoidal :=
  Adjunction.rightAdjointLaxMonoidal
    (F := Localization.Monoidal.toMonoidalCategory (sheafModuleSheafification X)
      (sheafModuleLocalEquivalences X) (sheafModuleUnitIso X))
    (G := localizedSheafModuleForget X)
    (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing X).obj))

attribute [local instance] localizedSheafModuleForgetLax

/-- The forgetful functor from sheaves of `O_X`-modules to presheaves of `O_X`-modules is lax
monoidal for `monoidal`; its structure maps are the sheafification units
(`monoidal_forget_mu`, `monoidal_forget_epsilon`). -/
@[instance_reducible]
noncomputable def sheafModuleForgetLax : (sheafModuleForget X).LaxMonoidal :=
  inferInstanceAs (sheafModuleToLocalized X ⋙ localizedSheafModuleForget X).LaxMonoidal

attribute [local instance] sheafModuleForgetLax

/-- The tensorator of `sheafModuleForgetLax`, as the composite of the tensorators of
`sheafModuleToLocalized` and `localizedSheafModuleForget`. -/
private theorem forgetLax_mu_comp (A B : SheafOfModules.{u} (structureSheafRing X)) :
    Functor.LaxMonoidal.μ (sheafModuleForget X) A B =
      Functor.LaxMonoidal.μ (localizedSheafModuleForget X) A B ≫
        (sheafModuleForget X).map
          (Functor.LaxMonoidal.μ (sheafModuleToLocalized X) A B) := rfl

/-- The inverse of the comparison isomorphism, written out.  The right-hand side is the only
place in this file where the tensor product of two morphisms has to be elaborated in the
localized monoidal category rather than in `monoidal`; naming it here lets every later
statement be phrased with `sheafModuleTensorCompareIso` instead. -/
private theorem sheafModuleTensorCompareIso_inv
    (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (sheafModuleTensorCompareIso X A B).inv =
      (Localization.Monoidal.μ (sheafModuleSheafification X) (sheafModuleLocalEquivalences X)
          (sheafModuleUnitIso X) A.val B.val).inv ≫
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (structureSheafRing X).obj)).counit.app A ⊗ₘ
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 (structureSheafRing X).obj)).counit.app B) := rfl

/-- The sheafification unit at the presheaf tensor product of the two underlying presheaves,
with its target *written* as the underlying presheaf of `tensorSheaf`.  The two spellings of
that object are definitionally equal but not equal at `implicit` transparency, so without this
ascription a goal mentioning the unit is not type-correct there and no `rw` fires. -/
private noncomputable abbrev tensorSheafifyUnit
    (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (sheafModuleForget X).obj A ⊗ (sheafModuleForget X).obj B ⟶
      (sheafModuleForget X).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B))) :=
  sheafifyUnit X ((sheafModuleForget X).obj A ⊗ (sheafModuleForget X).obj B)

/-- The tensorator of `sheafModuleForgetLax`, factored through the comparison isomorphism: the
tensorator of `localizedSheafModuleForgetLax` is the sheafification unit followed by the
inverse comparison, and the tensorator of `sheafModuleToLocalizedMonoidal` is the comparison
itself.  Both halves hold by definition, and so does their composite. -/
private theorem forgetLax_mu_factor (A B : SheafOfModules.{u} (structureSheafRing X)) :
    Functor.LaxMonoidal.μ (sheafModuleForget X) A B =
      tensorSheafifyUnit X A B ≫
        ((sheafModuleForget X).map (sheafModuleTensorCompareIso X A B).inv ≫
          (sheafModuleForget X).map
            ((sheafModuleTensorCompareIso X A B).hom ≫
              𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj
                  (B))))) := by
  conv_rhs => rw [sheafModuleTensorCompareIso_inv]
  rfl

/-- `tensorSheafifyUnit` is the sheafification unit at `presheafTensor`.  The two presheaf
tensor products are definitionally equal objects, which is all `congr 1` needs; comparing the
two spellings inside a *morphism* type is what the ascription of `tensorSheafifyUnit` avoids. -/
private theorem tensorSheafifyUnit_eq (A B : SheafOfModules.{u} (structureSheafRing X)) :
    tensorSheafifyUnit X A B =
      sheafifyUnit X ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B.val))) := by
  congr 1

/-- The inverse comparison followed by the comparison is the identity, so post-composing with
the pair changes nothing. -/
private theorem comp_compare_roundtrip {Q : presheafModuleCategory X}
    (A B : SheafOfModules.{u} (structureSheafRing X))
    (u : Q ⟶ (sheafModuleForget X).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B)))) :
    u ≫ ((sheafModuleForget X).map (sheafModuleTensorCompareIso X A B).inv ≫
      (sheafModuleForget X).map
        ((sheafModuleTensorCompareIso X A B).hom ≫
          𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj
              (B))))) = u :=
  (congrArg (u ≫ ·) (((sheafModuleForget X).map_comp _ _).symm.trans
    ((congrArg (sheafModuleForget X).map
        ((sheafModuleTensorCompareIso X A B).inv_hom_id_assoc _)).trans
      ((sheafModuleForget X).map_id _)))).trans (Category.comp_id u)

/-- The tensor-comparison map of the lax monoidal forgetful functor is the sheafification unit
of the presheaf tensor product. -/
theorem monoidal_forget_mu (A B : SheafOfModules.{u} (structureSheafRing X)) :
    Functor.LaxMonoidal.μ (sheafModuleForget X) A B =
      sheafifyUnit X ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B.val))) :=
  ((forgetLax_mu_factor X A B).trans
    (comp_compare_roundtrip X A B (tensorSheafifyUnit X A B))).trans
      (tensorSheafifyUnit_eq X A B)

/-- The unit of `sheafModuleForgetLax`, as the composite of the units of
`sheafModuleToLocalized` and `localizedSheafModuleForget`. -/
private theorem forgetLax_epsilon_comp :
    Functor.LaxMonoidal.ε (sheafModuleForget X) =
      Functor.LaxMonoidal.ε (localizedSheafModuleForget X) ≫
        (sheafModuleForget X).map
          (Functor.LaxMonoidal.ε (sheafModuleToLocalized X)) := rfl

/-- The unit of `sheafModuleToLocalizedMonoidal` is the identity. -/
private theorem toLocalized_epsilon_map :
    (sheafModuleForget X).map (Functor.LaxMonoidal.ε (sheafModuleToLocalized X)) =
      𝟙 ((SheafOfModules.unit (structureSheafRing X)).val) := rfl

/-- The unit of `localizedSheafModuleForgetLax`, read off the sheafification adjunction. -/
private theorem localizedForget_epsilon :
    Functor.LaxMonoidal.ε (localizedSheafModuleForget X) =
      (PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheafRing X).obj)).unit.app (𝟙_ (presheafModuleCategory X)) ≫
        (sheafModuleUnitIso X).hom.val := rfl

/-- The chosen unit isomorphism is the counit of the sheafification adjunction. -/
private theorem sheafModuleUnitIso_hom :
    (sheafModuleUnitIso X).hom =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).counit.app
          (SheafOfModules.unit (structureSheafRing X)) := by
  change (sheafModuleSheafification X).map
      (𝟙 ((sheafModuleForget X).obj (SheafOfModules.unit (structureSheafRing X)))) ≫
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheafRing X).obj)).counit.app
          (SheafOfModules.unit (structureSheafRing X)))).hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The unit of `localizedSheafModuleForgetLax` is the identity; this is the right triangle
identity of the sheafification adjunction. -/
private theorem localizedForget_epsilon_id :
    Functor.LaxMonoidal.ε (localizedSheafModuleForget X) =
      𝟙 (𝟙_ (presheafModuleCategory X)) := by
  rw [localizedForget_epsilon, sheafModuleUnitIso_hom]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)).right_triangle_components
      (SheafOfModules.unit (structureSheafRing X))

/-- The unit-comparison map of the lax monoidal forgetful functor is the identity. -/
theorem monoidal_forget_epsilon :
    Functor.LaxMonoidal.ε (sheafModuleForget X) =
      𝟙 (𝟙_ (presheafModuleCategory X)) := by
  refine (forgetLax_epsilon_comp X).trans ?_
  rw [toLocalized_epsilon_map]
  exact (Category.comp_id _).trans (localizedForget_epsilon_id X)

/-! ### Extensionality -/

/-- A morphism out of a sheafified tensor product is determined by its values on local pure
tensors. -/
theorem tensor_hom_ext {A B C : SheafOfModules.{u} (structureSheafRing X)}
    {f g : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B)) ⟶ C}
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      (f.val.app U).hom (toTensorSheafSection X A B U (a ⊗ₜ[X.presheaf.obj U] b)) =
      (g.val.app U).hom (toTensorSheafSection X A B U (a ⊗ₜ[X.presheaf.obj U] b))) :
    f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)).homEquiv _ C).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' fun a b => ?_
  exact h U a b

/-- A morphism of sheaves of modules is determined locally: if every point has a neighbourhood
`W` such that the two morphisms agree on all opens mapping to `W`, they are equal. -/
theorem hom_ext_of_locally {A B : SheafOfModules.{u} (structureSheafRing X)} (f g : A ⟶ B)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∀ (V : Opens X.carrier) (_ : V ⟶ W),
        f.val.app (op V) = g.val.app (op V)) : f = g := by
  ext U s
  have hS : Presheaf.equalizerSieve (F := B.val.presheaf)
      ((f.val.app U).hom s) ((g.val.app U).hom s) ∈ JX X U.unop := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨W, hxW, hW⟩ := h x
    refine ⟨W ⊓ U.unop, homOfLE inf_le_right, ?_, hxW, hx⟩
    change (B.val.map (homOfLE (inf_le_right : W ⊓ U.unop ≤ _)).op).hom ((f.val.app U).hom s) =
      (B.val.map (homOfLE (inf_le_right : W ⊓ U.unop ≤ _)).op).hom ((g.val.app U).hom s)
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply,
      hW (W ⊓ U.unop) (homOfLE inf_le_left)]
  exact B.isSheaf.isSeparated _ _ hS _ _ (fun _ _ hf => hf)

/-! ### Bridging the lax monoidal structure to local sections

These are the shallow steps out of which the `*_tmul` lemmas below are assembled.  Each is
stated with its morphisms as *variables*, and that is the point: evaluating a whiskering or an
associator on a pure tensor forces the morphism involved into weak head normal form, which for
the concrete tensorators of `sheafModuleForgetLax` is not affordable, while instantiating a
variable-only lemma costs nothing. -/

/-- A composite of morphisms of sheaves of modules, on a local section. -/
theorem sheaf_comp_app_apply {A B C : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ B) (g : B ⟶ C) (U : (Opens X.carrier)ᵒᵖ) (s : A.val.obj U) :
    ((f ≫ g).val.app U).hom s = (g.val.app U).hom ((f.val.app U).hom s) := rfl

/-- If an isomorphism of sheaves of modules sends `x` to `y` on local sections, its inverse sends
`y` back to `x`. -/
private theorem inv_app_apply_of_hom_app_apply {A B : SheafOfModules.{u} (structureSheafRing X)}
    (e : A ≅ B) (U : (Opens X.carrier)ᵒᵖ) {x : A.val.obj U} {y : B.val.obj U}
    (h : (e.hom.val.app U).hom x = y) : (e.inv.val.app U).hom y = x := by
  subst h
  refine (sheaf_comp_app_apply X e.hom e.inv U x).symm.trans ?_
  rw [e.hom_inv_id]
  rfl

/-- A three-step composite of morphisms of sheaves of modules, on a local section, with the
three one-step evaluations supplied as hypotheses.  Supplying them, rather than rewriting with
them afterwards, keeps the module structures on the intermediate sections the ones the
composite itself produces. -/
theorem sheaf_comp3_app_apply_of {A B C D : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ B) (g : B ⟶ C) (k : C ⟶ D) (U : (Opens X.carrier)ᵒᵖ) (s : A.val.obj U)
    {b : B.val.obj U} (hb : (f.val.app U).hom s = b)
    {c : C.val.obj U} (hc : (g.val.app U).hom b = c)
    {d : D.val.obj U} (hd : (k.val.app U).hom c = d) :
    ((f ≫ g ≫ k).val.app U).hom s = d := by
  subst hb hc hd
  rfl

/-- A morphism of sheaves of modules, pushed through the forgetful functor, on a local
section. -/
private theorem forgetMap_app_apply {A B : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ B) (U : (Opens X.carrier)ᵒᵖ) (s : A.val.obj U) :
    (((sheafModuleForget X).map f).app U).hom s = (f.val.app U).hom s := rfl

/-- The tensorator of the lax monoidal forgetful functor, on a pure tensor of local
sections. -/
private theorem mu_app_tmul (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    ((Functor.LaxMonoidal.μ (sheafModuleForget X) A B).app U).hom
        (a ⊗ₜ[X.presheaf.obj U] b) =
      tensorObjTmul X A B U a b := by
  rw [monoidal_forget_mu]
  rfl

/-- The associativity axiom of a lax monoidal functor between presheaves of modules, read on a
pure tensor of local sections.  The five one-step evaluations are taken as hypotheses, so that
the statement mentions no concrete morphism at all; the caller supplies them as four
`mu_app_tmul`s and one `forgetMap_app_apply`. -/
private theorem laxAssoc_tmul_of (PA PB PC : PresheafOfModules.{u} (O X))
    {QAB QABC QBC QT : PresheafOfModules.{u} (O X)}
    (m₁ : PA ⊗ PB ⟶ QAB) (m₂ : QAB ⊗ PC ⟶ QABC) (t : QABC ⟶ QT)
    (m₃ : PB ⊗ PC ⟶ QBC) (m₄ : PA ⊗ QBC ⟶ QT)
    (hyp : m₁ ▷ PC ≫ m₂ ≫ t = (α_ PA PB PC).hom ≫ PA ◁ m₃ ≫ m₄)
    (U : (Opens X.carrier)ᵒᵖ) (p : PA.obj U) (q : PB.obj U) (r : PC.obj U)
    {sab : QAB.obj U} (hab : (m₁.app U).hom (p ⊗ₜ[X.presheaf.obj U] q) = sab)
    {sabc : QABC.obj U} (habc : (m₂.app U).hom (sab ⊗ₜ[X.presheaf.obj U] r) = sabc)
    {lhs : QT.obj U} (hlhs : (t.app U).hom sabc = lhs)
    {sbc : QBC.obj U} (hbc : (m₃.app U).hom (q ⊗ₜ[X.presheaf.obj U] r) = sbc)
    {rhs : QT.obj U} (hrhs : (m₄.app U).hom (p ⊗ₜ[X.presheaf.obj U] sbc) = rhs) :
    lhs = rhs := by
  subst hab habc hlhs hbc hrhs
  exact congrArg (fun w => (w.app U).hom
    ((p ⊗ₜ[X.presheaf.obj U] q) ⊗ₜ[X.presheaf.obj U] r)) hyp

/-! ### The structural morphisms on local pure tensors -/

/-- The tensor product of two morphisms, on a local pure tensor. -/
theorem tensorHom_tmul {A A' B B' : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ A') (g : B ⟶ B')
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    ((f ⊗ₘ g).val.app U).hom (tensorObjTmul X A B U a b) =
    tensorObjTmul X A' B' U ((f.val.app U).hom a) ((g.val.app U).hom b) := by
  have h := Functor.LaxMonoidal.μ_natural (sheafModuleForget X) f g
  rw [monoidal_forget_mu, monoidal_forget_mu] at h
  exact congrArg (fun q => (q.app U).hom (a ⊗ₜ[X.presheaf.obj U] b)) h.symm

/-- The tensor product of two morphisms for `monoidal` is the canonical induced morphism
`tensorSheafMap`. -/
theorem monoidal_tensorHom {A A' B B' : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ A') (g : B ⟶ B') :
    eqToHom (monoidal_tensorObj X A B).symm ≫ (f ⊗ₘ g) ≫
      eqToHom (monoidal_tensorObj X A' B') =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
          ((f, g) : (_, _) ⟶ (_, _))) := by
  have key : (f ⊗ₘ g) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        ((f, g) : (_, _) ⟶ (_, _))) :=
    tensor_hom_ext X fun U a b =>
      (tensorHom_tmul X f g U a b).trans
        (tensorSheafMap_app_toTensorSheafSection X A B A' B' f g U.unop a b).symm
  refine Eq.trans ?_ key
  change (𝟙 _ ≫ (f ⊗ₘ g) ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- Whiskering a morphism on the right, on a local pure tensor. -/
theorem whiskerRight_tmul {A A' : SheafOfModules.{u} (structureSheafRing X)} (f : A ⟶ A')
    (B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    ((f ▷ B).val.app U).hom (tensorObjTmul X A B U a b) =
      tensorObjTmul X A' B U ((f.val.app U).hom a) b := by
  rw [← tensorHom_id]
  exact tensorHom_tmul X f (𝟙 B) U a b

/-- Whiskering a morphism on the left, on a local pure tensor. -/
theorem whiskerLeft_tmul (A : SheafOfModules.{u} (structureSheafRing X))
    {B B' : SheafOfModules.{u} (structureSheafRing X)} (g : B ⟶ B')
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    ((A ◁ g).val.app U).hom (tensorObjTmul X A B U a b) =
      tensorObjTmul X A B' U a ((g.val.app U).hom b) := by
  rw [← id_tensorHom]
  exact tensorHom_tmul X (𝟙 A) g U a b

/-- The associator, on a local pure tensor. -/
theorem associator_tmul (A B C : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U) :
    (((α_ A B C).hom).val.app U).hom
      (tensorObjTmul X (A ⊗ B) C U (tensorObjTmul X A B U a b) c) =
    tensorObjTmul X A (B ⊗ C) U a (tensorObjTmul X B C U b c) := by
  have h := Functor.LaxMonoidal.associativity (sheafModuleForget X) A B C
  exact laxAssoc_tmul_of X ((sheafModuleForget X).obj A) ((sheafModuleForget X).obj B)
    ((sheafModuleForget X).obj C) _ _ _ _ _ h U a b c
    (mu_app_tmul X A B U a b)
    (mu_app_tmul X (A ⊗ B) C U _ c)
    (forgetMap_app_apply X (α_ A B C).hom U _)
    (mu_app_tmul X B C U b c)
    (mu_app_tmul X A (B ⊗ C) U a _)

/-- The left unitor, on a local pure tensor. -/
theorem leftUnitor_tmul (A : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (r : X.presheaf.obj U) (a : A.val.obj U) :
    (((λ_ A).hom).val.app U).hom
      (tensorObjTmul X (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) A U
        (unitSection X U r) a) = r • a := by
  have h := Functor.LaxMonoidal.left_unitality (sheafModuleForget X) A
  rw [monoidal_forget_epsilon, monoidal_forget_mu] at h
  exact congrArg (fun q => (q.app U).hom (r ⊗ₜ[X.presheaf.obj U] a)) h.symm

/-- The right unitor, on a local pure tensor. -/
theorem rightUnitor_tmul (A : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (r : X.presheaf.obj U) :
    (((ρ_ A).hom).val.app U).hom
      (tensorObjTmul X A (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) U a
        (unitSection X U r)) = r • a := by
  have h := Functor.LaxMonoidal.right_unitality (sheafModuleForget X) A
  rw [monoidal_forget_epsilon, monoidal_forget_mu] at h
  exact congrArg (fun q => (q.app U).hom (a ⊗ₜ[X.presheaf.obj U] r)) h.symm

/-- The inverse associator, on a local pure tensor. -/
theorem associator_inv_tmul (A B C : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U) :
    (((α_ A B C).inv).val.app U).hom
      (tensorObjTmul X A (B ⊗ C) U a (tensorObjTmul X B C U b c)) =
    tensorObjTmul X (A ⊗ B) C U (tensorObjTmul X A B U a b) c := by
  exact inv_app_apply_of_hom_app_apply X (α_ A B C) U (associator_tmul X A B C U a b c)

/-- The inverse left unitor, on a local section. -/
theorem leftUnitor_inv_apply (A : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) :
    (((λ_ A).inv).val.app U).hom a =
    tensorObjTmul X (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) A U
      (unitSection X U 1) a := by
  have h := leftUnitor_tmul X A U 1 a
  rw [one_smul] at h
  exact inv_app_apply_of_hom_app_apply X (λ_ A) U h

/-- The inverse right unitor, on a local section. -/
theorem rightUnitor_inv_apply (A : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) :
    (((ρ_ A).inv).val.app U).hom a =
    tensorObjTmul X A (𝟙_ (SheafOfModules.{u} (structureSheafRing X))) U a
      (unitSection X U 1) := by
  have h := rightUnitor_tmul X A U a 1
  rw [one_smul] at h
  exact inv_app_apply_of_hom_app_apply X (ρ_ A) U h

/-! ### Sections of the tensor product -/

/-- The canonical map into the sheafified tensor product is additive on finite sums. -/
theorem tensorSection_sum (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) {I : Type*} (s : Finset I)
    (t : I → A.val.obj U ⊗[X.presheaf.obj U] B.val.obj U) :
    tensorObjSection X A B U (∑ i ∈ s, t i) =
      ∑ i ∈ s, tensorObjSection X A B U (t i) :=
  map_sum ((sheafifyUnit X
    ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B.val)))).app U).hom _ _

/-- `tensorObjTmul` is the canonical map of Stacks 01CB into the sheafified tensor product.
Stated with `U` a variable so that any instantiation is a substitution, which is what makes it
usable as a bridge to the lemmas phrased with `toTensorSheafSection`. -/
theorem tensorObjTmul_eq (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    tensorObjTmul X A B U a b =
      toTensorSheafSection X A B U (a ⊗ₜ[X.presheaf.obj U] b) := rfl

/-- `tensorObjTmul` is additive in its left argument. -/
theorem tensorObjTmul_sum_left (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) {I : Type*} (s : Finset I) (a : I → A.val.obj U)
    (b : B.val.obj U) :
    tensorObjTmul X A B U (∑ i ∈ s, a i) b = ∑ i ∈ s, tensorObjTmul X A B U (a i) b :=
  (congrArg (tensorObjSection X A B U) (TensorProduct.sum_tmul s a b)).trans
    (tensorSection_sum X A B U s _)

/-- `tensorObjTmul` is additive in its right argument. -/
theorem tensorObjTmul_sum_right (A B : SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (a : A.val.obj U) {I : Type*} (s : Finset I)
    (b : I → B.val.obj U) :
    tensorObjTmul X A B U a (∑ i ∈ s, b i) = ∑ i ∈ s, tensorObjTmul X A B U a (b i) :=
  (congrArg (tensorObjSection X A B U) (TensorProduct.tmul_sum a s b)).trans
    (tensorSection_sum X A B U s _)

/-- Restricting a local pure tensor restricts its two factors. -/
theorem tensorSection_restrict (A B : SheafOfModules.{u} (structureSheafRing X))
    {U V : Opens X.carrier} (k : V ⟶ U)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B))).val.map k.op).hom
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A B (op V)
      ((A.val.map k.op).hom a ⊗ₜ[X.presheaf.obj (op V)] (B.val.map k.op).hom b) :=
  (PresheafOfModules.naturality_apply
    (sheafifyUnit X ((PresheafOfModules.tensorObj (O := (X).presheaf) (A.val) (B.val)))) k.op
    (a ⊗ₜ[X.presheaf.obj (op U)] b)).symm

end Stacks.SheafOfModules.OnSpace
