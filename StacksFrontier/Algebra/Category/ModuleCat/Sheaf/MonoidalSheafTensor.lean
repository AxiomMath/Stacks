module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Closed
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The symmetric monoidal structure on `Mod(O)` whose tensor product is
  `Stacks.SheafOfModules.Tensor.sheafTensor`

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` equips `Mod(O)` with a symmetric
monoidal structure, obtained by transporting Mathlib's symmetric monoidal structure on
presheaves of modules along the localization `Mod_{pre}(O) ⥤ Mod(O)`.  Its tensor product is
therefore the localized bifunctor `Localization.Monoidal.tensorBifunctor`, and not
`Stacks.SheafOfModules.Tensor.sheafTensor`, the bifunctor `(ℱ, 𝒢) ↦ (ℱ ⊗_{pre} 𝒢)^#` which the
  Stacks tag
files actually use.

This file produces the isomorphism between the two and re-seats the structure on the second
one, so that `curriedTensor (Mod(O))` *is* `Stacks.SheafOfModules.Tensor.sheafTensor R` and `𝟙_
  (Mod(O))` *is*
`SheafOfModules.unit`, definitionally.  The isomorphism is
`((ℱ ⊗_{pre} 𝒢)^# ≅ ℱ^# ⊗ 𝒢^# ≅ ℱ ⊗ 𝒢` for `ℱ`, `𝒢` already sheaves: the first map is the
monoidality of sheafification, the second is the counit of the sheafification adjunction, which
is an isomorphism because the forgetful functor to presheaves of modules is fully faithful.

## Main definitions

* `SheafOfModules.sheafifyCounitIso`: the counit isomorphism `(ℱ^♭)^# ≅ ℱ`.
* `SheafOfModules.sheafTensorIso`: `ℱ ⊗ 𝒢 ≅ (Stacks.SheafOfModules.Tensor.sheafTensor R).obj ℱ
  |>.obj 𝒢`, and
  `SheafOfModules.sheafTensorNatIso`, its bifunctor form.
* `SheafOfModules.monoidalCategorySheafTensor`,
  `SheafOfModules.symmetricCategorySheafTensor`: the re-seated symmetric monoidal structure.

## Main results

* `SheafOfModules.curriedTensor_sheafTensor`: the tensor product of the re-seated structure is
  `Stacks.SheafOfModules.Tensor.sheafTensor R`.
* `SheafOfModules.tensorUnit_sheafTensor`: its unit is `SheafOfModules.unit`.
* `SheafOfModules.monoidalPreadditiveSheafTensor`: the re-seated tensor product is bilinear on
  morphisms.

## Implementation notes

`Mod(O)` carries two monoidal structures here, the localized one and the re-seated one, so the
re-seated one is always named by `@`-application and never left to instance synthesis; see the
implementation notes of `StacksFrontier/CategoryTheory/Monoidal/Reseat.lean`.

Everything is stated for the single sheaf of rings `Stacks.SheafOfModules.Tensor.ringSheaf R`,
the one `Stacks.SheafOfModules.Tensor.sheafTensor` is stated in.  The monoidal and symmetric
structures on presheaves of modules over it are the canonical instances
`Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory` and
`Stacks.SheafOfModules.Tensor.ringSheafPresheafSymmetricCategory`, and the monoidality of
sheafification is the instance `SheafOfModules.sheafification_monoidal`.

The counit isomorphism and its naturality are proved for an arbitrary sheaf of rings and then
specialized, rather than proved for `Stacks.SheafOfModules.Tensor.ringSheaf R` directly: in the
  specialized
spelling the elaborator has to unfold `Stacks.SheafOfModules.Tensor.ringSheaf` to see that the
adjunction's counit has the stated type, which is expensive.

**Universes.** The module universe is always equal to the universe of the sheaf of rings, as it
is for `SheafOfModules.monoidalCategory`: Mathlib's monoidal structure on presheaves of modules
ties the two together and to nothing else.  The file is in two halves, which differ only in how
free that common universe is of the two site universes `u` and `v`.

In `FreeSections` it is a free `w`.  Almost everything the re-seating needs is available there:
`SheafOfModules.monoidalCategory`,
`Stacks.SheafOfModules.Tensor.ringSheafPresheafMonoidalCategory` and the counit isomorphism are
all stated at a free `w`, and the `HasSheafCompose` the first of them asks for is supplied at a
free `w` by `Stacks.hasSheafCompose_forget₂_commRingCat`.  The one thing that is not automatic is
the additivity of `Stacks.SheafOfModules.Tensor.sheafTensor` in each variable: it goes through
the biproducts of `Mod(O)`, which come from the abelian structure and so need the *sheafifying*
`HasSheafify` rather than the `HasWeakSheafify` assumed here.  So the two `MonoidalPreadditive`
results, and only they, assume
`HasBinaryBiproducts (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))`, which
holds whenever `w` dominates the site universes.

In `Closed` it is `max u v w`.  The closed structure comes from Day's reflection theorem applied
to the *presheaf* internal hom, and the sections of that internal hom genuinely live in
`max u v w` -- see `PresheafOfModules.monoidalClosed` -- so there is no closed structure at the
presheaf level to reflect at a smaller module universe.  The colimit preservation of the tensor
product, being a consequence of closedness, is in this half too.  Both halves are free in `w`, so
a consumer on a site with `max u v = u` and a sheaf of rings in `CommRingCat.{u}` gets the whole
file at `w := u`.
-/

@[expose] public section



universe v u w

open CategoryTheory Limits MonoidalCategory Opposite
open Functor.LaxMonoidal Functor.Monoidal

noncomputable section

section TensorCounitNaturality

variable {D E : Type*} [Category* D] [Category* E]
  [MonoidalCategory D] [MonoidalCategory E] (L : D ⥤ E) [L.Monoidal]

private lemma tensorCounit_naturality_right
    {M' N₁' N₂' : D} {M N₁ N₂ : E}
    (eM : L.obj M' ≅ M) (eN₁ : L.obj N₁' ≅ N₁) (eN₂ : L.obj N₂' ≅ N₂)
    (g : N₁ ⟶ N₂) (g' : N₁' ⟶ N₂')
    (hg : g ≫ eN₂.inv = eN₁.inv ≫ L.map g') :
    M ◁ g ≫ (eM.inv ⊗ₘ eN₂.inv) ≫ μ L M' N₂' =
      (eM.inv ⊗ₘ eN₁.inv) ≫ μ L M' N₁' ≫ L.map (M' ◁ g') := by
  simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [hg, MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right]

private lemma tensorCounit_naturality_left
    {M₁' M₂' N' : D} {M₁ M₂ N : E}
    (eM₁ : L.obj M₁' ≅ M₁) (eM₂ : L.obj M₂' ≅ M₂) (eN : L.obj N' ≅ N)
    (f : M₁ ⟶ M₂) (f' : M₁' ⟶ M₂')
    (hf : f ≫ eM₂.inv = eM₁.inv ≫ L.map f') :
    f ▷ N ≫ (eM₂.inv ⊗ₘ eN.inv) ≫ μ L M₂' N' =
      (eM₁.inv ⊗ₘ eN.inv) ≫ μ L M₁' N' ≫ L.map (f' ▷ N') := by
  simp only [tensorHom_def, Category.assoc, ← MonoidalCategory.comp_whiskerRight_assoc]
  rw [hf, MonoidalCategory.comp_whiskerRight, Category.assoc,
    ← whisker_exchange_assoc, μ_natural_left]

end TensorCounitNaturality

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Counit

variable (R : Sheaf J RingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The counit of the sheafification adjunction for modules, as an isomorphism: the
sheafification of the underlying presheaf of modules of a sheaf of modules is itself. -/
def sheafifyCounitIso (M : SheafOfModules.{w} R) :
    (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj ((forget R).obj M) ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).app M

/-- Naturality of `SheafOfModules.sheafifyCounitIso`. -/
@[reassoc]
lemma sheafifyCounitIso_naturality {M N : SheafOfModules.{w} R} (f : M ⟶ N) :
    (PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map ((forget R).map f) ≫
        (sheafifyCounitIso R N).hom = (sheafifyCounitIso R M).hom ≫ f :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality f

end Counit

section FreeSections

variable (R : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory

/-- The counit isomorphism `(ℱ^♭)^# ≅ ℱ`, for the spelling `Stacks.SheafOfModules.Tensor.ringSheaf
  R`. -/
def counitIso (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M) ≅ M :=
  sheafifyCounitIso (Stacks.SheafOfModules.Tensor.ringSheaf R) M

/-- Naturality of `SheafOfModules.counitIso`. -/
@[reassoc]
lemma counitIso_naturality {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
  R)}
    (f : M ⟶ N) :
    (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map ((forget
      (Stacks.SheafOfModules.Tensor.ringSheaf R)).map f) ≫
        (counitIso R N).hom = (counitIso R M).hom ≫ f :=
  sheafifyCounitIso_naturality (Stacks.SheafOfModules.Tensor.ringSheaf R) f

/-- Naturality of the inverse of `SheafOfModules.counitIso`. -/
@[reassoc]
lemma comp_counitIso_inv {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (f : M ⟶ N) :
    f ≫ (counitIso R N).inv = (counitIso R M).inv ≫ (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, counitIso_naturality, Iso.inv_hom_id_assoc]

/-- **The tensor product of `Mod(O)` is the sheafified presheaf tensor product.**  This is the
composite of the inverse monoidality isomorphism of sheafification with the counit
isomorphisms. -/
def sheafTensorIso (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    M ⊗ N ≅ (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).obj
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M ⊗
        (forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N) :=
  (tensorIso (counitIso R M) (counitIso R N)).symm ≪≫ μIso (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) _ _

/-- Naturality of `SheafOfModules.sheafTensorIso` in the second variable. -/
lemma sheafTensorIso_naturality_right
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    {N₁ N₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (g : N₁ ⟶ N₂) :
    M ◁ g ≫ (sheafTensorIso R M N₂).hom =
      (sheafTensorIso R M N₁).hom ≫ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
        ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj M ◁
          (forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map g) := by
  simpa only [sheafTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_inv, μIso_hom,
    Category.assoc] using
    tensorCounit_naturality_right (PresheafOfModules.sheafification.{w}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
      (counitIso R M) (counitIso R N₁) (counitIso R N₂) g
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map g) (comp_counitIso_inv R g)

/-- Naturality of `SheafOfModules.sheafTensorIso` in the first variable. -/
lemma sheafTensorIso_naturality_left
    {M₁ M₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (f : M₁ ⟶ M₂)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    f ▷ N ≫ (sheafTensorIso R M₂ N).hom =
      (sheafTensorIso R M₁ N).hom ≫ (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
        ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map f ▷
          (forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj N) := by
  simpa only [sheafTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_inv, μIso_hom,
    Category.assoc] using
    tensorCounit_naturality_left (PresheafOfModules.sheafification.{w}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
      (counitIso R M₁) (counitIso R M₂) (counitIso R N) f
      ((forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map f) (comp_counitIso_inv R f)

/-- `ℱ ⊗ -` is `(Stacks.SheafOfModules.Tensor.sheafTensor R).obj ℱ`. -/
def sheafTensorIsoApp (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (curriedTensor (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))).obj M ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor R).obj M :=
  NatIso.ofComponents (sheafTensorIso R M) (sheafTensorIso_naturality_right R M)

/-- **The tensor product of `Mod(O)` is `Stacks.SheafOfModules.Tensor.sheafTensor R`**, as
  bifunctors. -/
def sheafTensorNatIso :
    curriedTensor (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅
      Stacks.SheafOfModules.Tensor.sheafTensor R :=
  NatIso.ofComponents (sheafTensorIsoApp R)
    (fun f ↦ NatTrans.ext (funext fun N ↦ sheafTensorIso_naturality_left R f N))

/-- **The unit of `Mod(O)` is the structure sheaf**, viewed as a sheaf of modules over
itself. -/
def unitIso :
    𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≅
      unit (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  counitIso R (unit (Stacks.SheafOfModules.Tensor.ringSheaf R))

variable [HasBinaryBiproducts
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))] in
/-- The localized tensor product of `Mod(O)` is bilinear on morphisms: it is isomorphic to
`Stacks.SheafOfModules.Tensor.sheafTensor R`, which is additive in each variable. -/
instance monoidalPreadditiveRingSheaf :
    MonoidalPreadditive (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) where
  whiskerLeft_zero {_ _ _} := by
    rw [reseat_whiskerLeft' (sheafTensorNatIso R), Functor.map_zero]
    simp only [comp_zero, zero_comp]
  zero_whiskerRight {_ _ _} := by
    rw [reseat_whiskerRight' (sheafTensorNatIso R), Functor.map_zero]
    simp only [NatTrans.app_zero, comp_zero, zero_comp]
  whiskerLeft_add f g := by
    rw [reseat_whiskerLeft' (sheafTensorNatIso R), reseat_whiskerLeft' (sheafTensorNatIso R),
      reseat_whiskerLeft' (sheafTensorNatIso R), Functor.map_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp]
  add_whiskerRight f g := by
    rw [reseat_whiskerRight' (sheafTensorNatIso R), reseat_whiskerRight' (sheafTensorNatIso R),
      reseat_whiskerRight' (sheafTensorNatIso R), Functor.map_add]
    simp only [Preadditive.comp_add, Preadditive.add_comp, NatTrans.app_add]

/-- **The monoidal structure on `Mod(O)` whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor R`** and whose unit is `SheafOfModules.unit`. -/
@[instance_reducible]
def monoidalCategorySheafTensor :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  reseat (sheafTensorNatIso R) (unitIso R)

/-- The tensor product of `monoidalCategorySheafTensor` is
  `Stacks.SheafOfModules.Tensor.sheafTensor R`. -/
lemma curriedTensor_sheafTensor :
    @curriedTensor _ _ (monoidalCategorySheafTensor R) = Stacks.SheafOfModules.Tensor.sheafTensor R
      :=
  curriedTensor_reseat _ _

/-- The unit of `monoidalCategorySheafTensor` is `SheafOfModules.unit`. -/
lemma tensorUnit_sheafTensor :
    @tensorUnit _ _ (monoidalCategorySheafTensor R).toMonoidalCategoryStruct =
      unit (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  tensorUnit_reseat _ _

/-- The re-seated monoidal structure on `Mod(O)` is symmetric. -/
@[instance_reducible]
def symmetricCategorySheafTensor :
    @SymmetricCategory _ _ (monoidalCategorySheafTensor R) :=
  letI := symmetricCategory R
  reseatSymmetric (sheafTensorNatIso R) (unitIso R)

variable [HasBinaryBiproducts
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))] in
/-- The re-seated tensor product on `Mod(O)` is bilinear on morphisms. -/
lemma monoidalPreadditiveSheafTensor :
    @MonoidalPreadditive _ _ _ (monoidalCategorySheafTensor R) :=
  reseatMonoidalPreadditive (sheafTensorNatIso R) (unitIso R)

end FreeSections

section Closed

variable (R : Sheaf J CommRingCat.{max u v w})
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

attribute [local instance] monoidalCategory

/-- The forgetful functor from sheaves of modules to presheaves of modules is fully faithful:
the counit of the sheafification adjunction is an isomorphism. -/
def fullyFaithfulForgetCompRestrictScalars :
    (forget.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).FullyFaithful :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).fullyFaithfulROfIsIsoCounit

/-- The forgetful functor from sheaves of modules to presheaves of modules is faithful. -/
lemma faithful_forgetCompRestrictScalars :
    (forget.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Faithful :=
  (fullyFaithfulForgetCompRestrictScalars R).faithful

/-- The forgetful functor from sheaves of modules to presheaves of modules is full. -/
lemma full_forgetCompRestrictScalars :
    (forget.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
      PresheafOfModules.restrictScalars.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Full :=
  (fullyFaithfulForgetCompRestrictScalars R).full

attribute [local instance] faithful_forgetCompRestrictScalars full_forgetCompRestrictScalars
  symmetricCategory

/-- **`Mod(O)` is monoidal closed.**  Sheaves of modules are a reflective subcategory of
presheaves of modules whose reflector is monoidal, and presheaves of modules are symmetric
monoidal closed, so Day's reflection theorem applies. -/
@[instance_reducible]
def monoidalClosed :
    MonoidalClosed (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  letI : MonoidalClosed (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    PresheafOfModules.monoidalClosed (R₀ := R.obj)
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))

attribute [local instance] monoidalClosed symmetricCategory

/-- `ℱ ⊗_O -` commutes with colimits: it is a left adjoint, `Mod(O)` being monoidal closed. -/
instance preservesColimitsOfSize_sheafTensor_obj {K : Type*} [Category K]
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (F : K ⥤ SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimit F ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M) :=
  reseatPreservesColimit_tensorLeft (sheafTensorNatIso R) F M

/-- `- ⊗_O 𝒢` commutes with colimits, by symmetry. -/
instance preservesColimitsOfSize_sheafTensor_flip_obj {K : Type*} [Category K]
    (N : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (F : K ⥤ SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimit F ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj N) :=
  letI : PreservesColimit F (tensorRight N) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight N)
  reseatPreservesColimit_tensorRight (sheafTensorNatIso R) F N

/-- The re-seated monoidal structure on `Mod(O)` is closed. -/
@[instance_reducible]
def monoidalClosedSheafTensor :
    @MonoidalClosed _ _ (monoidalCategorySheafTensor R) :=
  reseatClosed (sheafTensorNatIso R) (unitIso R)

end Closed

section TensorRightColimits

/-! The instance below is stated at the sections universe `max u v` of the two site universes,
not at the `max u v w` of the `Closed` section: as a global instance it is matched against
modules whose universe is already a single level `u`, where a free `w` would leave
`max u u ?w =?= u` unsolved and send instance search after sheafification hypotheses at an
unknown universe. -/

variable (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- `- ⊗_O 𝒢` commutes with colimits for the re-seated structure: it is isomorphic to `𝒢 ⊗_O -`
by the symmetry, and that is a left adjoint. -/
instance preservesColimit_tensorRight_sheafTensor {K : Type*} [Category K]
    (F : K ⥤ SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (N : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimit F (@tensorRight _ _ (monoidalCategorySheafTensor R) N) :=
  letI := monoidalCategorySheafTensor R
  letI := symmetricCategorySheafTensor R
  letI := monoidalClosedSheafTensor.{v, u, u} R
  preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight N)

end TensorRightColimits

end SheafOfModules

end

end
