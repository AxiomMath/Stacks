module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BraidingScalar.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf

/-!
# The monoidal structure on sheaves of modules and the tensor product sheaf

Let `O` be a sheaf of commutative rings on a site. There are two descriptions of the tensor
product of sheaves of `O`-modules:

* `Stacks.SheafOfModules.TensorSheafification.tensorSheaf O hO M N`, the sheafification of the
  objectwise tensor product, whose
  unit, associativity and symmetry constraints are
  `Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor`, `tensorProductRightUnitor`,
  `tensorProductAssociator` and `tensorProductBraiding` of
  `StacksFrontier/AlgebraicGeometry/Divisors/TensorPower.lean`; these are what
  [Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) states its coherence conditions
  against;
* the monoidal structure `Stacks.SheafOfModules.monoidalCategory`, obtained by localizing the
  monoidal structure on presheaves of modules along sheafification, which is what the general
  monoidal-category API applies to.

`Stacks.SheafOfModules.tensorObjIso` identifies the two tensor products. This file proves that
it identifies the four structure maps as well, which is what lets a statement about the monoidal
structure be read as a statement about the tensor product sheaf, and conversely.

## Main definitions

None mathematically new. `valIso`, `toSheafifyVal`, `sheafifyTensorIso`, `unitIso` and
`assocVal` are the library's `Stacks.SheafOfModules.sheafifyValIso`,
  `Stacks.SheafOfModules.TensorSheafification.toSheafify`,
`Stacks.SheafOfModules.sheafifyTensorIso`, `Stacks.SheafOfModules.sheafifyUnitIso` and
`tensorProductAssociator`, restated with the index of the presheaf category spelled
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` rather than
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O`. See the
implementation notes: the two spellings are the same category, and the restatements are all
`rfl` or a single `exact`, but only in the first spelling are the statements type-correct at
reducible transparency, which is what `rw` and `simp` need.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorObjIso_naturality`: `tensorObjIso` is natural, i.e.
  the monoidal tensor product of morphisms is the sheafification of the presheaf tensor product
  of the underlying morphisms.
* `Stacks.SheafOfModules.Invertible.leftUnitor_hom_eq_tensorProductLeftUnitor` and
  `rightUnitor_hom_eq_tensorProductRightUnitor`: **the unitors of the monoidal structure are the
  unit constraints of the tensor product sheaf.**
* `Stacks.SheafOfModules.Invertible.tensorObjIso_associativity`: **the associator of the
  monoidal structure is the associativity constraint of the tensor product sheaf.**
* `Stacks.SheafOfModules.Invertible.sheafifyTensorIso_natural`,
  `sheafifyTensorIso_associativity`, `leftUnitor_hom_app'`, `rightUnitor_hom_app'`: the
  monoidal-functor structure of sheafification, in the same spelling.

The braiding comparison is not here: it is
`Stacks.SheafOfModules.braiding_hom_eq_tensorSheafBraiding`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BraidingScalar/Basic.lean`), and
`Stacks.SheafOfModules.tensorSheafBraiding O hO M N` is
`Stacks.SheafOfModules.Invertible.tensorProductBraiding O hO M N` by `rfl`.

## Implementation notes

**One spelling per proof.** `Stacks.SheafOfModules.TensorSheafification.sheafify O hO` has source
  category
`PresheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` while
`Stacks.SheafOfModules.sheafifyFunctor O hO`, `sheafifyValIso`, `sheafifyTensorIso` and
`Stacks.SheafOfModules.TensorSheafification.toSheafify` are stated over `PresheafOfModules
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)`.
The two indexes are equal, but `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a
  plain `def`, so the projection
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` does not reduce at reducible
  transparency. Consequently a
term such as `sheafifyValIso O hO M` is type-correct only at default transparency, and `rw` —
whose `kabstract` works at reducible transparency — reports *"the target expression is not
type-correct under the `implicit` transparency level"* on any goal containing one. Restating each
such declaration once, in the `Stacks.SheafOfModules.TensorSheafification.sheafify` spelling,
  removes this for every proof
below; the restatements themselves are accepted because `:=` and `exact` elaborate at default
transparency. No transparency option is used anywhere in this file.

**`tensorProductAssociator` without its inverse.** The library's definition conjugates the
sheafified presheaf associator by two sheafification comparisons, so its `hom` mentions the
inverse of one of them. `toSheafifyVal_whiskerRight_comp_assocVal` states the same content with
that comparison moved to the other side, which is the form the associativity comparison uses.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization
universe v u w
namespace Stacks.SheafOfModules.Invertible

attribute [local implicit_reducible] TensorSheafification.structureSheaf

attribute [local irreducible] PresheafOfModules.sheafification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafOfModules.monoidalCategory Stacks.SheafOfModules.braidedCategory
  Stacks.SheafOfModules.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### The two spellings of the presheaf index -/

/-- `Stacks.SheafOfModules.sheafifyValIso`, restated with sheafification spelled
`Stacks.SheafOfModules.TensorSheafification.sheafify`, whose source category is indexed by the
  structure sheaf rather than by
the underlying presheaf of rings. The two spellings are the same category, but only this one
makes `M.val` a legal argument at reducible transparency, so only in this one can `rw` and
`simp` operate on the statements below. -/
noncomputable def valIso (M : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val ≅ M :=
  Stacks.SheafOfModules.sheafifyValIso O hO M

/-- `Stacks.SheafOfModules.TensorSheafification.toSheafify`, restated in the spelling of `valIso`.
-/
noncomputable def toSheafifyVal
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    A ⟶ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val :=
  Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A

/-- Sheafification of presheaves of modules is a monoidal functor, for the monoidal structure
on sheaves of modules obtained by localizing along it. -/
noncomputable local instance sheafifyMonoidal : (Stacks.SheafOfModules.TensorSheafification.sheafify
  O hO).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O)
    (Stacks.SheafOfModules.sheafifyUnitIso O hO)).Monoidal

/-- `Stacks.SheafOfModules.sheafifyTensorIso`, restated in the spelling of `valIso`. -/
noncomputable def sheafifyTensorIso
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A ⊗
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B ≅
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (A ⊗ B) :=
  Stacks.SheafOfModules.sheafifyTensorIso O hO A B

/-- `Stacks.SheafOfModules.sheafifyUnitIso`, restated in the spelling of `valIso`. -/
noncomputable def unitIso :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
        (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO).obj)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  Stacks.SheafOfModules.sheafifyUnitIso O hO

theorem unitIso_eq_valIso :
    unitIso O hO = valIso O hO (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) := rfl

theorem sheafifyTensorIso_hom_eq
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (sheafifyTensorIso O hO A B).hom =
      Functor.LaxMonoidal.μ (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) A B := rfl

/-! ### The comparison isomorphism and the two tensor products -/

theorem tensorObjIso_eq (M N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M N =
      ((valIso O hO M).symm ⊗ᵢ (valIso O hO N).symm) ≪≫
        sheafifyTensorIso O hO M.val N.val := rfl

theorem tensorObjIso_unit_left_eq (M : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M =
      ((unitIso O hO).symm ⊗ᵢ (valIso O hO M).symm) ≪≫
        sheafifyTensorIso O hO
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) M.val := rfl

theorem tensorObjIso_unit_right_eq (M : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) =
      ((valIso O hO M).symm ⊗ᵢ (unitIso O hO).symm) ≪≫
        sheafifyTensorIso O hO M.val
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) := rfl

theorem tensorProductLeftUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorProductLeftUnitor O hO M =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (λ_ M.val) ≪≫ valIso O hO M
        := by
  unfold tensorProductLeftUnitor valIso Stacks.SheafOfModules.sheafifyValIso
  rfl

theorem tensorProductRightUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorProductRightUnitor O hO M =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (ρ_ M.val) ≪≫ valIso O hO M
        := by with_unfolding_all rfl

theorem tensorProductIso_hom_eq
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : M ≅ M') (f : N ≅ N') :
    (tensorProductIso O hO e f).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (e.hom.val ⊗ₘ f.hom.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) := rfl

/-! ### Transport of the localized structure maps -/

@[reassoc]
theorem leftUnitor_hom_app'
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (λ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)).hom =
      (unitIso O hO).inv ▷ (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A ≫
        (sheafifyTensorIso O hO _ A).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
          hO).map (λ_ A).hom :=
  Localization.Monoidal.leftUnitor_hom_app (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O)
    (Stacks.SheafOfModules.sheafifyUnitIso O hO) A

@[reassoc]
theorem rightUnitor_hom_app'
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (ρ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A ◁ (unitIso O hO).inv ≫
        (sheafifyTensorIso O hO A _).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
          hO).map (ρ_ A).hom :=
  Localization.Monoidal.rightUnitor_hom_app (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O)
    (Stacks.SheafOfModules.sheafifyUnitIso O hO) A

@[reassoc]
theorem sheafifyTensorIso_natural_left
    {A A' : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : A ⟶ A')
    (B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ▷
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B ≫
        (sheafifyTensorIso O hO A' B).hom =
      (sheafifyTensorIso O hO A B).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (f ▷ B) :=
  Localization.Monoidal.μ_natural_left (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O)
    (Stacks.SheafOfModules.sheafifyUnitIso O hO) f B

@[reassoc]
theorem sheafifyTensorIso_natural_right
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
    {B B' : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (g : B ⟶ B') :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A ◁
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g ≫
        (sheafifyTensorIso O hO A B').hom =
      (sheafifyTensorIso O hO A B).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (A ◁ g) :=
  Localization.Monoidal.μ_natural_right (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O)
    (Stacks.SheafOfModules.sheafifyUnitIso O hO) A g

@[reassoc]
theorem sheafifyTensorIso_natural
    {A A' B B' : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj}
    (f : A ⟶ A') (g : B ⟶ B') :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ⊗ₘ
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g) ≫
        (sheafifyTensorIso O hO A' B').hom =
      (sheafifyTensorIso O hO A B).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) f g

@[reassoc]
theorem sheafifyTensorIso_associativity
    (A B E : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (sheafifyTensorIso O hO A B).hom ▷ (Stacks.SheafOfModules.TensorSheafification.sheafify O
      hO).obj E ≫
        (sheafifyTensorIso O hO (A ⊗ B) E).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ A B E).hom =
      (α_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B)
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj E)).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A ◁ (sheafifyTensorIso O hO B
          E).hom ≫
          (sheafifyTensorIso O hO A (B ⊗ E)).hom :=
  Functor.LaxMonoidal.associativity (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) A B E

@[reassoc]
theorem valIso_inv_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f :
      M ⟶ N) :
    f ≫ (valIso O hO N).inv =
      (valIso O hO M).inv ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f.val :=
        by
  apply (cancel_mono (valIso O hO N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [eq_comm, Iso.inv_comp_eq]
  exact (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit.naturality f

/-- The sheafification unit is natural. -/
theorem toSheafifyVal_naturality
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : A ⟶ B) :
    toSheafifyVal O hO A ≫ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f).val =
      f ≫ toSheafifyVal O hO B :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit.naturality f).symm

theorem valIso_inv_sheafify
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (valIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)).inv =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (toSheafifyVal O hO A) := by
  apply (cancel_mono (valIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
    A)).hom).mp
  rw [Iso.inv_hom_id]
  exact ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O
    hO).left_triangle_components A).symm

/-- `tensorProductAssociator`, restated in the spelling of `valIso`. -/
noncomputable def assocVal
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
        (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)).val ⊗
          P.val) ≅
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
        (M.val ⊗ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (N.val ⊗
          P.val)).val) :=
  tensorProductAssociator O hO M N P

set_option maxHeartbeats 1000000 in
-- the `IsIso` term for the sheafified whiskered unit is heavy to elaborate
/-- The associativity constraint of the tensor product sheaf, in the form which avoids naming
the inverse of the sheafified whiskered unit: it is the sheafified presheaf associator, read
between the two sheafification comparisons. -/
theorem toSheafifyVal_whiskerRight_comp_assocVal
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (toSheafifyVal O hO (M.val ⊗
      N.val) ▷ P.val) ≫
        (assocVal O hO M N P).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ M.val N.val P.val).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (M.val ◁ toSheafifyVal O hO (N.val ⊗ P.val)) := by
  have : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (toSheafifyVal O hO (M.val ⊗ N.val) ▷ P.val)) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)) P.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (M.val ⊗
        N.val))
  exact IsIso.hom_inv_id_assoc ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (toSheafifyVal O hO (M.val ⊗ N.val) ▷ P.val)) _

/-! ### The monoidal structure maps are the tensor product sheaf constraints -/

/-- **The left unitor of the monoidal structure on sheaves of modules is the left unit
constraint of the tensor product sheaf**, read through `tensorObjIso`. -/
theorem leftUnitor_hom_eq_tensorProductLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (λ_ M).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
            M).hom ≫
        (tensorProductLeftUnitor O hO M).hom := by
  have key : (λ_ M).hom =
      (((unitIso O hO).inv ⊗ₘ (valIso O hO M).inv) ≫
          (sheafifyTensorIso O hO
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj)) M.val).hom) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (λ_ M.val).hom ≫ (valIso O
          hO M).hom) := by
    rw [tensorHom_def', Category.assoc, Category.assoc,
      ← leftUnitor_hom_app'_assoc O hO M.val (valIso O hO M).hom]
    exact ((MonoidalCategory.leftUnitor_naturality_assoc
        (valIso O hO M).inv (valIso O hO M).hom).trans
      (by rw [Iso.inv_hom_id, Category.comp_id])).symm
  exact key

/-- **The right unitor of the monoidal structure on sheaves of modules is the right unit
constraint of the tensor product sheaf.** -/
theorem rightUnitor_hom_eq_tensorProductRightUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (ρ_ M).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO M
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))).hom ≫
        (tensorProductRightUnitor O hO M).hom := by
  have key : (ρ_ M).hom =
      (((valIso O hO M).inv ⊗ₘ (unitIso O hO).inv) ≫
          (sheafifyTensorIso O hO M.val
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj))).hom) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ M.val).hom ≫ (valIso O
          hO M).hom) := by
    rw [tensorHom_def, Category.assoc, Category.assoc,
      ← rightUnitor_hom_app'_assoc O hO M.val (valIso O hO M).hom]
    exact ((MonoidalCategory.rightUnitor_naturality_assoc
        (valIso O hO M).inv (valIso O hO M).hom).trans
      (by rw [Iso.inv_hom_id, Category.comp_id])).symm
  exact key

/-- **The tensor product of morphisms in the monoidal structure on sheaves of modules is the
sheafification of the tensor product of the underlying presheaf morphisms**, read through
`tensorObjIso`. -/
theorem tensorObjIso_naturality
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (Stacks.SheafOfModules.tensorObjIso O hO M' N').hom =
      (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (f.val ⊗ₘ g.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) := by
  have key : (f ⊗ₘ g) ≫
        (((valIso O hO M').inv ⊗ₘ (valIso O hO N').inv) ≫
          (sheafifyTensorIso O hO M'.val N'.val).hom) =
      (((valIso O hO M).inv ⊗ₘ (valIso O hO N).inv) ≫
          (sheafifyTensorIso O hO M.val N.val).hom) ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (f.val ⊗ₘ g.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, valIso_inv_naturality,
      valIso_inv_naturality, ← tensorHom_comp_tensorHom, Category.assoc,
      sheafifyTensorIso_natural, Category.assoc]
  exact key

/-- The left-hand side of the associativity comparison, with `tensorProductAssociator`
replaced by `assocVal`, which is the same isomorphism with its type in the spelling of
`valIso`.  This step and `tensorObjIso_assoc_lhs_eq_val` are `rfl`, and are separated from
`tensorObjIso_associativity` and from each other only so that each reconciliation of the two
spellings is elaborated on its own: carried out in a single `rfl` the left-hand side alone costs
332287 heartbeats, against 85079 and 91541 for the two steps here. -/
theorem tensorObjIso_assoc_lhs_eq_assocVal
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ▷ P ≫
        (Stacks.SheafOfModules.tensorObjIso O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N) P).hom ≫
        (tensorProductAssociator O hO M N P).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ▷ P ≫
        (Stacks.SheafOfModules.tensorObjIso O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N) P).hom ≫
        (assocVal O hO M N P).hom := rfl

/-- The left-hand side of the associativity comparison, with the comparison isomorphisms
replaced by the sheafification data they are defined to be.  See
`tensorObjIso_assoc_lhs_eq_assocVal`. -/
theorem tensorObjIso_assoc_lhs_eq_val
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ▷ P ≫
        (Stacks.SheafOfModules.tensorObjIso O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N) P).hom ≫
        (assocVal O hO M N P).hom =
      (((valIso O hO M).inv ⊗ₘ (valIso O hO N).inv) ≫
            (sheafifyTensorIso O hO M.val N.val).hom) ▷ P ≫
          (((valIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗
            N.val))).inv ⊗ₘ
                (valIso O hO P).inv) ≫
              (sheafifyTensorIso O hO
                ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)).val
                  P.val).hom) ≫
            (assocVal O hO M N P).hom := rfl

set_option maxHeartbeats 1000000 in
-- long `rw` chains over the sheafified tensor-product isomorphisms
/-- **The associator of the monoidal structure on sheaves of modules is the associativity
constraint of the tensor product sheaf**, read through `tensorObjIso`. -/
theorem tensorObjIso_associativity
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ▷ P ≫
        (Stacks.SheafOfModules.tensorObjIso O hO
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat)
                    (hO)⟩).obj (M)).obj (N))) P).hom ≫
          (tensorProductAssociator O hO M N P).hom =
      (α_ M N P).hom ≫ M ◁ (Stacks.SheafOfModules.tensorObjIso O hO N P).hom ≫
        (Stacks.SheafOfModules.tensorObjIso O hO M
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat)
                  (hO)⟩).obj (N)).obj (P)))).hom := by
  have key :
      (((valIso O hO M).inv ⊗ₘ (valIso O hO N).inv) ≫
            (sheafifyTensorIso O hO M.val N.val).hom) ▷ P ≫
          (((valIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗
            N.val))).inv ⊗ₘ
                (valIso O hO P).inv) ≫
              (sheafifyTensorIso O hO
                ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)).val
                  P.val).hom) ≫
            (assocVal O hO M N P).hom =
        (α_ M N P).hom ≫
          M ◁ (((valIso O hO N).inv ⊗ₘ (valIso O hO P).inv) ≫
            (sheafifyTensorIso O hO N.val P.val).hom) ≫
            (((valIso O hO M).inv ⊗ₘ
                (valIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (N.val
                  ⊗ P.val))).inv) ≫
              (sheafifyTensorIso O hO M.val
                ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (N.val ⊗
                  P.val)).val).hom) := by
    rw [valIso_inv_sheafify O hO (M.val ⊗ N.val),
      valIso_inv_sheafify O hO (N.val ⊗ P.val), comp_whiskerRight, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [tensorHom_def' ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (toSheafifyVal O hO (M.val ⊗ N.val))) (valIso O hO P).inv,
      tensorHom_def (valIso O hO M).inv ((Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map
        (toSheafifyVal O hO (N.val ⊗ P.val)))]
    simp only [Category.assoc]
    rw [sheafifyTensorIso_natural_left_assoc, sheafifyTensorIso_natural_right,
      toSheafifyVal_whiskerRight_comp_assocVal,
      ← whisker_exchange_assoc (sheafifyTensorIso O hO M.val N.val).hom (valIso O hO P).inv,
      whisker_exchange_assoc (valIso O hO M).inv (sheafifyTensorIso O hO N.val P.val).hom,
      ← tensorHom_def_assoc, ← tensorHom_def'_assoc,
      sheafifyTensorIso_associativity_assoc,
      MonoidalCategory.associator_naturality_assoc]
  exact (tensorObjIso_assoc_lhs_eq_assocVal O hO M N P).trans
    ((tensorObjIso_assoc_lhs_eq_val O hO M N P).trans key)


/-- `tensorObjIso` is natural in the left factor. -/
theorem tensorObjIso_whiskerRight
    {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : M ⟶ M')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (f.val ▷ N.val : M.val ⊗ N.val ⟶ M'.val ⊗ N.val) =
      f ▷ N ≫ (Stacks.SheafOfModules.tensorObjIso O hO M' N).hom := by
  have h := (tensorObjIso_naturality O hO f (𝟙 N)).symm
  simp only [tensorHom_id, SheafOfModules.id_val] at h
  exact h

/-- `tensorObjIso` is natural in the right factor. -/
theorem tensorObjIso_whiskerLeft
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (g
      : N ⟶ N') :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (M.val ◁ g.val : M.val ⊗ N.val ⟶ M.val ⊗ N'.val) =
      M ◁ g ≫ (Stacks.SheafOfModules.tensorObjIso O hO M N').hom := by
  have h := (tensorObjIso_naturality O hO (𝟙 M) g).symm
  simp only [id_tensorHom, SheafOfModules.id_val] at h
  exact h

/-- `tensorObjIso` is natural in both factors. -/
theorem tensorObjIso_tensorHom
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (f.val ⊗ₘ g.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) =
      (f ⊗ₘ g) ≫ (Stacks.SheafOfModules.tensorObjIso O hO M' N').hom :=
  (tensorObjIso_naturality O hO f g).symm

/-- The unit constraints of the tensor product sheaf, as the unitors of the monoidal structure
conjugated by `tensorObjIso`. -/
theorem tensorProductLeftUnitor_hom_eq_conj
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorProductLeftUnitor O hO M).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          M).inv ≫ (λ_ M).hom :=
  (Iso.eq_inv_comp _).mpr (leftUnitor_hom_eq_tensorProductLeftUnitor O hO M).symm

theorem tensorProductRightUnitor_hom_eq_conj
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorProductRightUnitor O hO M).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO M
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).inv
          ≫ (ρ_ M).hom :=
  (Iso.eq_inv_comp _).mpr (rightUnitor_hom_eq_tensorProductRightUnitor O hO M).symm

/-- The associativity constraint of the tensor product sheaf, as the associator of the monoidal
structure conjugated by `tensorObjIso`. -/
theorem tensorProductAssociator_hom_eq_conj
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorProductAssociator O hO M N P).hom =
      (Stacks.SheafOfModules.tensorObjIso O hO
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat)
                    (hO)⟩).obj (M)).obj (N))) P).inv ≫
        ((Stacks.SheafOfModules.tensorObjIso O hO M N).inv ▷ P) ≫ (α_ M N P).hom ≫
          (M ◁ (Stacks.SheafOfModules.tensorObjIso O hO N P).hom) ≫
            (Stacks.SheafOfModules.tensorObjIso O hO M
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat)
                      (hO)⟩).obj (N)).obj (P)))).hom := by
  exact (Iso.eq_inv_comp _).mpr ((Iso.eq_inv_comp (whiskerRightIso
    (Stacks.SheafOfModules.tensorObjIso O hO M N) P)).mpr (tensorObjIso_associativity O hO M N P))

/-- **The braiding of the monoidal structure on sheaves of modules is the symmetry constraint of
the tensor product sheaf**, read through `tensorObjIso`. This is
`Stacks.SheafOfModules.braiding_hom_eq_tensorSheafBraiding`, rearranged into the shape
`CategoryTheory.BraidedCategory.ofFaithful` asks for; the two spellings of the braiding of the
tensor product sheaf agree by `rfl`. -/
theorem tensorObjIso_braiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (tensorProductBraiding O hO M N).hom =
      (β_ M N).hom ≫ (Stacks.SheafOfModules.tensorObjIso O hO N M).hom :=
  (Iso.comp_inv_eq (Stacks.SheafOfModules.tensorObjIso O hO N M)).mp
    ((Category.assoc _ _ _).trans
      (Stacks.SheafOfModules.braiding_hom_eq_tensorSheafBraiding O hO M N).symm)

end Stacks.SheafOfModules.Invertible

end
