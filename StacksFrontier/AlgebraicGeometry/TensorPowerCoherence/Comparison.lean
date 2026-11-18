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

None mathematically new. `valIso`, `toSheafifyVal`, `sheafifyTensorIso` and `unitIso` are the
library's `Stacks.SheafOfModules.sheafifyValIso`,
  `Stacks.SheafOfModules.TensorSheafification.toSheafify`,
`Stacks.SheafOfModules.sheafifyTensorIso` and `Stacks.SheafOfModules.sheafifyUnitIso`,
restated with the index of the presheaf category spelled
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` rather than
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O`. See the
implementation notes: the two spellings are the same category, and the restatements are all
`rfl` or a single `exact`, but only in the first spelling are the statements type-correct at
reducible transparency, which is what `rw` and `simp` need.

The tensor product sheaf and its constraints sheafify with the sealed
`structureSheafification` (`Stacks.SheafOfModules.Tensor.sheafification`), while the monoidal
structure localizes along Mathlib's sheafification
`Stacks.SheafOfModules.TensorSheafification.sheafify`. `sheafifyIso` identifies the two
functors, the local instance `structureSheafificationMonoidal` transports the monoidal-functor
structure along it, and `structureValIso`, `structureUnit` are the counit and unit of the sealed
sheafification adjunction; `structureValIso_eq` and `tensorObjIso_eq_structureValIso` compare
them with the localized data.

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
* `Stacks.SheafOfModules.Invertible.tensorObjIso_eq_structureValIso`: `tensorObjIso` in terms of
  the sealed sheafification and its transported monoidal-functor structure.

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
inverse of one of them. `structureUnit_whiskerRight_comp_tensorProductAssociator` states the same
content with that comparison moved to the other side.

**The cost of the associativity comparison.** `tensorObjIso_associativity` is proved in the
spelling of the sealed sheafification and closed by one `exact`, which identifies the nested
`Stacks.SheafOfModules.Tensor.sheafTensor` objects of the statement with the sheafified presheaf
tensor products of the proof. That identification unfolds `sheafTensor` and the presheaf tensor
product and needs a raised heartbeat budget.

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

/-! ### The sealed sheafification -/

/-- `Stacks.SheafOfModules.TensorSheafification.sheafify`, along which the monoidal structure is
localized, is the sealed `structureSheafification` that ends the sheaf tensor product.
`Stacks.SheafOfModules.tensorObjIso` ends with the sealed comparison
`Stacks.SheafOfModules.Tensor.sheafificationIso`, which is this identification by
`Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso`. -/
noncomputable def sheafifyIso :
    Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅ structureSheafification O hO :=
  eqToIso (Stacks.SheafOfModules.Tensor.sheafification_def
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).symm

/-- The sealed sheafification is a monoidal functor: the monoidal structure of
`Stacks.SheafOfModules.TensorSheafification.sheafify`, transported along `sheafifyIso`. -/
noncomputable local instance structureSheafificationMonoidal :
    (structureSheafification O hO).Monoidal :=
  Functor.Monoidal.transport (sheafifyIso O hO)

theorem structureSheafification_μ
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    Functor.LaxMonoidal.μ (structureSheafification O hO) A B =
      ((sheafifyIso O hO).inv.app A ⊗ₘ (sheafifyIso O hO).inv.app B) ≫
        (sheafifyTensorIso O hO A B).hom ≫ (sheafifyIso O hO).hom.app (A ⊗ B) := rfl

theorem structureSheafification_ε :
    Functor.LaxMonoidal.ε (structureSheafification O hO) =
      (unitIso O hO).inv ≫ (sheafifyIso O hO).hom.app _ := rfl

/-- The sealed sheafification of a sheaf of modules is itself: the counit of
`structureSheafificationAdjunction`. -/
noncomputable def structureValIso (M : SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (structureSheafification O hO).obj M.val ≅ M :=
  (asIso (structureSheafificationAdjunction O hO).counit).app M

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Restricting scalars along the identity changes nothing. -/
private theorem forgetCompRestrictScalarsIdIso_inv_app (M : SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.forgetCompRestrictScalarsIdIso
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).inv.app M =
      𝟙 ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj M) := by
  ext; rfl

/-- Restricting scalars along the identity changes nothing, after sealed sheafification. -/
private theorem structureSheafification_map_forgetCompRestrictScalarsIdIso_inv_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (structureSheafification O hO).map
        ((Stacks.SheafOfModules.Tensor.forgetCompRestrictScalarsIdIso
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).inv.app M) =
      𝟙 _ := by
  rw [forgetCompRestrictScalarsIdIso_inv_app]
  exact (structureSheafification O hO).map_id _

/-- The counit of the sealed sheafification adjunction is that of
`Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction`, read through `sheafifyIso`. -/
theorem structureValIso_eq (M : SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    structureValIso O hO M = (sheafifyIso O hO).symm.app M.val ≪≫ valIso O hO M := by
  ext1
  exact (congrArg (· ≫ (Stacks.SheafOfModules.Tensor.sheafificationAdjunction
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit.app M)
    (structureSheafification_map_forgetCompRestrictScalarsIdIso_inv_app O hO M)).trans
      (Category.id_comp _)

@[reassoc]
theorem structureValIso_inv_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ N) :
    f ≫ (structureValIso O hO N).inv =
      (structureValIso O hO M).inv ≫ (structureSheafification O hO).map f.val :=
  (asIso (structureSheafificationAdjunction O hO).counit).inv.naturality f

/-- The unit of the monoidal functor `structureSheafification` is the inverse of the counit at the
tensor unit. -/
theorem structureSheafification_ε_eq :
    Functor.LaxMonoidal.ε (structureSheafification O hO) =
      (structureValIso O hO
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).inv
        := by
  rw [structureSheafification_ε, structureValIso_eq]
  rfl

/-! ### The comparison isomorphism and the two tensor products -/

theorem tensorObjIso_eq (M N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M N =
      ((valIso O hO M).symm ⊗ᵢ (valIso O hO N).symm) ≪≫
        sheafifyTensorIso O hO M.val N.val ≪≫ (sheafifyIso O hO).app (M.val ⊗ N.val) := by
  rw [Stacks.SheafOfModules.tensorObjIso_def,
    Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso]
  rfl

theorem tensorObjIso_unit_left_eq (M : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M =
      ((unitIso O hO).symm ⊗ᵢ (valIso O hO M).symm) ≪≫
        sheafifyTensorIso O hO
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) M.val ≪≫ (sheafifyIso O hO).app _ := by
  rw [Stacks.SheafOfModules.tensorObjIso_def,
    Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso]
  rfl

theorem tensorObjIso_unit_right_eq (M : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) =
      ((valIso O hO M).symm ⊗ᵢ (unitIso O hO).symm) ≪≫
        sheafifyTensorIso O hO M.val
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) ≪≫ (sheafifyIso O hO).app _ := by
  rw [Stacks.SheafOfModules.tensorObjIso_def,
    Stacks.SheafOfModules.Tensor.sheafificationIso_eq_eqToIso]
  rfl

/-- `tensorObjIso`, in terms of the sealed sheafification and its monoidal structure. -/
theorem tensorObjIso_eq_structureValIso (M N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M N =
      ((structureValIso O hO M).symm ⊗ᵢ (structureValIso O hO N).symm) ≪≫
        Functor.Monoidal.μIso (structureSheafification O hO) M.val N.val := by
  ext1
  simp only [tensorObjIso_eq, structureValIso_eq, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_hom, structureSheafification_μ, Iso.trans_inv, Iso.app_inv,
    Iso.symm_inv, Iso.app_hom, tensorHom_comp_tensorHom_assoc, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]
  rfl

theorem tensorProductLeftUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorProductLeftUnitor O hO M =
      (structureSheafification O hO).mapIso (λ_ M.val) ≪≫ structureValIso O hO M := rfl

theorem tensorProductRightUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorProductRightUnitor O hO M =
      (structureSheafification O hO).mapIso (ρ_ M.val) ≪≫ structureValIso O hO M := rfl

theorem tensorProductIso_hom_eq
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : M ≅ M') (f : N ≅ N') :
    (tensorProductIso O hO e f).hom =
      (structureSheafification O hO).map
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

/-! ### The sealed sheafification and the associativity constraint -/

/-- The unit of the sealed sheafification, in the spelling of `structureValIso`. -/
noncomputable abbrev structureUnit
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    A ⟶ ((structureSheafification O hO).obj A).val :=
  (structureSheafificationAdjunction O hO).unit.app A

theorem structureValIso_inv_obj
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (structureValIso O hO ((structureSheafification O hO).obj A)).inv =
      (structureSheafification O hO).map (structureUnit O hO A) := by
  rw [← cancel_mono (structureValIso O hO _).hom, Iso.inv_hom_id]
  exact ((structureSheafificationAdjunction O hO).left_triangle_components A).symm

/-- The associativity constraint of the tensor product sheaf, in the form which avoids naming
the inverse of the sheafified whiskered unit: it is the sheafified presheaf associator, read
between the two sheafification comparisons. -/
theorem structureUnit_whiskerRight_comp_tensorProductAssociator
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (structureSheafification O hO).map (structureUnit O hO (M.val ⊗ N.val) ▷ P.val) ≫
        (tensorProductAssociator O hO M N P).hom =
      (structureSheafification O hO).map (α_ M.val N.val P.val).hom ≫
        (structureSheafification O hO).map (M.val ◁ structureUnit O hO (N.val ⊗ P.val)) := by
  have : IsIso ((structureSheafification O hO).map
      (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) :=
    isIso_structureSheafification_map_whiskerRight O hO _ P.val
      (inferInstanceAs (IsIso ((structureSheafification O hO).map
        ((structureSheafificationAdjunction O hO).unit.app (M.val ⊗ N.val)))))
  exact IsIso.hom_inv_id_assoc ((structureSheafification O hO).map
    (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) _

/-- `tensorProductAssociator`, in the spelling of `structureValIso`. -/
theorem tensorProductAssociator_hom_eq
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    haveI : IsIso ((structureSheafification O hO).map
        (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) :=
      isIso_structureSheafification_map_whiskerRight O hO _ P.val
        (inferInstanceAs (IsIso ((structureSheafification O hO).map
          ((structureSheafificationAdjunction O hO).unit.app (M.val ⊗ N.val)))))
    (tensorProductAssociator O hO M N P).hom =
      inv ((structureSheafification O hO).map (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) ≫
        (structureSheafification O hO).map (α_ M.val N.val P.val).hom ≫
          (structureSheafification O hO).map (M.val ◁ structureUnit O hO (N.val ⊗ P.val)) :=
  rfl

/-- `tensorObjIso_eq_structureValIso` for a left factor which is itself a tensor product sheaf,
spelled as the sealed sheafification of the presheaf tensor product. -/
theorem tensorObjIso_sheafTensor_left_eq
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N)
        P =
      ((structureValIso O hO ((structureSheafification O hO).obj (M.val ⊗ N.val))).symm ⊗ᵢ
          (structureValIso O hO P).symm) ≪≫
        Functor.Monoidal.μIso (structureSheafification O hO)
          ((structureSheafification O hO).obj (M.val ⊗ N.val)).val P.val :=
  tensorObjIso_eq_structureValIso O hO _ P

/-- `tensorObjIso_eq_structureValIso` for a right factor which is itself a tensor product sheaf,
spelled as the sealed sheafification of the presheaf tensor product. -/
theorem tensorObjIso_sheafTensor_right_eq
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.tensorObjIso O hO M
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj
            P) =
      ((structureValIso O hO M).symm ⊗ᵢ
          (structureValIso O hO ((structureSheafification O hO).obj (N.val ⊗ P.val))).symm) ≪≫
        Functor.Monoidal.μIso (structureSheafification O hO) M.val
          ((structureSheafification O hO).obj (N.val ⊗ P.val)).val :=
  tensorObjIso_eq_structureValIso O hO M _

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
      ((Functor.LaxMonoidal.ε (structureSheafification O hO) ⊗ₘ (structureValIso O hO M).inv) ≫
          Functor.LaxMonoidal.μ (structureSheafification O hO) _ M.val) ≫
        ((structureSheafification O hO).map (λ_ M.val).hom ≫ (structureValIso O hO M).hom) := by
    rw [tensorHom_def', Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.left_unitality_assoc]
    exact ((MonoidalCategory.leftUnitor_naturality_assoc
        (structureValIso O hO M).inv (structureValIso O hO M).hom).trans
      (by rw [Iso.inv_hom_id, Category.comp_id])).symm
  rw [structureSheafification_ε_eq] at key
  rw [tensorObjIso_eq_structureValIso, tensorProductLeftUnitor_eq]
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
      (((structureValIso O hO M).inv ⊗ₘ Functor.LaxMonoidal.ε (structureSheafification O hO)) ≫
          Functor.LaxMonoidal.μ (structureSheafification O hO) M.val _) ≫
        ((structureSheafification O hO).map (ρ_ M.val).hom ≫ (structureValIso O hO M).hom) := by
    rw [tensorHom_def, Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.right_unitality_assoc]
    exact ((MonoidalCategory.rightUnitor_naturality_assoc
        (structureValIso O hO M).inv (structureValIso O hO M).hom).trans
      (by rw [Iso.inv_hom_id, Category.comp_id])).symm
  rw [structureSheafification_ε_eq] at key
  rw [tensorObjIso_eq_structureValIso, tensorProductRightUnitor_eq]
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
        (structureSheafification O hO).map
          (f.val ⊗ₘ g.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) := by
  have key : (f ⊗ₘ g) ≫
        (((structureValIso O hO M').inv ⊗ₘ (structureValIso O hO N').inv) ≫
          Functor.LaxMonoidal.μ (structureSheafification O hO) M'.val N'.val) =
      (((structureValIso O hO M).inv ⊗ₘ (structureValIso O hO N).inv) ≫
          Functor.LaxMonoidal.μ (structureSheafification O hO) M.val N.val) ≫
        (structureSheafification O hO).map
          (f.val ⊗ₘ g.val : M.val ⊗ N.val ⟶ M'.val ⊗ N'.val) := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, structureValIso_inv_naturality,
      structureValIso_inv_naturality, ← tensorHom_comp_tensorHom, Category.assoc,
      Functor.LaxMonoidal.μ_natural, Category.assoc]
  rw [tensorObjIso_eq_structureValIso, tensorObjIso_eq_structureValIso]
  exact key

set_option maxHeartbeats 1000000 in
-- the final `exact` unfolds the nested `sheafTensor` objects; see the implementation notes
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
  have : IsIso ((structureSheafification O hO).map
      (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) :=
    isIso_structureSheafification_map_whiskerRight O hO _ P.val
      (inferInstanceAs (IsIso ((structureSheafification O hO).map
        ((structureSheafificationAdjunction O hO).unit.app (M.val ⊗ N.val)))))
  have key :
      (((structureValIso O hO M).inv ⊗ₘ (structureValIso O hO N).inv) ≫
            Functor.LaxMonoidal.μ (structureSheafification O hO) M.val N.val) ▷ P ≫
          (((structureValIso O hO ((structureSheafification O hO).obj (M.val ⊗ N.val))).inv ⊗ₘ
                (structureValIso O hO P).inv) ≫
              Functor.LaxMonoidal.μ (structureSheafification O hO)
                ((structureSheafification O hO).obj (M.val ⊗ N.val)).val P.val) ≫
            inv ((structureSheafification O hO).map
              (structureUnit O hO (M.val ⊗ N.val) ▷ P.val)) ≫
              (structureSheafification O hO).map (α_ M.val N.val P.val).hom ≫
                (structureSheafification O hO).map
                  (M.val ◁ structureUnit O hO (N.val ⊗ P.val)) =
        (α_ M N P).hom ≫
          M ◁ (((structureValIso O hO N).inv ⊗ₘ (structureValIso O hO P).inv) ≫
            Functor.LaxMonoidal.μ (structureSheafification O hO) N.val P.val) ≫
            (((structureValIso O hO M).inv ⊗ₘ
                (structureValIso O hO ((structureSheafification O hO).obj (N.val ⊗ P.val))).inv) ≫
              Functor.LaxMonoidal.μ (structureSheafification O hO) M.val
                ((structureSheafification O hO).obj (N.val ⊗ P.val)).val) := by
    rw [structureValIso_inv_obj O hO (M.val ⊗ N.val),
      structureValIso_inv_obj O hO (N.val ⊗ P.val), comp_whiskerRight, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [tensorHom_def' ((structureSheafification O hO).map (structureUnit O hO (M.val ⊗ N.val)))
        (structureValIso O hO P).inv,
      tensorHom_def (structureValIso O hO M).inv
        ((structureSheafification O hO).map (structureUnit O hO (N.val ⊗ P.val)))]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_left_assoc, Functor.LaxMonoidal.μ_natural_right,
      IsIso.hom_inv_id_assoc,
      ← whisker_exchange_assoc (Functor.LaxMonoidal.μ (structureSheafification O hO) M.val N.val)
        (structureValIso O hO P).inv,
      whisker_exchange_assoc (structureValIso O hO M).inv
        (Functor.LaxMonoidal.μ (structureSheafification O hO) N.val P.val),
      ← tensorHom_def_assoc, ← tensorHom_def'_assoc,
      Functor.LaxMonoidal.associativity_assoc,
      MonoidalCategory.associator_naturality_assoc]
  rw [tensorObjIso_eq_structureValIso O hO M N, tensorObjIso_eq_structureValIso O hO N P,
    tensorObjIso_sheafTensor_left_eq, tensorObjIso_sheafTensor_right_eq,
    tensorProductAssociator_hom_eq]
  exact key

/-- `tensorObjIso` is natural in the left factor. -/
theorem tensorObjIso_whiskerRight
    {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : M ⟶ M')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorObjIso O hO M N).hom ≫
        (structureSheafification O hO).map
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
        (structureSheafification O hO).map
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
        (structureSheafification O hO).map
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
