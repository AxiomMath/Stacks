module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf

/-!
# The sheaf tensor product carries the symmetric monoidal structure of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` with sheafification.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` puts a symmetric monoidal structure
on `SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)` by
localizing the monoidal structure of presheaves of modules along sheafification; its tensor
product is pinned down only up to the isomorphism `Stacks.SheafOfModules.tensorObjIso` with the
tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` of Tag 05NA, and its constraints
are given by no formula. `StacksFrontier/AlgebraicGeometry/Divisors/TensorPower.lean`, on the other
hand, writes down the unit, associativity and symmetry constraints
`Stacks.SheafOfModules.Invertible.tensorProduct…` of `Stacks.SheafOfModules.Tensor.sheafTensor`
explicitly. This file proves that those explicit maps *are* a symmetric monoidal structure,
namely the localized one transported along `tensorObjIso`.

The point of doing so is that the coherence laws asserted by Tag 01CU for the multiplication of
tensor powers are stated in terms of those fixed constraints, while the construction of the
multiplication is an induction which is only manageable inside a monoidal category — for
instance it uses the pentagon and the hexagon, and the `monoidal` normalisation tactic. Without
this file the two would not be about the same maps.

## Main definitions

* `Stacks.SheafOfModules.sheafTensorStruct`: the `MonoidalCategoryStruct` whose tensor product
  is `Stacks.SheafOfModules.Tensor.sheafTensor` and whose constraints are the fixed ones.
* `Stacks.SheafOfModules.sheafTensorMonoidal`: that struct is a monoidal category.
* `Stacks.SheafOfModules.sheafTensorSymmetric`: it is symmetric, with braiding the fixed
  symmetry constraint `Invertible.tensorProductBraiding`.

## Implementation notes

The axioms are not checked by hand. `Monoidal.induced` transports them from the localized
structure across `tensorObjIso`; what has to be checked is only that `tensorObjIso` carries each
fixed constraint to the localized one, which is `tensorObjIso_associativity`,
`tensorObjIso_leftUnitor`, `tensorObjIso_rightUnitor` and `tensorObjIso_braiding`, and each of
those is one application of the corresponding law of the monoidal functor structure on
sheafification.

`sheafTensorStruct` and `sheafTensorMonoidal` are `@[instance_reducible]` but are deliberately
*not* instances, for the same reason `monoidalCategory` is not: the tensor product of sheaves of
modules is not globally the sheafification of a presheaf tensor product, and clients which want
this one say so with `attribute [local instance]`.

`sheafifyMonoidal` and `sheafifyBraided` record that sheafification is a monoidal, indeed
braided, functor for `monoidalCategory`. They are the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` analogues of
`SheafOfModules.sheafification_monoidal`, which is stated for the `ringSheafOf` spelling.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

attribute [local instance_reducible] CategoryTheory.LocalizedMonoidal
  CategoryTheory.Localization.Monoidal.toMonoidalCategory

attribute [local implicit_reducible] MonoidalCategoryStruct.tensorObj
  ConcreteCategory.hom ConcreteCategory.ofHom HasForget₂.forget₂
  monoidalCategoryPresheafOfModules Tensor.sheafTensor
  TensorSheafification.sheafify _root_.PresheafOfModules.tensorObj
  _root_.PresheafOfModules.Monoidal.tensorObj _root_.PresheafOfModules.Monoidal.tensorObjMap
  _root_.PresheafOfModules.restrictₛₗ ModuleCat.tensorRestrictMap
  ModuleCat.MonoidalCategory.tensorLift ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory braidedCategory symmetricCategory

/-- Sheaves of modules carrying the monoidal structure Mathlib's localization theory puts on
them, obtained from the monoidal structure on presheaves of modules. This is the type synonym
behind `monoidalCategory`; naming it lets a statement say which of the two monoidal structures
on sheaves of modules it is about. -/
abbrev SheafLocalizedMonoidal :=
  LocalizedMonoidal (sheafifyFunctor O hO) (localIso (J := J) O) (sheafifyUnitIso O hO)

/-- Sheafification is a monoidal functor for `monoidalCategory`. -/
@[instance_reducible]
noncomputable def sheafifyMonoidal : (sheafifyFunctor O hO).Monoidal :=
  show (Localization.Monoidal.toMonoidalCategory (sheafifyFunctor O hO)
    (localIso (J := J) O) (sheafifyUnitIso O hO)).Monoidal from inferInstance

attribute [local instance] sheafifyMonoidal

/-- Sheafification is a braided functor for `monoidalCategory` and `braidedCategory`. -/
@[instance_reducible]
noncomputable def sheafifyBraided : (sheafifyFunctor O hO).Braided :=
  show (Localization.Monoidal.toMonoidalCategory (sheafifyFunctor O hO)
    (localIso (J := J) O) (sheafifyUnitIso O hO)).Braided from inferInstance

attribute [local instance] sheafifyBraided

/-- Naturality of the sheafification unit, with the unit written through
`TensorSheafification.toSheafify`: for a morphism `f` of presheaves of modules, the unit followed
by the underlying morphism of presheaves of the sheafification of `f` equals `f` followed by the
unit. The value of the right adjoint at a morphism of sheaves of modules is its underlying
morphism of presheaves only by unfolding `restrictScalars` at the identity, so this is recorded
here rather than rewritten through. -/
theorem toSheafifyVal_naturality
    {P Q : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj} (f : P ⟶ Q) :
    TensorSheafification.toSheafify O hO P ≫ ((sheafifyFunctor O hO).map f).val =
      f ≫ TensorSheafification.toSheafify O hO Q :=
  ((TensorSheafification.sheafifyAdjunction O hO).unit.naturality f).symm

/-- The sheaf tensor product of Tag 05NA on a pair of morphisms: sheafify the tensor product of
the two morphisms of underlying presheaves. The monoidal structure on presheaves of modules is
fixed in the *result type* here, before the localized monoidal structure on sheaves of modules
comes into scope; after that, elaborating `f.val ⊗ₘ g.val` from the bare notation no longer
finds the presheaf structure. -/
noncomputable abbrev sheafifyTensorHom
    {M M' N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (sheafifyFunctor O hO).obj (M.val ⊗ N.val) ⟶
      (sheafifyFunctor O hO).obj (M'.val ⊗ N'.val) :=
  (sheafifyFunctor O hO).map (f.val ⊗ₘ g.val)

/-- Whiskering on the left in the sheaf tensor product of Tag 05NA, with the monoidal structure
on presheaves of modules fixed in the result type as for `sheafifyTensorHom`. -/
noncomputable abbrev sheafifyWhiskerLeft
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : N ⟶ N') :
    (sheafifyFunctor O hO).obj (M.val ⊗ N.val) ⟶
      (sheafifyFunctor O hO).obj (M.val ⊗ N'.val) :=
  (sheafifyFunctor O hO).map (M.val ◁ g.val)

/-- Whiskering on the right in the sheaf tensor product of Tag 05NA, with the monoidal structure
on presheaves of modules fixed in the result type as for `sheafifyTensorHom`. -/
noncomputable abbrev sheafifyWhiskerRight
    {M M' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (f : M ⟶ M')
    (N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (sheafifyFunctor O hO).obj (M.val ⊗ N.val) ⟶
      (sheafifyFunctor O hO).obj (M'.val ⊗ N.val) :=
  (sheafifyFunctor O hO).map (f.val ▷ N.val)

/-- At a sheafified presheaf the inverse of the counit is the sheafification of the unit. -/
theorem sheafifyValIso_inv_sheafify
    (P : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj) :
    (sheafifyValIso O hO ((sheafifyFunctor O hO).obj P)).inv =
      (sheafifyFunctor O hO).map (TensorSheafification.toSheafify O hO P) := by
  apply (cancel_mono (sheafifyValIso O hO ((sheafifyFunctor O hO).obj P)).hom).mp
  rw [Iso.inv_hom_id]
  exact ((TensorSheafification.sheafifyAdjunction O hO).left_triangle_components P).symm

/-- The comparison of the localized tensor product with the sheaf tensor product of Tag 05NA is
natural in both factors. -/
theorem tensorObjIso_naturality
    {M M' N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g) ≫ (tensorObjIso O hO M' N').hom =
      (tensorObjIso O hO M N).hom ≫ sheafifyTensorHom O hO f g := by
  show (f ⊗ₘ g) ≫
      (((sheafifyValIso O hO M').inv ⊗ₘ (sheafifyValIso O hO N').inv) ≫
        (sheafifyTensorIso O hO M'.val N'.val).hom) =
    (((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyValIso O hO N).inv) ≫
      (sheafifyTensorIso O hO M.val N.val).hom) ≫
        (sheafifyFunctor O hO).map (f.val ⊗ₘ g.val)
  simp only [← Category.assoc, tensorHom_comp_tensorHom, comp_sheafifyValIso_inv]
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  simp only [Category.assoc]
  exact congrArg (fun k => ((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyValIso O hO N).inv) ≫ k)
    (Functor.LaxMonoidal.μ_natural
      (Localization.Monoidal.toMonoidalCategory (sheafifyFunctor O hO)
        (localIso (J := J) O) (sheafifyUnitIso O hO)) f.val g.val)

/-- The comparison carries the localized associator to the fixed associativity constraint of the
sheaf tensor product. -/
theorem tensorObjIso_associativity
    (M N P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO M N).hom ▷ P ≫
      (tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (M)).obj (N))) P).hom ≫
      (Invertible.tensorProductAssociator O hO M N P).hom =
    (α_ M N P).hom ≫ M ◁ (tensorObjIso O hO N P).hom ≫
      (tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (N)).obj (P)))).hom := by
  let leftComparison := (tensorObjIso O hO M N ⊗ᵢ Iso.refl P) ≪≫
    tensorObjIso O hO
      (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N) P
  let rightComparison := (Iso.refl M ⊗ᵢ tensorObjIso O hO N P) ≪≫
    tensorObjIso O hO M
      (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj P)
  have constraintHom : leftComparison.inv ≫ (α_ M N P).hom ≫ rightComparison.hom =
      (Invertible.tensorProductAssociator O hO M N P).hom :=
    congrArg Iso.hom ((Strict.associator_eq O hO M N P).symm.trans
      (Strict_associator_eq O hO M N P))
  have coherence := ((Iso.inv_comp_eq leftComparison).mp constraintHom).symm
  have leftHom : leftComparison.hom = (tensorObjIso O hO M N).hom ▷ P ≫
      (tensorObjIso O hO
        (((Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N)
        P).hom :=
    congrArg (· ≫ _) (@MonoidalCategory.tensorHom_id _ _ (monoidalCategory O hO)
      _ _ (tensorObjIso O hO M N).hom P)
  have rightHom : rightComparison.hom = M ◁ (tensorObjIso O hO N P).hom ≫
      (tensorObjIso O hO M
        (((Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj
          P)).hom :=
    congrArg (· ≫ _) (@MonoidalCategory.id_tensorHom _ _ (monoidalCategory O hO)
      M _ _ (tensorObjIso O hO N P).hom)
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Invertible.tensorProductAssociator O hO M N P).hom) leftHom).symm.trans
      coherence)).trans (congrArg ((α_ M N P).hom ≫ ·) rightHom)

/-- The comparison carries the localized left unitor to the fixed left unit constraint. -/
theorem tensorObjIso_leftUnitor
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO (SheafOfModules.unit _) M).hom ≫
      (Invertible.tensorProductLeftUnitor O hO M).hom = (λ_ M).hom := by
  show ((sheafifyUnitIso O hO).inv ⊗ₘ (sheafifyValIso O hO M).inv) ≫
    Functor.LaxMonoidal.μ (sheafifyFunctor O hO) (𝟙_ _) M.val ≫
    (sheafifyFunctor O hO).map (λ_ M.val).hom ≫
    (sheafifyValIso O hO M).hom = _
  rw [tensorHom_def', Category.assoc]
  show _ ≫ Functor.LaxMonoidal.ε (sheafifyFunctor O hO) ▷ _ ≫ _ ≫ _ ≫ _ = _
  rw [← Functor.LaxMonoidal.left_unitality_assoc]
  show 𝟙_ (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) ◁
    (sheafifyValIso O hO M).inv ≫ _ = _
  rw [leftUnitor_naturality_assoc (sheafifyValIso O hO M).inv]
  rw [Iso.inv_hom_id, Category.comp_id]

/-- The comparison carries the localized right unitor to the fixed right unit constraint. -/
theorem tensorObjIso_rightUnitor
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO M (SheafOfModules.unit _)).hom ≫
      (Invertible.tensorProductRightUnitor O hO M).hom = (ρ_ M).hom := by
  show ((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyUnitIso O hO).inv) ≫
    Functor.LaxMonoidal.μ (sheafifyFunctor O hO) M.val (𝟙_ _) ≫
    (sheafifyFunctor O hO).map (ρ_ M.val).hom ≫
    (sheafifyValIso O hO M).hom = _
  rw [tensorHom_def, Category.assoc]
  show _ ≫ _ ◁ Functor.LaxMonoidal.ε (sheafifyFunctor O hO) ≫ _ ≫ _ ≫ _ = _
  rw [← Functor.LaxMonoidal.right_unitality_assoc]
  show (sheafifyValIso O hO M).inv ▷
    𝟙_ (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) ≫ _ = _
  rw [rightUnitor_naturality_assoc (sheafifyValIso O hO M).inv]
  rw [Iso.inv_hom_id, Category.comp_id]

/-- The comparison carries the localized braiding to the fixed symmetry constraint. -/
theorem tensorObjIso_braiding
    (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO M N).hom ≫ (Invertible.tensorProductBraiding O hO M N).hom =
      (β_ M N).hom ≫ (tensorObjIso O hO N M).hom := by
  show ((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyValIso O hO N).inv) ≫
      Functor.LaxMonoidal.μ (sheafifyFunctor O hO) M.val N.val ≫
      (sheafifyFunctor O hO).map (β_ M.val N.val).hom = _
  rw [Functor.LaxBraided.braided (F := sheafifyFunctor O hO) M.val N.val]
  rw [BraidedCategory.braiding_naturality_assoc (sheafifyValIso O hO M).inv
    (sheafifyValIso O hO N).inv]
  rfl

/-- The identity functor from sheaves of modules to the type synonym carrying the localized
monoidal structure. Writing the target as the synonym is what keeps the two monoidal structures
on sheaves of modules apart: the source carries `sheafTensorStruct` below and the target the
localized one, and `Monoidal.induced` transports the axioms from the second to the first. -/
noncomputable def toSheafLocalized :
    SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) ⥤ SheafLocalizedMonoidal O hO :=
  𝟭 _

/-- The functor `toSheafLocalized` is faithful. -/
instance toSheafLocalizedFaithful : (toSheafLocalized O hO).Faithful where
  map_injective h := h

/-- The fixed associativity constraint, in the form in which
`CategoryTheory.Monoidal.InducingFunctorData` asks for it: conjugating the localized associator
by the comparison isomorphism gives it back. -/
theorem tensorProductAssociator_eq_comparison
    (M N P : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductAssociator O hO M N P).hom =
      (((tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (M)).obj (N))) P).symm ≪≫
            ((tensorObjIso O hO M N).symm ⊗ᵢ Iso.refl P)) ≪≫
          α_ M N P ≪≫
          ((Iso.refl M ⊗ᵢ tensorObjIso O hO N P) ≪≫
            tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          (N)).obj (P))))).hom := by
  refine ((Iso.eq_inv_comp (whiskerRightIso (tensorObjIso O hO M N) P ≪≫
      tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N)) P)).mpr
    ((Category.assoc _ _ _).trans (tensorObjIso_associativity O hO M N P))).trans ?_
  show ((tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N)) P).inv ≫ (tensorObjIso O hO M N).inv ▷ P) ≫
      (α_ M N P).hom ≫ M ◁ (tensorObjIso O hO N P).hom ≫
        (tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            N).obj P))).hom =
    ((tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          M).obj N)) P).inv ≫ ((tensorObjIso O hO M N).inv ⊗ₘ 𝟙 P)) ≫
      (α_ M N P).hom ≫ (𝟙 M ⊗ₘ (tensorObjIso O hO N P).hom) ≫
        (tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
            N).obj P))).hom
  rw [tensorHom_id (tensorObjIso O hO M N).inv P, id_tensorHom M (tensorObjIso O hO N P).hom]

/-- The fixed left unit constraint, in the form `CategoryTheory.Monoidal.InducingFunctorData`
asks for it. -/
theorem tensorProductLeftUnitor_eq_comparison
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductLeftUnitor O hO M).hom =
      (((tensorObjIso O hO (SheafOfModules.unit _) M).symm ≪≫
          ((Iso.refl (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).symm ⊗ᵢ
            Iso.refl M)) ≪≫ λ_ M).hom := by
  refine ((Iso.eq_inv_comp (tensorObjIso O hO (SheafOfModules.unit _) M)).mpr
    (tensorObjIso_leftUnitor O hO M)).trans ?_
  show _ = ((tensorObjIso O hO (SheafOfModules.unit _) M).inv ≫
    (𝟙 (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) ⊗ₘ 𝟙 M)) ≫ (λ_ M).hom
  rw [id_tensorHom_id, Category.comp_id (tensorObjIso O hO (SheafOfModules.unit _) M).inv]

/-- The fixed right unit constraint, in the form `CategoryTheory.Monoidal.InducingFunctorData`
asks for it. -/
theorem tensorProductRightUnitor_eq_comparison
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (Invertible.tensorProductRightUnitor O hO M).hom =
      (((tensorObjIso O hO M (SheafOfModules.unit _)).symm ≪≫
          (Iso.refl M ⊗ᵢ
            (Iso.refl (SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).symm)) ≪≫
        ρ_ M).hom := by
  refine ((Iso.eq_inv_comp (tensorObjIso O hO M (SheafOfModules.unit _))).mpr
    (tensorObjIso_rightUnitor O hO M)).trans ?_
  show _ = ((tensorObjIso O hO M (SheafOfModules.unit _)).inv ≫
    (𝟙 M ⊗ₘ 𝟙 (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)))) ≫ (ρ_ M).hom
  rw [id_tensorHom_id, Category.comp_id (tensorObjIso O hO M (SheafOfModules.unit _)).inv]

/-- Whiskering on the left for the sheaf tensor product, conjugated into the localized monoidal
structure by the comparison isomorphism. -/
theorem sheafifyWhiskerLeft_eq_comparison
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (g : N ⟶ N') :
    sheafifyWhiskerLeft O hO M g =
      (tensorObjIso O hO M N).inv ≫ M ◁ g ≫ (tensorObjIso O hO M N').hom := by
  refine (Iso.eq_inv_comp (tensorObjIso O hO M N)).mpr ?_
  rw [← MonoidalCategory.id_tensorHom M g]
  exact (tensorObjIso_naturality O hO (𝟙 M) g).symm

/-- Whiskering on the right for the sheaf tensor product, conjugated into the localized monoidal
structure by the comparison isomorphism. -/
theorem sheafifyWhiskerRight_eq_comparison
    {M M' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (f : M ⟶ M')
    (N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    sheafifyWhiskerRight O hO f N =
      (tensorObjIso O hO M N).inv ≫ f ▷ N ≫ (tensorObjIso O hO M' N).hom := by
  refine (Iso.eq_inv_comp (tensorObjIso O hO M N)).mpr ?_
  rw [← MonoidalCategory.tensorHom_id f N]
  exact (tensorObjIso_naturality O hO f (𝟙 N)).symm

/-- The sheaf tensor product of a pair of morphisms, conjugated into the localized monoidal
structure by the comparison isomorphism. -/
theorem sheafifyTensorHom_eq_comparison
    {M M' N N' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (g : N ⟶ N') :
    sheafifyTensorHom O hO f g =
      (tensorObjIso O hO M N).inv ≫ (f ⊗ₘ g) ≫ (tensorObjIso O hO M' N').hom :=
  (Iso.eq_inv_comp (tensorObjIso O hO M N)).mpr (tensorObjIso_naturality O hO f g).symm

/-- The monoidal category structure data on sheaves of modules carried by the sheaf tensor
product of Tag 05NA and the fixed constraints. -/
@[instance_reducible]
noncomputable def sheafTensorStruct :
    MonoidalCategoryStruct (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) where
  tensorObj M N := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj (M)).obj (N))
  tensorHom f g := sheafifyTensorHom O hO f g
  whiskerLeft M _ _ g := sheafifyWhiskerLeft O hO M g
  whiskerRight f N := sheafifyWhiskerRight O hO f N
  tensorUnit := SheafOfModules.unit _
  leftUnitor := Invertible.tensorProductLeftUnitor O hO
  rightUnitor := Invertible.tensorProductRightUnitor O hO
  associator := Invertible.tensorProductAssociator O hO

/-- The identity functor from `sheafTensorStruct` to the localized monoidal structure is an
inducing functor: the comparison `tensorObjIso` is monoidal for the fixed constraints. -/
noncomputable def sheafTensorInducingData :
    letI := sheafTensorStruct O hO
    Monoidal.InducingFunctorData (toSheafLocalized O hO) :=
  letI := sheafTensorStruct O hO
  { μIso := tensorObjIso O hO
    εIso := Iso.refl _
    whiskerLeft_eq := fun M _ _ g => sheafifyWhiskerLeft_eq_comparison O hO M g
    whiskerRight_eq := fun f N => sheafifyWhiskerRight_eq_comparison O hO f N
    tensorHom_eq := fun f g => sheafifyTensorHom_eq_comparison O hO f g
    associator_eq := fun M N P => tensorProductAssociator_eq_comparison O hO M N P
    leftUnitor_eq := fun M => tensorProductLeftUnitor_eq_comparison O hO M
    rightUnitor_eq := fun M => tensorProductRightUnitor_eq_comparison O hO M }

/-- **The sheaf tensor product of Tag 05NA, with the fixed unit and associativity constraints,
is a monoidal structure on sheaves of modules.** -/
@[instance_reducible]
noncomputable def sheafTensorMonoidal :
    MonoidalCategory (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :=
  letI := sheafTensorStruct O hO
  Monoidal.induced (toSheafLocalized O hO) (sheafTensorInducingData O hO)

/-- **That monoidal structure is symmetric, with braiding the fixed symmetry constraint
`Invertible.tensorProductBraiding`.** -/
@[instance_reducible]
noncomputable def sheafTensorSymmetric :
    letI := sheafTensorMonoidal O hO
    SymmetricCategory (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :=
  letI := sheafTensorStruct O hO
  letI := sheafTensorMonoidal O hO
  letI : (toSheafLocalized O hO).Monoidal :=
    Monoidal.fromInducedMonoidal (toSheafLocalized O hO) (sheafTensorInducingData O hO)
  letI : BraidedCategory (SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :=
    BraidedCategory.ofFaithful (toSheafLocalized O hO) (Invertible.tensorProductBraiding O hO)
      fun M N => tensorObjIso_braiding O hO M N
  letI : (toSheafLocalized O hO).Braided :=
    { braided := fun M N => tensorObjIso_braiding O hO M N }
  SymmetricCategory.ofFaithful (toSheafLocalized O hO)

end Stacks.SheafOfModules

end
