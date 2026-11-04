module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalFiniteFreeSummand
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# The unitors of the tensor product sheaf, on local sections

Let `(C, J, 𝒪)` be a ringed site.  The tensor product sheaf of Stacks Tag 01CA,
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, is the sheafification of the objectwise
  tensor product of the
underlying presheaves of modules, and the structure sheaf is the unit for it: there is a
canonical isomorphism `A ⊗_𝒪 𝒪 ≅ A`, and dually `𝒪 ⊗_𝒪 A ≅ A`.  This file constructs those two
isomorphisms for an arbitrary ringed site and, which is the point of the file, **computes all
four of them on local sections**: the forward maps send the sheafification-unit image of a pure
tensor `x ⊗ r` (respectively `r ⊗ x`) to `r • x`, and the inverse maps send a local section `x`
to the image of `x ⊗ 1` (respectively `1 ⊗ x`).

## Main definitions

* `Stacks.SheafOfModules.tensorSheafUnitRightIso` and
  `Stacks.SheafOfModules.tensorSheafUnitLeftIso`: the right and left unitors
  `A ⊗_𝒪 𝒪 ≅ A` and `𝒪 ⊗_𝒪 A ≅ A` of the tensor product sheaf on a ringed site.
* `Stacks.RingedSpace.tensorSheafUnitRightIso` and
  `Stacks.RingedSpace.tensorSheafUnitLeftIso`: the same two isomorphisms on a ringed space, typed
  over the tensor bifunctor `Stacks.RingedSpace.tensorSheaf` of Tag 0GMW.
* `AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso` and
  `AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso`: the same two isomorphisms again, in
  the `Stacks.SheafOfModules.TensorStalkRingedSpace` spelling of the tensor product sheaf.

## Main results

* `Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul` and
  `Stacks.SheafOfModules.tensorSheafUnitLeftIso_hom_toSheafify_tmul`: **the section formulas**
  `ρ(x ⊗ r) = r • x` and `λ(r ⊗ x) = r • x`, where `x ⊗ r` means the image under the
  sheafification unit of the pure tensor of local sections.
* `Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app` and
  `Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app`: the inverses are `x ↦ x ⊗ 1` and
  `x ↦ 1 ⊗ x`.
* `Stacks.RingedSpace.tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul`,
  `tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul` and their two `_inv_app_tensorSheafUnit`
  companions: the same four formulas on a ringed space, written with
  `Stacks.RingedSpace.tensorSheafUnit`, the sheafification unit of Tag 0GMW.
* `AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso_hom_toTensorSheafSection`,
  `tensorSheafUnitLeftIso_hom_toTensorSheafSection` and the two `_inv_app` companions: the same
  four formulas again, written with
    `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, the canonical map on
  sections `F(U) ⊗_{𝒪(U)} G(U) → (F ⊗_{𝒪_X} G)(U)`.
* `AlgebraicGeometry.SheafOfModules.toTensorSheafSection_eq_tensorSheafUnit`: those last two maps
  on sections are the same, so all the formulas are about one map.

## Implementation notes

**Why a section formula is not a formality.** The monoidal structure on sheaves of modules of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` is obtained by localizing the presheaf
monoidal structure along sheafification, so its unitors come from the universal property of the
localization and have no explicit description; that file's implementation notes say so.  What is
explicit is the *presheaf* right unitor, `PresheafOfModules.monoidalCategoryStruct`'s
`rightUnitor`, whose action on sections is Mathlib's
`ModuleCat.MonoidalCategory.rightUnitor_hom_apply`.  The two isomorphisms here are therefore
built by transporting the presheaf unitors through sheafification — `sheafifyFunctor.mapIso (ρ_
A.val)` followed by `Stacks.SheafOfModules.sheafifyValIso`, the counit of the sheafification
adjunction at a sheaf — and the section formulas follow from naturality of the sheafification
unit together with the right triangle identity of that adjunction.  No statement here mentions
`MonoidalCategory (SheafOfModules _)`, so nothing in this file depends on which monoidal
structure one puts on sheaves of modules.

**The spelling of the structure sheaf of rings.**  Everything is phrased through
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨𝒪, _⟩`, the sheaf of rings
`𝒪 ⋙ forget₂ CommRingCat RingCat` of the ringed site, at the anonymous-constructor index
`⟨𝒪, _⟩` that this file's tensor products
(`Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, _⟩`) are themselves indexed at, and through
  `Stacks.SheafOfModules.sheafifyFunctor`,
the retyping of `Stacks.SheafOfModules.TensorSheafification.sheafify` over
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`.  Both are
load-bearing: with `Stacks.SheafOfModules.TensorSheafification.structureSheaf` in the types, `ρ_
  A.val` fails to elaborate with
"failed to synthesize `MonoidalCategoryStruct (PresheafOfModules
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
h𝒪).obj)`", because Mathlib's monoidal structure on presheaves of modules is indexed by a ring
presheaf of the syntactic shape `𝒪 ⋙ forget₂ CommRingCat RingCat` and instance search does not
unfold a plain `def` to see it.  `Stacks.SheafOfModules.Tensor.ringSheaf` is itself a plain
`def`, so it is declared `local implicit_reducible` below: that is what lets the unitors of
`PresheafOfModules (Tensor.ringSheaf ⟨𝒪, _⟩).obj` be recognised as unitors of the tensor
bifunctor of `⟨𝒪, _⟩.obj`.  This is the same difficulty recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalFiniteFreeSummand` and in the implementation
notes of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal`.

**Three tensor-product constructions, one object.**
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 A B`,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X A B` and
  `(Stacks.RingedSpace.tensorSheaf X).obj (A, B)` are equal
by `rfl` on a ringed space (with `𝒪 = X.presheaf`), as are the three structure sheaves of rings,
so the ringed-space statements below are definitional specialisations of the ringed-site ones
and no bridge is constructed.

**One term, three spellings, and why.**  The ringed-space declarations delegate to the
ringed-site ones and the `Stacks.SheafOfModules.TensorStalkRingedSpace` ones delegate to the
  `Stacks.RingedSpace` ones, so there
is a single underlying isomorphism; what the retypings buy is that a calculation can stay in one
spelling.  That matters: a `rw` on a goal mentioning two of the spellings fails with "the target
expression is not type-correct under the `implicit` transparency level", because unfolding
`Stacks.RingedSpace.structureRingSheaf` exposes `CategoryTheory.Sheaf.toRingCat _ X.sheaf` and
`X.sheaf : TopCat.Sheaf CommRingCat _` does not reduce at that transparency.  This is the same
pattern as `Stacks.RingedSpace.pullbackFunctor` and `pushforwardFunctor`.

**Relation to the two isomorphisms already in the tree.**
`Stacks.SheafOfModules.TensorOver.tensorUnitRightIso`
(`StacksFrontier/AlgebraicGeometry/TensorCoherence/Basic.lean`) is this file's right unitor for
the slice site over an open of a ringed space, and is the instance
`𝒪 = (X.sheaf.over U).obj` of `Stacks.SheafOfModules.tensorSheafUnitRightIso`; it carries no
section formula.  `AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso` used to be declared
in `StacksFrontier/AlgebraicGeometry/CurveTensorEuler/Basic.lean` with the same type and the
same body; it is declared here instead, so that the section formulas can live beside it and so
that a consumer of the unitor does not have to import the Euler-characteristic development.
DEDUP OWED: `TensorOver.tensorUnitRightIso` should be replaced by
`tensorSheafUnitRightIso (X.sheaf.over U).obj (TensorOver.hOU U)`.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [The Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### Sections of a sheafified morphism, and of the sheafification counit -/

/-- The sheafification of a morphism of presheaves of modules, read on the image of a local
section under the sheafification unit.  This is naturality of that unit. -/
lemma sheafify_map_toSheafify_apply
    {P Q : PresheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj}
    (f : P ⟶ Q) (V : Cᵒᵖ) (x : P.obj V) :
    ((sheafifyFunctor 𝒪 h𝒪).map f).val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify
      𝒪 h𝒪 P).app V x) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 Q).app V (f.app V x) :=
  (congrArg (fun k ↦ k.app V x) ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪
    h𝒪).unit.naturality f)).symm

/-- Identifying the sheafification of a sheaf of modules with itself undoes the sheafification
unit on local sections.  This is the right triangle identity of the sheafification
adjunction. -/
lemma sheafifyValIso_hom_toSheafify_apply (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (x : A.val.obj V) :
    (sheafifyValIso 𝒪 h𝒪 A).hom.val.app V ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪
      h𝒪 A.val).app V x) = x :=
  congrArg (fun k ↦ (PresheafOfModules.Hom.app k V) x)
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).right_triangle_components
      A)

/-- The inverse of `sheafifyValIso` is the sheafification unit. -/
lemma sheafifyValIso_inv_app (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (x : A.val.obj V) :
    (sheafifyValIso 𝒪 h𝒪 A).inv.val.app V x = (Stacks.SheafOfModules.TensorSheafification.toSheafify
      𝒪 h𝒪 A.val).app V x := by
  have h : (⟨Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 A.val⟩ :
        A ⟶ (sheafifyFunctor 𝒪 h𝒪).obj A.val) = (sheafifyValIso 𝒪 h𝒪 A).inv :=
    (Iso.comp_hom_eq_id (sheafifyValIso 𝒪 h𝒪 A)).mp (SheafOfModules.hom_ext
      ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪
        h𝒪).right_triangle_components A))
  exact congrArg (fun k ↦ (PresheafOfModules.Hom.app (SheafOfModules.Hom.val k) V) x) h.symm

/-- A morphism into `A.val`, sheafified and followed by `sheafifyValIso`, is itself on the image
of a local section under the sheafification unit. -/
private lemma sheafifyValIso_hom_map_toSheafify_apply (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    {P : PresheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj}
    (f : P ⟶ A.val) (V : Cᵒᵖ) (z : P.obj V) :
    (sheafifyValIso 𝒪 h𝒪 A).hom.val.app V (((sheafifyFunctor 𝒪 h𝒪).map f).val.app V
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V z)) = f.app V z :=
  (congrArg _ (sheafify_map_toSheafify_apply 𝒪 h𝒪 f V z)).trans
    (sheafifyValIso_hom_toSheafify_apply 𝒪 h𝒪 A V _)

/-- A morphism out of `A.val`, sheafified, sends the image of a local section under the inverse of
`sheafifyValIso` to the sheafification unit of its image. -/
private lemma sheafify_map_sheafifyValIso_inv_apply (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    {P : PresheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj}
    (f : A.val ⟶ P) (V : Cᵒᵖ) (x : A.val.obj V) :
    ((sheafifyFunctor 𝒪 h𝒪).map f).val.app V ((sheafifyValIso 𝒪 h𝒪 A).inv.val.app V x) =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P).app V (f.app V x) :=
  (congrArg _ (sheafifyValIso_inv_app 𝒪 h𝒪 A V x)).trans
    (sheafify_map_toSheafify_apply 𝒪 h𝒪 f V x)

/-! ### The right unitor -/

/-- **The right unitor of the tensor product sheaf of Tag 01CA on a ringed site**:
`A ⊗_𝒪 𝒪 ≅ A`.  It is the presheaf right unitor, which is objectwise the canonical
`M ⊗_R R ≅ M`, carried through sheafification. -/
noncomputable def tensorSheafUnitRightIso (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        (A)).obj ((SheafOfModules.unit (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)))) ≅ A :=
  (sheafifyFunctor 𝒪 h𝒪).mapIso (ρ_ A.val) ≪≫ sheafifyValIso 𝒪 h𝒪 A

/-- **The section formula for the right unitor**: on the image under the sheafification unit of
the pure tensor of a local section `x` of `A` with a local section `r` of the structure sheaf,
the right unitor is `r • x`. -/
lemma tensorSheafUnitRightIso_hom_toSheafify_tmul (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (x : A.val.obj V) (r : (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) :
    (tensorSheafUnitRightIso 𝒪 h𝒪 A).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            (A.val ⊗ (SheafOfModules.unit (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
                (forget₂ CommRingCat RingCat) h𝒪⟩)).val)).app V
          (x ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] r)) = r • x := by
  refine (sheafifyValIso_hom_map_toSheafify_apply 𝒪 h𝒪 A (ρ_ A.val).hom V _).trans ?_
  exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply x r

/-- **The inverse right unitor on local sections**: tensoring with the unit section `1`. -/
lemma tensorSheafUnitRightIso_inv_app (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (x : A.val.obj V) :
    (tensorSheafUnitRightIso 𝒪 h𝒪 A).inv.val.app V x =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          (A.val ⊗ (SheafOfModules.unit (Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩)).val)).app V
        (x ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V]
          (1 : (Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V)) := by
  refine (sheafify_map_sheafifyValIso_inv_apply 𝒪 h𝒪 A (ρ_ A.val).inv V x).trans ?_
  exact congrArg ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 _).app V)
    (ModuleCat.MonoidalCategory.rightUnitor_inv_apply x)

/-! ### The left unitor -/

/-- **The left unitor of the tensor product sheaf of Tag 01CA on a ringed site**:
`𝒪 ⊗_𝒪 A ≅ A`. -/
noncomputable def tensorSheafUnitLeftIso (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
        ((SheafOfModules.unit (Tensor.ringSheaf
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
            (forget₂ CommRingCat RingCat) h𝒪⟩)))).obj (A)) ≅ A :=
  (sheafifyFunctor 𝒪 h𝒪).mapIso (λ_ A.val) ≪≫ sheafifyValIso 𝒪 h𝒪 A

/-- **The section formula for the left unitor**. -/
lemma tensorSheafUnitLeftIso_hom_toSheafify_tmul (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (r : (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V)
    (x : A.val.obj V) :
    (tensorSheafUnitLeftIso 𝒪 h𝒪 A).hom.val.app V
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            ((SheafOfModules.unit (Tensor.ringSheaf
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
                (forget₂ CommRingCat RingCat) h𝒪⟩)).val ⊗ A.val)).app V
          (r ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] x)) = r • x := by
  refine (sheafifyValIso_hom_map_toSheafify_apply 𝒪 h𝒪 A (λ_ A.val).hom V _).trans ?_
  exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply r x

/-- **The inverse left unitor on local sections**: tensoring with the unit section `1` on the
left. -/
lemma tensorSheafUnitLeftIso_inv_app (A : SheafOfModules.{w} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩))
    (V : Cᵒᵖ) (x : A.val.obj V) :
    (tensorSheafUnitLeftIso 𝒪 h𝒪 A).inv.val.app V x =
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
          ((SheafOfModules.unit (Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩)).val ⊗ A.val)).app V
        ((1 : (Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V) ⊗ₜ[(Tensor.ringSheaf
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj.obj V] x) := by
  refine (sheafify_map_sheafifyValIso_inv_apply 𝒪 h𝒪 A (λ_ A.val).inv V x).trans ?_
  exact congrArg ((Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 _).app V)
    (ModuleCat.MonoidalCategory.leftUnitor_inv_apply x)

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

open PresheafOfModules

variable (X : _root_.AlgebraicGeometry.RingedSpace.{u, u})
  (A : _root_.SheafOfModules.{u} (structureRingSheaf X))

/-! ### The unitors on a ringed space, in the `Stacks.RingedSpace` spelling of Tag 0GMW

These are the ringed-site unitors above, specialised to the site of opens of a ringed space and
typed over `Stacks.RingedSpace.tensorSheaf` and `Stacks.RingedSpace.structureRingSheaf` — the
spelling the comparison morphism of Tag 01CD and the projection-formula morphism are written
against.  The `Stacks.SheafOfModules.TensorStalkRingedSpace` spelling of the same two isomorphisms
  is in the next section.

They are plain `def`s rather than `abbrev`s on purpose, and that is load-bearing: a *reducible*
retyping is unfolded by `rw`'s motive type-check, which then sees
`CategoryTheory.Sheaf.toRingCat _ X.sheaf` with `X.sheaf : TopCat.Sheaf CommRingCat _`, and
reports the motive ill-typed at `implicit` transparency, because `TopCat.Sheaf` does not unfold
there either.  An opaque constant is invisible to that check, and then every `rw` in a
calculation that mentions the unitor goes through. -/

/-- The right unitor `A ⊗_{𝒪_X} 𝒪_X ≅ A`, typed over `Stacks.RingedSpace.tensorSheaf`. -/
noncomputable def tensorSheafUnitRightIso :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj (A, _root_.SheafOfModules.unit (structureRingSheaf X)) ≅ A :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso X.sheaf.obj (structureRingSheaf X).property A

/-- The left unitor `𝒪_X ⊗_{𝒪_X} A ≅ A`, typed over `Stacks.RingedSpace.tensorSheaf`. -/
noncomputable def tensorSheafUnitLeftIso :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj (_root_.SheafOfModules.unit (structureRingSheaf X), A) ≅ A :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso X.sheaf.obj (structureRingSheaf X).property A

/-- **The right unitor on local sections**, in the spelling of Tag 0GMW. -/
lemma tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul (U : (Opens X.carrier)ᵒᵖ)
    (x : A.val.obj U) (r : (structureRingSheaf X).obj.obj U) :
    (tensorSheafUnitRightIso X A).hom.val.app U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val ((_root_.SheafOfModules.unit (structureRingSheaf X))).val)) U
          (x ⊗ₜ r)) = r • x :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul X.sheaf.obj
    (structureRingSheaf X).property A U x r

/-- **The inverse right unitor on local sections**, in the spelling of Tag 0GMW. -/
lemma tensorSheafUnitRightIso_inv_app_tensorSheafUnit (U : (Opens X.carrier)ᵒᵖ)
    (x : A.val.obj U) :
    (tensorSheafUnitRightIso X A).inv.val.app U x =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val ((_root_.SheafOfModules.unit (structureRingSheaf X))).val)) U
        (x ⊗ₜ (1 : (structureRingSheaf X).obj.obj U)) :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app X.sheaf.obj
    (structureRingSheaf X).property A U x

/-- **The left unitor on local sections**, in the spelling of Tag 0GMW. -/
lemma tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul (U : (Opens X.carrier)ᵒᵖ)
    (r : (structureRingSheaf X).obj.obj U) (x : A.val.obj U) :
    (tensorSheafUnitLeftIso X A).hom.val.app U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) ((_root_.SheafOfModules.unit (structureRingSheaf X))).val (A).val)) U
          (r ⊗ₜ x)) = r • x :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso_hom_toSheafify_tmul X.sheaf.obj
    (structureRingSheaf X).property A U r x

/-- **The inverse left unitor on local sections**, in the spelling of Tag 0GMW. -/
lemma tensorSheafUnitLeftIso_inv_app_tensorSheafUnit (U : (Opens X.carrier)ᵒᵖ)
    (x : A.val.obj U) :
    (tensorSheafUnitLeftIso X A).inv.val.app U x =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) ((_root_.SheafOfModules.unit (structureRingSheaf X))).val (A).val)) U
        ((1 : (structureRingSheaf X).obj.obj U) ⊗ₜ x) :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app X.sheaf.obj
    (structureRingSheaf X).property A U x

end Stacks.RingedSpace

namespace AlgebraicGeometry.SheafOfModules

variable (X : RingedSpace.{u, u})
  (F : _root_.SheafOfModules.{u} (structureSheafRing
    X))

/-! ### The unitors on a ringed space, in the `Stacks.SheafOfModules.TensorStalkRingedSpace`
  spelling of Tag 01CA

The same two isomorphisms once more, re-typed over
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.  There is one
underlying term: these delegate to the `Stacks.RingedSpace` declarations above, which delegate to
the ringed-site ones, and the three spellings of the tensor product sheaf agree by `rfl`. -/

/-- **The right unitor of the tensor product sheaf**: `ℱ ⊗_{𝒪_X} 𝒪_X ≅ ℱ` for the tensor
product of Tag 01CA on a ringed space. -/
noncomputable def tensorSheafUnitRightIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj ((_root_.SheafOfModules.unit (structureSheafRing
          X)))) ≅ F :=
  Stacks.RingedSpace.tensorSheafUnitRightIso X F

/-- **The left unitor of the tensor product sheaf**: `𝒪_X ⊗_{𝒪_X} ℱ ≅ ℱ`. -/
noncomputable def tensorSheafUnitLeftIso :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj ((_root_.SheafOfModules.unit (structureSheafRing
          X)))).obj (F)) ≅ F :=
  Stacks.RingedSpace.tensorSheafUnitLeftIso X F

/-- **The section formula for the right unitor on a ringed space**: it carries the image in
`(ℱ ⊗ 𝒪_X)(U)` of a pure tensor `x ⊗ r` to `r • x`. -/
lemma tensorSheafUnitRightIso_hom_toTensorSheafSection (U : (Opens X.carrier)ᵒᵖ)
    (x : F.val.obj U) (r : (structureSheafRing
      X).obj.obj U) :
    (tensorSheafUnitRightIso X F).hom.val.app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F
          (_root_.SheafOfModules.unit
            (structureSheafRing X)) U (x ⊗ₜ r)) =
      r • x :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul X.sheaf.obj
    (structureSheafRing X).property F U x r

/-- **The inverse right unitor on sections, on a ringed space**: `x ↦ x ⊗ 1`. -/
lemma tensorSheafUnitRightIso_inv_app (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) :
    (tensorSheafUnitRightIso X F).inv.val.app U x =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F
        (_root_.SheafOfModules.unit (structureSheafRing
          X)) U
        (x ⊗ₜ (1 : (structureSheafRing X).obj.obj U))
          :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app X.sheaf.obj
    (structureSheafRing X).property F U x

/-- **The section formula for the left unitor on a ringed space**. -/
lemma tensorSheafUnitLeftIso_hom_toTensorSheafSection (U : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X).obj.obj U) (x :
      F.val.obj U) :
    (tensorSheafUnitLeftIso X F).hom.val.app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X
          (_root_.SheafOfModules.unit
            (structureSheafRing X)) F U (r ⊗ₜ x)) =
      r • x :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso_hom_toSheafify_tmul X.sheaf.obj
    (structureSheafRing X).property F U r x

/-- **The inverse left unitor on sections, on a ringed space**: `x ↦ 1 ⊗ x`. -/
lemma tensorSheafUnitLeftIso_inv_app (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) :
    (tensorSheafUnitLeftIso X F).inv.val.app U x =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X
        (_root_.SheafOfModules.unit (structureSheafRing
          X)) F U
        ((1 : (structureSheafRing X).obj.obj U) ⊗ₜ x)
          :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app X.sheaf.obj
    (structureSheafRing X).property F U x

/-- The canonical map on sections into the tensor product sheaf of Tag 01CA is the
sheafification unit `Stacks.RingedSpace.tensorSheafUnit` of Tag 0GMW, so the section formulas
above and the ones of the previous section are about the same map. -/
lemma toTensorSheafSection_eq_tensorSheafUnit
    (A B : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X A B U (x ⊗ₜ y) =
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction (R := Stacks.RingedSpace.structureRingSheaf (X)) (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app (PresheafOfModules.tensorObj (O := (X).presheaf) (A).val (B).val)) U (x ⊗ₜ y) :=
  rfl

end AlgebraicGeometry.SheafOfModules

end
