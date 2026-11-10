module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport

/-!
# The Picard transport is an isomorphism when the functor is an equivalence on a subcategory

`Stacks.SheafOfModules.Picard.mapAddEquiv` shows that a functor `F : Mod(O₁) ⥤ Mod(O₂)` with
object-level unit and tensor comparisons induces an isomorphism of the Picard groups of
Tag 01CX *when `F` itself is an equivalence*.  That hypothesis is stronger than what the Picard
group sees.  The functor `𝓕 ↦ 𝓕^a` of Descent, Proposition 03DX is **not** an equivalence of the
full categories of modules; it is an equivalence of the *quasi-coherent* ones.  What makes the
Picard groups agree all the same is that an invertible module is quasi-coherent, so the whole
Picard group already lives inside the subcategory on which `F` is an equivalence.

This file isolates that argument.  The input is a pair of predicates `P₁` and `P₂` on the two
categories of modules, each satisfied by the invertible modules, with `P₁` closed under the
tensor product sheaf and holding at the structure sheaf, such that `F` reflects isomorphisms
between `P₁`-objects and every `P₂`-object is the image of a `P₁`-object.  No functoriality of
the subcategories, no monoidal structure, and no coherence is used; see the discussion in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean`.

## Why `P₁` has to be closed under `⊗` and to hold at `O₁`

Injectivity needs only reflection of isomorphisms at invertible modules.  Surjectivity needs
more: the `P₁`-object `𝓕` whose image is a given invertible `𝓐` has to be shown *invertible*,
and all that is known of it is that `F 𝓕 ≅ 𝓐` is invertible.  Through Tag 0B8K this produces an
`𝓝` with `F 𝓕 ⊗ 𝓝 ≅ O₂`; `𝓝` is itself invertible, hence a `P₂`-object, hence `F 𝓝₁` for some
`P₁`-object `𝓝₁`, and the tensor comparison turns the relation into
`F(𝓕 ⊗ 𝓝₁) ≅ O₂ ≅ F(O₁)`.  Reflection of isomorphisms applies to that pair exactly because
`𝓕 ⊗ 𝓝₁` and `O₁` are `P₁`-objects, and then `𝓕 ⊗ 𝓝₁ ≅ O₁` says `𝓕` is invertible.

## Main results

* `Stacks.SheafOfModules.Picard.bijective_map_of_subcategory`: **the induced homomorphism of
  Picard groups is bijective.**
* `Stacks.SheafOfModules.Picard.mapAddEquivOfSubcategory`: the induced **isomorphism** of Picard
  groups, with `Stacks.SheafOfModules.Picard.mapAddEquivOfSubcategory_classOf` fixing it on the
  class of an invertible module.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v₁ u₁ v₂ u₂ w

namespace Stacks.SheafOfModules.Picard

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  (O₁ : C₁ᵒᵖ ⥤ CommRingCat.{w}) (hO₁ : Presheaf.IsSheaf J₁ (structureRingPresheaf O₁))
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₁ AddCommGrpCat.{w}]
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  (O₂ : C₂ᵒᵖ ⥤ CommRingCat.{w}) (hO₂ : Presheaf.IsSheaf J₂ (structureRingPresheaf O₂))
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₂ AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (structureSheaf O₁ hO₁) ⥤ SheafOfModules.{w} (structureSheaf O₂ hO₂))

/-- **A tensor inverse of an invertible module is invertible.**  If `L ⊗ N ≅ O`, then
`N ⊗ L ≅ O` by the braiding of the tensor product sheaf. -/
theorem isInvertible_of_tensor_iso_unit
    {L N : SheafOfModules.{w} (structureSheaf O₁ hO₁)}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁
          (forget₂ CommRingCat RingCat) hO₁⟩).obj L).obj N ≅
      SheafOfModules.unit (structureSheaf O₁ hO₁)) :
    IsInvertible O₁ hO₁ N :=
  (isInvertible_iff_exists_tensor_iso_unit N).2
    ⟨L, ⟨tensorSheafBraiding O₁ hO₁ N L ≪≫ e⟩⟩

/-- **The homomorphism of Picard groups induced by `F` is bijective** as soon as `F` reflects
isomorphisms between `P₁`-objects and hits every `P₂`-object, where `P₁` and `P₂` are predicates
satisfied by the invertible modules, `P₁` holding at the structure sheaf and closed under the
tensor product sheaf.

`F` itself need not be an equivalence; what is asked is that it be one on the subcategories, and
only through the two clauses the proof uses. -/
theorem bijective_map_of_subcategory (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    {P₁ : SheafOfModules.{w} (structureSheaf O₁ hO₁) → Prop}
    {P₂ : SheafOfModules.{w} (structureSheaf O₂ hO₂) → Prop}
    (hP₁ : ∀ M, IsInvertible O₁ hO₁ M → P₁ M)
    (hP₂ : ∀ A, IsInvertible O₂ hO₂ A → P₂ A)
    (hP₁unit : P₁ (SheafOfModules.unit (structureSheaf O₁ hO₁)))
    (hP₁tensor : ∀ M N, P₁ M → P₁ N → P₁ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj M).obj N))
    (hreflect : ∀ M N, P₁ M → P₁ N → (F.obj M ≅ F.obj N) → Nonempty (M ≅ N))
    (hhit : ∀ A, P₂ A → ∃ M, P₁ M ∧ Nonempty (F.obj M ≅ A)) :
    Function.Bijective (map O₁ hO₁ O₂ hO₂ F hunit hten) := by
  constructor
  · intro x y hxy
    obtain ⟨L, hL, rfl⟩ := exists_classOf_eq O₁ hO₁ x
    obtain ⟨N, hN, rfl⟩ := exists_classOf_eq O₁ hO₁ y
    rw [map_classOf, map_classOf] at hxy
    obtain ⟨e⟩ := (classOf_eq_classOf_iff O₂ hO₂ _ _ _ _).1 hxy
    exact (classOf_eq_classOf_iff O₁ hO₁ L N hL hN).2
      (hreflect L N (hP₁ L hL) (hP₁ N hN) e)
  · intro y
    obtain ⟨A, hA, rfl⟩ := exists_classOf_eq O₂ hO₂ y
    obtain ⟨𝓕, hP𝓕, ⟨e⟩⟩ := hhit A (hP₂ A hA)
    obtain ⟨N, ⟨eN⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit A).1 hA
    have hN : IsInvertible O₂ hO₂ N := isInvertible_of_tensor_iso_unit O₂ hO₂ eN
    obtain ⟨𝓝, hP𝓝, ⟨eF𝓝⟩⟩ := hhit N (hP₂ N hN)
    have hkey : F.obj (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj
        𝓕).obj 𝓝) ≅
        F.obj (SheafOfModules.unit (structureSheaf O₁ hO₁)) :=
      hten 𝓕 𝓝 ≪≫ Invertible.tensorProductIso O₂ hO₂ e eF𝓝 ≪≫ eN ≪≫ hunit.symm
    obtain ⟨e𝓕⟩ := hreflect (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj 𝓕).obj 𝓝)
      (SheafOfModules.unit (structureSheaf O₁ hO₁))
      (hP₁tensor 𝓕 𝓝 hP𝓕 hP𝓝) hP₁unit hkey
    have h𝓕 : IsInvertible O₁ hO₁ 𝓕 :=
      (isInvertible_iff_exists_tensor_iso_unit 𝓕).2 ⟨𝓝, ⟨e𝓕⟩⟩
    refine ⟨classOf O₁ hO₁ 𝓕 h𝓕, ?_⟩
    rw [map_classOf]
    exact (classOf_eq_classOf_iff O₂ hO₂ _ _ _ hA).2 ⟨e⟩

/-- **The isomorphism of Picard groups induced by a functor which is an equivalence on a
subcategory containing the invertible modules.** -/
def mapAddEquivOfSubcategory (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    {P₁ : SheafOfModules.{w} (structureSheaf O₁ hO₁) → Prop}
    {P₂ : SheafOfModules.{w} (structureSheaf O₂ hO₂) → Prop}
    (hP₁ : ∀ M, IsInvertible O₁ hO₁ M → P₁ M)
    (hP₂ : ∀ A, IsInvertible O₂ hO₂ A → P₂ A)
    (hP₁unit : P₁ (SheafOfModules.unit (structureSheaf O₁ hO₁)))
    (hP₁tensor : ∀ M N, P₁ M → P₁ N → P₁ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj M).obj N))
    (hreflect : ∀ M N, P₁ M → P₁ N → (F.obj M ≅ F.obj N) → Nonempty (M ≅ N))
    (hhit : ∀ A, P₂ A → ∃ M, P₁ M ∧ Nonempty (F.obj M ≅ A)) :
    PicardGroup O₁ hO₁ ≃+ PicardGroup O₂ hO₂ :=
  AddEquiv.ofBijective (map O₁ hO₁ O₂ hO₂ F hunit hten)
    (bijective_map_of_subcategory O₁ hO₁ O₂ hO₂ F hunit hten hP₁ hP₂ hP₁unit hP₁tensor
      hreflect hhit)

/-- The isomorphism sends the class of an invertible module to the class of its image, which
fixes it rather than only asserting that some isomorphism exists. -/
theorem mapAddEquivOfSubcategory_classOf (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    {P₁ : SheafOfModules.{w} (structureSheaf O₁ hO₁) → Prop}
    {P₂ : SheafOfModules.{w} (structureSheaf O₂ hO₂) → Prop}
    (hP₁ : ∀ M, IsInvertible O₁ hO₁ M → P₁ M)
    (hP₂ : ∀ A, IsInvertible O₂ hO₂ A → P₂ A)
    (hP₁unit : P₁ (SheafOfModules.unit (structureSheaf O₁ hO₁)))
    (hP₁tensor : ∀ M N, P₁ M → P₁ N → P₁ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ O₁ (forget₂ CommRingCat RingCat) hO₁⟩).obj M).obj N))
    (hreflect : ∀ M N, P₁ M → P₁ N → (F.obj M ≅ F.obj N) → Nonempty (M ≅ N))
    (hhit : ∀ A, P₂ A → ∃ M, P₁ M ∧ Nonempty (F.obj M ≅ A))
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) (hL : IsInvertible O₁ hO₁ L) :
    mapAddEquivOfSubcategory O₁ hO₁ O₂ hO₂ F hunit hten hP₁ hP₂ hP₁unit hP₁tensor hreflect hhit
        (classOf O₁ hO₁ L hL) =
      classOf O₂ hO₂ (F.obj L) (isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten L hL) :=
  map_classOf O₁ hO₁ O₂ hO₂ F hunit hten L hL

end Stacks.SheafOfModules.Picard

end
