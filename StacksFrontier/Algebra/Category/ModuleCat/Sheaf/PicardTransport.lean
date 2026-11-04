module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard

/-!
# Transporting the Picard group along a functor with an object-level tensor comparison

Let `O₁` and `O₂` be sheaves of commutative rings on two sites and let

`F : Mod(O₁) ⥤ Mod(O₂)`

be a functor carrying the structure sheaf to the structure sheaf and the tensor product sheaf of
Tag 01CA to the tensor product sheaf, *on objects only*.  This file shows that such an `F` carries
invertible modules to invertible modules and induces a homomorphism of the Picard groups of
Tag 01CX, `Stacks.SheafOfModules.Picard.PicardGroup`, sending the class of an invertible module to
the class of its image; and that the homomorphism is an isomorphism of abelian groups when `F` is
an equivalence.

## What is and is not needed

The input is *two isomorphisms of objects*, `F(O₁) ≅ O₂` and `F(L ⊗ N) ≅ F L ⊗ F N`, with **no
naturality in `L` and `N` and no monoidal coherence** — no associativity constraint, no unitality,
no pentagon and no triangle.  That this suffices is not an accident of the construction: the
Picard group of Tag 01CX is a group of *isomorphism classes*, and
`Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff` together with
`Stacks.SheafOfModules.Picard.classOf_tensor` pin its addition down completely in terms of the
tensor product sheaf on objects.  A coherence condition is a statement about morphisms between
tensor products, and every such statement is invisible after passing to isomorphism classes.

The contrast is with `Stacks.SheafPicardGroup.map`, which asks for a bundled
`CategoryTheory.Functor.Monoidal` structure — hence for `εIso`, `μIso`, the naturality of `μIso` in
both variables, associativity and both unitalities — and which is moreover stated for
`Stacks.SheafPicardGroup.PicardGroup`, a different carrier from the one Tag 040E
(`Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup`) produces.  Nothing below needs
a monoidal structure on either category of modules, so neither
`Stacks.SheafOfModules.Strict.monoidalCategory` nor any other choice of tensor product has to be
activated, and the two sites keep independent object and morphism universes.

## Main definitions

* `Stacks.SheafOfModules.Picard.mapInvertibleModules`: `F` restricted to the invertible modules.
* `Stacks.SheafOfModules.Picard.map`: **the induced homomorphism of Picard groups.**
* `Stacks.SheafOfModules.Picard.tensorIsoOfEquivalence` and
  `Stacks.SheafOfModules.Picard.unitIsoOfEquivalence`: the two object-level comparisons for the
  inverse of an equivalence, built from those of the equivalence.  This is where "object level
  only" pays for a second time: each is a short composite of isomorphisms of objects, while
  transporting a bundled monoidal structure to an inverse functor is a separate theorem.
* `Stacks.SheafOfModules.Picard.mapAddEquiv`: **the induced isomorphism, for an equivalence `F`.**

## Main results

* `Stacks.SheafOfModules.Picard.isInvertible_map_obj`: **`F` carries an invertible module to an
  invertible module.**  Through Tag 0B8K,
  `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`, invertibility of `L` is the
  existence of an `N` with `L ⊗ N ≅ O`, and the two input isomorphisms carry such an `N` to `F N`.
* `Stacks.SheafOfModules.Picard.map_classOf`: `map` sends the class of `L` to the class of `F L`,
  which fixes the homomorphism rather than only asserting that one exists.

## Implementation notes

The two input isomorphisms are explicit arguments rather than fields of a structure, so that a
consumer supplying them is visibly supplying *constructed data* and nothing is carried as an
unproved condition.  `F(O₁) ≅ O₂` is used only for `isInvertible_map_obj`; the additivity of `map`
needs the tensor comparison alone.

`((Stacks.SheafOfModules.Tensor.sheafTensor O).obj L).obj N` and
`(Stacks.SheafOfModules.tensorLeftFunctor O hO L).obj N` are the same sheaf of modules by `rfl`, as
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Ample/AmpleCriteria.lean`, so the statement of Tag 0B8K is consumed
at the `sheafTensor` spelling with no comparison morphism.

`map` is built with `AddMonoidHom.mk'`, so only additivity has to be proved; the Picard group is a
group, and the zero class therefore needs no separate argument.  Injectivity of `map` for an
equivalence is likewise argued on classes rather than through the kernel: two invertible modules
with the same image class have isomorphic images, hence are isomorphic by full faithfulness, hence
have the same class.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 040C](https://stacks.math.columbia.edu/tag/040C)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

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

/-- The object-level unit comparison of a functor between categories of sheaves of modules: its
value at the structure sheaf is the structure sheaf. -/
abbrev UnitIso : Type _ :=
  F.obj (SheafOfModules.unit (structureSheaf O₁ hO₁)) ≅
    SheafOfModules.unit (structureSheaf O₂ hO₂)

/-- The object-level tensor comparison of a functor between categories of sheaves of modules: its
value at a tensor product sheaf of Tag 01CA is the tensor product sheaf of the values.  No
naturality in the two arguments is asked for. -/
abbrev TensorIso : Type _ :=
  ∀ L N : SheafOfModules.{w} (structureSheaf O₁ hO₁),
    F.obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
      (L)).obj (N)))) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₂, Presheaf.isSheaf_of_isSheaf_comp _ (O₂) (forget₂ CommRingCat RingCat) (hO₂)⟩).obj
        ((F.obj L))).obj ((F.obj N))))

/-- The object-level tensor comparison of a functor between categories of sheaves of modules,
asked for **only at the arguments satisfying `P`** — that is, only on the full subcategory of
`Mod(O₁)` that `P` cuts out.  `Stacks.SheafOfModules.Picard.TensorIso` is the case `P = ⊤`. -/
abbrev TensorIsoOn (P : SheafOfModules.{w} (structureSheaf O₁ hO₁) → Prop) : Type _ :=
  ∀ L N : SheafOfModules.{w} (structureSheaf O₁ hO₁), P L → P N →
    (F.obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
      (L)).obj (N)))) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₂, Presheaf.isSheaf_of_isSheaf_comp _ (O₂) (forget₂ CommRingCat RingCat) (hO₂)⟩).obj
        ((F.obj L))).obj ((F.obj N)))))

/-! ### Invertibility transports -/

/-- **A functor whose object-level tensor comparison is available only on a full subcategory
containing the invertible modules still carries invertible sheaves of modules to invertible
sheaves of modules.**

Through Tag 0B8K, `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`, invertibility
of `L` says that some `N` has `L ⊗_{O₁} N ≅ O₁`; applying `F` and the two comparisons gives
`F L ⊗_{O₂} F N ≅ F(L ⊗_{O₁} N) ≅ F O₁ ≅ O₂`.  The comparison is needed at the single pair
`(L, N)`, and `N` is itself invertible — it is a tensor inverse of `L`, and the braiding of the
tensor product sheaf turns `L ⊗ N ≅ O₁` into `N ⊗ L ≅ O₁` — so `hP` puts both arguments inside
the subcategory.  No naturality and no coherence is used.

This is what a right adjoint supplies: restriction along a morphism of ringed sites is only
*laxly* compatible with the tensor product, and becomes compatible on the quasi-coherent modules,
where it is the inverse of an equivalence.  `P` is then quasi-coherence and `hP` is the statement
that an invertible module is quasi-coherent. -/
theorem isInvertible_map_obj_of_tensorIsoOn
    {P : SheafOfModules.{w} (structureSheaf O₁ hO₁) → Prop}
    (hP : ∀ M : SheafOfModules.{w} (structureSheaf O₁ hO₁), IsInvertible O₁ hO₁ M → P M)
    (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIsoOn O₁ hO₁ O₂ hO₂ F P)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) (hL : IsInvertible O₁ hO₁ L) :
    IsInvertible O₂ hO₂ (F.obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit L).1 hL
  have hN : IsInvertible O₁ hO₁ N :=
    (isInvertible_iff_exists_tensor_iso_unit N).2
      ⟨L, ⟨tensorSheafBraiding O₁ hO₁ N L ≪≫ e⟩⟩
  refine (isInvertible_iff_exists_tensor_iso_unit (F.obj L)).2 ⟨F.obj N, ⟨?_⟩⟩
  exact (hten L N (hP L hL) (hP N hN)).symm ≪≫ F.mapIso e ≪≫ hunit

/-- **A functor with an object-level tensor comparison and unit comparison carries invertible
sheaves of modules to invertible sheaves of modules.**

Through Tag 0B8K, `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`, invertibility
of `L` says that some `N` has `L ⊗_{O₁} N ≅ O₁`; applying `F` and the two comparisons gives
`F L ⊗_{O₂} F N ≅ F(L ⊗_{O₁} N) ≅ F O₁ ≅ O₂`.  No naturality and no coherence is used.

This is `Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn` at `P = ⊤`. -/
theorem isInvertible_map_obj (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) (hL : IsInvertible O₁ hO₁ L) :
    IsInvertible O₂ hO₂ (F.obj L) :=
  isInvertible_map_obj_of_tensorIsoOn O₁ hO₁ O₂ hO₂ F (P := fun _ => True)
    (fun _ _ => trivial) hunit (fun L N _ _ => hten L N) L hL

variable [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C₂, (J₂.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The restriction of `F` to the invertible sheaves of modules, by
`Stacks.SheafOfModules.Picard.isInvertible_map_obj`. -/
noncomputable def mapInvertibleModules (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F) :
    InvertibleModules O₁ hO₁ ⥤ InvertibleModules O₂ hO₂ :=
  ObjectProperty.lift _ (ObjectProperty.ι (IsInvertible O₁ hO₁) ⋙ F) fun L =>
    isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten L.obj L.property

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C₂, (J₂.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The underlying sheaf of modules of the image of `L` under `mapInvertibleModules` is `F L`. -/
theorem mapInvertibleModules_obj_obj (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F) (L : InvertibleModules O₁ hO₁) :
    ((mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).obj L).obj = F.obj L.obj := rfl

/-! ### The homomorphism of Picard groups -/

/-- The image under `F` of an isomorphism class of invertible modules: the action of
`Stacks.SheafOfModules.Picard.mapInvertibleModules` on skeleta. -/
noncomputable def mapSkeleton (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F) :
    Skeleton (InvertibleModules O₁ hO₁) → Skeleton (InvertibleModules O₂ hO₂) :=
  (mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).mapSkeleton.obj

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C₂, (J₂.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `mapSkeleton` sends the class of `L` to the class of its image under
`mapInvertibleModules`. -/
theorem mapSkeleton_toSkeleton (hunit : UnitIso O₁ hO₁ O₂ hO₂ F)
    (hten : TensorIso O₁ hO₁ O₂ hO₂ F) (L : InvertibleModules O₁ hO₁) :
    mapSkeleton O₁ hO₁ O₂ hO₂ F hunit hten (toSkeleton L) =
      toSkeleton ((mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).obj L) :=
  (mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).mapSkeleton_obj_toSkeleton L

/-- The identification of the Picard group of Tag 01CX with the isomorphism classes of invertible
sheaves of modules, retyped so that its target is `Stacks.SheafOfModules.Picard.PicardGroup` on the
nose.  `PicardGroupData.classEquiv` lands in the carrier field of the datum, which is the same type
but not the same expression, and the `Equiv` lemmas are then not applicable by rewriting. -/
noncomputable def skeletonEquiv : Skeleton (InvertibleModules O₁ hO₁) ≃ PicardGroup O₁ hO₁ :=
  (picardGroupData O₁ hO₁).classEquiv

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `skeletonEquiv` sends the isomorphism class of an invertible module `L` to `classOf L`. -/
theorem skeletonEquiv_toSkeleton (L : SheafOfModules.{w} (structureSheaf O₁ hO₁))
    (hL : IsInvertible O₁ hO₁ L) :
    skeletonEquiv O₁ hO₁ (toSkeleton (C := InvertibleModules O₁ hO₁) ⟨L, hL⟩) =
      classOf O₁ hO₁ L hL := rfl

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Addition of Picard classes is the tensor product sheaf, read on the skeleton. -/
theorem skeletonEquiv_add (A B : InvertibleModules O₁ hO₁)
    (hAB : IsInvertible O₁ hO₁ (((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
      (A.obj)).obj (B.obj))))) :
    skeletonEquiv O₁ hO₁ (toSkeleton A) + skeletonEquiv O₁ hO₁ (toSkeleton B) =
      skeletonEquiv O₁ hO₁
        (toSkeleton (C := InvertibleModules O₁ hO₁) ⟨((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
          (A.obj)).obj (B.obj))), hAB⟩) :=
  (picardGroupData O₁ hO₁).classEquiv_tensor A.obj B.obj A.property B.property hAB

/-- **The homomorphism of Picard groups induced by `F`.**  On the class of an invertible module `L`
it is the class of `F L`, which is `Stacks.SheafOfModules.Picard.map_classOf`.

Additivity is the one thing to prove, and it is exactly the tensor comparison read through
`Stacks.SheafOfModules.Picard.skeletonEquiv_add` on both sides: every element of a Picard group is
the class of an invertible module, so additivity has only to be checked there. -/
noncomputable def map (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIso O₁ hO₁ O₂ hO₂ F) :
    PicardGroup O₁ hO₁ →+ PicardGroup O₂ hO₂ :=
  AddMonoidHom.mk'
    (fun x => skeletonEquiv O₂ hO₂
      (mapSkeleton O₁ hO₁ O₂ hO₂ F hunit hten ((skeletonEquiv O₁ hO₁).symm x)))
    (by
      intro x y
      obtain ⟨A, hA⟩ : ∃ A : InvertibleModules O₁ hO₁,
          toSkeleton A = (skeletonEquiv O₁ hO₁).symm x :=
        ⟨_, toSkeleton_fromSkeleton_obj _⟩
      obtain ⟨B, hB⟩ : ∃ B : InvertibleModules O₁ hO₁,
          toSkeleton B = (skeletonEquiv O₁ hO₁).symm y :=
        ⟨_, toSkeleton_fromSkeleton_obj _⟩
      have hx : x = skeletonEquiv O₁ hO₁ (toSkeleton A) := by
        rw [hA, Equiv.apply_symm_apply]
      have hy : y = skeletonEquiv O₁ hO₁ (toSkeleton B) := by
        rw [hB, Equiv.apply_symm_apply]
      have hAB : IsInvertible O₁ hO₁ (((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
        (A.obj)).obj (B.obj)))) :=
        haveI := A.property
        haveI := B.property
        isInvertible_tensorSheaf O₁ hO₁ A.obj B.obj
      have hFA : IsInvertible O₂ hO₂ (F.obj A.obj) :=
        isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten A.obj A.property
      have hFB : IsInvertible O₂ hO₂ (F.obj B.obj) :=
        isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten B.obj B.property
      have hFAB : IsInvertible O₂ hO₂ (((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O₂, Presheaf.isSheaf_of_isSheaf_comp _ (O₂) (forget₂ CommRingCat RingCat) (hO₂)⟩).obj
        ((F.obj A.obj))).obj ((F.obj B.obj))))) :=
        haveI := hFA
        haveI := hFB
        isInvertible_tensorSheaf O₂ hO₂ (F.obj A.obj) (F.obj B.obj)
      have hsum : x + y = skeletonEquiv O₁ hO₁
          (toSkeleton (C := InvertibleModules O₁ hO₁) ⟨((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁) (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
            (A.obj)).obj (B.obj))), hAB⟩) := by
        rw [hx, hy]
        exact skeletonEquiv_add O₁ hO₁ A B hAB
      have key : mapSkeleton O₁ hO₁ O₂ hO₂ F hunit hten
            (toSkeleton (C := InvertibleModules O₁ hO₁)
              ⟨((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨O₁, Presheaf.isSheaf_of_isSheaf_comp _ (O₁)
                  (forget₂ CommRingCat RingCat) (hO₁)⟩).obj
                (A.obj)).obj (B.obj))), hAB⟩) =
          toSkeleton (C := InvertibleModules O₂ hO₂)
            ⟨((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O₂, Presheaf.isSheaf_of_isSheaf_comp _ (O₂) (forget₂ CommRingCat RingCat) (hO₂)⟩).obj
              ((F.obj A.obj))).obj ((F.obj B.obj)))), hFAB⟩ := by
        rw [mapSkeleton_toSkeleton]
        exact toSkeleton_eq_toSkeleton_iff.2 ⟨ObjectProperty.isoMk _ (hten A.obj B.obj)⟩
      change skeletonEquiv O₂ hO₂ (mapSkeleton O₁ hO₁ O₂ hO₂ F hunit hten
          ((skeletonEquiv O₁ hO₁).symm (x + y))) = _
      rw [hsum, Equiv.symm_apply_apply, key, hx, hy, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply, mapSkeleton_toSkeleton, mapSkeleton_toSkeleton]
      exact (skeletonEquiv_add O₂ hO₂
        ((mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).obj A)
        ((mapInvertibleModules O₁ hO₁ O₂ hO₂ F hunit hten).obj B) hFAB).symm)

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C₂, (J₂.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The induced homomorphism sends the class of `L` to the class of `F L`.**  This fixes `map`,
rather than only asserting that some homomorphism exists. -/
theorem map_classOf (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    (L : SheafOfModules.{w} (structureSheaf O₁ hO₁)) (hL : IsInvertible O₁ hO₁ L) :
    map O₁ hO₁ O₂ hO₂ F hunit hten (classOf O₁ hO₁ L hL) =
      classOf O₂ hO₂ (F.obj L) (isInvertible_map_obj O₁ hO₁ O₂ hO₂ F hunit hten L hL) := by
  show skeletonEquiv O₂ hO₂ (mapSkeleton O₁ hO₁ O₂ hO₂ F hunit hten
      ((skeletonEquiv O₁ hO₁).symm
        (skeletonEquiv O₁ hO₁ (toSkeleton (C := InvertibleModules O₁ hO₁) ⟨L, hL⟩)))) = _
  rw [Equiv.symm_apply_apply, mapSkeleton_toSkeleton]
  rfl

/-! ### The case of an equivalence -/

section Equivalence

variable [F.IsEquivalence]

/-- **The object-level tensor comparison of the inverse of an equivalence.**  For `F` an
equivalence with an object-level tensor comparison, `F.inv` has one too:

`F⁻¹(A ⊗ B) ≅ F⁻¹(F(F⁻¹A) ⊗ F(F⁻¹B)) ≅ F⁻¹(F(F⁻¹A ⊗ F⁻¹B)) ≅ F⁻¹A ⊗ F⁻¹B`,

using the counit of the equivalence twice, the comparison of `F` once and the unit once.  Three
isomorphisms of objects, with no coherence. -/
noncomputable def tensorIsoOfEquivalence (hten : TensorIso O₁ hO₁ O₂ hO₂ F) :
    TensorIso O₂ hO₂ O₁ hO₁ F.inv := fun A B =>
  F.inv.mapIso (Invertible.tensorProductIso O₂ hO₂
        (F.asEquivalence.counitIso.app A).symm (F.asEquivalence.counitIso.app B).symm ≪≫
      (hten (F.inv.obj A) (F.inv.obj B)).symm) ≪≫
    F.asEquivalence.unitIso.symm.app _

/-- **The object-level unit comparison of the inverse of an equivalence**, from the one of the
equivalence: `F⁻¹(O₂) ≅ F⁻¹(F(O₁)) ≅ O₁`. -/
noncomputable def unitIsoOfEquivalence (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) :
    UnitIso O₂ hO₂ O₁ hO₁ F.inv :=
  F.inv.mapIso hunit.symm ≪≫ F.asEquivalence.unitIso.symm.app _

/-- **An equivalence with object-level unit and tensor comparisons induces an isomorphism of
Picard groups.**

Injectivity: two invertible modules whose images have the same class have isomorphic images, hence
are isomorphic because an equivalence is fully faithful, hence have the same class.  Surjectivity:
the class of `A` is the image of the class of `F⁻¹A`, which is invertible by
`Stacks.SheafOfModules.Picard.isInvertible_map_obj` applied to `F.inv` with the two comparisons
`Stacks.SheafOfModules.Picard.unitIsoOfEquivalence` and
`Stacks.SheafOfModules.Picard.tensorIsoOfEquivalence`.  Both halves go through
`Stacks.SheafOfModules.Picard.map_classOf` and
`Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff` and use no coherence. -/
noncomputable def mapAddEquiv (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIso O₁ hO₁ O₂ hO₂ F) :
    PicardGroup O₁ hO₁ ≃+ PicardGroup O₂ hO₂ := by
  refine AddEquiv.ofBijective (map O₁ hO₁ O₂ hO₂ F hunit hten) ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨L, hL, rfl⟩ := exists_classOf_eq O₁ hO₁ x
    obtain ⟨N, hN, rfl⟩ := exists_classOf_eq O₁ hO₁ y
    rw [map_classOf, map_classOf] at hxy
    obtain ⟨e⟩ := (classOf_eq_classOf_iff O₂ hO₂ _ _ _ _).1 hxy
    exact (classOf_eq_classOf_iff O₁ hO₁ L N hL hN).2 ⟨F.preimageIso e⟩
  · intro y
    obtain ⟨A, hA, rfl⟩ := exists_classOf_eq O₂ hO₂ y
    have hinv : IsInvertible O₁ hO₁ (F.inv.obj A) :=
      isInvertible_map_obj O₂ hO₂ O₁ hO₁ F.inv
        (unitIsoOfEquivalence O₁ hO₁ O₂ hO₂ F hunit)
        (tensorIsoOfEquivalence O₁ hO₁ O₂ hO₂ F hten) A hA
    refine ⟨classOf O₁ hO₁ (F.inv.obj A) hinv, ?_⟩
    rw [map_classOf]
    exact (classOf_eq_classOf_iff O₂ hO₂ _ _ _ hA).2 ⟨F.asEquivalence.counitIso.app A⟩

omit [∀ V : C₁, (J₁.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C₂, (J₂.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The isomorphism `mapAddEquiv` agrees with the homomorphism `map` on every element. -/
theorem mapAddEquiv_apply (hunit : UnitIso O₁ hO₁ O₂ hO₂ F) (hten : TensorIso O₁ hO₁ O₂ hO₂ F)
    (x : PicardGroup O₁ hO₁) :
    mapAddEquiv O₁ hO₁ O₂ hO₂ F hunit hten x = map O₁ hO₁ O₂ hO₂ F hunit hten x := rfl

end Equivalence

end Stacks.SheafOfModules.Picard

end
