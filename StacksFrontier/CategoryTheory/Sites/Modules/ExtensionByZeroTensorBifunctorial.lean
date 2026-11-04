module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and the tensor product: naturality in the module on the big site

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe `c` while its
morphisms, the sections of `O` and the sections of its modules all lie in one universe `u`, let
`C` be essentially `u`-small, and let `U` be an object of `C`.
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso` is Stacks 0E8I at that
universe shape,

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`,

as an isomorphism of functors in the sheaf `G` of `O|_U`-modules.  A comparison of the two
*bicomplexes* attached to a pair of complexes needs it to be natural in the sheaf `F` of
`O`-modules as well, one differential of the bicomplex being covered by each of the two
naturalities.  This file provides the three ingredients of that second naturality and the
decomposition of the comparison which they are to be pasted along.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.tensorSheafificationIso_naturality`: **Stacks
  05NB is natural in the fixed tensor factor** — the exchange of sheafification with the tensor
  product commutes with a morphism of that factor.  It is assembled from the same naturality for
  `Stacks.SheafOfModules.TensorColimits.tensorSheafificationIsoGeneral` and for the passage from
  tensoring on the left to tensoring on the right.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.presheafExtensionTensorIso_naturality`: **the
  presheaf-level step of `restrictionTensorIso` is natural in the presheaf of `O`-modules.**
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso_hom_app`: the four steps
  `restrictionTensorIso` is assembled from, at an object.
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso_naturality_right`:
  **Stacks 0E8I is natural in the sheaf of `O`-modules as well**, so that together with
  `restrictionTensorIso` the comparison is bifunctorial.  It is the paste of the four naturality
  squares of those four steps.

## Implementation notes

The four steps of `restrictionTensorIso` are the comparison of the two models of sheaf-level
extension by zero, the exchange of sheafification with the tensor product, the presheaf-level
comparison of the extension formula, and the exchange of sheafification with extension by zero.
Of these the first and the last are naturality squares of a natural transformation, and the
middle two are `tensorSheafificationIso_naturality` and
`presheafExtensionTensorIso_naturality` below.

Two spellings of the ring presheaf of the slice site occur in those steps and are *not*
reducibly equal: `Stacks.SheafOfModules.ringPresheaf ((Over.forget U).op ⋙ O)`, in which the
extension formula and its comparison are stated, and
`((Stacks.SheafOfModules.Tensor.ringSheaf O).over U).obj`, in which
`restrictionTensorIso` is stated.  Identifying them at the level of *functors*, as
`restrictionTensorIso` does, is affordable.  At the level of presheaves of *modules*, which is
what composing the four squares into one asks for, the identification is affordable only if
`Stacks.Sites.OverModules.FormulaExtension.extensionFunctor` is opaque while it is made: that
functor unfolds to the objectwise direct sum of the extension formula, and the unifier
otherwise descends into the direct sum rather than comparing the two arguments it is applied
to.  The identification is therefore made exactly once, in
`presheafExtensionTensorIso_naturality_whiskered`, under a `local irreducible` attribute on
`extensionFunctor`; every other statement below is written in one spelling throughout, with
`sliceSheafifyModules`, `sliceTensorObj` and `slicePresheafTensorMap` naming the pieces of the
spelling `restrictionTensorIso` is given in.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

open Stacks.Sites.OverModules
open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules (ringPresheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)
open Stacks.SheafOfModules.TensorColimits (tensorCommIso tensorSheafificationIsoGeneral)

/-! ### Pasting commuting squares -/

section Pasting

variable {D : Type*} [Category D]

/-- Three commuting squares pasted along their common edges.  The re-association is stated in
an arbitrary category, so that no spelling of a presheaf of rings occurs in it and the
composites below can be re-associated without a defeq check.

`Stacks.Cohomology.MixedDerivedTensor.eq_of_three_squares` is the same device at a different
association of the two composites; it is not reused here because its module sits far above this
one in the import graph. -/
lemma comp_eq_comp_of_three_squares {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : D}
    {a₀ : X₀ ⟶ Y₀} {s₁ : Y₀ ⟶ Y₁} {s₂ : Y₁ ⟶ Y₂} {s₃ : Y₂ ⟶ Y₃}
    {t₁ : X₀ ⟶ X₁} {t₂ : X₁ ⟶ X₂} {t₃ : X₂ ⟶ X₃} {a₃ : X₃ ⟶ Y₃}
    {b₁ : X₁ ⟶ Y₁} {b₂ : X₂ ⟶ Y₂}
    (h₁ : a₀ ≫ s₁ = t₁ ≫ b₁) (h₂ : b₁ ≫ s₂ = t₂ ≫ b₂) (h₃ : b₂ ≫ s₃ = t₃ ≫ a₃) :
    a₀ ≫ (s₁ ≫ s₂ ≫ s₃) = (t₁ ≫ t₂ ≫ t₃) ≫ a₃ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- Four commuting squares pasted along their common edges, the two composites associated as
`restrictionTensorIso_hom_app` presents them. -/
lemma comp_eq_comp_of_four_squares {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : D}
    {a₀ : X₀ ⟶ Y₀} {s₁ : Y₀ ⟶ Y₁} {s₂ : Y₁ ⟶ Y₂} {s₃ : Y₂ ⟶ Y₃} {s₄ : Y₃ ⟶ Y₄}
    {t₁ : X₀ ⟶ X₁} {t₂ : X₁ ⟶ X₂} {t₃ : X₂ ⟶ X₃} {t₄ : X₃ ⟶ X₄} {a₄ : X₄ ⟶ Y₄}
    {b₁ : X₁ ⟶ Y₁} {b₂ : X₂ ⟶ Y₂} {b₃ : X₃ ⟶ Y₃}
    (h₁ : a₀ ≫ s₁ = t₁ ≫ b₁) (h₂ : b₁ ≫ s₂ = t₂ ≫ b₂) (h₃ : b₂ ≫ s₃ = t₃ ≫ b₃)
    (h₄ : b₃ ≫ s₄ = t₄ ≫ a₄) :
    a₀ ≫ (s₁ ≫ s₂ ≫ s₃ ≫ s₄) = (t₁ ≫ t₂ ≫ t₃ ≫ t₄) ≫ a₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- A commuting square transported along a functor.  The square is supplied as a hypothesis
rather than left to the unifier: both of its composites carry four endpoints, and solving them
from the conclusion instead would make each of the two `Functor.map_comp` steps a
higher-order unification problem. -/
lemma map_comp_eq_map_comp_of_eq {A : Type*} [Category A] (Φ : A ⥤ D)
    {W X Y Z : A} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : Φ.map f ≫ Φ.map g = Φ.map h ≫ Φ.map k :=
  ((Φ.map_comp f g).symm.trans (congrArg Φ.map e)).trans (Φ.map_comp h k)

/-- A commuting square whose two horizontal edges are components of natural isomorphisms, read
in the inverse direction.  It is stated for the components rather than for isomorphisms of
objects, so that no `CategoryTheory.Iso` has to be formed out of a natural isomorphism at an
object. -/
lemma natIso_inv_square {A₁ : Type*} [Category A₁] {A₂ : Type*} [Category A₂]
    {F G : A₁ ⥤ D} (e : F ≅ G) (X₁ : A₁) {F' G' : A₂ ⥤ D} (e' : F' ≅ G') (X₂ : A₂)
    {a : G.obj X₁ ⟶ G'.obj X₂} {b : F.obj X₁ ⟶ F'.obj X₂}
    (h : b ≫ e'.hom.app X₂ = e.hom.app X₁ ≫ a) :
    a ≫ e'.inv.app X₂ = e.inv.app X₁ ≫ b := by
  refine (cancel_epi (e.hom.app X₁)).mp ?_
  rw [← Category.assoc, ← h, Category.assoc, e'.hom_inv_id_app, Category.comp_id,
    ← Category.assoc, e.hom_inv_id_app, Category.id_comp]

end Pasting

/-! ### The objectwise tensor product is a bifunctor -/

section Presheaf

variable {C : Type c} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})

/-- **Tensoring in the first and in the second variable commute**, for the objectwise tensor
product of presheaves of modules: both composites send a pure tensor `x ⊗ y` to `φ x ⊗ α y`. -/
lemma tensorRightMap_naturality
    {F F' : PresheafOfModules.{u} (ringPresheaf O)} (α : F ⟶ F')
    {A B : PresheafOfModules.{u} (ringPresheaf O)} (φ : A ⟶ B) :
    (tensorRight (O := O) F).map φ ≫ FormulaExtension.tensorRightMap O B α =
      FormulaExtension.tensorRightMap O A α ≫ (tensorRight (O := O) F').map φ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

/-- The component of `Stacks.Sites.OverModules.FormulaExtension.extensionTensorIso`, which is
`extensionTensorObjIso` by construction.  Naming it lets the comparison be decomposed by
rewriting, inside the spelling `ringPresheaf O` in which the extension formula is given. -/
lemma extensionTensorIso_hom_app (U : C)
    (F : PresheafOfModules.{u} (ringPresheaf O))
    (G : PresheafOfModules.{u} (OverModules.overRingPresheaf (ringPresheaf O) U)) :
    (FormulaExtension.extensionTensorIso O U F).hom.app G =
      (FormulaExtension.extensionTensorObjIso O U F G).hom :=
  rfl

end Presheaf

/-! ### Stacks 05NB is natural in the fixed tensor factor -/

section SheafLevel

variable {C : Type c} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- **Tensoring in the first and in the second variable commute**, with the first variable read
through the native `PresheafOfModules.tensorBifunctor`. -/
lemma presheafTensorLeft_naturality
    {F F' : PresheafOfModules.{u} (ringSheaf O).obj} (α : F ⟶ F')
    {A B : PresheafOfModules.{u} (ringSheaf O).obj} (φ : A ⟶ B) :
    ((PresheafOfModules.tensorBifunctor.{u, c, u, u, u} O.obj).obj F).map φ ≫
        (tensorRight (O := O.obj) B).map α =
      (tensorRight (O := O.obj) A).map α ≫
        ((PresheafOfModules.tensorBifunctor.{u, c, u, u, u} O.obj).obj F').map φ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- **The braiding of the objectwise tensor product is natural in the fixed factor.** -/
lemma tensorCommIso_naturality
    {F F' : PresheafOfModules.{u} (ringSheaf O).obj} (α : F ⟶ F')
    (A : PresheafOfModules.{u} (ringSheaf O).obj) :
    (tensorRight (O := O.obj) A).map α ≫ (tensorCommIso J O F').hom.app A =
      (tensorCommIso J O F).hom.app A ≫ FormulaExtension.tensorRightMap O.obj A α := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 05NB is natural in the fixed tensor factor**: the identification of tensoring
followed by sheafification with sheafification followed by tensoring commutes with a morphism
of the fixed factor.  Both sides are sheafifications of presheaf-level morphisms, and the
presheaf-level square is the bifunctoriality of the objectwise tensor product at the unit of
sheafification. -/
lemma tensorSheafificationIsoGeneral_naturality
    {F F' : SheafOfModules.{u} (ringSheaf O)} (α : F ⟶ F')
    (P : PresheafOfModules.{u} (ringSheaf O).obj) :
    (sheafifyModules J O).map ((tensorRight (O := O.obj) P).map α.val) ≫
        (tensorSheafificationIsoGeneral J O F').hom.app P =
      (tensorSheafificationIsoGeneral J O F).hom.app P ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor O).map α).app ((sheafifyModules J O).obj P) :=
  map_comp_eq_map_comp_of_eq (sheafifyModules J O)
    (presheafTensorLeft_naturality J O α.val
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (ringSheaf O).obj)).unit.app P)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The passage from tensoring on the left to tensoring on the right is natural in the fixed
factor.** -/
lemma tensorLeftIsoSheafTensorRight_naturality
    {F F' : SheafOfModules.{u} (ringSheaf O)} (α : F ⟶ F')
    (A : SheafOfModules.{u} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).map α).app A ≫
        (tensorLeftIsoSheafTensorRight J O F').hom.app A =
      (tensorLeftIsoSheafTensorRight J O F).hom.app A ≫
        (sheafifyModules J O).map (FormulaExtension.tensorRightMap O.obj A.val α.val) :=
  map_comp_eq_map_comp_of_eq (sheafifyModules J O) (tensorCommIso_naturality J O α.val A.val)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The passage from tensoring on the left to tensoring on the right is natural in the fixed
factor**, read in the inverse direction. -/
lemma tensorLeftIsoSheafTensorRight_inv_naturality
    {F F' : SheafOfModules.{u} (ringSheaf O)} (α : F ⟶ F')
    (A : SheafOfModules.{u} (ringSheaf O)) :
    (sheafifyModules J O).map (FormulaExtension.tensorRightMap O.obj A.val α.val) ≫
        (tensorLeftIsoSheafTensorRight J O F').inv.app A =
      (tensorLeftIsoSheafTensorRight J O F).inv.app A ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor O).map α).app A :=
  natIso_inv_square (tensorLeftIsoSheafTensorRight J O F) A
    (tensorLeftIsoSheafTensorRight J O F') A
    (tensorLeftIsoSheafTensorRight_naturality J O α A)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 05NB is natural in the fixed tensor factor**, read in the inverse direction. -/
lemma tensorSheafificationIsoGeneral_inv_naturality
    {F F' : SheafOfModules.{u} (ringSheaf O)} (α : F ⟶ F')
    (P : PresheafOfModules.{u} (ringSheaf O).obj) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).map α).app ((sheafifyModules J O).obj P) ≫
        (tensorSheafificationIsoGeneral J O F').inv.app P =
      (tensorSheafificationIsoGeneral J O F).inv.app P ≫
        (sheafifyModules J O).map ((tensorRight (O := O.obj) P).map α.val) :=
  natIso_inv_square (tensorSheafificationIsoGeneral J O F) P
    (tensorSheafificationIsoGeneral J O F') P
    (tensorSheafificationIsoGeneral_naturality J O α P)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The three steps `tensorSheafificationIso` is assembled from, at an object. -/
lemma tensorSheafificationIso_hom_app
    (F : SheafOfModules.{u} (ringSheaf O))
    (Y : PresheafOfModules.{u} (ringSheaf O).obj) :
    (tensorSheafificationIso J O F).hom.app Y =
      (tensorLeftIsoSheafTensorRight J O F).inv.app ((sheafifyModules J O).obj Y) ≫
        (tensorSheafificationIsoGeneral J O F).inv.app Y ≫
        (sheafifyModules J O).map ((tensorCommIso J O F.val).hom.app Y) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The exchange of sheafification with the tensor product is natural in the fixed tensor
factor.** -/
lemma tensorSheafificationIso_naturality
    {F F' : SheafOfModules.{u} (ringSheaf O)} (α : F ⟶ F')
    (Y : PresheafOfModules.{u} (ringSheaf O).obj) :
    (sheafifyModules J O).map (FormulaExtension.tensorRightMap O.obj
          ((sheafifyModules J O).obj Y).val α.val) ≫
        (tensorSheafificationIso J O F').hom.app Y =
      (tensorSheafificationIso J O F).hom.app Y ≫
        (sheafifyModules J O).map (FormulaExtension.tensorRightMap O.obj Y α.val) := by
  rw [tensorSheafificationIso_hom_app, tensorSheafificationIso_hom_app]
  exact comp_eq_comp_of_three_squares
    (tensorLeftIsoSheafTensorRight_inv_naturality J O α ((sheafifyModules J O).obj Y))
    (tensorSheafificationIsoGeneral_inv_naturality J O α Y)
    (map_comp_eq_map_comp_of_eq (sheafifyModules J O) (tensorCommIso_naturality J O α.val Y))

end SheafLevel

/-! ### Extension by zero and tensoring over a ringed site with large objects -/

section Sheaf

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}] in
/-- **The presheaf-level step of `restrictionTensorIso` is natural in the presheaf of modules
on `C`.**  That step is the comparison `extensionTensorObjIso` of the extension formula, read
through the identification `presheafExtendByZeroIsoExtension` of Mathlib's model of extension by
zero with the direct-sum model; so its three sub-squares are the bifunctoriality of the
objectwise tensor product, the naturality
`Stacks.Sites.OverModules.FormulaExtension.extensionTensorObjIso_naturality_right`, and the
naturality of that identification.

The composite is written out rather than named as an isomorphism of functors.  Naming it forces
the ascribed target `tensorRight (F.over U).val` to be checked against
`tensorRight ((PresheafOfModules.pushforward₀ (Over.forget U) _).obj F.val)` once for the name
and again at each unfolding, and that check does not fit in the default elaboration budget. -/
lemma presheafExtensionTensorIso_naturality
    {F F' : SheafOfModules.{u} (ringSheaf X.O)} (α : F ⟶ F')
    (H : PresheafOfModules.{u} ((ringSheaf X.O).over U).obj) :
    FormulaExtension.tensorRightMap X.O.obj
          ((presheafExtendByZero X.J (ringSheaf X.O) U).obj H) α.val ≫
        ((tensorRight (O := X.O.obj) F'.val).map
            ((presheafExtendByZeroIsoExtension X.J
              (ringSheaf X.O) U).hom.app H) ≫
          (FormulaExtension.extensionTensorObjIso X.O.obj U F'.val H).hom ≫
          (presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U).inv.app
            (FormulaExtension.tensorPullback X.O.obj U F'.val H)) =
      ((tensorRight (O := X.O.obj) F.val).map
          ((presheafExtendByZeroIsoExtension X.J
            (ringSheaf X.O) U).hom.app H) ≫
        (FormulaExtension.extensionTensorObjIso X.O.obj U F.val H).hom ≫
        (presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U).inv.app
          (FormulaExtension.tensorPullback X.O.obj U F.val H)) ≫
        (presheafExtendByZero X.J (ringSheaf X.O) U).map
          (FormulaExtension.tensorPullbackMap X.O.obj U α.val H) :=
  comp_eq_comp_of_three_squares
    (tensorRightMap_naturality X.O.obj α.val
      ((presheafExtendByZeroIsoExtension X.J
        (ringSheaf X.O) U).hom.app H)).symm
    (FormulaExtension.extensionTensorObjIso_naturality_right X.O.obj U α.val H)
    ((presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U).inv.naturality
      (FormulaExtension.tensorPullbackMap X.O.obj U α.val H))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The four steps `restrictionTensorIso` is assembled from, at an object: the comparison of the
two models of sheaf-level extension by zero, the exchange of sheafification with the tensor
product, the presheaf-level comparison, and the exchange of sheafification with extension by
zero.

The two adjunctions are supplied in the statement rather than left to instance search: the
module universe of `SheafOfModules.pullbackIso` is free, so a search for its `IsRightAdjoint`
hypothesis runs with that universe still a metavariable and never reaches the library's
instances. -/
lemma restrictionTensorIso_hom_app
    (F : SheafOfModules.{u} (ringSheaf X.O))
    (G : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    (restrictionTensorIso X U F).hom.app G =
      haveI := sheafRestrictionIsRightAdjoint X.J (ringSheaf X.O) U
      haveI := presheafRestrictionSheafIsRightAdjoint X.J (ringSheaf X.O) U
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map
          ((SheafOfModules.pullbackIso
            (𝟙 ((ringSheaf X.O).over U))).hom.app G) ≫
        (tensorSheafificationIso X.J X.O F).hom.app
          ((presheafExtendByZero X.J (ringSheaf X.O) U).obj
            ((SheafOfModules.forget.{u} ((ringSheaf X.O).over U)).obj G)) ≫
        (sheafifyModules X.J X.O).map
          ((Functor.isoWhiskerRight
              (presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U)
              (tensorRight (O := X.O.obj) F.val) ≪≫
            FormulaExtension.extensionTensorIso X.O.obj U F.val ≪≫
            Functor.isoWhiskerLeft
              (tensorRight (O := (X.O.over U).obj) (F.over U).val)
              (presheafExtendByZeroIsoExtension X.J
                (ringSheaf X.O) U).symm).hom.app
            ((SheafOfModules.forget.{u} ((ringSheaf X.O).over U)).obj G)) ≫
        (SheafOfModules.sheafificationCompPullback
          (𝟙 ((ringSheaf X.O).over U))).symm.hom.app
          ((tensorRight (O := (X.O.over U).obj) (F.over U).val).obj
            ((SheafOfModules.forget.{u} ((ringSheaf X.O).over U)).obj G)) :=
  rfl

/-! ### Stacks 0E8I is natural in the module on the big site -/

/-- Sheafification of presheaves of modules on the slice, with the ring sheaf pinned to the
spelling `(ringSheaf X.O).over U` in which the fourth step of
`restrictionTensorIso` is given.  The other spelling,
`ringSheaf (X.O.over U)`, is the one `sheafifyModules (X.J.over U) (X.O.over U)`
carries; the two differ by the order of restriction to the slice and of forgetting
commutativity, and pinning one of them here is what keeps that identification out of the
proofs below. -/
noncomputable abbrev sliceSheafifyModules :
    PresheafOfModules.{u} ((ringSheaf X.O).over U).obj ⥤
      SheafOfModules.{u} ((ringSheaf X.O).over U) :=
  PresheafOfModules.sheafification.{u} (R := (ringSheaf X.O).over U)
    (𝟙 ((ringSheaf X.O).over U).obj)

/-- The objectwise tensor product on the slice, `G ⊗_{O|_U} A|_U`, with its presheaf of rings
pinned to `((ringSheaf X.O).over U).obj`.  It is
`Stacks.Sites.OverModules.FormulaExtension.tensorPullback`, whose result type is spelled
`(Over.forget U).op ⋙ (X.O.obj ⋙ forget₂ _ _)` rather than
`((Over.forget U).op ⋙ X.O.obj) ⋙ forget₂ _ _`; being an abbreviation, this name is transparent
to the matching of the statements below while fixing which of the two spellings they carry. -/
noncomputable abbrev sliceTensorObj
    (A : SheafOfModules.{u} (ringSheaf X.O))
    (H : PresheafOfModules.{u} ((ringSheaf X.O).over U).obj) :
    PresheafOfModules.{u} ((ringSheaf X.O).over U).obj :=
  (tensorRight (O := (X.O.over U).obj) (A.over U).val).obj H

/-- The morphism `G ⊗ F|_U ⟶ G ⊗ F'|_U` of presheaves of modules on the slice induced by
`α : F ⟶ F'`, with its source and target spelled through `sliceTensorObj`. -/
noncomputable def slicePresheafTensorMap
    {F F' : SheafOfModules.{u} (ringSheaf X.O)} (α : F ⟶ F')
    (H : PresheafOfModules.{u} ((ringSheaf X.O).over U).obj) :
    sliceTensorObj X U F H ⟶ sliceTensorObj X U F' H :=
  FormulaExtension.tensorPullbackMap X.O.obj U α.val H

/-- The morphism of sheaves of modules on the slice induced by `α : F ⟶ F'`: the sheafification
of `slicePresheafTensorMap`.  This is the morphism the target of `restrictionTensorIso` is
natural along. -/
noncomputable def sliceTensorRightMap
    {F F' : SheafOfModules.{u} (ringSheaf X.O)} (α : F ⟶ F')
    (G : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    (sliceSheafifyModules X U).obj (sliceTensorObj X U F G.val) ⟶
      (sliceSheafifyModules X U).obj (sliceTensorObj X U F' G.val) :=
  (sliceSheafifyModules X U).map (slicePresheafTensorMap X U α G.val)

section Bridge

/- `FormulaExtension.extensionFunctor` is made opaque for the one statement below.

That statement is `presheafExtensionTensorIso_naturality` with its middle factor written as the
composite of natural isomorphisms out of which `restrictionTensorIso` is built, and the two
presentations differ in the argument of the last factor: the extension formula's comparison
`extensionTensorObjIso` has
`(extensionFunctor _ U).obj (FormulaExtension.tensorPullback X.O.obj U F.val H)` for its target,
while the whiskering has `(extensionFunctor _ U).obj (sliceTensorObj X U F H)`.  The two
arguments are reducibly equal — but `extensionFunctor` unfolds to the objectwise direct sum of
the extension formula, so without this attribute the unifier descends into that direct sum
instead of comparing the arguments, and the check does not fit in the elaboration budget.  With
`extensionFunctor` opaque the comparison is first-order and the identification is paid once,
here. -/
attribute [local irreducible] FormulaExtension.extensionFunctor

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}] in
/-- **The presheaf-level step of `restrictionTensorIso` is natural in the presheaf of modules
on `C`**, with that step written as the composite of natural isomorphisms
`restrictionTensorIso` is assembled from rather than as the three morphisms
`presheafExtensionTensorIso_naturality` gives it by.  This is the one identification between
the two spellings of the slice tensor product; everything downstream is in the spelling
`restrictionTensorIso` is given in. -/
lemma presheafExtensionTensorIso_naturality_whiskered
    {F F' : SheafOfModules.{u} (ringSheaf X.O)} (α : F ⟶ F')
    (H : PresheafOfModules.{u} ((ringSheaf X.O).over U).obj) :
    FormulaExtension.tensorRightMap X.O.obj
          ((presheafExtendByZero X.J (ringSheaf X.O) U).obj H) α.val ≫
        (Functor.isoWhiskerRight
              (presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U)
              (tensorRight (O := X.O.obj) F'.val) ≪≫
            FormulaExtension.extensionTensorIso X.O.obj U F'.val ≪≫
            Functor.isoWhiskerLeft
              (tensorRight (O := (X.O.over U).obj) (F'.over U).val)
              (presheafExtendByZeroIsoExtension X.J
                (ringSheaf X.O) U).symm).hom.app H =
      (Functor.isoWhiskerRight
            (presheafExtendByZeroIsoExtension X.J (ringSheaf X.O) U)
            (tensorRight (O := X.O.obj) F.val) ≪≫
          FormulaExtension.extensionTensorIso X.O.obj U F.val ≪≫
          Functor.isoWhiskerLeft
            (tensorRight (O := (X.O.over U).obj) (F.over U).val)
            (presheafExtendByZeroIsoExtension X.J
              (ringSheaf X.O) U).symm).hom.app H ≫
        (presheafExtendByZero X.J (ringSheaf X.O) U).map
          (slicePresheafTensorMap X U α H) :=
  presheafExtensionTensorIso_naturality X U α H

end Bridge

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 0E8I is natural in the sheaf of modules on `X` as well.**  Together with
`restrictionTensorIso`, which is its naturality in the sheaf of modules on the slice, this makes
the comparison

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`

bifunctorial, which is what a comparison of the two *bicomplexes* attached to a pair of
complexes is assembled from: one differential of the bicomplex is covered by each of the two
naturalities.

The proof is the paste of the four naturality squares of the four steps
`restrictionTensorIso_hom_app` decomposes the comparison into: the naturality of the comparison
of the two models of sheaf-level extension by zero, `tensorSheafificationIso_naturality`,
`presheafExtensionTensorIso_naturality_whiskered`, and the naturality of the exchange of
sheafification with extension by zero.

The two adjunctions are supplied before the rewriting rather than left to instance search, for
the reason recorded at `restrictionTensorIso_hom_app`. -/
lemma restrictionTensorIso_naturality_right
    {F F' : SheafOfModules.{u} (ringSheaf X.O)} (α : F ⟶ F')
    (G : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.map α).app ((extendByZero X U).obj G) ≫
        (restrictionTensorIso X U F').hom.app G =
      (restrictionTensorIso X U F).hom.app G ≫
        (extendByZero X U).map (sliceTensorRightMap X U α G) := by
  have := sheafRestrictionIsRightAdjoint X.J (ringSheaf X.O) U
  have := presheafRestrictionSheafIsRightAdjoint X.J (ringSheaf X.O) U
  rw [restrictionTensorIso_hom_app, restrictionTensorIso_hom_app]
  exact comp_eq_comp_of_four_squares
    ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.map α).naturality _).symm)
    (tensorSheafificationIso_naturality X.J X.O α _)
    (map_comp_eq_map_comp_of_eq (sheafifyModules X.J X.O)
      (presheafExtensionTensorIso_naturality_whiskered X U α G.val))
    ((SheafOfModules.sheafificationCompPullback
      (𝟙 ((ringSheaf X.O).over U))).symm.hom.naturality
      (slicePresheafTensorMap X U α G.val))

end Sheaf

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

end
