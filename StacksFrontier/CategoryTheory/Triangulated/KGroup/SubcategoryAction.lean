module

public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of a tensor structure on a second triangulated subcategory

Let `C` be a pretriangulated category with a tensor structure `T` in the sense of
`CategoryTheory.Pretriangulated.K0.TensorStructure`, and let `P` and `Q` be triangulated
subcategories of `C` with `P` closed under the tensor product and containing its unit, so that
`T` restricts to a tensor structure on `P`. If moreover `Y ⊗ Z` lies in `Q` whenever `Y` lies in
`P` and `Z` lies in `Q`, then the tensor product restricts to a bifunctor `P × Q ⟶ Q`, and that
bifunctor is an action of the restricted tensor structure in the sense of
`CategoryTheory.Pretriangulated.K0.TensorAction`. Consequently `K₀(Q)` is a module over the
Grothendieck ring `K₀(P)`.

## Main definitions

* `CategoryTheory.Pretriangulated.K0.liftBifunctorPair`: the restriction of a bifunctor
  `C ⥤ C ⥤ C` to a pair of full subcategories, the first variable in `P` and the second variable
  and the target in `Q`.
* `CategoryTheory.Pretriangulated.K0.TensorAction.restrictPair`: the resulting action of the
  restricted tensor structure on `Q`.

## Main results

* `CategoryTheory.Pretriangulated.K0.liftBifunctorPair_isTriangulatedRight` and
  `liftBifunctorPair_isTriangulatedLeft`: a bifunctor exact in one variable stays exact there
  after restriction to the pair of subcategories.
* `CategoryTheory.Pretriangulated.K0.TensorAction.exists_module`: the module structure on
  `K₀(D)` over the Grothendieck ring of `C`, together with the property that characterises it,
  namely that the scalar multiple of the class of an object of `D` by the class of an object of
  `C` is the class of the acted object.

## Implementation notes

This is `CategoryTheory.Pretriangulated.K0.TensorStructure.restrict` with the second variable
allowed to range over a *second* subcategory. Everything is carried out exactly as there, and
for the same reasons: the shift-commutation data is transported along the identification of the
restricted bifunctor with the original one after composing with the inclusion
(`CategoryTheory.Functor.CommShift.ofComp`), exactness along the same identification
(`CategoryTheory.Functor.isTriangulated_iff_comp_right`), and the associativity and unit
isomorphisms are those of the ambient tensor structure read on underlying objects, which is all
`K₀` sees.

Only one of the two inclusions appears in each of the two identifications: fixing an object of
`P` gives a functor `Q ⟶ Q`, which is compared along the inclusion of `Q`, while fixing an
object of `Q` gives a functor `P ⟶ Q`, whose composite with the inclusion of `Q` is the
inclusion of `P` followed by the ambient functor.

Every declaration binds all of its parameters explicitly rather than through a `variable`
block: which of the two triangulated-subcategory instances a given declaration needs differs
from declaration to declaration, so a shared block would give them different argument orders.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated.K0

universe v u

section PairSubcategory

/-- The restriction of a bifunctor `C ⥤ C ⥤ C` to a pair of full subcategories: the first
variable ranges over `P`, the second variable and the target over `Q`. -/
noncomputable def liftBifunctorPair {C : Type u} [Category.{v} C] (P Q : ObjectProperty C)
    (F : C ⥤ C ⥤ C) (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z)) :
    P.FullSubcategory ⥤ Q.FullSubcategory ⥤ Q.FullSubcategory where
  obj Y := Q.lift (Q.ι ⋙ F.obj Y.obj) fun Z => hF Y.obj Z.obj Y.property Z.property
  map f :=
    { app := fun Z => Q.homMk ((F.map f.hom).app Z.obj)
      naturality := fun Z W g => Q.ι.map_injective (by simp) }
  map_id Y := by ext Z; simp
  map_comp f g := by ext Z; simp

/-- Restricting a bifunctor to a pair of subcategories commutes with the inclusion of the second
one, in the right variable. -/
noncomputable def liftBifunctorPairObjCompιIso {C : Type u} [Category.{v} C]
    (P Q : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z)) (Y : P.FullSubcategory) :
    (liftBifunctorPair P Q F hF).obj Y ⋙ Q.ι ≅ Q.ι ⋙ F.obj Y.obj :=
  Q.liftCompιIso (Q.ι ⋙ F.obj Y.obj) fun Z => hF Y.obj Z.obj Y.property Z.property

/-- Restricting a bifunctor to a pair of subcategories commutes with the two inclusions, in the
left variable. -/
noncomputable def liftBifunctorPairFlipObjCompιIso {C : Type u} [Category.{v} C]
    (P Q : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z)) (Z : Q.FullSubcategory) :
    (liftBifunctorPair P Q F hF).flip.obj Z ⋙ Q.ι ≅ P.ι ⋙ F.flip.obj Z.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by simp [liftBifunctorPair]

/-- Fixing an object of `P`, the restricted bifunctor commutes with the shift. -/
@[instance_reducible]
noncomputable def liftBifunctorPairCommShiftRight {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [Q.IsTriangulated] (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z))
    (csR : ∀ Y : C, (F.obj Y).CommShift ℤ) (Y : P.FullSubcategory) :
    ((liftBifunctorPair P Q F hF).obj Y).CommShift ℤ :=
  letI := csR Y.obj
  Functor.CommShift.ofComp (liftBifunctorPairObjCompιIso P Q F hF Y) ℤ

/-- Fixing an object of `Q`, the restricted bifunctor commutes with the shift. -/
@[instance_reducible]
noncomputable def liftBifunctorPairCommShiftLeft {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated] (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z))
    (csL : ∀ Z : C, (F.flip.obj Z).CommShift ℤ) (Z : Q.FullSubcategory) :
    ((liftBifunctorPair P Q F hF).flip.obj Z).CommShift ℤ :=
  letI := csL Z.obj
  Functor.CommShift.ofComp (liftBifunctorPairFlipObjCompιIso P Q F hF Z) ℤ

/-- A functor into `Q` is exact once its composite with the inclusion of `Q` is, the shift
commutation being transported along the isomorphism. -/
private theorem isTriangulated_ofComp_ι {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (Q : ObjectProperty C) [Q.IsTriangulated] {X : Type*} [Category* X] [HasZeroObject X]
    [HasShift X ℤ] [Preadditive X] [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
    (F : X ⥤ Q.FullSubcategory) (H : X ⥤ C) (e : F ⋙ Q.ι ≅ H)
    [H.CommShift ℤ] [H.IsTriangulated] :
    letI := Functor.CommShift.ofComp e ℤ
    F.IsTriangulated := by
  let := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

/-- Fixing an object of `P`, the restricted bifunctor is exact: it becomes the restriction of an
exact functor after composing with the inclusion of `Q`, which is exact and detects exactness. -/
theorem liftBifunctorPair_isTriangulatedRight {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [Q.IsTriangulated] (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z))
    (csR : ∀ Y : C, (F.obj Y).CommShift ℤ)
    (hR : ∀ Y : C, letI := csR Y; (F.obj Y).IsTriangulated) (Y : P.FullSubcategory) :
    letI := liftBifunctorPairCommShiftRight P Q F hF csR Y
    ((liftBifunctorPair P Q F hF).obj Y).IsTriangulated := by
  let := csR Y.obj
  let := hR Y.obj
  exact isTriangulated_ofComp_ι Q _ _ (liftBifunctorPairObjCompιIso P Q F hF Y)

/-- Fixing an object of `Q`, the restricted bifunctor is exact. -/
theorem liftBifunctorPair_isTriangulatedLeft {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated] (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → Q Z → Q ((F.obj Y).obj Z))
    (csL : ∀ Z : C, (F.flip.obj Z).CommShift ℤ)
    (hL : ∀ Z : C, letI := csL Z; (F.flip.obj Z).IsTriangulated) (Z : Q.FullSubcategory) :
    letI := liftBifunctorPairCommShiftLeft P Q F hF csL Z
    ((liftBifunctorPair P Q F hF).flip.obj Z).IsTriangulated := by
  let := csL Z.obj
  let := hL Z.obj
  exact isTriangulated_ofComp_ι Q _ _ (liftBifunctorPairFlipObjCompιIso P Q F hF Z)

/-- **A tensor structure restricted to `P` acts on a triangulated subcategory `Q` which the
tensor product carries into itself against `P`.** -/
noncomputable def TensorAction.restrictPair {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated] (T : TensorStructure C)
    (hT : ∀ Y Z : C, P Y → P Z → P ((T.tensor.obj Y).obj Z)) (hOne : P T.one)
    (hA : ∀ Y Z : C, P Y → Q Z → Q ((T.tensor.obj Y).obj Z)) :
    TensorAction (T.restrict P hT hOne) Q.FullSubcategory where
  act := liftBifunctorPair P Q T.tensor hA
  commShiftRight := liftBifunctorPairCommShiftRight P Q T.tensor hA T.commShiftRight
  isTriangulatedRight := liftBifunctorPair_isTriangulatedRight P Q T.tensor hA T.commShiftRight
    T.isTriangulatedRight
  commShiftLeft := liftBifunctorPairCommShiftLeft P Q T.tensor hA T.commShiftLeft
  isTriangulatedLeft := liftBifunctorPair_isTriangulatedLeft P Q T.tensor hA T.commShiftLeft
    T.isTriangulatedLeft
  associator Y Z W := Q.isoMk (T.associator Y.obj Z.obj W.obj)
  unitor W := Q.isoMk (T.leftUnitor W.obj)

end PairSubcategory

/-! ### The module structure, with its characterising property -/

/-- **The Grothendieck group of `D` as a module over the Grothendieck ring of `C`, with the
property that characterises it.** There is a module structure on `K₀(D)` over the Grothendieck
ring of `C` for which the scalar multiple of the class of an object of `D` by the class of an
object of `C` is the class of the acted object. -/
@[sga "6 IV 2.10" "more general"]
theorem TensorAction.exists_module {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : TensorStructure C} {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (A : TensorAction T D) :
    letI := T.commRing
    ∃ m : Module (K0 C) (K0 D),
      ∀ (Y : C) (W : D), letI := m; cls Y • cls W = cls ((A.act.obj Y).obj W) :=
  let := T.commRing
  ⟨A.module, fun Y W => A.cls_smul Y W⟩

/-- **The Grothendieck group of a triangulated subcategory `Q` as a module over the Grothendieck
ring of a tensor-closed triangulated subcategory `P`, with the property that characterises it.**
The scalar multiple of the class of an object of `Q` by the class of an object of `P` is the
class of their tensor product in the ambient category.

This is `CategoryTheory.Pretriangulated.K0.TensorAction.exists_module` at the action of
`CategoryTheory.Pretriangulated.K0.TensorAction.restrictPair`, with the characterising property
stated through the tensor product of the *ambient* category rather than through the restricted
bifunctor. -/
@[sga "6 IV 2.10" "more general"]
theorem TensorAction.exists_module_restrictPair {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated] (T : TensorStructure C)
    (hT : ∀ Y Z : C, P Y → P Z → P ((T.tensor.obj Y).obj Z)) (hOne : P T.one)
    (hA : ∀ Y Z : C, P Y → Q Z → Q ((T.tensor.obj Y).obj Z)) :
    letI := (T.restrict P hT hOne).commRing
    ∃ m : Module (K0 P.FullSubcategory) (K0 Q.FullSubcategory),
      ∀ (Y Z : C) (hY : P Y) (hZ : Q Z) (h : Q ((T.tensor.obj Y).obj Z)),
        letI := m
        cls (⟨Y, hY⟩ : P.FullSubcategory) • cls (⟨Z, hZ⟩ : Q.FullSubcategory) =
          cls (⟨(T.tensor.obj Y).obj Z, h⟩ : Q.FullSubcategory) :=
  let := (T.restrict P hT hOne).commRing
  ⟨(TensorAction.restrictPair P Q T hT hOne hA).module,
    fun Y Z hY hZ _ => (TensorAction.restrictPair P Q T hT hOne hA).cls_smul ⟨Y, hY⟩ ⟨Z, hZ⟩⟩

end CategoryTheory.Pretriangulated.K0

end
