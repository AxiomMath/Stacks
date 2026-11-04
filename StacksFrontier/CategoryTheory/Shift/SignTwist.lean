module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# The sign-twisted identity of a category with a shift

Let `C` be a preadditive category with a shift by `ℤ` whose shift functors are additive. The
identity endofunctor of `C` commutes with the shift in more than one way: besides the trivial
comparison carried by `CategoryTheory.Functor.id`, there is the one given by the sign
`ε(n) = (-1)^n` of the shift. This file gives the identity endofunctor a constant of its own,
`CategoryTheory.signTwist`, so that the twisted comparison can be attached to it, and records
what the twist does.

Two things make the twist useful. First, `signTwist C` carries a triangle to the same triangle
with its third arrow negated, so it exchanges the two sign conventions for the third arrow of a
distinguished triangle: a functor exact for one convention becomes, after composing with
`signTwist`, exact for the other. Second, the sign is its own inverse, so composing with
`signTwist` on both sides of an adjunction changes nothing: the compatibility of the adjunction
with the shift transfers unchanged.

## Main definitions

* `CategoryTheory.signTwist`: the identity endofunctor of `C`, under a name of its own.
* `CategoryTheory.shiftSignAut`: the automorphism `ε(n) • 𝟙` of the shift by `n`.
* `CategoryTheory.signTwistCommShift`: the shift comparison of `signTwist C`, twisted by the
  sign of the shift.

## Main results

* `CategoryTheory.signTwist_mapTriangle_obj`: `signTwist C` negates the third arrow of a
  triangle.
* `CategoryTheory.signTwist_comp_commShiftIso_hom_app`,
  `CategoryTheory.comp_signTwist_commShiftIso_hom_app` and
  `CategoryTheory.comp_signTwist_comp_commShiftIso_hom_app`: composing with `signTwist` on
  either side, or inserting it in the middle of a composite, multiplies the shift comparison by
  the sign of the shift.
* `CategoryTheory.signTwist_comp_comp_signTwist_commShiftIso_hom_app` and
  `CategoryTheory.comp_signTwist_signTwist_comp_commShiftIso_hom_app`: two insertions of the
  twist cancel, the sign being its own inverse.
* `CategoryTheory.NatTrans.commShift_signTwist`: a natural transformation
  `L ⋙ F' ⟶ F` compatible with the shift stays compatible when read as a transformation
  `L ⋙ (signTwist _ ⋙ F') ⟶ signTwist _ ⋙ F`, the sign appearing on both sides.
* `CategoryTheory.Adjunction.signTwistComp` and `CategoryTheory.Adjunction.compSignTwist`: an
  adjunction `F ⊣ G` read as `signTwist _ ⋙ F ⊣ G ⋙ signTwist _` and as
  `F ⋙ signTwist _ ⊣ signTwist _ ⋙ G`, together with
  `CategoryTheory.Adjunction.commShift_signTwistComp` and
  `CategoryTheory.Adjunction.commShift_compSignTwist`: compatibility with the shift survives,
  the two signs cancelling.

## Implementation notes

`signTwist C` is *equal* to `CategoryTheory.Functor.id C` — the two have the same fields — and
the equality is `rfl`, so `signTwist C ⋙ F = F` and `F ⋙ signTwist C = F` are also `rfl`, and an
adjunction `F ⊣ G` is already a term of type `signTwist _ ⋙ F ⊣ G ⋙ signTwist _`. What the
constant buys is a *different* `CommShift` instance: the class can hold only once per functor,
and Mathlib's instance on `𝟭 C` is the trivial comparison. Everything below is therefore about
the comparison with the shift and nothing about the underlying functor, which never changes;
in particular a statement that does not mention the shift — full faithfulness, preservation of
colimits — transfers across the twist by definitional equality alone.

The hypothesis that the shift functors of `C` be additive is what lets the sign be pulled out of
`(shiftFunctor C n).map`, and the additivity of a functor being composed with the twist is what
lets it be pulled out of that functor's action. Both are needed for the coherence of the twisted
comparison and for the cancellation of two twists.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

universe v v' v'' u u' u''

section Aux

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The sign of a shift is its own inverse. -/
private theorem negOnePow_mul_self (n : ℤ) :
    (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

/-- Two factors of the sign of a shift, one on each side of a composite, cancel, even when the
first one sits under an additive functor. -/
private theorem map_zsmul_comp_zsmul_cancel {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {P Q : C} {R : D} (f : P ⟶ Q) (g : F.obj Q ⟶ R) (n : ℤ) :
    F.map ((n.negOnePow : ℤ) • f) ≫ ((n.negOnePow : ℤ) • g) = F.map f ≫ g := by
  rw [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
    negOnePow_mul_self, one_smul]

/-- A sign on the first factor of one side of a commuting square moves to the other side. -/
private theorem zsmul_comp_eq_comp_zsmul {P Q R S : C} {a : P ⟶ Q} {f : Q ⟶ R} {g : P ⟶ S}
    {b : S ⟶ R} (h : a ≫ f = g ≫ b) (k : ℤ) : (k • a) ≫ f = g ≫ (k • b) := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, h]

end Aux

section

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]

/-- The identity endofunctor of `C`, under a name of its own so that the sign-twisted shift
comparison can be attached to it. It is equal to `CategoryTheory.Functor.id C`, by `rfl`; only
the `CategoryTheory.Functor.CommShift` instance differs. -/
def signTwist : C ⥤ C where
  obj X := X
  map f := f

omit [Preadditive C] [HasShift C ℤ] in
/-- `CategoryTheory.signTwist` is the identity on objects. -/
@[simp] theorem signTwist_obj (X : C) : (signTwist C).obj X = X := rfl

omit [Preadditive C] [HasShift C ℤ] in
/-- `CategoryTheory.signTwist` is the identity on morphisms. -/
@[simp] theorem signTwist_map {X Y : C} (f : X ⟶ Y) : (signTwist C).map f = f := rfl

omit [Preadditive C] [HasShift C ℤ] in
/-- The sign-twisted identity is the identity endofunctor. The two carry different
`CategoryTheory.Functor.CommShift` instances, which is the whole reason the twist has a name. -/
theorem signTwist_eq_id : signTwist C = 𝟭 C := rfl

/-- The automorphism of the shift by `n` given by the sign `(-1)^n`. -/
noncomputable def shiftSignAut (n : ℤ) :
    CategoryTheory.shiftFunctor C n ≅ CategoryTheory.shiftFunctor C n where
  hom :=
    { app := fun _ => (n.negOnePow : ℤ) • 𝟙 _
      naturality := fun _ _ _ => by
        rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp] }
  inv :=
    { app := fun _ => (n.negOnePow : ℤ) • 𝟙 _
      naturality := fun _ _ _ => by
        rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp] }
  hom_inv_id := by
    ext X
    rw [NatTrans.comp_app, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id,
      smul_smul, negOnePow_mul_self, one_smul, NatTrans.id_app]
  inv_hom_id := by
    ext X
    rw [NatTrans.comp_app, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id,
      smul_smul, negOnePow_mul_self, one_smul, NatTrans.id_app]

/-- The component of `CategoryTheory.shiftSignAut` at `X` is `(-1)^n` times the identity. -/
theorem shiftSignAut_hom_app (n : ℤ) (X : C) :
    (shiftSignAut C n).hom.app X =
      (n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor C n).obj X) := rfl

/-- The component of the inverse of `CategoryTheory.shiftSignAut` at `X` is `(-1)^n` times the
identity. -/
theorem shiftSignAut_inv_app (n : ℤ) (X : C) :
    (shiftSignAut C n).inv.app X =
      (n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor C n).obj X) := rfl

/-- The comparison of `CategoryTheory.signTwist` with the shift by `n`: the sign `(-1)^n` on the
identity.

The two functors compared are definitionally equal, `signTwist C` being the identity, so this
*is* `CategoryTheory.shiftSignAut`. -/
noncomputable def signTwistCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor C n ⋙ signTwist C ≅
      signTwist C ⋙ CategoryTheory.shiftFunctor C n :=
  shiftSignAut C n

variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]

/-- `CategoryTheory.signTwist` commutes with the shift, the comparison being the sign of the
shift. -/
noncomputable instance signTwistCommShift : (signTwist C).CommShift ℤ where
  commShiftIso := signTwistCommShiftIso C
  commShiftIso_zero := by
    ext X
    dsimp only [signTwistCommShiftIso, shiftSignAut, signTwist_map, signTwist_obj,
      Functor.comp_obj]
    rw [Int.negOnePow_zero, Units.val_one, one_zsmul]
    simp
  commShiftIso_add a b := by
    ext X
    rw [Functor.CommShift.isoAdd_hom_app]
    dsimp only [signTwistCommShiftIso, shiftSignAut, signTwist_map, signTwist_obj,
      Functor.comp_obj]
    rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, Category.id_comp, Preadditive.zsmul_comp, Category.id_comp,
      Preadditive.comp_zsmul, Iso.hom_inv_id_app, smul_smul, Int.negOnePow_add, Units.val_mul,
      mul_comm]

/-- The component at `X` of the shift comparison of `CategoryTheory.signTwist` is `(-1)^n` times
the identity. -/
@[simp] theorem signTwist_commShiftIso_hom_app (n : ℤ) (X : C) :
    ((signTwist C).commShiftIso n).hom.app X =
      (n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor C n).obj X) := rfl

/-- The component at `X` of the inverse shift comparison of `CategoryTheory.signTwist` is `(-1)^n`
times the identity. -/
@[simp] theorem signTwist_commShiftIso_inv_app (n : ℤ) (X : C) :
    ((signTwist C).commShiftIso n).inv.app X =
      (n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor C n).obj X) := rfl

/-- **The sign-twisted identity negates the third arrow.** `signTwist C` carries a triangle to
the same triangle with its third arrow negated. -/
theorem signTwist_mapTriangle_obj (T : Triangle C) :
    (signTwist C).mapTriangle.obj T = Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) := by
  refine congrArg (Triangle.mk T.mor₁ T.mor₂) ?_
  show T.mor₃ ≫ (((1 : ℤ).negOnePow : ℤ) •
      𝟙 ((CategoryTheory.shiftFunctor C (1 : ℤ)).obj T.obj₁)) = -T.mor₃
  rw [Int.negOnePow_one, Units.val_neg, Units.val_one, Preadditive.comp_zsmul, Category.comp_id]
  simp

end

/-! ### The twist on the shift comparison of a composite -/

section Comp

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Precomposing with the sign-twisted identity multiplies the shift comparison by the sign of
the shift. -/
theorem signTwist_comp_commShiftIso_hom_app (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] (n : ℤ)
    (X : C) :
    ((signTwist C ⋙ F).commShiftIso n).hom.app X =
      (n.negOnePow : ℤ) • (F.commShiftIso n).hom.app X := by
  have h : ((signTwist C ⋙ F).commShiftIso n).hom.app X =
      F.map ((n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor C n).obj X)) ≫
        (F.commShiftIso n).hom.app X :=
    Functor.commShiftIso_comp_hom_app ..
  rw [h, Functor.map_zsmul, CategoryTheory.Functor.map_id, Preadditive.zsmul_comp,
    Category.id_comp]

omit [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] in
/-- Postcomposing with the sign-twisted identity multiplies the shift comparison by the sign of
the shift. -/
theorem comp_signTwist_commShiftIso_hom_app (F : C ⥤ D) [F.CommShift ℤ] (n : ℤ) (X : C) :
    ((F ⋙ signTwist D).commShiftIso n).hom.app X =
      (n.negOnePow : ℤ) • (F.commShiftIso n).hom.app X :=
  have h : (F.commShiftIso n).hom.app X ≫
        ((n.negOnePow : ℤ) • 𝟙 ((CategoryTheory.shiftFunctor D n).obj (F.obj X))) =
      (n.negOnePow : ℤ) • (F.commShiftIso n).hom.app X :=
    (Preadditive.comp_zsmul ..).trans (congrArg (fun z => (n.negOnePow : ℤ) • z)
      (Category.comp_id ((F.commShiftIso n).hom.app X)))
  (Functor.commShiftIso_comp_hom_app ..).trans h

/-- **The two sides of the twist have the same effect on triangles.** The image of a triangle
under `F ⋙ signTwist _` is the image under `signTwist _ ⋙ F`: each is the image under `F` with
the third arrow negated. -/
theorem comp_signTwist_mapTriangle_obj_eq (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]
    (T : Triangle C) :
    (F ⋙ signTwist D).mapTriangle.obj T = (signTwist C ⋙ F).mapTriangle.obj T := by
  refine congrArg (Triangle.mk (F.map T.mor₁) (F.map T.mor₂)) ?_
  rw [comp_signTwist_commShiftIso_hom_app, signTwist_comp_commShiftIso_hom_app]
  rfl

variable {H : Type u''} [Category.{v''} H] [Preadditive H] [HasShift H ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor H n).Additive]

omit [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Inserting the sign-twisted identity in the middle of a composite multiplies the shift
comparison by the sign of the shift. -/
theorem comp_signTwist_comp_commShiftIso_hom_app (L : C ⥤ H) [L.CommShift ℤ] (F : H ⥤ D)
    [F.CommShift ℤ] [F.Additive] (n : ℤ) (X : C) :
    ((L ⋙ (signTwist H ⋙ F)).commShiftIso n).hom.app X =
      (n.negOnePow : ℤ) • ((L ⋙ F).commShiftIso n).hom.app X := by
  rw [Functor.commShiftIso_comp_hom_app L (signTwist H ⋙ F),
    Functor.commShiftIso_comp_hom_app L F, signTwist_comp_commShiftIso_hom_app]
  exact Preadditive.comp_zsmul ..

omit [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Preadditive H]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor H n).Additive] in
/-- Postcomposing a composite with the sign-twisted identity multiplies the shift comparison by
the sign of the shift. Unlike
`CategoryTheory.comp_signTwist_comp_commShiftIso_hom_app`, which inserts the twist in the
middle, this needs no additivity: the twist is outermost, so its comparison is never carried
through a functor. -/
theorem comp_comp_signTwist_commShiftIso_hom_app (L : C ⥤ H) [L.CommShift ℤ] (F : H ⥤ D)
    [F.CommShift ℤ] (n : ℤ) (X : C) :
    ((L ⋙ (F ⋙ signTwist D)).commShiftIso n).hom.app X =
      (n.negOnePow : ℤ) • ((L ⋙ F).commShiftIso n).hom.app X := by
  rw [Functor.commShiftIso_comp_hom_app L (F ⋙ signTwist D),
    Functor.commShiftIso_comp_hom_app L F, comp_signTwist_commShiftIso_hom_app]
  exact Preadditive.comp_zsmul ..

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Two insertions of the sign-twisted identity cancel: the sign is its own inverse. -/
theorem signTwist_comp_comp_signTwist_commShiftIso_hom_app (F : C ⥤ D) [F.CommShift ℤ]
    [F.Additive] (G : D ⥤ C) [G.CommShift ℤ] [G.Additive] (n : ℤ) (X : C) :
    (((signTwist C ⋙ F) ⋙ (G ⋙ signTwist C)).commShiftIso n).hom.app X =
      ((F ⋙ G).commShiftIso n).hom.app X := by
  rw [Functor.commShiftIso_comp_hom_app (signTwist C ⋙ F) (G ⋙ signTwist C),
    Functor.commShiftIso_comp_hom_app F G, signTwist_comp_commShiftIso_hom_app,
    comp_signTwist_commShiftIso_hom_app]
  exact map_zsmul_comp_zsmul_cancel G ..

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Two insertions of the sign-twisted identity cancel, in the other order. -/
theorem comp_signTwist_signTwist_comp_commShiftIso_hom_app (F : C ⥤ D) [F.CommShift ℤ]
    [F.Additive] (G : D ⥤ C) [G.CommShift ℤ] [G.Additive] (n : ℤ) (Y : D) :
    (((G ⋙ signTwist C) ⋙ (signTwist C ⋙ F)).commShiftIso n).hom.app Y =
      ((G ⋙ F).commShiftIso n).hom.app Y := by
  rw [Functor.commShiftIso_comp_hom_app (G ⋙ signTwist C) (signTwist C ⋙ F),
    Functor.commShiftIso_comp_hom_app G F, comp_signTwist_commShiftIso_hom_app,
    signTwist_comp_commShiftIso_hom_app]
  exact map_zsmul_comp_zsmul_cancel F ..

end Comp

/-! ### Transfer of the compatibilities -/

namespace NatTrans

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
  {H : Type u''} [Category.{v''} H] [Preadditive H] [HasShift H ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor H n).Additive]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- **The comparison of a right extension survives the twist.** A natural transformation
`α : L ⋙ F' ⟶ F` compatible with the shift is still compatible when read as a transformation
`L ⋙ (signTwist _ ⋙ F') ⟶ signTwist _ ⋙ F`: the twist multiplies the shift comparison of each
side by the same sign, which cancels out of the compatibility equation.

The two functors being compared are definitionally equal to the untwisted ones, `signTwist`
being the identity, so `α` itself is a term of the twisted type. -/
theorem commShift_signTwist (L : C ⥤ H) [L.CommShift ℤ] (F' : H ⥤ D) [F'.CommShift ℤ]
    [F'.Additive] (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] (α : L ⋙ F' ⟶ F)
    [NatTrans.CommShift α ℤ] :
    NatTrans.CommShift
      (show L ⋙ (signTwist H ⋙ F') ⟶ signTwist C ⋙ F from α) ℤ where
  shift_comm n := by
    ext X
    have h := NatTrans.shift_app_comm α n X
    show ((L ⋙ (signTwist H ⋙ F')).commShiftIso n).hom.app X ≫ (α.app X)⟦n⟧' =
      α.app (X⟦n⟧) ≫ ((signTwist C ⋙ F).commShiftIso n).hom.app X
    rw [comp_signTwist_comp_commShiftIso_hom_app, signTwist_comp_commShiftIso_hom_app]
    exact zsmul_comp_eq_comp_zsmul h _

omit [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Preadditive H]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor H n).Additive] in
/-- **The comparison of a right extension survives the twist, taken on the target.** The twist
applied to the common target multiplies the shift comparison of each side by the same sign,
which cancels out of the compatibility equation. Unlike
`CategoryTheory.NatTrans.commShift_signTwist` this needs no additivity: the twist is outermost
on both sides. -/
theorem commShift_signTwist' (L : C ⥤ H) [L.CommShift ℤ] (F' : H ⥤ D) [F'.CommShift ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (α : L ⋙ F' ⟶ F) [NatTrans.CommShift α ℤ] :
    NatTrans.CommShift
      (show L ⋙ (F' ⋙ signTwist D) ⟶ F ⋙ signTwist D from α) ℤ where
  shift_comm n := by
    ext X
    have h := NatTrans.shift_app_comm α n X
    show ((L ⋙ (F' ⋙ signTwist D)).commShiftIso n).hom.app X ≫ (α.app X)⟦n⟧' =
      α.app (X⟦n⟧) ≫ ((F ⋙ signTwist D).commShiftIso n).hom.app X
    rw [comp_comp_signTwist_commShiftIso_hom_app, comp_signTwist_commShiftIso_hom_app]
    exact zsmul_comp_eq_comp_zsmul h _

end NatTrans

namespace Adjunction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/-- An adjunction `F ⊣ G`, read as an adjunction between the composites with the sign-twisted
identity of the source of `F`. The underlying data are unchanged, `signTwist` being the identity
on objects and on morphisms; what changes is the comparison with the shift that each side
carries. -/
def signTwistComp {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (signTwist C ⋙ F) ⊣ (G ⋙ signTwist C) where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components := adj.left_triangle_components
  right_triangle_components := adj.right_triangle_components

/-- An adjunction `F ⊣ G`, read as an adjunction between the composites with the sign-twisted
identity of the target of `F`. The mirror of `CategoryTheory.Adjunction.signTwistComp`. -/
def compSignTwist {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (F ⋙ signTwist D) ⊣ (signTwist D ⋙ G) where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components := adj.left_triangle_components
  right_triangle_components := adj.right_triangle_components

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- **An adjunction survives the twist on both sides.** If the `CommShift` structures of `F` and
`G` are compatible with `F ⊣ G`, then those of `signTwist _ ⋙ F` and `G ⋙ signTwist _` are
compatible with `CategoryTheory.Adjunction.signTwistComp`: each of the two compatibility
equations acquires the sign of the shift twice, and the sign is its own inverse. -/
instance commShift_signTwistComp {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ]
    [F.Additive] [G.CommShift ℤ] [G.Additive] [adj.CommShift ℤ] :
    adj.signTwistComp.CommShift ℤ where
  commShift_unit :=
    { shift_comm := fun n => by
        ext X
        have h := NatTrans.shift_app_comm adj.unit n X
        change ((𝟭 C).commShiftIso n).hom.app X ≫ (adj.unit.app X)⟦n⟧' =
          adj.unit.app (X⟦n⟧) ≫
            (((signTwist C ⋙ F) ⋙ (G ⋙ signTwist C)).commShiftIso n).hom.app X
        rw [signTwist_comp_comp_signTwist_commShiftIso_hom_app]
        exact h }
  commShift_counit :=
    { shift_comm := fun n => by
        ext Y
        have h := NatTrans.shift_app_comm adj.counit n Y
        change (((G ⋙ signTwist C) ⋙ (signTwist C ⋙ F)).commShiftIso n).hom.app Y ≫
            (adj.counit.app Y)⟦n⟧' =
          adj.counit.app (Y⟦n⟧) ≫ ((𝟭 D).commShiftIso n).hom.app Y
        rw [comp_signTwist_signTwist_comp_commShiftIso_hom_app]
        exact h }

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] in
/-- **An adjunction survives the twist taken on the target of the left adjoint.** The mirror of
`CategoryTheory.Adjunction.commShift_signTwistComp`: the two cancellation lemmas are the same
two, with the roles of the two functors exchanged. -/
instance commShift_compSignTwist {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.CommShift ℤ]
    [F.Additive] [G.CommShift ℤ] [G.Additive] [adj.CommShift ℤ] :
    adj.compSignTwist.CommShift ℤ where
  commShift_unit :=
    { shift_comm := fun n => by
        ext X
        have h := NatTrans.shift_app_comm adj.unit n X
        change ((𝟭 C).commShiftIso n).hom.app X ≫ (adj.unit.app X)⟦n⟧' =
          adj.unit.app (X⟦n⟧) ≫
            (((F ⋙ signTwist D) ⋙ (signTwist D ⋙ G)).commShiftIso n).hom.app X
        rw [comp_signTwist_signTwist_comp_commShiftIso_hom_app]
        exact h }
  commShift_counit :=
    { shift_comm := fun n => by
        ext Y
        have h := NatTrans.shift_app_comm adj.counit n Y
        change (((signTwist D ⋙ G) ⋙ (F ⋙ signTwist D)).commShiftIso n).hom.app Y ≫
            (adj.counit.app Y)⟦n⟧' =
          adj.counit.app (Y⟦n⟧) ≫ ((𝟭 D).commShiftIso n).hom.app Y
        rw [signTwist_comp_comp_signTwist_commShiftIso_hom_app]
        exact h }

end Adjunction

end CategoryTheory

end
