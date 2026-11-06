module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint

/-!
# Fibres at a point of a sheaf which is constant on a slice

Let `(C, J)` be a site, let `Φ` be a point of it, let `X` be an object of `C` and let `x` be an
element of the fibre of `Φ` at `X`, so that `Φ` lifts to a point `Φ.over x` of the localized site
`J.over X`. If a sheaf `F` on `C` becomes the constant sheaf on `E` after restriction to
`J.over X`, then the fibre of `F` at `Φ` is `E`, because the fibre at `Φ` agrees with the fibre at
`Φ.over x` of the restriction and the fibre of a constant sheaf is its value. A morphism of
sheaves which becomes a morphism of constant sheaves on the slice therefore induces the
corresponding morphism of values on fibres.

## Main definitions

* `Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver`: the fibre at `Φ` of a sheaf which restricts
  to the constant sheaf on `E` over `X` is `E`.

## Main results

* `Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver_naturality`: a morphism of sheaves compatible
  with the two trivializations induces the given morphism of values on fibres.
* `Stacks.ConstantSheaf.exists_equiv_sheafFiber_map_of_constantOver`: the same statement for
  sheaves of sets, read as an equivalence of fibres with the values and an elementwise identity.

## Implementation notes

The identification of the fibre of the constant sheaf is taken from
`CategoryTheory.Sites.constantSheafFiberIso`, which is stated for the fibre of the *presheaf*
`sheafify (J.over X) ((Functor.const (Over X)ᵒᵖ).obj E)`. That presheaf is the underlying presheaf
of `(constantSheaf (J.over X) D).obj E` by definition, and the fibre functor on sheaves is the
fibre functor on presheaves precomposed with `sheafToPresheaf`, so the two readings are
definitionally equal and the isomorphisms below are composed directly.

The hypotheses on `J.over Y` are stated for every object `Y` of `C` rather than for `X` alone,
since `X` is implicit in the statements and would otherwise not be available to instance
resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v₂ u₂ v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]

section Sheaf

variable {D : Type u₂} {FD : D → D → Type*} {CD : D → Type v₂}
  [∀ A B, FunLike (FD A B) (CD A) (CD B)] [Category.{v₂} D] [ConcreteCategory.{v₂} D FD]
  [∀ Y : C, HasWeakSheafify (J.over Y) D] [∀ Y : C, (J.over Y).WEqualsLocallyBijective D]
  [UnivLE.{w, v₂}] [PreservesFilteredColimitsOfSize.{v₂, v₂} (forget D)]
  [(forget D).ReflectsIsomorphisms] [HasColimitsOfSize.{w, w} D]

include FD CD

/-- If a sheaf `F` restricts over `X` to the constant sheaf on `E`, then its fibre at a point `Φ`
of the site lifting to `x : Φ.fiber.obj X` is `E`. -/
noncomputable def sheafFiberIsoOfConstantOver
    (Φ : J.Point.{w}) {X : C} (x : Φ.fiber.obj X) (F : Sheaf J D) (E : D)
    (e : (constantSheaf (J.over X) D).obj E ≅ (J.overPullback D X).obj F) :
    Φ.sheafFiber.obj F ≅ E :=
  ((Φ.sheafFiberOverIso x D).app F).symm ≪≫ ((Φ.over x).sheafFiber.mapIso e).symm ≪≫
    Sites.constantSheafFiberIso (Φ.over x) E

/-- A morphism of sheaves which restricts over `X` to the constant sheaf morphism on `g` induces
`g` itself on the fibres at `Φ`, read through
`Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver`. -/
theorem sheafFiberIsoOfConstantOver_naturality
    (Φ : J.Point.{w}) {X : C} (x : Φ.fiber.obj X) {F G : Sheaf J D} (φ : F ⟶ G)
    {E E' : D} (g : E ⟶ E')
    (eF : (constantSheaf (J.over X) D).obj E ≅ (J.overPullback D X).obj F)
    (eG : (constantSheaf (J.over X) D).obj E' ≅ (J.overPullback D X).obj G)
    (hsq : (constantSheaf (J.over X) D).map g ≫ eG.hom =
      eF.hom ≫ (J.overPullback D X).map φ) :
    Φ.sheafFiber.map φ ≫ (sheafFiberIsoOfConstantOver Φ x G E' eG).hom =
      (sheafFiberIsoOfConstantOver Φ x F E eF).hom ≫ g := by
  have hinv : (J.overPullback D X).map φ ≫ eG.inv =
      eF.inv ≫ (constantSheaf (J.over X) D).map g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hnat : Φ.sheafFiber.map φ ≫ ((Φ.sheafFiberOverIso x D).app G).inv =
      ((Φ.sheafFiberOverIso x D).app F).inv ≫
        (Φ.over x).sheafFiber.map ((J.overPullback D X).map φ) :=
    (Φ.sheafFiberOverIso x D).inv.naturality φ
  have hmap : (Φ.over x).sheafFiber.map ((J.overPullback D X).map φ) ≫
      (Φ.over x).sheafFiber.map eG.inv =
      (Φ.over x).sheafFiber.map eF.inv ≫
        (Φ.over x).sheafFiber.map ((constantSheaf (J.over X) D).map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hinv]
  have key : (Φ.over x).sheafFiber.map ((J.overPullback D X).map φ) ≫
      (Φ.over x).sheafFiber.map eG.inv ≫ (Sites.constantSheafFiberIso (Φ.over x) E').hom =
      ((Φ.over x).sheafFiber.map eF.inv ≫
        (Sites.constantSheafFiberIso (Φ.over x) E).hom) ≫ g :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) hmap).trans <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (Sites.constantSheafFiberIso_naturality (Φ.over x) g).symm).trans
          (Category.assoc _ _ _).symm
  change Φ.sheafFiber.map φ ≫ ((Φ.sheafFiberOverIso x D).app G).inv ≫
      (Φ.over x).sheafFiber.map eG.inv ≫ (Sites.constantSheafFiberIso (Φ.over x) E').hom =
    (((Φ.sheafFiberOverIso x D).app F).inv ≫ (Φ.over x).sheafFiber.map eF.inv ≫
      (Sites.constantSheafFiberIso (Φ.over x) E).hom) ≫ g
  rw [reassoc_of% hnat, key, Category.assoc]

end Sheaf

section Types

variable [∀ Y : C, HasWeakSheafify (J.over Y) (Type w')]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective (Type w')] [UnivLE.{w, w'}]

/-- For sheaves of sets: a morphism of sheaves which restricts over `X` to the constant sheaf
morphism on `g` identifies the fibres at `Φ` with the values, compatibly with `g`. -/
theorem exists_equiv_sheafFiber_map_of_constantOver
    (Φ : J.Point.{w}) {X : C} (x : Φ.fiber.obj X) {F G : Sheaf J (Type w')} (φ : F ⟶ G)
    {E E' : Type w'} (g : E ⟶ E')
    (eF : (constantSheaf (J.over X) (Type w')).obj E ≅ (J.overPullback (Type w') X).obj F)
    (eG : (constantSheaf (J.over X) (Type w')).obj E' ≅ (J.overPullback (Type w') X).obj G)
    (hsq : (constantSheaf (J.over X) (Type w')).map g ≫ eG.hom =
      eF.hom ≫ (J.overPullback (Type w') X).map φ) :
    ∃ (uF : Φ.sheafFiber.obj F ≃ E) (uG : Φ.sheafFiber.obj G ≃ E'),
      ∀ a, uG (Φ.sheafFiber.map φ a) = g (uF a) := by
  refine ⟨(sheafFiberIsoOfConstantOver Φ x F E eF).toEquiv,
    (sheafFiberIsoOfConstantOver Φ x G E' eG).toEquiv, fun a => ?_⟩
  have h := ConcreteCategory.congr_hom
    (sheafFiberIsoOfConstantOver_naturality Φ x φ g eF eG hsq) a
  simpa using h

end Types

end Stacks.ConstantSheaf

end
