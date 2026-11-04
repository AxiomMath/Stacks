module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ParametrizedAdjointUniqueness
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Twisting an internal hom by an invertible object

Let `C` be a closed monoidal category and let `ℒ` be an invertible object of `C`, with a chosen
two-sided inverse `ℒ'` as in `CategoryTheory.MonoidalCategory.HasInverse`. Tensoring by `ℒ`
commutes with the internal hom in its target variable,

`RHom(K, Z ⊗ ℒ) ≅ RHom(K, Z) ⊗ ℒ`,

and tensoring the *source* by `ℒ` instead twists by the inverse,

`RHom(K ⊗ ℒ, Z) ⊗ ℒ ≅ RHom(K, Z)`.

Both are pure adjunction bookkeeping. The first holds because the two sides are right adjoint to
the two bracketings of `K ⊗ (- ⊗ ℒ')`, which the associator identifies; the second adds the
currying isomorphism `RHom(A ⊗ B, -) ≅ RHom(B, RHom(A, -))` and the computation of
`RHom(ℒ, -)` as `ℒ' ⊗ -`, which holds because `ℒ ⊗ -` is an equivalence with quasi-inverse
`ℒ' ⊗ -`. Only the second needs a braiding, to move the twist past the hom object.

These are the closed-monoidal inputs to the independence of `f_new^!` of the choice of a
dualizing complex on the base, [Stacks, Tag 0BV3], which is formalized in
`StacksFrontier/AlgebraicGeometry/Duality/GlueingDualizingComplexes.lean`.

## Main definitions

All in the namespace `Stacks.Duality`.

* `tensorRightAdjunctionOfInverse`, `tensorLeftAdjunctionOfInverse` — the adjunctions
  `- ⊗ ℒ' ⊣ - ⊗ ℒ` and `ℒ ⊗ - ⊣ ℒ' ⊗ -` carried by a two-sided inverse.
* `hasInverseObjOfTensorIso` — an inverse for the image of an invertible object under a functor
  compatible with the tensor product and the unit; the data counterpart of
  `Stacks.Duality.isInvertible_obj_of_tensorIso`.

## Main results

* `Stacks.Duality.ihomIsoTensorLeftInv` — `RHom(ℒ, -) ≅ ℒ' ⊗ -` for invertible `ℒ`.
* `Stacks.Duality.ihomTensorLeftComp` — the currying isomorphism
  `RHom(A ⊗ B, -) ≅ RHom(B, RHom(A, -))`.
* `Stacks.Duality.ihomTensorRightComm` — `RHom(K, -) ⊗ ℒ ≅ RHom(K, - ⊗ ℒ)`, the twist moving
  through the target variable of the internal hom.
* `Stacks.Duality.ihomTensorRightCancel` — `RHom(A ⊗ ℒ, Z) ⊗ ℒ ≅ RHom(A, Z)`, the twist in the
  source variable cancelling against a twist outside.
* `Stacks.Duality.ihomTensorRightCommBifunctor` and
  `Stacks.Duality.ihomTensorLeftCompBifunctor` — the first two of those, upgraded to
  isomorphisms of **bifunctors** `Cᵒᵖ ⥤ C ⥤ C`, hence natural in the contravariant variable of
  the internal hom as well.
* `Stacks.Duality.tensorLeftInvTensorRightIso` — `ℒ' ⊗ (-) ⊗ ℒ ≅ 𝟭 C`.

## Implementation notes

Each isomorphism is produced from two adjunctions with isomorphic left adjoints, rather than
written down as a curried evaluation map. That keeps the constructions short. The object-level
forms use `CategoryTheory.Adjunction.rightAdjointUniq`, which gives naturality in the variable
the internal hom is covariant in; the bifunctor forms use
`Stacks.Duality.parametrizedRightAdjointUniq`, which gives it in both variables at once, the
contravariant one being the parameter of the adjunction with a parameter
`CategoryTheory.MonoidalClosed.internalHomAdjunction₂`.

The inverse of an invertible object is carried as *data*, a
`CategoryTheory.MonoidalCategory.HasInverse`, not as the proposition
`CategoryTheory.MonoidalCategory.IsInvertible`. All four results below produce an isomorphism
whose shape mentions the chosen inverse, so there is nothing to choose from an existence
statement at the point of use.

## References

* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0BV3](https://stacks.math.columbia.edu/tag/0BV3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe v v' u u'

namespace Stacks.Duality

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Invertible objects and the two tensoring adjunctions -/

/-- The adjunction `- ⊗ ℒ' ⊣ - ⊗ ℒ` attached to a two-sided inverse `ℒ'` of `ℒ`: tensoring on
the right by `ℒ` is an equivalence with quasi-inverse tensoring on the right by `ℒ'`. -/
def tensorRightAdjunctionOfInverse {L : C} (h : HasInverse L) :
    tensorRight h.inv ⊣ tensorRight L :=
  h.tensorRightEquivalence.symm.toAdjunction

/-- The adjunction `ℒ ⊗ - ⊣ ℒ' ⊗ -` attached to a two-sided inverse `ℒ'` of `ℒ`. -/
def tensorLeftAdjunctionOfInverse {L : C} (h : HasInverse L) :
    tensorLeft L ⊣ tensorLeft h.inv :=
  h.tensorLeftEquivalence.toAdjunction

/-- An inverse for the image of an invertible object under a functor carrying tensor products to
tensor products and the unit to the unit. This is the data form of
`Stacks.Duality.isInvertible_obj_of_tensorIso`: only the values of the comparison on objects are
used, so no coherence or naturality is required. -/
def hasInverseObjOfTensorIso {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D)
    (t : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B) (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    {L : C} (h : HasInverse L) : HasInverse (F.obj L) where
  inv := F.obj h.inv
  isoLeft := (t L h.inv).symm ≪≫ F.mapIso h.isoLeft ≪≫ e
  isoRight := (t h.inv L).symm ≪≫ F.mapIso h.isoRight ≪≫ e

/-! ### The internal hom out of an invertible object -/

variable [MonoidalClosed C]

/-- For an invertible object `ℒ` with two-sided inverse `ℒ'`, the internal hom out of `ℒ` is
tensoring by `ℒ'`: both are right adjoint to `ℒ ⊗ -`. -/
def ihomIsoTensorLeftInv {L : C} (h : HasInverse L) : ihom L ≅ tensorLeft h.inv :=
  (ihom.adjunction L).rightAdjointUniq (tensorLeftAdjunctionOfInverse h)

/-- The currying isomorphism `RHom(A ⊗ B, -) ≅ RHom(B, RHom(A, -))`: both sides are right
adjoint to `B ⊗ (A ⊗ -)`, which the associator identifies with `(A ⊗ B) ⊗ -`. -/
def ihomTensorLeftComp (A B : C) : ihom (A ⊗ B) ≅ ihom A ⋙ ihom B :=
  ((ihom.adjunction (A ⊗ B)).ofNatIsoLeft (tensorLeftTensor A B)).rightAdjointUniq
    ((ihom.adjunction B).comp (ihom.adjunction A))

/-! ### Moving an invertible twist through the target of an internal hom -/

/-- **`RHom(K, -) ⊗ ℒ ≅ RHom(K, - ⊗ ℒ)` for an invertible `ℒ`.** Both sides are right adjoint to
the two bracketings of `K ⊗ (- ⊗ ℒ')`, which the associator identifies. -/
def ihomTensorRightComm (K : C) {L : C} (h : HasInverse L) :
    ihom K ⋙ tensorRight L ≅ tensorRight L ⋙ ihom K :=
  ((tensorRightAdjunctionOfInverse h).comp (ihom.adjunction K)).rightAdjointUniq
    (((ihom.adjunction K).comp (tensorRightAdjunctionOfInverse h)).ofNatIsoLeft
      (NatIso.ofComponents (fun T => (α_ K T h.inv).symm) (by intros; simp)).symm)

/-- `RHom(K, Z ⊗ ℒ) ≅ RHom(K, Z) ⊗ ℒ`, the object form of
`Stacks.Duality.ihomTensorRightComm`. -/
def ihomObjTensorRightIso (K : C) {L : C} (h : HasInverse L) (Z : C) :
    (ihom K).obj (Z ⊗ L) ≅ (ihom K).obj Z ⊗ L :=
  ((ihomTensorRightComm K h).app Z).symm

/-! ### Cancelling an invertible twist in the source of an internal hom -/

variable [BraidedCategory C]

/-- **`RHom(A ⊗ ℒ, Z) ⊗ ℒ ≅ RHom(A, Z)` for an invertible `ℒ`.** Currying turns the twist in the
source into `RHom(ℒ, -)`, which is tensoring by the inverse `ℒ'`; the braiding moves that factor
outside, where it cancels against the twist by `ℒ`. -/
def ihomTensorRightCancel {L : C} (h : HasInverse L) (A Z : C) :
    ((ihom (A ⊗ L)).obj Z) ⊗ L ≅ (ihom A).obj Z :=
  whiskerRightIso
      ((ihomTensorLeftComp A L).app Z ≪≫ (ihomIsoTensorLeftInv h).app ((ihom A).obj Z) ≪≫
        β_ h.inv ((ihom A).obj Z)) L ≪≫
    α_ ((ihom A).obj Z) h.inv L ≪≫ whiskerLeftIso ((ihom A).obj Z) h.isoRight ≪≫
      ρ_ ((ihom A).obj Z)

/-! ### The twisting isomorphisms as isomorphisms of bifunctors -/

/-- The associator, read as an isomorphism of the two bifunctors `K ↦ T ↦ (K ⊗ T) ⊗ M` and
`K ↦ T ↦ K ⊗ (T ⊗ M)`. -/
def curriedTensorRightAssoc (M : C) :
    curriedTensor C ⋙ (Functor.whiskeringRight C C C).obj (tensorRight M) ≅
      curriedTensor C ⋙ (Functor.whiskeringLeft C C C).obj (tensorRight M) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun T => α_ K T M) (by intros; simp))
    (by intros; ext T; simp)

/-- The associator, read as an isomorphism of the two bifunctors `K ↦ T ↦ (K ⊗ M) ⊗ T` and
`K ↦ T ↦ K ⊗ (M ⊗ T)`. -/
def curriedTensorLeftAssoc (M : C) :
    tensorRight M ⋙ curriedTensor C ≅
      curriedTensor C ⋙ (Functor.whiskeringLeft C C C).obj (tensorLeft M) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents (fun T => α_ K M T) (by intros; simp))
    (by intros; ext T; simp)

/-- **`RHom(−, −) ⊗ ℒ ≅ RHom(−, − ⊗ ℒ)` as an isomorphism of bifunctors**, for an invertible
`ℒ`: `Stacks.Duality.ihomTensorRightComm` made natural in the contravariant variable too. Both
bifunctors are parametrized right adjoints of the two bracketings of `K ⊗ (T ⊗ ℒ')`, which the
associator identifies. -/
def ihomTensorRightCommBifunctor {L : C} (h : HasInverse L) :
    (internalHom (C := C) ⋙ (Functor.whiskeringLeft C C C).obj (tensorRight L)) ≅
      (internalHom (C := C) ⋙ (Functor.whiskeringRight C C C).obj (tensorRight L)) :=
  parametrizedRightAdjointUniq
    (parametrizedCompTarget internalHomAdjunction₂ (tensorRightAdjunctionOfInverse h))
    (parametrizedOfNatIsoLeft
      (parametrizedCompSource internalHomAdjunction₂ (tensorRightAdjunctionOfInverse h))
      (curriedTensorRightAssoc h.inv).symm)

/-- **The currying isomorphism `RHom(− ⊗ ℒ, −) ≅ RHom(ℒ, RHom(−, −))` as an isomorphism of
bifunctors**: `Stacks.Duality.ihomTensorLeftComp` made natural in the contravariant variable
too. -/
def ihomTensorLeftCompBifunctor (L : C) :
    ((tensorRight L).op ⋙ internalHom (C := C)) ≅
      (internalHom (C := C) ⋙ (Functor.whiskeringRight C C C).obj (ihom L)) :=
  parametrizedRightAdjointUniq
    (parametrizedCompParam internalHomAdjunction₂ (tensorRight L))
    (parametrizedOfNatIsoLeft
      (parametrizedCompSource internalHomAdjunction₂ (ihom.adjunction L))
      (curriedTensorLeftAssoc L).symm)

/-- `ℒ' ⊗ (−) ⊗ ℒ ≅ 𝟭 C` for an invertible `ℒ` with two-sided inverse `ℒ'`: the braiding moves
the inverse factor across, where it cancels. -/
def tensorLeftInvTensorRightIso {L : C} (h : HasInverse L) :
    tensorLeft h.inv ⋙ tensorRight L ≅ 𝟭 C :=
  Functor.isoWhiskerRight (NatIso.ofComponents (fun D => β_ h.inv D) (by intros; simp))
      (tensorRight L) ≪≫
    (tensorRightTensor h.inv L).symm ≪≫ (tensoringRight C).mapIso h.isoRight ≪≫
      rightUnitorNatIso C

end Stacks.Duality

end
