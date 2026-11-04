module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Shift compatibility of the tensorator of a lax monoidal functor

Let `R : E ⥤ A` be a lax monoidal functor between monoidal categories carrying a shift by an
additive monoid `T`, with `R` compatible with that shift.  The tensorator

`μ R X Y : R X ⊗ R Y ⟶ R (X ⊗ Y)`

is a morphism of bifunctors, and reading it in one variable at a time produces two natural
transformations of ordinary functors `E ⥤ A`,

`μNatTransFst R Y : R ⋙ - ⊗ R Y ⟶ - ⊗ Y ⋙ R`  and
`μNatTransSnd R X : R ⋙ R X ⊗ - ⟶ X ⊗ - ⋙ R`,

each of which may or may not commute with the shift.  That it does is an extra condition on `R`,
not a consequence of lax monoidality: it is the analogue for a monoidal functor of
`CategoryTheory.Adjunction.CommShift` for an adjunction, and like it it is recorded here as a
`Prop`-valued class, `CategoryTheory.Functor.LaxMonoidal.CommShift`.

For the two one-variable readings to be natural transformations between functors that commute
with the shift, the tensor product of each of `E` and `A` must itself commute with the shift in
each variable; and for a *morphism* in one variable to be whiskered into such a transformation,
the action of the tensor product on morphisms must be compatible with those commutations.  That
second condition is `CategoryTheory.MonoidalCategory.TensorCommShift`.

## Main definitions

* `CategoryTheory.Functor.LaxMonoidal.μNatTransFst` and
  `CategoryTheory.Functor.LaxMonoidal.μNatTransSnd`: the tensorator of a lax monoidal functor read
  as a natural transformation in one of its two variables.
* `CategoryTheory.MonoidalCategory.TensorCommShift`: **the tensor product of a monoidal category
  with a shift acts on morphisms compatibly with the shift.**
* `CategoryTheory.Functor.LaxMonoidal.CommShift`: **the tensorator of a lax monoidal functor
  commutes with the shift in each variable.**

## Main results

* `CategoryTheory.Functor.LaxMonoidal.CommShift.id`: the identity functor satisfies the condition.
* `CategoryTheory.Functor.LaxMonoidal.commTensorRight_hom` and
  `CategoryTheory.Functor.LaxMonoidal.commTensorLeft_hom`: for a *strong* monoidal functor the two
  readings are the isomorphisms `CategoryTheory.Functor.Monoidal.commTensorRight` and
  `commTensorLeft` of Mathlib.

## Implementation notes

`Mathlib/CategoryTheory/Shift/` contains no monoidal file and
`Mathlib/CategoryTheory/Monoidal/` no shift file, so none of this exists upstream; the two
classes here are the minimal statements that let a transformation built from a tensorator be
whiskered, composed and reassociated inside `CategoryTheory.NatTrans.CommShift`, which is what
a dévissage of such a transformation along a generating family consumes.

The two fields of `CategoryTheory.MonoidalCategory.TensorCommShift` are exactly the fields
`commShift_map` and `commShift_flip_map` of Mathlib's `CategoryTheory.Functor.CommShift₂` for the
bifunctor `CategoryTheory.MonoidalCategory.curriedTensor`, and the two instance arguments
`(tensorLeft X).CommShift T`, `(tensorRight Y).CommShift T` are its fields `commShiftObj` and
`commShiftFlipObj`.  They are restated rather than packaged as `CommShift₂` because
`CommShift₂` additionally carries the sign coherence `comm` between the two variables, which
nothing here uses, and because it is indexed by a `CategoryTheory.CommShift₂Setup` and so needs
`T` commutative and the twisting data chosen; a transformation in one variable needs neither.
The shift structures on the `tensorLeft` and `tensorRight` functors are instance arguments and
hence fixed data: `CategoryTheory.NatTrans.CommShift` is a statement *about* a chosen pair of
`CategoryTheory.Functor.CommShift` structures, so a consumer must seat the same ones.

The condition in `CategoryTheory.Functor.LaxMonoidal.CommShift` is stated in both variables even
though a dévissage in one variable uses only one of them: the two are symmetric, a braiding
exchanges them, and a statement carrying only the one a particular application happens to need
would have to be restated for the other.

The two one-variable readings are not new transformations: Mathlib has them already for a
*strong* monoidal functor, as the isomorphisms `CategoryTheory.Functor.Monoidal.commTensorRight`
and `commTensorLeft`, and `commTensorRight_hom`, `commTensorLeft_hom` identify the two spellings
there.  What is new is only that they are available for a lax monoidal functor, where the
tensorator has no inverse to put in an `Iso`; a comparison morphism whose invertibility is the
assertion being formalized cannot be written with Mathlib's spelling.

Nothing here assumes `R` strong monoidal, nothing assumes the categories additive or
triangulated, and no coherence between the two variables is asserted.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂

/-! ### The shift compatibility of the tensor product of a monoidal category -/

namespace MonoidalCategory

section

variable (A : Type u₁) [Category.{v₁} A] [MonoidalCategory A]
  (T : Type*) [AddMonoid T] [HasShift A T]
  [∀ X : A, (tensorLeft X).CommShift T] [∀ Y : A, (tensorRight Y).CommShift T]

/-- **The tensor product of a monoidal category with a shift acts on morphisms compatibly with
the shift.**  The two fields say that for a morphism `f : X ⟶ X'` the transformation
`- ↦ f ▷ -` and for a morphism `g : Y ⟶ Y'` the transformation `- ↦ - ◁ g` commute with the
shift, for the commutations of `X ⊗ -` and `- ⊗ Y` with the shift given as instance arguments.

These are the fields `commShift_map` and `commShift_flip_map` of Mathlib's
`CategoryTheory.Functor.CommShift₂` for the bifunctor
`CategoryTheory.MonoidalCategory.curriedTensor`; the sign coherence between the two variables,
which that class also carries, is not asserted and is not needed to whisker a transformation in
a single variable. -/
class TensorCommShift : Prop where
  /-- Whiskering a morphism on the right of the tensor product commutes with the shift. -/
  commShift_curriedTensor_map {X X' : A} (f : X ⟶ X') :
    NatTrans.CommShift ((curriedTensor A).map f) T
  /-- Whiskering a morphism on the left of the tensor product commutes with the shift. -/
  commShift_curriedTensor_flip_map {Y Y' : A} (g : Y ⟶ Y') :
    NatTrans.CommShift ((curriedTensor A).flip.map g) T

attribute [instance] TensorCommShift.commShift_curriedTensor_map
  TensorCommShift.commShift_curriedTensor_flip_map

end

/-- **Mathlib's two-variable shift coherence of the tensor product implies
`CategoryTheory.MonoidalCategory.TensorCommShift`.**  The two fields of this class are the fields
`commShift_map` and `commShift_flip_map` of `CategoryTheory.Functor.CommShift₂`; the commutations
of `X ⊗ -` and `- ⊗ Y` with the shift that it is relative to are the fields `commShiftObj` and
`commShiftFlipObj` of the same structure, and are the ones instance search finds here.

This is how the class is discharged in practice: a derived tensor product carries
`CategoryTheory.Functor.CommShift₂Int` by descent from the sign coherence on complexes, and
`CategoryTheory.Functor.CommShift₂.ofIso` moves it along a comparison of bifunctors. -/
theorem TensorCommShift.of_commShift₂ (A : Type u₁) [Category.{v₁} A] [MonoidalCategory A]
    {T : Type*} [AddCommMonoid T] [HasShift A T]
    (h : CommShift₂Setup A T) [(curriedTensor A).CommShift₂ h] :
    TensorCommShift A T where
  commShift_curriedTensor_map _ := inferInstance
  commShift_curriedTensor_flip_map _ := inferInstance

end MonoidalCategory

/-! ### The tensorator in one variable -/

namespace Functor.LaxMonoidal

open Functor.LaxMonoidal

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A]
  (R : E ⥤ A) [R.LaxMonoidal]

/-- **The tensorator of a lax monoidal functor, read as a natural transformation in its first
variable.**  At `X` its value is `μ R X Y : R X ⊗ R Y ⟶ R (X ⊗ Y)`, and naturality in `X` is
`CategoryTheory.Functor.LaxMonoidal.μ_natural_left`. -/
def μNatTransFst (Y : E) : R ⋙ tensorRight (R.obj Y) ⟶ tensorRight Y ⋙ R where
  app X := μ R X Y
  naturality _ _ f := μ_natural_left R f Y

/-- The component of `μNatTransFst R Y` at `X` is `μ R X Y`. -/
@[simp]
lemma μNatTransFst_app (Y : E) (X : E) : (μNatTransFst R Y).app X = μ R X Y := rfl

/-- **The tensorator of a lax monoidal functor, read as a natural transformation in its second
variable.**  At `Y` its value is `μ R X Y : R X ⊗ R Y ⟶ R (X ⊗ Y)`, and naturality in `Y` is
`CategoryTheory.Functor.LaxMonoidal.μ_natural_right`. -/
def μNatTransSnd (X : E) : R ⋙ tensorLeft (R.obj X) ⟶ tensorLeft X ⋙ R where
  app Y := μ R X Y
  naturality _ _ f := μ_natural_right R X f

/-- The component of `μNatTransSnd R X` at `Y` is `μ R X Y`. -/
@[simp]
lemma μNatTransSnd_app (X : E) (Y : E) : (μNatTransSnd R X).app Y = μ R X Y := rfl

section Strong

variable (F : E ⥤ A) [F.Monoidal]

/-- **For a strong monoidal functor the first one-variable reading of the tensorator is the
isomorphism `CategoryTheory.Functor.Monoidal.commTensorRight` of Mathlib.**  That isomorphism is
the same transformation; it exists only for a strong monoidal functor, since its inverse is built
from `CategoryTheory.Functor.LaxMonoidal.μIso`, whereas the two readings above are defined for a
lax one and are what a comparison morphism which is not known to be invertible is built from. -/
lemma commTensorRight_hom (Y : E) :
    (Functor.Monoidal.commTensorRight F Y).hom = μNatTransFst F Y :=
  rfl

/-- **For a strong monoidal functor the second one-variable reading of the tensorator is the
isomorphism `CategoryTheory.Functor.Monoidal.commTensorLeft` of Mathlib.**  The companion of
`CategoryTheory.Functor.LaxMonoidal.commTensorRight_hom`. -/
lemma commTensorLeft_hom (X : E) :
    (Functor.Monoidal.commTensorLeft F X).hom = μNatTransSnd F X :=
  rfl

end Strong

variable (T : Type*) [AddMonoid T] [HasShift E T] [HasShift A T] [R.CommShift T]
  [∀ X : E, (tensorLeft X).CommShift T] [∀ Y : E, (tensorRight Y).CommShift T]
  [∀ X : A, (tensorLeft X).CommShift T] [∀ Y : A, (tensorRight Y).CommShift T]

/-- **The tensorator of a lax monoidal functor commutes with the shift.**  A condition on a lax
monoidal functor between monoidal categories with a shift, asserted separately in each variable:
the two one-variable readings `CategoryTheory.Functor.LaxMonoidal.μNatTransFst` and
`CategoryTheory.Functor.LaxMonoidal.μNatTransSnd` of the tensorator are compatible with the
shift.

This does **not** follow from lax monoidality together with
`CategoryTheory.Functor.CommShift`: it relates three independently chosen structures -- the
commutation of `R` with the shift, the commutations of the two tensor products with the shift,
and the tensorator -- and is the monoidal analogue of `CategoryTheory.Adjunction.CommShift`,
which is likewise a condition and not a theorem. -/
class CommShift : Prop where
  /-- The tensorator, read in the first variable, commutes with the shift. -/
  commShift_μNatTransFst (Y : E) : NatTrans.CommShift (μNatTransFst R Y) T
  /-- The tensorator, read in the second variable, commutes with the shift. -/
  commShift_μNatTransSnd (X : E) : NatTrans.CommShift (μNatTransSnd R X) T

attribute [instance] CommShift.commShift_μNatTransFst CommShift.commShift_μNatTransSnd

/-- **The identity functor satisfies the condition.**  Its tensorator is the identity, and the
two commutations with the shift that the condition compares are then the same one. -/
instance CommShift.id : CommShift (𝟭 E) T where
  commShift_μNatTransFst _ := NatTrans.CommShift.of_core fun _ ↦ ⟨by
    ext
    simp [μNatTransFst, Functor.commShiftIso_comp_hom_app]⟩
  commShift_μNatTransSnd _ := NatTrans.CommShift.of_core fun _ ↦ ⟨by
    ext
    simp [μNatTransSnd, Functor.commShiftIso_comp_hom_app]⟩

end Functor.LaxMonoidal

end CategoryTheory

end
