module

public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Grothendieck ring of a tensor triangulated category

Let `C` be a pretriangulated category carrying a tensor product `⊗ : C × C → C` which is exact
in each variable. The bilinear map on `K`-groups of [Stacks, Tag 0FCT] then makes `K₀(C)` a
ring, with `[K] · [L] = [K ⊗ L]`; it is commutative with unit `[𝟙_C]` as soon as the tensor
product is associative, commutative and unital. Likewise, an action `C × D → D` on a second
pretriangulated category `D`, exact in each variable, makes `K₀(D)` a module over `K₀(C)`.

## Main definitions

* `CategoryTheory.Pretriangulated.K0.NonUnitalTensorStructure`: the data a tensor product has
  to carry for `K₀` to become a non-unital commutative ring — everything below except a unit.
* `CategoryTheory.Pretriangulated.K0.NonUnitalTensorStructure.nonUnitalCommRing`: the
  resulting non-unital commutative ring structure on `K₀(C)`.
* `CategoryTheory.Pretriangulated.K0.TensorStructure`: the data a tensor product has to carry
  for `K₀` to become a commutative ring.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.commRing`: the resulting commutative ring
  structure on `K₀(C)`.
* `CategoryTheory.Pretriangulated.K0.TensorAction`: the data an action of such a tensor product
  on a second pretriangulated category has to carry for `K₀` of the latter to become a module.
* `CategoryTheory.Pretriangulated.K0.TensorAction.module`: the resulting module structure.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.ofMonoidal`: the tensor structure of a
  braided monoidal pretriangulated category whose tensor product is exact in each variable.
* `CategoryTheory.Pretriangulated.K0.liftBifunctor`: the restriction of a bifunctor to a full
  subcategory closed under it.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.restrict`: the tensor structure induced on
  a triangulated subcategory closed under the tensor product and containing the unit object.
* `CategoryTheory.Pretriangulated.K0.NonUnitalTensorStructure.restrict`: the non-unital
  tensor structure induced on a triangulated subcategory closed under the tensor product.

## Main results

* `CategoryTheory.Pretriangulated.K0.cls_eq_of_iso`: isomorphic objects have the same class.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.cls_mul`,
  `TensorStructure.one_eq_cls_one`: the multiplication is the tensor product and the unit is
  the class of the unit object.
* `CategoryTheory.Pretriangulated.K0.TensorStructure.exists_commRing`: the ring structure
  together with its three characterising properties, asserted at once.
* `CategoryTheory.Pretriangulated.K0.TensorAction.cls_smul`: scalar multiplication is the
  action.
* `CategoryTheory.Pretriangulated.K0.cls_eq_add_of_distinguished_of_prop`: classes in `K₀` of a
  triangulated subcategory add along a distinguished triangle of the ambient category whose
  three vertices lie in the subcategory.
* `CategoryTheory.Pretriangulated.K0.liftBifunctor_isTriangulatedRight`,
  `liftBifunctor_isTriangulatedLeft`: a bifunctor exact in one variable stays exact there after
  restriction to a triangulated subcategory.

## Implementation notes

Only *object-level* associativity, commutativity and unit isomorphisms are asked for: no
naturality and no coherence diagram. That is all `K₀` can see, since a class depends on its
object only up to isomorphism (`cls_eq_of_iso`), so requiring a monoidal structure instead
would be requiring strictly more than the conclusion needs. A monoidal category supplies the
data of a `TensorStructure` by taking its associator, braiding and left unitor componentwise,
and a tensor-closed triangulated subcategory of a monoidal pretriangulated category supplies
one by restriction.

The three ring axioms are proved by iterated `hom_ext` rather than by induction on formal sums:
associativity, for instance, is an equality of two homomorphisms `K₀(C) →+ K₀(C)` for each
fixed pair of arguments, and each of those arguments is in turn eliminated by `hom_ext`, so
that only the case of three classes of objects is argued, where the associativity isomorphism
applies. `evalHom` is what lets the outer two eliminations be phrased as equalities of
homomorphisms: it turns an element into a homomorphism out of the group of endomorphisms.

The additive group of the ring is the one `K₀(C)` already has, as `commRing_toAddCommGroup`
records; this is why the construction overrides the additive group of
`CommRing.ofMinimalAxioms` rather than accepting the one that lemma manufactures.

Exactness of the restricted bifunctor is not reproved: the restriction composed with the
inclusion of the subcategory is the inclusion composed with the original functor, and
`CategoryTheory.Functor.isTriangulated_iff_comp_right` transports exactness across that
identification, the inclusion of a triangulated subcategory being exact and conservative
enough to detect it. The shift-commutation data is transported the same way, by
`CategoryTheory.Functor.CommShift.ofComp`.

## Relation to the Grothendieck ring of a scheme

For a scheme `X`, [Stacks, Tag 0FDK] asserts that `K₀(X) = K₀(D_perf(O_X))` is a commutative
ring under the derived tensor product, and that `K'₀(X)` is a module over it. Those two
conclusions are `TensorStructure.commRing` and `TensorAction.module` here, with the input the
source actually appeals to — Tag 0FCT together with the isomorphisms `K ⊗ L ≅ L ⊗ K` and
`(K ⊗ L) ⊗ M ≅ K ⊗ (L ⊗ M)` — made explicit, and `TensorStructure.restrict` is the passage
from the ambient derived category to its perfect objects.

No declaration below carries the `0FDK` tag. Discharging the hypotheses of
`TensorStructure.restrict` for the perfect objects of `D(O_X)` needs the derived tensor
product of two perfect objects to be perfect, and that is available only over a ring
(`StacksDraft.Perfect.isPerfect_derivedTensorProduct`, Tag 0GM0), not for sheaves of modules
on a ringed space. Until it is, the statements below are about an arbitrary tensor
triangulated category and say nothing about `D_perf(O_X)` in particular, so tagging them
would overstate what is proved.

## References

* [Stacks, Tag 0FCT](https://stacks.math.columbia.edu/tag/0FCT)
* [Stacks, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.Pretriangulated.K0

universe v u v' u'

/-! ### Classes of isomorphic objects -/

section Classes

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The relation imposed by a distinguished triangle, in additive form: for a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` one has `[Y] = [X] + [Z]` in `K₀(C)`. -/
@[sga "6 0 3.1" "partial"]
theorem cls_eq_add_of_distinguished {T : Triangle C} (hT : T ∈ distTriang C) :
    cls T.obj₂ = cls T.obj₁ + cls T.obj₃ := by
  have h := cls_rel T hT
  rwa [sub_sub, sub_eq_zero] at h

/-- A zero object has class zero in `K₀(C)`, by the contractible triangle on it. -/
@[simp] theorem cls_zero : cls (0 : C) = 0 :=
  left_eq_add.mp (cls_eq_add_of_distinguished (contractible_distinguished (0 : C)))

/-- Isomorphic objects have the same class in `K₀(C)`: an isomorphism `e : Y ≅ Z` extends to a
distinguished triangle `Y ⟶ Z ⟶ 0`, which imposes `[Z] = [Y] + [0]`. -/
theorem cls_eq_of_iso {Y Z : C} (e : Y ≅ Z) : cls Y = cls Z := by
  have h := cls_eq_add_of_distinguished (T := Triangle.mk e.hom (0 : Z ⟶ 0) 0)
    ((Triangle.distinguished_iff_of_isZero₃ _ (isZero_zero C)).2 (by dsimp; infer_instance))
  simpa using h.symm

end Classes

/-! ### Evaluation as a homomorphism -/

/-- Evaluation at a fixed element, as a homomorphism from the additive group of endomorphisms
of an abelian group to that group. It is used to turn an identity between values of a bilinear
map into an identity between homomorphisms, which `hom_ext` can then prove. -/
def evalHom {A : Type*} [AddCommGroup A] (x : A) : (A →+ A) →+ A where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation at `x` sends an endomorphism `f` to `f x`. -/
@[simp] theorem evalHom_apply {A : Type*} [AddCommGroup A] (x : A) (f : A →+ A) :
    evalHom x f = f x := rfl

/-! ### The Grothendieck ring -/

/-- A **non-unital tensor structure** on a pretriangulated category `C`: a bifunctor which is
an exact functor of triangulated categories in each variable separately, together with
associativity and commutativity isomorphisms of objects. No unit object is asked for, and no
naturality or coherence of the two isomorphisms is required, since `K₀(C)` does not see it.

This is the data that makes `K₀(C)` a *non-unital* commutative ring. It is a separate structure
from `TensorStructure` because the unit is genuinely optional: a triangulated subcategory
closed under the tensor product of an ambient category need not contain the unit object, and
then its `K`-group has an associative commutative multiplication and no unit — which is the
situation of [Stacks, Tag 0FDN]. -/
structure NonUnitalTensorStructure (C : Type u) [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] where
  /-- The tensor product, as a curried bifunctor. -/
  tensor : C ⥤ C ⥤ C
  /-- Tensoring on the right with a fixed object commutes with the shift. -/
  commShiftRight (Y : C) : (tensor.obj Y).CommShift ℤ
  /-- Tensoring on the right with a fixed object is exact. -/
  isTriangulatedRight (Y : C) :
    letI := commShiftRight Y
    (tensor.obj Y).IsTriangulated
  /-- Tensoring on the left with a fixed object commutes with the shift. -/
  commShiftLeft (Z : C) : (tensor.flip.obj Z).CommShift ℤ
  /-- Tensoring on the left with a fixed object is exact. -/
  isTriangulatedLeft (Z : C) :
    letI := commShiftLeft Z
    (tensor.flip.obj Z).IsTriangulated
  /-- The tensor product is associative on objects. -/
  associator (Y Z W : C) :
    (tensor.obj ((tensor.obj Y).obj Z)).obj W ≅ (tensor.obj Y).obj ((tensor.obj Z).obj W)
  /-- The tensor product is commutative on objects. -/
  braiding (Y Z : C) : (tensor.obj Y).obj Z ≅ (tensor.obj Z).obj Y

namespace NonUnitalTensorStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (T : NonUnitalTensorStructure C)

/-- The bilinear multiplication of `K₀(C)` induced by a tensor structure, through the bilinear
map of [Stacks, Tag 0FCT]. -/
noncomputable def mul : K0 C →+ K0 C →+ K0 C :=
  (exists_bilinear_of_bifunctor C C C T.tensor T.commShiftRight T.isTriangulatedRight
    T.commShiftLeft T.isTriangulatedLeft).choose

/-- The product of the classes of two objects is the class of their tensor product. -/
@[simp] theorem mul_cls (Y Z : C) : T.mul (cls Y) (cls Z) = cls ((T.tensor.obj Y).obj Z) :=
  (exists_bilinear_of_bifunctor C C C T.tensor T.commShiftRight T.isTriangulatedRight
    T.commShiftLeft T.isTriangulatedLeft).choose_spec Y Z

/-- The multiplication of `K₀(C)` is associative, by the associativity of the tensor product on
objects. -/
theorem mul_assoc' (a b c : K0 C) : T.mul (T.mul a b) c = T.mul a (T.mul b c) := by
  have inner : ∀ Y Z : C,
      T.mul (T.mul (cls Y) (cls Z)) = (T.mul (cls Y)).comp (T.mul (cls Z)) := fun Y Z => by
    refine hom_ext fun W => ?_
    rw [AddMonoidHom.comp_apply, T.mul_cls Z W, T.mul_cls Y Z, T.mul_cls, T.mul_cls]
    exact cls_eq_of_iso (T.associator Y Z W)
  have step : ∀ Y : C, ((evalHom c).comp T.mul).comp (T.mul (cls Y)) =
      (T.mul (cls Y)).comp ((evalHom c).comp T.mul) := fun Y => by
    refine hom_ext fun Z => ?_
    simp only [AddMonoidHom.comp_apply, evalHom_apply]
    exact DFunLike.congr_fun (inner Y Z) c
  have outer : ((evalHom c).comp T.mul).comp ((evalHom b).comp T.mul) =
      (evalHom (T.mul b c)).comp T.mul := by
    refine hom_ext fun Y => ?_
    simp only [AddMonoidHom.comp_apply, evalHom_apply]
    exact DFunLike.congr_fun (step Y) b
  exact DFunLike.congr_fun outer a

/-- The multiplication of `K₀(C)` is commutative, by the commutativity of the tensor product on
objects. -/
theorem mul_comm' (a b : K0 C) : T.mul a b = T.mul b a := by
  have key : ∀ Y : C, T.mul (cls Y) = (evalHom (cls Y)).comp T.mul := fun Y => by
    refine hom_ext fun Z => ?_
    rw [AddMonoidHom.comp_apply, evalHom_apply, T.mul_cls, T.mul_cls]
    exact cls_eq_of_iso (T.braiding Y Z)
  have h : (evalHom b).comp T.mul = T.mul b := by
    refine hom_ext fun Y => ?_
    rw [AddMonoidHom.comp_apply, evalHom_apply]
    exact DFunLike.congr_fun (key Y) b
  exact DFunLike.congr_fun h a

/-- **The non-unital Grothendieck ring of a non-unital tensor triangulated category.**
`K₀(C)` is a non-unital commutative ring whose addition is the one it already has and whose
multiplication is induced by the tensor product. Distributivity and the two annihilation laws
are the additivity of the bilinear map of [Stacks, Tag 0FCT] in each variable. -/
@[instance_reducible]
noncomputable def nonUnitalCommRing : NonUnitalCommRing (K0 C) :=
  { (inferInstance : AddCommGroup (K0 C)) with
    mul := fun a b => T.mul a b
    left_distrib := fun a b c => (T.mul a).map_add b c
    right_distrib := fun a b c =>
      congrArg (fun f : K0 C →+ K0 C => f c) (T.mul.map_add a b)
    zero_mul := fun a => congrArg (fun f : K0 C →+ K0 C => f a) T.mul.map_zero
    mul_zero := fun a => (T.mul a).map_zero
    mul_assoc := T.mul_assoc'
    mul_comm := T.mul_comm' }

/-- The additive group of the non-unital Grothendieck ring is the additive group of `K₀(C)`. -/
theorem nonUnitalCommRing_toAddCommGroup :
    T.nonUnitalCommRing.toAddCommGroup = (inferInstance : AddCommGroup (K0 C)) := rfl

/-- Multiplication in the non-unital Grothendieck ring is the tensor product. -/
theorem cls_mul (Y Z : C) :
    letI := T.nonUnitalCommRing
    cls Y * cls Z = cls ((T.tensor.obj Y).obj Z) :=
  T.mul_cls Y Z

/-- **The non-unital Grothendieck ring, with its two characterising properties.** There is a
non-unital commutative ring structure on `K₀(C)` whose additive group is the given one and
whose product of the classes of two objects is the class of their tensor product.

No unit is asserted, and none exists in general. -/
theorem exists_nonUnitalCommRing :
    ∃ r : NonUnitalCommRing (K0 C),
      r.toAddCommGroup = (inferInstance : AddCommGroup (K0 C)) ∧
        ∀ Y Z : C, r.mul (cls Y) (cls Z) = cls ((T.tensor.obj Y).obj Z) :=
  ⟨T.nonUnitalCommRing, T.nonUnitalCommRing_toAddCommGroup, fun Y Z => T.mul_cls Y Z⟩

end NonUnitalTensorStructure

/-- A **tensor structure** on a pretriangulated category `C`: a bifunctor which is an exact
functor of triangulated categories in each variable separately, a unit object, and
associativity, commutativity and unit isomorphisms of objects. No naturality or coherence of
the three isomorphisms is required, since `K₀(C)` does not see it. -/
structure TensorStructure (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The tensor product, as a curried bifunctor. -/
  tensor : C ⥤ C ⥤ C
  /-- Tensoring on the right with a fixed object commutes with the shift. -/
  commShiftRight (Y : C) : (tensor.obj Y).CommShift ℤ
  /-- Tensoring on the right with a fixed object is exact. -/
  isTriangulatedRight (Y : C) :
    letI := commShiftRight Y
    (tensor.obj Y).IsTriangulated
  /-- Tensoring on the left with a fixed object commutes with the shift. -/
  commShiftLeft (Z : C) : (tensor.flip.obj Z).CommShift ℤ
  /-- Tensoring on the left with a fixed object is exact. -/
  isTriangulatedLeft (Z : C) :
    letI := commShiftLeft Z
    (tensor.flip.obj Z).IsTriangulated
  /-- The unit object. -/
  one : C
  /-- The tensor product is associative on objects. -/
  associator (Y Z W : C) :
    (tensor.obj ((tensor.obj Y).obj Z)).obj W ≅ (tensor.obj Y).obj ((tensor.obj Z).obj W)
  /-- The tensor product is commutative on objects. -/
  braiding (Y Z : C) : (tensor.obj Y).obj Z ≅ (tensor.obj Z).obj Y
  /-- The unit object is a left unit for the tensor product. -/
  leftUnitor (Y : C) : (tensor.obj one).obj Y ≅ Y

namespace TensorStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (T : TensorStructure C)

/-- The non-unital tensor structure underlying a tensor structure: everything but the unit
object and the unit isomorphism. -/
def toNonUnitalTensorStructure : NonUnitalTensorStructure C where
  tensor := T.tensor
  commShiftRight := T.commShiftRight
  isTriangulatedRight := T.isTriangulatedRight
  commShiftLeft := T.commShiftLeft
  isTriangulatedLeft := T.isTriangulatedLeft
  associator := T.associator
  braiding := T.braiding

/-- The bilinear multiplication of `K₀(C)` induced by a tensor structure, through the bilinear
map of [Stacks, Tag 0FCT]. -/
noncomputable def mul : K0 C →+ K0 C →+ K0 C :=
  (exists_bilinear_of_bifunctor C C C T.tensor T.commShiftRight T.isTriangulatedRight
    T.commShiftLeft T.isTriangulatedLeft).choose

/-- The product of the classes of two objects is the class of their tensor product. -/
@[simp] theorem mul_cls (Y Z : C) : T.mul (cls Y) (cls Z) = cls ((T.tensor.obj Y).obj Z) :=
  (exists_bilinear_of_bifunctor C C C T.tensor T.commShiftRight T.isTriangulatedRight
    T.commShiftLeft T.isTriangulatedLeft).choose_spec Y Z

/-- The multiplication of `K₀(C)` is associative, by the associativity of the tensor product on
objects. -/
theorem mul_assoc' (a b c : K0 C) : T.mul (T.mul a b) c = T.mul a (T.mul b c) :=
  T.toNonUnitalTensorStructure.mul_assoc' a b c

/-- The multiplication of `K₀(C)` is commutative, by the commutativity of the tensor product on
objects. -/
theorem mul_comm' (a b : K0 C) : T.mul a b = T.mul b a :=
  T.toNonUnitalTensorStructure.mul_comm' a b

/-- The class of the unit object is a left unit for the multiplication of `K₀(C)`. -/
theorem one_mul' (a : K0 C) : T.mul (cls T.one) a = a := by
  have h : T.mul (cls T.one) = AddMonoidHom.id (K0 C) := by
    refine hom_ext fun Y => ?_
    rw [AddMonoidHom.id_apply, T.mul_cls]
    exact cls_eq_of_iso (T.leftUnitor Y)
  exact DFunLike.congr_fun h a

/-- **The Grothendieck ring of a tensor triangulated category.** `K₀(C)` is a commutative ring
whose addition is the one it already has, whose multiplication is induced by the tensor product
and whose unit is the class of the unit object. -/
@[instance_reducible, sga "6 IV 2.7" "more general"]
noncomputable def commRing : CommRing (K0 C) :=
  letI : Mul (K0 C) := ⟨fun a b => T.mul a b⟩
  letI : One (K0 C) := ⟨cls T.one⟩
  let r : CommRing (K0 C) := CommRing.ofMinimalAxioms
    (add_assoc := fun a b c => add_assoc a b c)
    (zero_add := fun a => zero_add a)
    (neg_add_cancel := fun a => neg_add_cancel a)
    (mul_assoc := T.mul_assoc')
    (mul_comm := T.mul_comm')
    (one_mul := T.one_mul')
    (left_distrib := fun a b c => (T.mul a).map_add b c)
  { r with toRing := { r.toRing with toAddCommGroup := inferInstance } }

/-- The additive group of the Grothendieck ring is the additive group of `K₀(C)`. -/
theorem commRing_toAddCommGroup :
    T.commRing.toAddCommGroup = (inferInstance : AddCommGroup (K0 C)) := rfl

/-- Multiplication in the Grothendieck ring is the tensor product. -/
theorem cls_mul (Y Z : C) :
    letI := T.commRing
    cls Y * cls Z = cls ((T.tensor.obj Y).obj Z) :=
  T.mul_cls Y Z

/-- The unit of the Grothendieck ring is the class of the unit object. -/
theorem one_eq_cls_one :
    letI := T.commRing
    (1 : K0 C) = cls T.one := rfl

/-- **The Grothendieck ring, with its three characterising properties.** There is a commutative
ring structure on `K₀(C)` whose additive group is the given one, whose product of classes of
objects is the class of their tensor product, and whose unit is the class of the unit object. -/
@[sga "6 IV 2.7" "more general"]
theorem exists_commRing :
    ∃ r : CommRing (K0 C),
      r.toAddCommGroup = (inferInstance : AddCommGroup (K0 C)) ∧
        (∀ Y Z : C, r.mul (cls Y) (cls Z) = cls ((T.tensor.obj Y).obj Z)) ∧
        r.one = cls T.one :=
  ⟨T.commRing, T.commRing_toAddCommGroup, fun Y Z => T.mul_cls Y Z, rfl⟩

end TensorStructure

/-! ### The Grothendieck module -/

/-- An **action** of a tensor structure on `C` on a second pretriangulated category `D`: a
bifunctor `C × D → D` which is an exact functor of triangulated categories in each variable
separately, together with an associativity isomorphism against the tensor product of `C` and a
unit isomorphism, both on objects only. -/
structure TensorAction {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : TensorStructure C) (D : Type u') [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] where
  /-- The action, as a curried bifunctor. -/
  act : C ⥤ D ⥤ D
  /-- Acting by a fixed object of `C` commutes with the shift. -/
  commShiftRight (Y : C) : (act.obj Y).CommShift ℤ
  /-- Acting by a fixed object of `C` is exact. -/
  isTriangulatedRight (Y : C) :
    letI := commShiftRight Y
    (act.obj Y).IsTriangulated
  /-- Acting on a fixed object of `D` commutes with the shift. -/
  commShiftLeft (Z : D) : (act.flip.obj Z).CommShift ℤ
  /-- Acting on a fixed object of `D` is exact. -/
  isTriangulatedLeft (Z : D) :
    letI := commShiftLeft Z
    (act.flip.obj Z).IsTriangulated
  /-- The action is associative against the tensor product of `C`, on objects. -/
  associator (Y Z : C) (W : D) :
    (act.obj ((T.tensor.obj Y).obj Z)).obj W ≅ (act.obj Y).obj ((act.obj Z).obj W)
  /-- The unit object of `C` acts as the identity, on objects. -/
  unitor (W : D) : (act.obj T.one).obj W ≅ W

namespace TensorAction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {T : TensorStructure C}
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (A : TensorAction T D)

/-- The bilinear pairing `K₀(C) × K₀(D) → K₀(D)` induced by an action, through the bilinear map
of [Stacks, Tag 0FCT]. -/
noncomputable def smul : K0 C →+ K0 D →+ K0 D :=
  (exists_bilinear_of_bifunctor C D D A.act A.commShiftRight A.isTriangulatedRight
    A.commShiftLeft A.isTriangulatedLeft).choose

/-- The pairing sends a pair of classes of objects to the class of the acted object. -/
@[simp] theorem smul_cls (Y : C) (W : D) :
    A.smul (cls Y) (cls W) = cls ((A.act.obj Y).obj W) :=
  (exists_bilinear_of_bifunctor C D D A.act A.commShiftRight A.isTriangulatedRight
    A.commShiftLeft A.isTriangulatedLeft).choose_spec Y W

/-- The class of the unit object of `C` acts as the identity on `K₀(D)`. -/
theorem one_smul' (w : K0 D) : A.smul (cls T.one) w = w := by
  have h : A.smul (cls T.one) = AddMonoidHom.id (K0 D) := by
    refine hom_ext fun W => ?_
    rw [AddMonoidHom.id_apply, A.smul_cls]
    exact cls_eq_of_iso (A.unitor W)
  exact DFunLike.congr_fun h w

/-- The pairing is associative against the multiplication of `K₀(C)`. -/
theorem mul_smul' (a b : K0 C) (w : K0 D) :
    A.smul (T.mul a b) w = A.smul a (A.smul b w) := by
  have inner : ∀ Y Z : C,
      A.smul (T.mul (cls Y) (cls Z)) = (A.smul (cls Y)).comp (A.smul (cls Z)) := fun Y Z => by
    refine hom_ext fun W => ?_
    rw [AddMonoidHom.comp_apply, A.smul_cls Z W, T.mul_cls Y Z, A.smul_cls, A.smul_cls]
    exact cls_eq_of_iso (A.associator Y Z W)
  have step : ∀ Y : C, ((evalHom w).comp A.smul).comp (T.mul (cls Y)) =
      (A.smul (cls Y)).comp ((evalHom w).comp A.smul) := fun Y => by
    refine hom_ext fun Z => ?_
    simp only [AddMonoidHom.comp_apply, evalHom_apply]
    exact DFunLike.congr_fun (inner Y Z) w
  have outer : ((evalHom w).comp A.smul).comp ((evalHom b).comp T.mul) =
      (evalHom (((evalHom w).comp A.smul) b)).comp A.smul := by
    refine hom_ext fun Y => ?_
    simp only [AddMonoidHom.comp_apply, evalHom_apply]
    exact DFunLike.congr_fun (step Y) b
  exact DFunLike.congr_fun outer a

/-- **The Grothendieck group of `D` as a module over the Grothendieck ring of `C`.** -/
@[instance_reducible, sga "6 IV 2.10" "more general"]
noncomputable def module :
    letI := T.commRing
    Module (K0 C) (K0 D) :=
  letI := T.commRing
  { smul := fun a w => A.smul a w
    one_smul := A.one_smul'
    mul_smul := fun a b w => A.mul_smul' a b w
    smul_zero := fun a => (A.smul a).map_zero
    smul_add := fun a w w' => (A.smul a).map_add w w'
    add_smul := fun a b w => congrArg (fun f : K0 D →+ K0 D => f w) (A.smul.map_add a b)
    zero_smul := fun w => congrArg (fun f : K0 D →+ K0 D => f w) A.smul.map_zero }

/-- Scalar multiplication of the class of an object of `D` by the class of an object of `C` is
the class of the acted object. -/
theorem cls_smul (Y : C) (W : D) :
    letI := T.commRing
    letI := A.module
    cls Y • cls W = cls ((A.act.obj Y).obj W) :=
  A.smul_cls Y W

end TensorAction

/-! ### Tensor structures from a monoidal structure -/

section Monoidal

open CategoryTheory.MonoidalCategory

/-- **A braided monoidal structure on a pretriangulated category whose tensor product is exact
in each variable is a tensor structure.** The associator, braiding and left unitor of the
monoidal category are taken componentwise; their coherence is not used. A braiding suffices,
since `K₀` only needs the isomorphism `Y ⊗ Z ≅ Z ⊗ Y` and not that it is an involution. -/
noncomputable def TensorStructure.ofMonoidal (C : Type u) [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [BraidedCategory C]
    (csR : ∀ Y : C, ((curriedTensor C).obj Y).CommShift ℤ)
    (hR : ∀ Y : C, letI := csR Y; ((curriedTensor C).obj Y).IsTriangulated)
    (csL : ∀ Z : C, ((curriedTensor C).flip.obj Z).CommShift ℤ)
    (hL : ∀ Z : C, letI := csL Z; ((curriedTensor C).flip.obj Z).IsTriangulated) :
    TensorStructure C where
  tensor := curriedTensor C
  commShiftRight := csR
  isTriangulatedRight := hR
  commShiftLeft := csL
  isTriangulatedLeft := hL
  one := 𝟙_ C
  associator Y Z W := α_ Y Z W
  braiding Y Z := β_ Y Z
  leftUnitor Y := λ_ Y

end Monoidal

/-! ### Tensor structures on a triangulated subcategory -/

section Subcategory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The restriction of a bifunctor `C ⥤ C ⥤ C` to a full subcategory closed under it. -/
noncomputable def liftBifunctor (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z)) :
    P.FullSubcategory ⥤ P.FullSubcategory ⥤ P.FullSubcategory where
  obj Y := P.lift (P.ι ⋙ F.obj Y.obj) fun Z => hF Y.obj Z.obj Y.property Z.property
  map f :=
    { app := fun Z => P.homMk ((F.map f.hom).app Z.obj)
      naturality := fun Z W g => P.ι.map_injective (by simp) }
  map_id Y := by ext Z; simp
  map_comp f g := by ext Z; simp

/-- Restricting a bifunctor commutes with the inclusion of the subcategory, in the right
variable. -/
noncomputable def liftBifunctorObjCompιIso (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z)) (Y : P.FullSubcategory) :
    (liftBifunctor P F hF).obj Y ⋙ P.ι ≅ P.ι ⋙ F.obj Y.obj :=
  P.liftCompιIso (P.ι ⋙ F.obj Y.obj) fun Z => hF Y.obj Z.obj Y.property Z.property

/-- Restricting a bifunctor commutes with the inclusion of the subcategory, in the left
variable. -/
noncomputable def liftBifunctorFlipObjCompιIso (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z)) (Z : P.FullSubcategory) :
    (liftBifunctor P F hF).flip.obj Z ⋙ P.ι ≅ P.ι ⋙ F.flip.obj Z.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by simp [liftBifunctor]

/-- A functor `G` on a triangulated subcategory is exact for the shift-commutation transported
along an isomorphism `G ⋙ ι ≅ ι ⋙ F'` with an exact functor `F'`. -/
private theorem isTriangulated_ofComp_ι (P : ObjectProperty C) [P.IsTriangulated]
    (G : P.FullSubcategory ⥤ P.FullSubcategory) (F' : C ⥤ C) [F'.CommShift ℤ]
    [F'.IsTriangulated] (e : G ⋙ P.ι ≅ P.ι ⋙ F') :
    letI := Functor.CommShift.ofComp e ℤ
    G.IsTriangulated := by
  let := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

variable (P : ObjectProperty C) [P.IsTriangulated] (F : C ⥤ C ⥤ C)
  (hF : ∀ Y Z : C, P Y → P Z → P ((F.obj Y).obj Z))

/-- Fixing a right argument, the restricted bifunctor commutes with the shift. -/
@[instance_reducible]
noncomputable def liftBifunctorCommShiftRight (csR : ∀ Y : C, (F.obj Y).CommShift ℤ)
    (Y : P.FullSubcategory) : ((liftBifunctor P F hF).obj Y).CommShift ℤ :=
  letI := csR Y.obj
  Functor.CommShift.ofComp (liftBifunctorObjCompιIso P F hF Y) ℤ

/-- Fixing a left argument, the restricted bifunctor commutes with the shift. -/
@[instance_reducible]
noncomputable def liftBifunctorCommShiftLeft (csL : ∀ Z : C, (F.flip.obj Z).CommShift ℤ)
    (Z : P.FullSubcategory) : ((liftBifunctor P F hF).flip.obj Z).CommShift ℤ :=
  letI := csL Z.obj
  Functor.CommShift.ofComp (liftBifunctorFlipObjCompιIso P F hF Z) ℤ

/-- Fixing a right argument, the restricted bifunctor is exact: it becomes the restriction of
an exact functor after composing with the inclusion, which is exact and detects exactness. -/
theorem liftBifunctor_isTriangulatedRight (csR : ∀ Y : C, (F.obj Y).CommShift ℤ)
    (hR : ∀ Y : C, letI := csR Y; (F.obj Y).IsTriangulated) (Y : P.FullSubcategory) :
    letI := liftBifunctorCommShiftRight P F hF csR Y
    ((liftBifunctor P F hF).obj Y).IsTriangulated := by
  let := csR Y.obj
  let := hR Y.obj
  exact isTriangulated_ofComp_ι P _ _ (liftBifunctorObjCompιIso P F hF Y)

/-- Fixing a left argument, the restricted bifunctor is exact. -/
theorem liftBifunctor_isTriangulatedLeft (csL : ∀ Z : C, (F.flip.obj Z).CommShift ℤ)
    (hL : ∀ Z : C, letI := csL Z; (F.flip.obj Z).IsTriangulated) (Z : P.FullSubcategory) :
    letI := liftBifunctorCommShiftLeft P F hF csL Z
    ((liftBifunctor P F hF).flip.obj Z).IsTriangulated := by
  let := csL Z.obj
  let := hL Z.obj
  exact isTriangulated_ofComp_ι P _ _ (liftBifunctorFlipObjCompιIso P F hF Z)

/-- **A non-unital tensor structure restricts to a triangulated subcategory closed under the
tensor product.** No unit object is asked for and none is produced: the subcategory need not
contain one. -/
noncomputable def NonUnitalTensorStructure.restrict (T : NonUnitalTensorStructure C)
    (P : ObjectProperty C) [P.IsTriangulated]
    (hT : ∀ Y Z : C, P Y → P Z → P ((T.tensor.obj Y).obj Z)) :
    NonUnitalTensorStructure P.FullSubcategory where
  tensor := liftBifunctor P T.tensor hT
  commShiftRight := liftBifunctorCommShiftRight P T.tensor hT T.commShiftRight
  isTriangulatedRight := liftBifunctor_isTriangulatedRight P T.tensor hT T.commShiftRight
    T.isTriangulatedRight
  commShiftLeft := liftBifunctorCommShiftLeft P T.tensor hT T.commShiftLeft
  isTriangulatedLeft := liftBifunctor_isTriangulatedLeft P T.tensor hT T.commShiftLeft
    T.isTriangulatedLeft
  associator Y Z W := P.isoMk (T.associator Y.obj Z.obj W.obj)
  braiding Y Z := P.isoMk (T.braiding Y.obj Z.obj)

/-- **A tensor structure restricts to a triangulated subcategory closed under the tensor
product and containing the unit object.** This is what turns a tensor product on an ambient
pretriangulated category into the Grothendieck ring of a subcategory of it. -/
noncomputable def TensorStructure.restrict (T : TensorStructure C) (P : ObjectProperty C)
    [P.IsTriangulated] (hT : ∀ Y Z : C, P Y → P Z → P ((T.tensor.obj Y).obj Z))
    (hOne : P T.one) : TensorStructure P.FullSubcategory where
  tensor := liftBifunctor P T.tensor hT
  commShiftRight := liftBifunctorCommShiftRight P T.tensor hT T.commShiftRight
  isTriangulatedRight := liftBifunctor_isTriangulatedRight P T.tensor hT T.commShiftRight
    T.isTriangulatedRight
  commShiftLeft := liftBifunctorCommShiftLeft P T.tensor hT T.commShiftLeft
  isTriangulatedLeft := liftBifunctor_isTriangulatedLeft P T.tensor hT T.commShiftLeft
    T.isTriangulatedLeft
  one := ⟨T.one, hOne⟩
  associator Y Z W := P.isoMk (T.associator Y.obj Z.obj W.obj)
  braiding Y Z := P.isoMk (T.braiding Y.obj Z.obj)
  leftUnitor Y := P.isoMk (T.leftUnitor Y.obj)

/-- **Classes in `K₀` of a triangulated subcategory add along a distinguished triangle of the
ambient category.** A distinguished triangle of `C` all three of whose vertices lie in `P` is
the image of a triangle of `P.FullSubcategory`, the maps being taken back along the fully
faithful inclusion and the connecting map composed with its shift-commutation isomorphism;
that triangle is distinguished by definition of the pretriangulated structure of a
triangulated subcategory, so the relation of [Stacks, Tag 0FCT] applies to it there. -/
@[sga "6 0 3.1" "partial"]
theorem cls_eq_add_of_distinguished_of_prop (P : ObjectProperty C) [P.IsTriangulated]
    {Y₁ Y₂ Y₃ : C} (h₁ : P Y₁) (h₂ : P Y₂) (h₃ : P Y₃) (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (δ : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧) (hT : Triangle.mk f g δ ∈ distTriang C) :
    cls (⟨Y₂, h₂⟩ : P.FullSubcategory) =
      cls (⟨Y₁, h₁⟩ : P.FullSubcategory) + cls (⟨Y₃, h₃⟩ : P.FullSubcategory) := by
  let Z₁ : P.FullSubcategory := ⟨Y₁, h₁⟩
  let Z₂ : P.FullSubcategory := ⟨Y₂, h₂⟩
  let Z₃ : P.FullSubcategory := ⟨Y₃, h₃⟩
  let e := (P.ι.commShiftIso (1 : ℤ)).app Z₁
  let T : Triangle P.FullSubcategory := Triangle.mk
    (P.fullyFaithfulι.preimage (X := Z₁) (Y := Z₂) f)
    (P.fullyFaithfulι.preimage (X := Z₂) (Y := Z₃) g)
    (P.fullyFaithfulι.preimage (X := Z₃) (Y := Z₁⟦(1 : ℤ)⟧) (δ ≫ e.inv))
  have hT' : T ∈ distTriang P.FullSubcategory := by
    change P.ι.mapTriangle.obj T ∈ distTriang C
    simpa [T, e, Z₁, Z₂, Z₃] using hT
  exact cls_eq_add_of_distinguished hT'

end Subcategory

end CategoryTheory.Pretriangulated.K0

end

end
