module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import Mathlib.CategoryTheory.Monoidal.Skeleton

/-!
# The Picard group of a ringed site

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)`. Stacks Tag 01CX asserts that the
isomorphism classes of invertible sheaves of `𝒪`-modules form an abelian group under tensor
product, the Picard group. This file constructs that group and proves the facts that make it
*the* Picard group rather than some abelian group:

* its elements are exactly the isomorphism classes of invertible sheaves of modules
  (`classOf_eq_classOf_iff` and `exists_classOf`);
* multiplication is tensor product (`classOf_mul` and `classOf_tensorSheaf`);
* the neutral element is the class of `𝒪` (`classOf_unit`);
* the inverse of a class is the class of the inverse sheaf (`classOf_tensorInv`).

## Main definitions

* `Stacks.SheafPicardGroup.ClassMonoid`: the commutative monoid of isomorphism classes of
  *all* sheaves of `𝒪`-modules, with multiplication the tensor product. This is the skeleton
  of the monoidal category `SheafOfModules (structureSheaf 𝒪 h𝒪)`.
* `Stacks.SheafPicardGroup.mk`: the isomorphism class of a sheaf of modules.
* `Stacks.SheafPicardGroup.PicardGroup`: **the Picard group**, the units of `ClassMonoid`.
* `Stacks.SheafPicardGroup.classOf`: the Picard class of an invertible sheaf of modules.

## Main results

* `Stacks.SheafPicardGroup.isInvertible_iff_isUnit`: a sheaf of modules is invertible exactly
  when its isomorphism class is a unit of `ClassMonoid`. This is what pins the carrier down:
  the group is neither larger nor smaller than the invertible sheaves demand.
* `Stacks.SheafPicardGroup.exists_classOf`: every element of the Picard group is the class of
  an invertible sheaf of modules, so `classOf` is onto.
* `Stacks.SheafPicardGroup.classOf_eq_classOf_iff`: two invertible sheaves have the same Picard
  class exactly when they are isomorphic.
* `Stacks.SheafPicardGroup.classOf_mul` and `Stacks.SheafPicardGroup.classOf_tensorSheaf`:
  multiplication of classes is tensor product, in the monoidal and in the
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling. The second needs no monoidal
    instance in its statement.
* `Stacks.SheafPicardGroup.classOf_tensorPow`: the class of the `n`-th tensor power of Stacks
  Tag 01CU is the `n`-th power of the class, for every `n : ℤ`.
* `Stacks.SheafPicardGroup.subsingleton_iff`: the Picard group is trivial exactly when every
  invertible sheaf of modules is isomorphic to the structure sheaf.

## Implementation notes

**The carrier is the units of the skeleton of the whole category, not a skeleton of the
invertible objects.** Three shapes are available and they are not equally cheap.

1. A small model of the skeleton of the full subcategory of invertible sheaves, carrying a
   `CommGroup` structure assembled by hand. This needs *essential smallness* of the invertible
   objects to shrink the skeleton, and it needs associativity, both unitors, commutativity and
   the inverse law proved one at a time on the subcategory, each by transporting the ambient
   monoidal coherence through the full-subcategory inclusion.
2. A `Quotient` of the isomorphism setoid on the subtype of invertible sheaves. The same six
   coherence obligations, and without even the skeleton API to carry them.
3. The units of the skeleton of `SheafOfModules (structureSheaf 𝒪 h𝒪)` itself. The repository
   already supplies `Stacks.SheafInternalHom.braidedCategory`, and Mathlib's
   `CategoryTheory.Skeleton.instCommMonoid` turns a braided monoidal category into a
   commutative monoid; `Units.instCommGroup` then gives the group for free. No smallness input
   is needed, because the skeleton of a category is a type in the universe of that category's
   objects already, and no coherence lemma is proved by hand.

This file takes (3). The price is that the carrier sits in the universe of
`SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)` rather than in `Type (max u v w)`; the Stacks
statement says nothing about the universe level, and the only thing lost by the extra level is
the ability to use the group as an index type for a construction at level `max u v w`, which
nothing here does. What is *gained* is that the construction needs no essential-smallness
hypothesis — and essential smallness of the invertible sheaves (Stacks Tag 040B) is proved
nowhere in this repository.

The invertible objects are not cut out as a full subcategory at all. Instead `ClassMonoid`
collects *every* isomorphism class and `isInvertible_iff_isUnit` identifies the invertible ones
with its units; this is the same move Mathlib's ring-level `CommRing.Pic` makes, and it is what
removes the smallness obligation, since no subcategory has to be replaced by a small model.

**Multiplicative, not additive.** Stacks writes `Pic(X)` additively in places and
multiplicatively in others. The carrier here is a `Units` type, so the multiplicative spelling
is the one the Mathlib API speaks, and `Additive (PicardGroup 𝒪 h𝒪)` is the additive reading
with no further work. Mathlib's `CommRing.Pic` is multiplicative for the same reason.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers
open AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafPicardGroup

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

/-- **Isomorphism classes of sheaves of `𝒪`-modules**, as a commutative monoid under tensor
product. This is the skeleton of the monoidal category of sheaves of modules; the Picard group
is its group of units. -/
def ClassMonoid : Type _ := Skeleton (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- Tensor product makes the isomorphism classes a commutative monoid. The structure is
Mathlib's `CategoryTheory.Skeleton.instCommMonoid`, available because
`Stacks.SheafInternalHom.braidedCategory` makes sheaves of modules braided monoidal. -/
noncomputable instance instCommMonoid : CommMonoid (ClassMonoid 𝒪 h𝒪) :=
  inferInstanceAs (CommMonoid (Skeleton (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))))

/-- The isomorphism class of a sheaf of `𝒪`-modules. -/
def mk (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) : ClassMonoid 𝒪 h𝒪 := toSkeleton L

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Two sheaves of modules have the same class exactly when they are isomorphic.** -/
theorem mk_eq_mk_iff {L N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} :
    mk 𝒪 h𝒪 L = mk 𝒪 h𝒪 N ↔ Nonempty (L ≅ N) :=
  toSkeleton_eq_toSkeleton_iff

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Isomorphic sheaves of modules have the same isomorphism class. -/
theorem mk_eq_mk_of_iso {L N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (e : L ≅ N) :
    mk 𝒪 h𝒪 L = mk 𝒪 h𝒪 N :=
  (mk_eq_mk_iff 𝒪 h𝒪).mpr ⟨e⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Every isomorphism class is the class of a sheaf of modules. -/
theorem mk_surjective : Function.Surjective (mk 𝒪 h𝒪) := fun x =>
  ⟨(fromSkeleton (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))).obj x,
    toSkeleton_fromSkeleton_obj x⟩

/-- **Multiplication of isomorphism classes is tensor product.** -/
theorem mk_mul (L N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    mk 𝒪 h𝒪 (L ⊗ N) = mk 𝒪 h𝒪 L * mk 𝒪 h𝒪 N :=
  Skeleton.toSkeleton_tensorObj L N

/-- **Multiplication of isomorphism classes is the tensor product sheaf.** This is the spelling
whose statement mentions no monoidal structure. -/
theorem mk_tensorSheaf (L N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    mk 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj
      (N))) = mk 𝒪 h𝒪 L * mk 𝒪 h𝒪 N :=
  (mk_eq_mk_of_iso 𝒪 h𝒪 (tensorIso 𝒪 h𝒪 L N).symm).trans (mk_mul 𝒪 h𝒪 L N)

/-- The neutral class is the class of the monoidal unit. -/
theorem mk_tensorUnit :
    mk 𝒪 h𝒪 (𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) = 1 :=
  Skeleton.one_eq.symm

/-- A sheaf of modules has the neutral class exactly when it is isomorphic to the unit. -/
private theorem mk_eq_one_iff {X : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} :
    mk 𝒪 h𝒪 X = 1 ↔ Nonempty (X ≅ 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) := by
  rw [← mk_tensorUnit 𝒪 h𝒪, mk_eq_mk_iff]

/-- **The neutral class is the class of the structure sheaf.** -/
theorem mk_unit : mk 𝒪 h𝒪 (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) = 1 :=
  (mk_eq_one_iff 𝒪 h𝒪).mpr ⟨(unitIso 𝒪 h𝒪).symm⟩

/-- The class of an iterated tensor product is the corresponding power. -/
theorem mk_natTensorPow (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) (m : ℕ) :
    mk 𝒪 h𝒪 (natTensorPow M m) = mk 𝒪 h𝒪 M ^ m := by
  induction m with
  | zero => exact mk_tensorUnit 𝒪 h𝒪
  | succ k ih =>
    rw [pow_succ, ← ih]
    exact mk_mul 𝒪 h𝒪 (natTensorPow M k) M

/-- **The Picard group of `𝒪`**, Stacks Tag 01CX: the isomorphism classes of *invertible*
sheaves of `𝒪`-modules, with multiplication induced by tensor product. It is realised as the
group of units of the monoid `ClassMonoid 𝒪 h𝒪` of all isomorphism classes; that these units
are exactly the invertible sheaves is `isInvertible_iff_isUnit`, and that every one of them is
the class of such a sheaf is `exists_classOf`. -/
@[stacks 01CX "the Picard group"]
abbrev PicardGroup : Type _ := (ClassMonoid 𝒪 h𝒪)ˣ

/-- **The Picard group is an abelian group**, Stacks Tag 01CX. The structure is
`Units.instCommGroup` over `instCommMonoid`: no coherence law is proved by hand, because the
skeleton of a braided monoidal category is already a commutative monoid. The additive reading
the source sometimes uses is `Additive (PicardGroup 𝒪 h𝒪)`, and
`instAddCommGroupAdditivePicardGroup` records it. -/
@[instance_reducible, stacks 01CX "abelian group structure"]
noncomputable def commGroup : CommGroup (PicardGroup 𝒪 h𝒪) :=
  inferInstanceAs (CommGroup (ClassMonoid 𝒪 h𝒪)ˣ)

/-- **The Picard group, written additively**, as Stacks Tag 01CX sometimes does. -/
@[stacks 01CX "abelian group structure"]
noncomputable instance instAddCommGroupAdditivePicardGroup :
    AddCommGroup (Additive (PicardGroup 𝒪 h𝒪)) :=
  inferInstanceAs (AddCommGroup (Additive (ClassMonoid 𝒪 h𝒪)ˣ))

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- **The Picard class of an invertible sheaf of modules.** Its inverse is the class of
`AlgebraicGeometry.SheafOfModules.tensorInv`, the chosen tensor inverse. -/
noncomputable def classOf [IsInvertible 𝒪 h𝒪 L] : PicardGroup 𝒪 h𝒪 :=
  Units.mkOfMulEqOne (mk 𝒪 h𝒪 L) (mk 𝒪 h𝒪 (tensorInv 𝒪 h𝒪 L)) <| by
    rw [← mk_mul, mk_eq_mk_of_iso 𝒪 h𝒪 (tensorInvMulIso 𝒪 h𝒪 L), mk_tensorUnit]

/-- The underlying class of `classOf 𝒪 h𝒪 L` is the isomorphism class of `L`. -/
@[simp]
theorem val_classOf [IsInvertible 𝒪 h𝒪 L] :
    ((classOf 𝒪 h𝒪 L : PicardGroup 𝒪 h𝒪) : ClassMonoid 𝒪 h𝒪) = mk 𝒪 h𝒪 L :=
  rfl

/-- The underlying class of the inverse of `classOf 𝒪 h𝒪 L` is the isomorphism class of
`tensorInv 𝒪 h𝒪 L`. -/
@[simp]
theorem val_inv_classOf [IsInvertible 𝒪 h𝒪 L] :
    (((classOf 𝒪 h𝒪 L)⁻¹ : PicardGroup 𝒪 h𝒪) : ClassMonoid 𝒪 h𝒪) =
      mk 𝒪 h𝒪 (tensorInv 𝒪 h𝒪 L) :=
  rfl

/-- **A sheaf of modules is invertible exactly when its isomorphism class is a unit.** This is
what makes `PicardGroup` the Picard group: the units of `ClassMonoid` are precisely the classes
of invertible sheaves, no more and no fewer. The forward direction is `classOf`; the reverse
turns a monoid inverse into a tensor inverse and appeals to Stacks Tag 01CS. -/
theorem isInvertible_iff_isUnit : IsInvertible 𝒪 h𝒪 L ↔ IsUnit (mk 𝒪 h𝒪 L) := by
  refine ⟨fun _ => ⟨classOf 𝒪 h𝒪 L, rfl⟩, ?_⟩
  rintro ⟨u, hu⟩
  obtain ⟨N, hN⟩ := mk_surjective 𝒪 h𝒪 ((u⁻¹ : PicardGroup 𝒪 h𝒪) : ClassMonoid 𝒪 h𝒪)
  have hmul : mk 𝒪 h𝒪 (L ⊗ N) = 1 := by
    rw [mk_mul, hN, ← hu, Units.mul_inv]
  obtain ⟨e⟩ := (mk_eq_one_iff 𝒪 h𝒪).mp hmul
  exact (isInvertible_iff_isEquivalence_tensorLeft 𝒪 h𝒪 L).mpr
    (TensorInverse.isEquivalence_tensorLeft ⟨N, e, β_ N L ≪≫ e⟩)

/-- **Every element of the Picard group is the class of an invertible sheaf of modules**, so
`classOf` is onto. -/
@[stacks 01CX "the Picard group"]
theorem exists_classOf (x : PicardGroup 𝒪 h𝒪) :
    ∃ (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) (_ : IsInvertible 𝒪 h𝒪 M),
      classOf 𝒪 h𝒪 M = x := by
  obtain ⟨M, hM⟩ := mk_surjective 𝒪 h𝒪 (x : ClassMonoid 𝒪 h𝒪)
  have hinv : IsInvertible 𝒪 h𝒪 M :=
    (isInvertible_iff_isUnit 𝒪 h𝒪 M).mpr (hM ▸ x.isUnit)
  exact ⟨M, hinv, Units.ext (by rw [val_classOf, hM])⟩

variable (N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- **Two invertible sheaves have the same Picard class exactly when they are isomorphic.** -/
@[stacks 01CX "the Picard group"]
theorem classOf_eq_classOf_iff [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N] :
    classOf 𝒪 h𝒪 L = classOf 𝒪 h𝒪 N ↔ Nonempty (L ≅ N) := by
  rw [← mk_eq_mk_iff 𝒪 h𝒪 (L := L) (N := N), ← val_classOf 𝒪 h𝒪 L, ← val_classOf 𝒪 h𝒪 N]
  exact ⟨congrArg _, Units.ext⟩

/-- **Multiplication in the Picard group is tensor product**, Stacks Tag 01CX. -/
@[stacks 01CX "addition is tensor product"]
theorem classOf_mul [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N] :
    classOf 𝒪 h𝒪 (L ⊗ N) = classOf 𝒪 h𝒪 L * classOf 𝒪 h𝒪 N :=
  Units.ext <| by rw [val_classOf, Units.val_mul, val_classOf, val_classOf, mk_mul]

/-- **Multiplication in the Picard group is the tensor product sheaf**, Stacks Tag 01CX in the
spelling whose statement mentions no monoidal structure. -/
@[stacks 01CX "addition is tensor product"]
theorem classOf_tensorSheaf [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N]
    [IsInvertible 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj
      (N)))] :
    classOf 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj
      (N))) = classOf 𝒪 h𝒪 L * classOf 𝒪 h𝒪 N :=
  Units.ext (mk_tensorSheaf 𝒪 h𝒪 L N)

/-- **The neutral element of the Picard group is the class of the structure sheaf**, Stacks
Tag 01CX. -/
@[stacks 01CX "abelian group structure"]
theorem classOf_unit :
    classOf 𝒪 h𝒪 (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) = 1 :=
  Units.ext <| by rw [val_classOf, Units.val_one, mk_unit]

/-- **The inverse of a Picard class is the class of the inverse sheaf**, Stacks Tag 01CT (2)
read in the Picard group of Stacks Tag 01CX. -/
@[stacks 01CX "abelian group structure"]
theorem classOf_tensorInv [IsInvertible 𝒪 h𝒪 L] :
    classOf 𝒪 h𝒪 (tensorInv 𝒪 h𝒪 L) = (classOf 𝒪 h𝒪 L)⁻¹ :=
  Units.ext <| by rw [val_classOf, val_inv_classOf]

/-- A Picard class is trivial exactly when the sheaf is isomorphic to the structure sheaf. -/
theorem classOf_eq_one_iff [IsInvertible 𝒪 h𝒪 L] :
    classOf 𝒪 h𝒪 L = 1 ↔
      Nonempty (L ≅ _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) := by
  rw [← classOf_unit 𝒪 h𝒪, classOf_eq_classOf_iff]

/-- **The Picard group is trivial exactly when every invertible sheaf of modules is isomorphic
to the structure sheaf.** This is the form in which triviality of a Picard group is used in
this repository, and it is now a theorem about the group rather than a definition standing in
for it. -/
theorem subsingleton_iff : Subsingleton (PicardGroup 𝒪 h𝒪) ↔
    ∀ (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)), IsInvertible 𝒪 h𝒪 M →
      Nonempty (M ≅ _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) := by
  refine ⟨fun _ M hM => (classOf_eq_one_iff 𝒪 h𝒪 M).mp (Subsingleton.elim _ _),
    fun h => subsingleton_of_forall_eq 1 fun x => ?_⟩
  obtain ⟨M, hM, rfl⟩ := exists_classOf 𝒪 h𝒪 x
  exact (classOf_eq_one_iff 𝒪 h𝒪 M).mpr (h M hM)

/-- **The class of a nonnegative tensor power is the corresponding power of the class.** -/
theorem classOf_tensorPow_natCast [IsInvertible 𝒪 h𝒪 L] (m : ℕ) :
    classOf 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (m : ℤ)) = classOf 𝒪 h𝒪 L ^ m :=
  Units.ext <| by
    rw [val_classOf, Units.val_pow_eq_pow_val, val_classOf]
    exact mk_natTensorPow 𝒪 h𝒪 L m

/-- **The class of the `n`-th tensor power is the `n`-th power of the class**, for every
integer `n`. The powers are the integer tensor powers of Stacks Tag 01CU; this is the sense in
which the Picard group records them. -/
@[stacks 01CX "addition is tensor product"]
theorem classOf_tensorPow [IsInvertible 𝒪 h𝒪 L] (n : ℤ) :
    classOf 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L n) = classOf 𝒪 h𝒪 L ^ n := by
  match n with
  | .ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact classOf_tensorPow_natCast 𝒪 h𝒪 L m
  | .negSucc m =>
    have hval : classOf 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L (Int.negSucc m)) =
        classOf 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 (tensorInv 𝒪 h𝒪 L) ((m + 1 : ℕ) : ℤ)) := rfl
    rw [hval, classOf_tensorPow_natCast, classOf_tensorInv, Int.negSucc_eq,
      ← Nat.cast_succ, zpow_neg, zpow_natCast, inv_pow]

/-! ### Faithfulness against the three labels of Tag 01CX

Tag 01CX carries three labels — "the Picard group", "abelian group structure" and "addition is
tensor product" — and they are claimed here over exactly the variable block above, in this
order: the site and its topology, the sheaf of rings `𝒪` and its sheaf condition `h𝒪`, then
`J.WEqualsLocallyBijective AddCommGrpCat.{w}` and `HasWeakSheafify J AddCommGrpCat.{w}`.
Nothing further is assumed here and nothing is weakened: the examples below restate each
label's content in this file's vocabulary and discharge it from the tagged declarations.

The construction has to avoid essential smallness of the invertible sheaves, Tag 040B, which is
proved nowhere in this repository; taking the units of the skeleton of the whole category rather
than a small model of the skeleton of the invertible objects is what achieves that, as the
implementation notes record. Invertibility of a tensor product, Tag 01CT (1), *is* available —
`AlgebraicGeometry.SheafOfModules.isInvertible_tensor` — and is used. -/

noncomputable section Faithfulness

variable (L N : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

-- "the Picard group": a type whose elements are exactly the isomorphism classes of invertible
-- sheaves of `𝒪`-modules — every element is such a class, and two sheaves give the same
-- element precisely when they are isomorphic.
example (x : PicardGroup 𝒪 h𝒪) :
    ∃ (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) (_ : IsInvertible 𝒪 h𝒪 M),
      classOf 𝒪 h𝒪 M = x :=
  exists_classOf 𝒪 h𝒪 x

example [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N] :
    classOf 𝒪 h𝒪 L = classOf 𝒪 h𝒪 N ↔ Nonempty (L ≅ N) :=
  classOf_eq_classOf_iff 𝒪 h𝒪 L N

-- "abelian group structure", in both spellings the source uses.
example : CommGroup (PicardGroup 𝒪 h𝒪) := commGroup 𝒪 h𝒪

example : AddCommGroup (Additive (PicardGroup 𝒪 h𝒪)) := inferInstance

-- "addition is tensor product", in the source's own shape: the tensor product sheaf, and the
-- group written additively.
example [IsInvertible 𝒪 h𝒪 L] [IsInvertible 𝒪 h𝒪 N]
    [IsInvertible 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj
      (N)))] :
    Additive.ofMul (classOf 𝒪 h𝒪 L) + Additive.ofMul (classOf 𝒪 h𝒪 N) =
      Additive.ofMul (classOf 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (L)).obj
        (N)))) := by
  rw [← ofMul_mul, classOf_tensorSheaf]

end Faithfulness

end Stacks.SheafPicardGroup

end
