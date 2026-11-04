module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.End
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integer tensor powers of an invertible object of a monoidal category

Let `C` be a monoidal category and `L` an object of `C` carrying a two-sided tensor inverse
`L'`, i.e. isomorphisms `L ⊗ L' ≅ 𝟙_ C` and `L' ⊗ L ≅ 𝟙_ C`. This file constructs the integer
tensor powers `L ^⊗ n` for `n : ℤ`, together with the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, and deduces that every power again has a two-sided tensor
inverse, namely `L ^⊗ (-n)`.

This is the category-theoretic core of Stacks Tag 01CU; the sibling file
`StacksFrontier/AlgebraicGeometry/TensorPowers/Basic.lean` instantiates it at
`SheafOfModules` and the library's `AlgebraicGeometry.SheafOfModules.IsInvertible`.

## Main definitions

* `Stacks.TensorPowers.TensorInverse`: a two-sided tensor inverse of an object, as data.
* `Stacks.TensorPowers.natTensorPow`: the `n`-fold tensor product `(⋯ (𝟙_ ⊗ L) ⊗ ⋯) ⊗ L`, for
  `n : ℕ`.
* `Stacks.TensorPowers.intTensorPow`: the integer tensor power, `natTensorPow L n` in degree
  `n ≥ 0` and `natTensorPow L' (-n)` in degree `n < 0`. This is Stacks Tag 01CU's explicit
  formula, taken as the definition; `intTensorPow_natCast` and
  `intTensorPow_neg_natCast_succ` record that it is.
* `Stacks.TensorPowers.TensorInverse.succIso` and `Stacks.TensorPowers.TensorInverse.predIso`:
  the one-step comparisons `L ^⊗ (n + 1) ≅ L ^⊗ n ⊗ L` and `L ^⊗ (n - 1) ≅ L ^⊗ n ⊗ L'`. These
  are the only place where the inverse isomorphisms are used, and everything else is formal.

## Main results

* `Stacks.TensorPowers.TensorInverse.addIso`: **the addition law**
  `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, for all `n m : ℤ`.
* `Stacks.TensorPowers.TensorInverse.tensorInversePow`: **every integer tensor power again has
  a two-sided tensor inverse**, which is `L ^⊗ (-n)`.
* `Stacks.TensorPowers.TensorInverse.isEquivalence_tensorLeft` and
  `Stacks.TensorPowers.tensorInverseOfTensorLeft`: in a braided monoidal category, having a
  two-sided tensor inverse is equivalent to `MonoidalCategory.tensorLeft` being an equivalence
  of categories — the form in which invertibility is stated in this repository.
* `Stacks.TensorPowers.TensorInverse.tensor`: a tensor product of two objects with two-sided
  tensor inverses has one. This is the abstract form of clause (1) of Stacks Tag 01CT.

## Implementation notes

**Why the powers are not defined by iterating the equivalence.** Stacks Tag 01CU defines
`L ^⊗ n` as the image of the unit under `n` applications of the autoequivalence
`F ↦ F ⊗ L`, and Mathlib has `CategoryTheory.Equivalence.pow : (C ≌ C) → ℤ → (C ≌ C)` for
exactly this. That route is not taken: `Equivalence.pow` ships only `pow_zero`,
`pow_one` and `pow_neg_one`, has no `pow_add` and no successor lemma, and is applied nowhere in
Mathlib. Since the addition law is the entire content of the definition, iterating the
equivalence would still require an induction over `ℤ` crossing zero through the counit — the
same work, carried out on a less convenient definition. So the explicit formula is taken as the
definition and the addition law is proved from `succIso` and `predIso` by a single induction on
the second exponent.

**The shape of the induction.** `addIso` is *data*, so `Int.induction_on` is unavailable: it
eliminates into `Prop`. Instead `addNatIso` and `subNatIso` recurse structurally on a natural
number, and `addIso` splits `m : ℤ` into the two constructors with `rcases`, which compiles to
`Int.casesOn` and so does eliminate into a type.

**Transparency.** No transparency option is set, and none is needed: `natTensorPow` and
`intTensorPow` are plain structural recursions, and the one place where the elaborator will not
see through arithmetic on `Int` constructors — `Int.ofNat (k + 1) - 1`, whose reduction needs
`Nat.sub 1 (k + 1)` for a variable `k` — is bridged by `reindex` with an `omega`-proved index
equation rather than by relaxing transparency. `Int.ofNat k + 1`, `Int.negSucc k - 1` and
`Int.negSucc (k + 1) + 1` all do reduce, so the corresponding cases of `succIso` and `predIso`
are `Iso.refl`.

**Universes.** Fully polymorphic: `C : Type u` with `[Category.{v} C]`, with `u` and `v`
independent and no constraint between them.

## What is not done

The **associativity** constraint is now proved, in
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerAssoc.lean`:
`Stacks.TensorPowers.TensorInverse.addIso_assoc` gives it for an arbitrary integer *tridegree*,
carrying the snake compatibility `hs` of `L`'s two inverse laws as a hypothesis — which is free for
an invertible sheaf of modules, `AlgebraicGeometry.SheafOfModules.tensorInverse_snake`. The snake
itself at a tensor power is `Stacks.TensorPowers.TensorInverse.addIso_snake`.

The **commutativity** constraint is still not proved, and it cannot be proved here in the bare form
one might expect: `addIso 1 (-1)` is built from `predIso`, hence from `mulIso` alone, while
`addIso (-1) 1` is built from `succIso`, hence from `mulIso'` alone, so rescaling `mulIso'` by an
automorphism of the unit object breaks the equation while leaving everything else intact. Any
statement of it must carry `hs`, exactly as `addIso_assoc` does.

`Stacks.TensorPowers.TensorInverse` is data, not a `Prop`-valued class, so no two-sided tensor
inverse is canonical here; the bridge to the existential `Prop` used in this repository is in
the sibling file. No graded ring of sections is constructed — that is Stacks Tag 01CV. Its
associativity input is now available (`addIso_assoc` above); what it still needs is the
commutativity constraint.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A two-sided tensor inverse of `L`. -/
structure TensorInverse (L : C) where
  /-- The inverse object. -/
  inv : C
  /-- `L ⊗ inv ≅ 𝟙_ C`. -/
  mulIso : L ⊗ inv ≅ 𝟙_ C
  /-- `inv ⊗ L ≅ 𝟙_ C`. -/
  mulIso' : inv ⊗ L ≅ 𝟙_ C

/-- The natural-number tensor power. -/
def natTensorPow (L : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => natTensorPow L n ⊗ L

/-- The integer tensor power. -/
def intTensorPow (L L' : C) : ℤ → C
  | .ofNat n => natTensorPow L n
  | .negSucc n => natTensorPow L' (n + 1)

/-- The empty tensor product is the unit. -/
theorem natTensorPow_zero (L : C) : natTensorPow L 0 = 𝟙_ C := rfl

/-- One more factor of `L`. -/
theorem natTensorPow_succ (L : C) (n : ℕ) :
    natTensorPow L (n + 1) = natTensorPow L n ⊗ L := rfl

/-- The zeroth tensor power is the unit. -/
theorem intTensorPow_zero (L L' : C) : intTensorPow L L' 0 = 𝟙_ C := rfl

/-- For `n ≥ 0` the `n`-th integer tensor power is the `n`-fold tensor product of `L`. -/
theorem intTensorPow_natCast (L L' : C) (n : ℕ) :
    intTensorPow L L' (n : ℤ) = natTensorPow L n := rfl

/-- For `n < 0` the `n`-th integer tensor power is the `|n|`-fold tensor product of `L'`. -/
theorem intTensorPow_neg_natCast_succ (L L' : C) (n : ℕ) :
    intTensorPow L L' (-((n : ℤ) + 1)) = natTensorPow L' (n + 1) := rfl

/-- `L ^⊗ 0 ≅ 𝟙_ C`. -/
def zeroIso (L L' : C) : intTensorPow L L' 0 ≅ 𝟙_ C := Iso.refl _

/-- `L ^⊗ 1 ≅ L`. -/
def oneIso (L L' : C) : intTensorPow L L' 1 ≅ L := λ_ L

/-- `L ^⊗ (-1) ≅ L'`. -/
def negOneIso (L L' : C) : intTensorPow L L' (-1) ≅ L' := λ_ L'

/-- Reindexing. -/
def reindex (L L' : C) {n m : ℤ} (h : n = m) : intTensorPow L L' n ≅ intTensorPow L L' m :=
  eqToIso (by rw [h])

namespace TensorInverse

variable {L : C} (h : TensorInverse L)

/-- `L ^⊗ (n+1) ≅ L ^⊗ n ⊗ L`. -/
noncomputable def succIso (n : ℤ) :
    intTensorPow L h.inv (n + 1) ≅ intTensorPow L h.inv n ⊗ L := by
  rcases n with k | k
  · exact Iso.refl _
  · cases k with
    | zero =>
        exact (α_ (𝟙_ C) h.inv L ≪≫ whiskerLeftIso (𝟙_ C) h.mulIso' ≪≫ λ_ (𝟙_ C)).symm
    | succ k =>
        exact (α_ (natTensorPow h.inv (k + 1)) h.inv L ≪≫
          whiskerLeftIso _ h.mulIso' ≪≫ ρ_ _).symm

/-- `L ^⊗ (n-1) ≅ L ^⊗ n ⊗ L⁻¹`. -/
noncomputable def predIso (n : ℤ) :
    intTensorPow L h.inv (n - 1) ≅ intTensorPow L h.inv n ⊗ h.inv := by
  rcases n with k | k
  · cases k with
    | zero => exact Iso.refl _
    | succ k =>
        exact reindex L h.inv (show ((k : ℤ) + 1) - 1 = (k : ℤ) by omega) ≪≫
          (α_ (natTensorPow L k) L h.inv ≪≫ whiskerLeftIso _ h.mulIso ≪≫ ρ_ _).symm
  · exact Iso.refl _

/-- The addition law for a nonnegative second exponent. -/
@[ega "0 5.4.4" "partial"]
noncomputable def addNatIso (n : ℤ) : (k : ℕ) →
    intTensorPow L h.inv n ⊗ intTensorPow L h.inv (k : ℤ) ≅
      intTensorPow L h.inv (n + (k : ℤ))
  | 0 => ρ_ _ ≪≫ reindex L h.inv (by omega)
  | k + 1 =>
      whiskerLeftIso _ (h.succIso (k : ℤ)) ≪≫
        (α_ _ _ _).symm ≪≫ whiskerRightIso (addNatIso n k) L ≪≫
          (h.succIso (n + (k : ℤ))).symm ≪≫ reindex L h.inv (by omega)

/-- The addition law for a nonpositive second exponent. -/
@[ega "0 5.4.4" "partial"]
noncomputable def subNatIso (n : ℤ) : (k : ℕ) →
    intTensorPow L h.inv n ⊗ intTensorPow L h.inv (-(k : ℤ)) ≅
      intTensorPow L h.inv (n - (k : ℤ))
  | 0 => ρ_ _ ≪≫ reindex L h.inv (by omega)
  | k + 1 =>
      whiskerLeftIso _ (reindex L h.inv (show -((k : ℤ) + 1) = -(k : ℤ) - 1 by omega) ≪≫
          h.predIso (-(k : ℤ))) ≪≫
        (α_ _ _ _).symm ≪≫ whiskerRightIso (subNatIso n k) h.inv ≪≫
          (h.predIso (n - (k : ℤ))).symm ≪≫ reindex L h.inv (by omega)

/-- **The addition law for integer tensor powers.** -/
@[ega "0 5.4.4" "more general"]
noncomputable def addIso (n m : ℤ) :
    intTensorPow L h.inv n ⊗ intTensorPow L h.inv m ≅ intTensorPow L h.inv (n + m) := by
  rcases m with k | k
  · exact h.addNatIso n k
  · exact whiskerLeftIso _ (reindex L h.inv
        (show (Int.negSucc k : ℤ) = -((k : ℤ) + 1) from Int.negSucc_eq k)) ≪≫
      h.subNatIso n (k + 1) ≪≫ reindex L h.inv (by omega)

/-- **Every integer tensor power of an invertible object is invertible**, the inverse of
`L ^⊗ n` being `L ^⊗ (-n)`. -/
noncomputable def tensorInversePow (n : ℤ) : TensorInverse (intTensorPow L h.inv n) where
  inv := intTensorPow L h.inv (-n)
  mulIso := h.addIso n (-n) ≪≫ reindex L h.inv (by omega) ≪≫ zeroIso L h.inv
  mulIso' := h.addIso (-n) n ≪≫ reindex L h.inv (by omega) ≪≫ zeroIso L h.inv

include h in
/-- Tensoring on the left by an object with a two-sided tensor inverse is an equivalence. -/
theorem isEquivalence_tensorLeft : (tensorLeft L).IsEquivalence :=
  CategoryTheory.Equivalence.isEquivalence_functor
    (CategoryTheory.Equivalence.mk (tensorLeft L) (tensorLeft h.inv)
      ((leftUnitorNatIso C).symm ≪≫ ((tensoringLeft C).mapIso h.mulIso').symm ≪≫
        tensorLeftTensor h.inv L)
      ((tensorLeftTensor L h.inv).symm ≪≫ (tensoringLeft C).mapIso h.mulIso ≪≫
        leftUnitorNatIso C))

end TensorInverse

section Braided

variable [BraidedCategory C]

/-- Conversely, if tensoring on the left by `L` is an equivalence then `L` has a two-sided
tensor inverse, namely the image of the unit under the inverse equivalence. -/
noncomputable def tensorInverseOfTensorLeft (L : C) [(tensorLeft L).IsEquivalence] :
    TensorInverse L where
  inv := (tensorLeft L).inv.obj (𝟙_ C)
  mulIso := (tensorLeft L).asEquivalence.counitIso.app (𝟙_ C)
  mulIso' := β_ _ _ ≪≫ (tensorLeft L).asEquivalence.counitIso.app (𝟙_ C)

/-- A tensor product of two objects with two-sided tensor inverses again has one. -/
noncomputable def TensorInverse.tensor {L N : C} (h : TensorInverse L) (k : TensorInverse N) :
    TensorInverse (L ⊗ N) := by
  letI := h.isEquivalence_tensorLeft
  letI := k.isEquivalence_tensorLeft
  letI : (tensorLeft (L ⊗ N)).IsEquivalence :=
    Functor.isEquivalence_of_iso (tensorLeftTensor L N).symm
  exact tensorInverseOfTensorLeft (L ⊗ N)

end Braided

end Stacks.TensorPowers
