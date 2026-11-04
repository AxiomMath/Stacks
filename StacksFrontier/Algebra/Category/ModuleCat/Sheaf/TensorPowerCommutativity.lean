module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerInteger
public import StacksCore.Tactic.StacksAttribute

/-!
# Commutativity of the canonical multiplication on the integer tensor powers

Let `L` be an invertible object of a symmetric monoidal category `D`, so that `- ⊗ L` is an
autoequivalence, and let `L^{⊗ n} = ((- ⊗ L) ^ n).obj (𝟙_ D)` be its integer tensor powers.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerInteger` constructs the canonical
multiplication `mul L n m p : L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ p}` of Tag 01CU and proves three of the
four normalisations the source asserts for it: the two unit constraints, the degree-`(n, 1)`
normalisation by the defining iteration, and associativity against the associativity constraint.
This file proves the fourth, **commutativity against the symmetry constraint**, and then assembles
all of them into the coherence package which Tag 01CU asserts to exist.

Commutativity is *not* a consequence of the symmetric monoidal axioms: an invertible object of a
general symmetric monoidal category satisfies only `β ≫ β = 𝟙`, and the odd line in super vector
spaces has `β = -𝟙`. The missing input is the rank-one local structure of an invertible sheaf of
modules, available as `Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints`, and it is needed **only in
the single degree `(1, 1)`**: `braiding_eq_mulSwap` derives every other degree from it.

## Main definitions

* `Stacks.MonoidalCategory.mulSwap`: the **canonical swap**
  `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ m} ⊗ L^{⊗ n}`, the canonical multiplication in one order followed by
  the inverse of the canonical multiplication in the other. Commutativity says exactly that this
  is the symmetry constraint.
* `Stacks.MonoidalCategory.powReindex` and `powOf`, `powReindexOf`, `powSuccIsoOf`: reindexing of
  tensor powers, and the tensor powers, their reindexing and their successor comparison computed
  from a right-tensor functor presented abstractly rather than as `tensorRight L`.
* `Stacks.MonoidalCategory.PowCoherence`: the coherence package of Tag 01CU, for tensor powers
  computed from such an abstract functor.
* `Stacks.SheafOfModules.TensorPower.TensorPowerCoherence`: that package in the vocabulary of the
  tensor product sheaf of Tag 01CA — the unit, associativity and symmetry constraints built from
  sheafification in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`.

## Main results

* `Stacks.MonoidalCategory.mulSwap_hexagon`: **the canonical swap satisfies the forward hexagon
  identity.** This is the whole content of `Stacks.MonoidalCategory.mul_assoc` read as a statement
  about the swap, and it is three applications of associativity of the canonical multiplication,
  in the degrees `(n, m, k)`, `(m, n, k)` and `(m, k, n)`. No braiding occurs in it, and no
  induction on the exponents is needed.
* `Stacks.MonoidalCategory.braiding_eq_mulSwap_add` and `braiding_eq_mulSwap_cancel`:
  **the normalisation is additive in its second exponent, and cancellable.** Comparing
  `mulSwap_hexagon` with the hexagon law for the symmetry constraint turns a statement in the
  degrees `(n, m)` and `(n, k)` into one in the degree `(n, m + k)`, and conversely. The
  cancellation form is what carries the induction into the negative exponents, and it needs
  faithfulness of left whiskering by a tensor power (`whiskerLeft_pow_injective`).
* `Stacks.MonoidalCategory.braiding_eq_mulSwap`: **the symmetry constraint on
  `L^{⊗ n} ⊗ L^{⊗ m}` is the canonical swap**, given that it is the identity in the degree
  `(1, 1)`. It is two runs of the one-variable induction `braiding_eq_mulSwap_of_one`: the first
  at `n = 1`, started by the degree-`(1, 1)` hypothesis, the second at a general `n`, started by
  the degree `(n, 1)` case, which is the degree `(1, n)` case of the first row read backwards.
* `Stacks.MonoidalCategory.mul_comm` and
  `Stacks.SheafOfModules.TensorPower.mulIso_comm`: **commutativity of the canonical
  multiplication**, in the abstract monoidal setting and for the tensor product sheaf.
* `Stacks.SheafOfModules.TensorPower.braiding_pow_one_self_eq_id`: the degree-`(1, 1)` input,
  supplied for an invertible sheaf of modules.
* `Stacks.MonoidalCategory.nonempty_powCoherence` and
  `Stacks.SheafOfModules.TensorPower.tensorPowerCoherence_exists`: **the coherence package of
  Tag 01CU is inhabited** — a multiplication on the integer tensor powers satisfying all four
  normalisations, together with naturality of the successor comparison and invertibility of every
  power.

## Implementation notes

What is *forced*. The degree-`(1, 1)` hypothesis of `braiding_eq_mulSwap` cannot be dropped, by
the super-vector-space counterexample above. Symmetry of the braiding is used in exactly one
place, `braiding_eq_mulSwap_symm`, and is taken there as the hypothesis
`hsym : ∀ X Y, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _` rather than as a `SymmetricCategory` instance,
so that no second `BraidedCategory` instance is ever in play: for sheaves of modules the braiding
is `Stacks.SheafOfModules.Strict.braidedCategory` and the lemmas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence` are stated against it, while
`Strict.symmetricCategory` would supply a second, definitionally equal but syntactically distinct
one. The universes are those of `TensorPowerInteger`: the site `C : Type u` with `Category.{v} C`
is arbitrary, while the ring sheaf and the modules share the single universe `w`. **Nothing is
narrowed**; in particular no `GrothendieckTopology.HasSheafCompose` hypothesis is used, and
`tensorPowerCoherence_exists` asks only for `Stacks.SheafOfModules.IsInvertible` and the
hypothesis under which the tensor powers of Tag 01CU are defined.

Also *forced*: the abstraction over the right-tensor functor in `PowCoherence`. Tag 01CU builds
its tensor powers from the right-tensor functor
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L`, the sheafification of the objectwise
tensor product, while the multiplication is built from
`CategoryTheory.MonoidalCategory.tensorRight`. The two functors are *equal*
(`tensorRightFunctor_eq`) but not definitionally so, and for a negative exponent the power applies
the quasi-inverse *chosen for the functor it is given*, so `tensorPower O hO L n` and `pow L n`
are equal objects with no common normal form. Stating the coherence package for an abstract `F`
together with `F = tensorRight L` lets a single `subst` discharge the whole transport, so no
`eqToIso` conjugation appears anywhere; the two `HEq` hypotheses of `nonempty_powCoherence` are
the price, and they are discharged by `heq_of_eq` because at the two functors of interest the
types coincide definitionally.

What is *chosen*: the **spelling discipline** inherited from `TensorPowerInteger`. Every statement
is at the level of morphisms or of isomorphisms between named objects, the exponent targets are
carried as an explicit argument with an equation (`mul L n m p h`) so that no reindexing
isomorphism appears in `mulSwap_hexagon`, and `powReindexOf` is defined as the transport
isomorphism rather than by `subst`, which is what makes it definitionally the reindexing used by
the monoidal development and provably (`powReindexOf_eq_tensorPowerReindex`) the one used by
`tensorPowerReindex`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.MonoidalCategory

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

section Swap

variable (L : D) [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence]

/-- The **canonical swap** of two tensor powers: the composite
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ p} ≅ L^{⊗ m} ⊗ L^{⊗ n}` of the canonical multiplication in one order
with the inverse of the canonical multiplication in the other. -/
noncomputable def mulSwap (n m p : ℤ) (h : n + m = p) :
    pow L n ⊗ pow L m ≅ pow L m ⊗ pow L n :=
  mul L n m p h ≪≫ (mul L m n p (by omega)).symm

/-- The forward map of `mulSwap L n m p h` is the multiplication `(mul L n m p h).hom` followed
by the inverse of `mul L m n p h'`, for any proof `h'` of `m + n = p`. -/
theorem mulSwap_hom (n m p : ℤ) (h : n + m = p) (h' : m + n = p) :
    (mulSwap L n m p h).hom = (mul L n m p h).hom ≫ (mul L m n p h').inv := rfl

/-- The canonical swaps in the two orders are mutually inverse. -/
theorem mulSwap_symm (n m p : ℤ) (h : n + m = p) (h' : m + n = p) :
    (mulSwap L m n p h').hom = (mulSwap L n m p h).inv := rfl

/-- Composing the forward map of `mulSwap L n m p h` with `(mul L m n p h').hom` gives
`(mul L n m p h).hom`. -/
theorem mulSwap_hom_comp (n m p : ℤ) (h : n + m = p) (h' : m + n = p) :
    (mulSwap L n m p h).hom ≫ (mul L m n p h').hom = (mul L n m p h).hom := by
  rw [mulSwap_hom L n m p h h', Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **In equal degrees the canonical swap is the identity**, because it is the composite of one
and the same multiplication isomorphism with its own inverse. -/
theorem mulSwap_self (n p : ℤ) (h : n + n = p) : (mulSwap L n n p h).hom = 𝟙 _ :=
  (mul L n n p h).hom_inv_id

/-- Reindexing a tensor power along an equality of exponents. -/
noncomputable def powReindex {n m : ℤ} (h : n = m) : pow L n ≅ pow L m :=
  eqToIso (congrArg (pow L) h)

/-- Reindexing the target of the canonical multiplication is absorbed by the exponent target. -/
theorem mul_reindex (n m p p' : ℤ) (h : n + m = p) (h' : p = p') (h'' : n + m = p') :
    mul L n m p h ≪≫ powReindex L h' = mul L n m p' h'' := by
  subst h'
  exact Iso.trans_refl _

/-- Tensoring on the right by a tensor power is an autoequivalence: it is isomorphic, by
`powFunctorIso`, to the corresponding power of the autoequivalence `- ⊗ L`. -/
theorem isEquivalence_tensorRight_pow (m : ℤ) :
    (CategoryTheory.MonoidalCategory.tensorRight (pow L m)).IsEquivalence :=
  Functor.isEquivalence_of_iso (powFunctorIso L m)

/-- **The canonical swap satisfies the forward hexagon identity.** This is the whole content of
`mul_assoc`, read as a statement about the swap rather than about the multiplication: it is three
applications of associativity of the canonical multiplication, in the degrees `(n, m, k)`,
`(m, n, k)` and `(m, k, n)`. Note that no braiding occurs, and no induction on the exponents is
needed; the hexagon for the symmetry constraint is a law, and comparing the two is what the
commutativity normalisation reduces to. -/
theorem mulSwap_hexagon (n m k p q t s : ℤ)
    (h₁ : n + m = p) (hq : n + k = q) (h₂ : m + k = t) (hs : n + t = s) :
    (pow L n ◁ (mul L m k t h₂).hom) ≫ (mulSwap L n t s hs).hom =
      (α_ (pow L n) (pow L m) (pow L k)).inv ≫ ((mulSwap L n m p h₁).hom ▷ pow L k) ≫
        (α_ (pow L m) (pow L n) (pow L k)).hom ≫
          (pow L m ◁ (mulSwap L n k q hq).hom) ≫
            (α_ (pow L m) (pow L k) (pow L n)).inv ≫ ((mul L m k t h₂).hom ▷ pow L n) := by
  have hpk : p + k = s := by omega
  have htn : t + n = s := by omega
  have hmn : m + n = p := by omega
  have hkn : k + n = q := by omega
  have A2 : ((mul L m n p hmn).hom ▷ pow L k) ≫ (mul L p k s hpk).hom =
      (α_ (pow L m) (pow L n) (pow L k)).hom ≫ (pow L m ◁ (mul L n k q hq).hom) ≫
        (mul L m q s (by omega)).hom := mul_assoc L m n k p q s hmn hq hpk
  rw [← cancel_mono (mul L t n s htn).hom]
  simp only [Category.assoc]
  rw [mulSwap_hom_comp L n t s hs htn, mul_assoc L m k n t q s h₂ hkn htn, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, mulSwap_hom_comp L n k q hq hkn, ← A2, ← comp_whiskerRight_assoc,
    mulSwap_hom_comp L n m p h₁ hmn, mul_assoc L n m k p t s h₁ h₂ hpk, Iso.inv_hom_id_assoc]

end Swap

section Braided

variable [BraidedCategory D] (L : D)
  [(CategoryTheory.MonoidalCategory.tensorRight L).IsEquivalence]

/-- Left whiskering by a tensor power is injective on morphisms: tensoring by a tensor power is an
autoequivalence, hence faithful, and the braiding turns left whiskering into right whiskering. -/
theorem whiskerLeft_pow_injective (m : ℤ) {X Y : D} {f g : X ⟶ Y}
    (h : pow L m ◁ f = pow L m ◁ g) : f = g := by
  have := isEquivalence_tensorRight_pow L m
  have h2 : f ▷ pow L m = g ▷ pow L m := by
    rw [← cancel_epi (β_ (pow L m) X).hom,
      ← BraidedCategory.braiding_naturality_right (pow L m) f,
      ← BraidedCategory.braiding_naturality_right (pow L m) g, h]
  exact (CategoryTheory.MonoidalCategory.tensorRight (pow L m)).map_injective h2

/-- The forward hexagon identity for the symmetry constraint, conjugated by the canonical
multiplication so that it has exactly the shape of `mulSwap_hexagon`. It is
`BraidedCategory.braiding_tensor_right_hom` together with naturality of the braiding. -/
theorem braiding_hexagon (n m k t : ℤ) (h₂ : m + k = t) :
    (pow L n ◁ (mul L m k t h₂).hom) ≫ (β_ (pow L n) (pow L t)).hom =
      (α_ (pow L n) (pow L m) (pow L k)).inv ≫ ((β_ (pow L n) (pow L m)).hom ▷ pow L k) ≫
        (α_ (pow L m) (pow L n) (pow L k)).hom ≫
          (pow L m ◁ (β_ (pow L n) (pow L k)).hom) ≫
            (α_ (pow L m) (pow L k) (pow L n)).inv ≫ ((mul L m k t h₂).hom ▷ pow L n) := by
  rw [BraidedCategory.braiding_naturality_right,
    BraidedCategory.braiding_tensor_right_hom (pow L n) (pow L m) (pow L k)]
  simp only [Category.assoc]

/-- **The commutativity normalisation is additive in its second exponent.** If the symmetry
constraint is the canonical swap in the degrees `(n, m)` and `(n, k)` then it is the canonical
swap in the degree `(n, m + k)`. Both hexagons are consumed here, one for each of the two maps
being compared. -/
theorem braiding_eq_mulSwap_add (n m k p q t s : ℤ)
    (h₁ : n + m = p) (hq : n + k = q) (h₂ : m + k = t) (hs : n + t = s)
    (hm : (β_ (pow L n) (pow L m)).hom = (mulSwap L n m p h₁).hom)
    (hk : (β_ (pow L n) (pow L k)).hom = (mulSwap L n k q hq).hom) :
    (β_ (pow L n) (pow L t)).hom = (mulSwap L n t s hs).hom := by
  have e1 := braiding_hexagon L n m k t h₂
  rw [hm, hk, ← mulSwap_hexagon L n m k p q t s h₁ hq h₂ hs] at e1
  exact (cancel_epi (pow L n ◁ (mul L m k t h₂).hom)).mp e1

/-- The cancellation form of `braiding_eq_mulSwap_add`, which carries the induction into the
negative exponents: the normalisation in the degrees `(n, m)` and `(n, m + k)` gives it in the
degree `(n, k)`. -/
theorem braiding_eq_mulSwap_cancel (n m k p q t s : ℤ)
    (h₁ : n + m = p) (hq : n + k = q) (h₂ : m + k = t) (hs : n + t = s)
    (hm : (β_ (pow L n) (pow L m)).hom = (mulSwap L n m p h₁).hom)
    (ht : (β_ (pow L n) (pow L t)).hom = (mulSwap L n t s hs).hom) :
    (β_ (pow L n) (pow L k)).hom = (mulSwap L n k q hq).hom := by
  have e1 := braiding_hexagon L n m k t h₂
  rw [hm, ht, mulSwap_hexagon L n m k p q t s h₁ hq h₂ hs, Iso.cancel_iso_inv_left,
    cancel_epi, Iso.cancel_iso_hom_left, cancel_mono] at e1
  exact (whiskerLeft_pow_injective L m e1).symm

/-- **The commutativity normalisation in the degrees `(n, 0)`**: multiplication by the zeroth
tensor power is the unit constraint in either order, and the symmetry constraint at the tensor
unit is `BraidedCategory.braiding_tensorUnit_right`. -/
theorem braiding_eq_mulSwap_zero (n p : ℤ) (h : n + 0 = p) :
    (β_ (pow L n) (pow L 0)).hom = (mulSwap L n 0 p h).hom := by
  have hp : n = p := by omega
  subst hp
  rw [mulSwap_hom L n 0 n h (by omega), mul_zero_right L n h, mul_zero_left L n (by omega)]
  exact braiding_tensorUnit_right (pow L n)

/-- **The row induction.** If the commutativity normalisation holds in the degree `(n, 1)` then it
holds in the degree `(n, m)` for every integer `m`: the non-negative exponents are reached from
the degree `(n, 0)` by `braiding_eq_mulSwap_add` and the negative ones from it by
`braiding_eq_mulSwap_cancel`. -/
theorem braiding_eq_mulSwap_of_one (n : ℤ)
    (h1 : (β_ (pow L n) (pow L 1)).hom = (mulSwap L n 1 (n + 1) rfl).hom) :
    ∀ (m p : ℤ) (h : n + m = p), (β_ (pow L n) (pow L m)).hom = (mulSwap L n m p h).hom := by
  intro m
  induction m using Int.induction_on with
  | zero => exact braiding_eq_mulSwap_zero L n
  | succ i ih =>
    exact fun p h => braiding_eq_mulSwap_add L n (i : ℤ) 1 (n + (i : ℤ)) (n + 1) ((i : ℤ) + 1) p
      rfl rfl rfl h (ih (n + (i : ℤ)) rfl) h1
  | pred i ih =>
    exact fun p h => braiding_eq_mulSwap_cancel L n 1 (-(i : ℤ) - 1) (n + 1) p (-(i : ℤ))
      (n + -(i : ℤ)) rfl h (by omega) rfl h1 (ih (n + -(i : ℤ)) rfl)

/-- The commutativity normalisation is symmetric in its two exponents: the symmetry constraint and
the canonical swap are both reversed by exchanging them. This is the only place the braiding is
required to be a *symmetry*; `hsym` is `CategoryTheory.SymmetricCategory.symmetry`, taken as a
hypothesis rather than as an instance so that no second `BraidedCategory` instance is in play. -/
theorem braiding_eq_mulSwap_symm (hsym : ∀ X Y : D, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y))
    (n m p : ℤ) (h : n + m = p) (h' : m + n = p)
    (hnm : (β_ (pow L n) (pow L m)).hom = (mulSwap L n m p h).hom) :
    (β_ (pow L m) (pow L n)).hom = (mulSwap L m n p h').hom := by
  rw [Iso.inv_ext' (hsym (pow L n) (pow L m)), mulSwap_symm L n m p h h', Iso.ext hnm]

/-- **The commutativity normalisation of Tag 01CU, in every pair of degrees.** The symmetry
constraint on `L^{⊗ n} ⊗ L^{⊗ m}` is the canonical swap, provided it is the identity in the degree
`(1, 1)` — which is *not* a consequence of the symmetric monoidal axioms, and is where the
rank-one local structure of an invertible sheaf of modules enters.

The proof is two rows of `braiding_eq_mulSwap_of_one`: the first, at `n = 1`, is started by the
degree `(1, 1)` hypothesis; the second, at a general `n`, is started by the degree `(n, 1)` case,
which is the degree `(1, n)` case of the first row read backwards. -/
theorem braiding_eq_mulSwap (hsym : ∀ X Y : D, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y))
    (hβ : (β_ (pow L 1) (pow L 1)).hom = 𝟙 (pow L 1 ⊗ pow L 1))
    (n m p : ℤ) (h : n + m = p) :
    (β_ (pow L n) (pow L m)).hom = (mulSwap L n m p h).hom :=
  braiding_eq_mulSwap_of_one L n
    (braiding_eq_mulSwap_symm L hsym 1 n (n + 1) (by omega) rfl
      (braiding_eq_mulSwap_of_one L 1 (hβ.trans (mulSwap_self L 1 (1 + 1) rfl).symm)
        n (n + 1) (by omega))) m p h

/-- **Commutativity of the canonical multiplication on the integer tensor powers**, against the
symmetry constraint of the monoidal category. This is the last of the normalisations asserted by
Tag 01CU. -/
theorem mul_comm (hsym : ∀ X Y : D, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y))
    (hβ : (β_ (pow L 1) (pow L 1)).hom = 𝟙 (pow L 1 ⊗ pow L 1))
    (n m p : ℤ) (h : n + m = p) (h' : m + n = p) :
    mul L n m p h = β_ (pow L n) (pow L m) ≪≫ mul L m n p h' := by
  refine Iso.ext ?_
  rw [Iso.trans_hom, braiding_eq_mulSwap L hsym hβ n m p h]
  exact (mulSwap_hom_comp L n m p h h').symm

/-! ### The coherence package, for a right-tensor functor presented abstractly

Tag 01CU builds the tensor powers from a functor `F` which *is* `- ⊗ L` but is given by another
formula — for sheaves of modules, the sheafification of the objectwise tensor product. The two
functors are equal (`Stacks.SheafOfModules.TensorPower.tensorRightFunctor_eq`) but not
definitionally so, and for a negative exponent `F ^ n` applies the quasi-inverse *chosen for `F`*,
so `powOf F n` and `pow L n` are equal objects with no common normal form. Everything below is
therefore stated for an abstract `F` together with the equation `F = tensorRight L`, which a
single `subst` discharges; the consumer never has to transport along the equality of objects. -/

/-- The `n`th tensor power computed from a right-tensor functor presented abstractly. -/
noncomputable def powOf (F : D ⥤ D) [F.IsEquivalence] (n : ℤ) : D :=
  (F.asEquivalence ^ n).functor.obj (𝟙_ D)

/-- Reindexing abstract tensor powers along an equality of exponents. -/
noncomputable def powReindexOf (F : D ⥤ D) [F.IsEquivalence] {n m : ℤ} (h : n = m) :
    powOf F n ≅ powOf F m :=
  eqToIso (congrArg (powOf F) h)

/-- The successor comparison for abstract tensor powers: the comparison of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower`, whose source is written using `F`
rather than the tensor product. -/
noncomputable def powSuccIsoOf (F : D ⥤ D) [F.IsEquivalence] (n : ℤ) :
    F.obj (powOf F n) ≅ powOf F (n + 1) :=
  Stacks.Equivalence.powSuccIso F.asEquivalence n (𝟙_ D)

/-- **The coherence package of Tag 01CU**, for tensor powers computed from an abstract
right-tensor functor `F`. The datum `τ` identifies `- ⊗ L^{⊗ 1}` with `F`; it is what lets the
degree-`(n, 1)` normalisation be stated without knowing that `F` is `- ⊗ L`. -/
structure PowCoherence (F : D ⥤ D) [F.IsEquivalence] (τ : ∀ X : D, X ⊗ powOf F 1 ≅ F.obj X) where
  /-- Multiplication of tensor powers adds their exponents. -/
  mulIso (n m : ℤ) : powOf F n ⊗ powOf F m ≅ powOf F (n + m)
  /-- Left multiplication by the zeroth power is the left unit constraint. -/
  mul_zero_left (n : ℤ) :
    mulIso 0 n ≪≫ powReindexOf F (Int.zero_add n) = λ_ (powOf F n)
  /-- Right multiplication by the zeroth power is the right unit constraint. -/
  mul_zero_right (n : ℤ) :
    mulIso n 0 ≪≫ powReindexOf F (Int.add_zero n) = ρ_ (powOf F n)
  /-- Multiplication by the first power is one more iteration of `F`. -/
  mul_one_right (n : ℤ) : mulIso n 1 = τ (powOf F n) ≪≫ powSuccIsoOf F n
  /-- Multiplication respects the associativity constraint. -/
  mul_assoc (n m k : ℤ) :
    whiskerRightIso (mulIso n m) (powOf F k) ≪≫ mulIso (n + m) k =
      α_ (powOf F n) (powOf F m) (powOf F k) ≪≫
        whiskerLeftIso (powOf F n) (mulIso m k) ≪≫ mulIso n (m + k) ≪≫
          powReindexOf F (Int.add_assoc n m k).symm
  /-- Multiplication respects the symmetry constraint. -/
  mul_comm (n m : ℤ) :
    mulIso n m =
      β_ (powOf F n) (powOf F m) ≪≫ mulIso m n ≪≫ powReindexOf F (Int.add_comm m n)

/-- **The coherence package of Tag 01CU is inhabited**, for tensor powers computed from any
functor which is equal to right-tensoring by `L` and any `τ` which is the first-power
identification. The two `HEq`s are the price of the abstraction: before `F` is known to be
`tensorRight L` the two sides do not have the same type, and after the `subst` they do. -/
theorem nonempty_powCoherence (F : D ⥤ D) [F.IsEquivalence]
    (τ : ∀ X : D, X ⊗ powOf F 1 ≅ F.obj X)
    (hF : F = CategoryTheory.MonoidalCategory.tensorRight L)
    (hτ : HEq τ fun X : D => whiskerLeftIso X (powOneIso L))
    (hsym : ∀ X Y : D, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y))
    (hβ : (β_ (pow L 1) (pow L 1)).hom = 𝟙 (pow L 1 ⊗ pow L 1)) :
    Nonempty (PowCoherence F τ) := by
  subst hF
  obtain rfl := eq_of_heq hτ
  refine ⟨{ mulIso := fun n m => mul L n m (n + m) rfl
            mul_zero_left := fun n => ?_
            mul_zero_right := fun n => ?_
            mul_one_right := fun n => ?_
            mul_assoc := fun n m k => ?_
            mul_comm := fun n m => ?_ }⟩
  · exact (mul_reindex L 0 n (0 + n) n rfl (Int.zero_add n) (Int.zero_add n)).trans
      (mul_zero_left L n (Int.zero_add n))
  · exact (mul_reindex L n 0 (n + 0) n rfl (Int.add_zero n) (Int.add_zero n)).trans
      (mul_zero_right L n (Int.add_zero n))
  · show mul L n 1 (n + 1) rfl =
      whiskerLeftIso (pow L n) (powOneIso L) ≪≫
        Stacks.Equivalence.powSuccIso (tensorRightEquiv L) n (𝟙_ D)
    rw [mul_one_right L n (n + 1) rfl, powSuccIso, powSuccFunctorIso]
    exact congrArg (fun z => whiskerLeftIso (pow L n) (powOneIso L) ≪≫ z)
      (Stacks.Equivalence.powSucc_app (tensorRightEquiv L) n (𝟙_ D))
  · show whiskerRightIso (mul L n m (n + m) rfl) (pow L k) ≪≫ mul L (n + m) k (n + m + k) rfl =
      α_ (pow L n) (pow L m) (pow L k) ≪≫ whiskerLeftIso (pow L n) (mul L m k (m + k) rfl) ≪≫
        mul L n (m + k) (n + (m + k)) rfl ≪≫ powReindex L (Int.add_assoc n m k).symm
    rw [mul_reindex L n (m + k) (n + (m + k)) (n + m + k) rfl (Int.add_assoc n m k).symm
      (by omega)]
    exact Iso.ext (mul_assoc L n m k (n + m) (m + k) (n + m + k) rfl rfl rfl)
  · show mul L n m (n + m) rfl =
      β_ (pow L n) (pow L m) ≪≫ mul L m n (m + n) rfl ≪≫ powReindex L (Int.add_comm m n)
    rw [mul_reindex L m n (m + n) (n + m) rfl (Int.add_comm m n) (by omega)]
    exact mul_comm L hsym hβ n m (n + m) rfl (by omega)

end Braided

end Stacks.MonoidalCategory

namespace Stacks.SheafOfModules.TensorPower

open CategoryTheory MonoidalCategory Stacks.MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The symmetry constraint of the tensor product sheaf is a symmetry: this is
`Stacks.SheafOfModules.tensorSheafBraiding_trans_self`, read through
`Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding`. -/
theorem braiding_symmetry (M N : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (β_ M N).hom ≫ (β_ N M).hom = 𝟙 (M ⊗ N) := by
  rw [Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding O hO M N,
    Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding O hO N M]
  exact congrArg Iso.hom (Stacks.SheafOfModules.tensorSheafBraiding_trans_self O hO M N)

variable (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [Stacks.SheafOfModules.IsInvertible O hO L]
  [hRightEquivalence : (@CategoryTheory.MonoidalCategory.tensorRight _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory O hO) L).IsEquivalence]

/-- **The symmetry constraint on `L^{⊗ 1} ⊗ L^{⊗ 1}` is the identity.** This is the input the
commutativity normalisation of Tag 01CU genuinely needs, and it is not a consequence of the
symmetric monoidal axioms: the first tensor power is an invertible sheaf of modules, and
`Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl` -- whose proof is the rank-one local
structure of an invertible sheaf, in trace form -- says that the symmetry constraint of such a
sheaf with itself is the identity. -/
theorem braiding_pow_one_self_eq_id :
    (β_ (pow L 1) (pow L 1)).hom = 𝟙 (pow L 1 ⊗ pow L 1) := by
  have hinv : Stacks.SheafOfModules.IsInvertible O hO (pow L 1) :=
    tensorPower_eq_pow O hO L 1 ▸ Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
      O hO L 1
  exact congrArg Iso.hom
    ((Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding O hO (pow L 1) (pow L 1)).trans
      (Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl O hO (pow L 1)))

/-- **The commutativity normalisation of Tag 01CU**: the canonical multiplication on the integer
tensor powers of an invertible sheaf of modules agrees with itself after the symmetry constraint
of the tensor product sheaf. This was the last of the four normalisations of Tag 01CU still
outstanding. -/
@[stacks 01CU "commutativity of the canonical multiplication"]
theorem mulIso_comm (n m p : ℤ) (h : n + m = p) (h' : m + n = p) :
    mulIso O hO L n m p h =
      Stacks.SheafOfModules.tensorSheafBraiding O hO (pow L n) (pow L m) ≪≫
        mulIso O hO L m n p h' := by
  rw [mulIso, mulIso,
    ← Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding O hO (pow L n) (pow L m)]
  exact Stacks.MonoidalCategory.mul_comm L (braiding_symmetry O hO)
    (braiding_pow_one_self_eq_id O hO L) n m p h h'

omit [Stacks.SheafOfModules.IsInvertible O hO L] in
/-- The tensor product sheaf of an isomorphism with an identity is right whiskering. -/
theorem tensorSheafMapIso_refl_right
    {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (i : M ≅ M')
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorSheafMapIso O hO i (Iso.refl N) = whiskerRightIso i N := by
  refine Iso.ext ?_
  rw [Stacks.SheafOfModules.tensorSheafMapIso_hom_eq]
  exact MonoidalCategory.tensorHom_id i.hom N

omit [Stacks.SheafOfModules.IsInvertible O hO L] in
/-- The tensor product sheaf of an identity with an isomorphism is left whiskering. -/
theorem tensorSheafMapIso_refl_left
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (j : N ≅ N') :
    tensorSheafMapIso O hO (Iso.refl M) j = whiskerLeftIso M j := by
  refine Iso.ext ?_
  rw [Stacks.SheafOfModules.tensorSheafMapIso_hom_eq]
  exact MonoidalCategory.id_tensorHom M j.hom

omit [Stacks.SheafOfModules.IsInvertible O hO L] in
/-- The identification of the first tensor power with `L` is the left unit constraint of the
tensor product sheaf, hence the left unitor of the monoidal structure. -/
theorem tensorPowerOneIso_eq_powOneIso
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence] :
    tensorPowerOneIso O hO L = powOneIso L := by
  show tensorPowerOneIso O hO L = λ_ L
  rw [Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor]
  exact rfl

section Coherence

variable [hNativeEquivalence : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]

omit [Stacks.SheafOfModules.IsInvertible O hO L]
    hRightEquivalence in
/-- The abstract reindexing of `Stacks.MonoidalCategory.powReindexOf` is the reindexing of
tensor powers. Both are the transport isomorphism, by `tensorPowerReindex_eq_eqToIso`. -/
theorem powReindexOf_eq_tensorPowerReindex {n m : ℤ} (h : n = m) :
    @Stacks.MonoidalCategory.powReindexOf _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory O hO)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L)
        hNativeEquivalence n m h =
      tensorPowerReindex O hO L h :=
  (tensorPowerReindex_eq_eqToIso O hO L h).symm

/-- **The canonical coherent structure carried by the integer tensor powers of an invertible sheaf
of modules.** The multiplication isomorphisms are required to respect the fixed unit,
associativity and symmetry constraints of the tensor product sheaf of Tag 01CA, and to be the
successor comparison of the defining iteration in degree `(n, 1)`; that last normalisation is what
removes the cocycle ambiguity. None of the constraints is a choice: they are the ones built from
sheafification in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`. -/
structure TensorPowerCoherence where
  /-- Every integer tensor power is again invertible. -/
  isInvertible (n : ℤ) : Stacks.SheafOfModules.IsInvertible O hO (tensorPower O hO L n)
  /-- Multiplication of tensor powers adds their exponents. -/
  mulIso (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((tensorPower O hO L n))).obj ((tensorPower O hO L m))) ≅
      tensorPower O hO L (n + m)
  /-- Left multiplication by the zeroth power is the left unit constraint. -/
  mul_zero_left (n : ℤ) :
    mulIso 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      Stacks.SheafOfModules.tensorSheafLeftUnitor O hO (tensorPower O hO L n)
  /-- Right multiplication by the zeroth power is the right unit constraint. -/
  mul_zero_right (n : ℤ) :
    mulIso n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO (tensorPower O hO L n)
  /-- Multiplication by the first power is one more iteration of right tensoring, after
  identifying the first power with `L`. -/
  mul_one_right (n : ℤ) :
    mulIso n 1 =
      tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n)) (tensorPowerOneIso O hO L) ≪≫
        tensorPowerSuccIso O hO L n
  /-- The successor comparison is natural in the sheaf the iterated autoequivalence acts on. -/
  pow_succ_natural (n : ℤ) {M N : SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
      (f : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).map
        ((tensorPowerEquivalence O hO L n).functor.map f) ≫
        (Stacks.Equivalence.powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L).asEquivalence n N).hom =
      (Stacks.Equivalence.powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L).asEquivalence n M).hom ≫
        (tensorPowerEquivalence O hO L (n + 1)).functor.map f
  /-- Multiplication respects the associativity constraint of the tensor product sheaf. -/
  mul_assoc (n m k : ℤ) :
    tensorSheafMapIso O hO (mulIso n m) (Iso.refl (tensorPower O hO L k)) ≪≫
        mulIso (n + m) k =
      Stacks.SheafOfModules.tensorSheafAssociator O hO (tensorPower O hO L n)
          (tensorPower O hO L m) (tensorPower O hO L k) ≪≫
        tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n)) (mulIso m k) ≪≫
        mulIso n (m + k) ≪≫
        tensorPowerReindex O hO L (Int.add_assoc n m k).symm
  /-- Multiplication respects the symmetry constraint of the tensor product sheaf. -/
  mul_comm (n m : ℤ) :
    mulIso n m =
      Stacks.SheafOfModules.tensorSheafBraiding O hO (tensorPower O hO L n)
          (tensorPower O hO L m) ≪≫
        mulIso m n ≪≫ tensorPowerReindex O hO L (Int.add_comm m n)

omit hRightEquivalence in
/-- **The canonical multiplication on the integer tensor powers of an invertible sheaf of modules
exists and satisfies every normalisation asserted by Tag 01CU**: the two unit constraints, the
degree-`(n, 1)` normalisation by the defining iteration, naturality of that comparison,
associativity against the associativity constraint of the tensor product sheaf, and commutativity
against its symmetry constraint.

The multiplication is transported from `Stacks.MonoidalCategory.mul` by
`Stacks.MonoidalCategory.nonempty_powCoherence`, which is what absorbs the fact that the tensor
powers of Tag 01CU are built from `(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L` while
the multiplication is built from `tensorRight`: the two functors are equal but their chosen
quasi-inverses, used by the negative exponents, have no common normal form. -/
@[stacks 01CU "canonical multiplication and coherence", ega "0 5.4.4" "partial"]
theorem tensorPowerCoherence_exists : Nonempty (TensorPowerCoherence O hO L) := by
  have : (@CategoryTheory.MonoidalCategory.tensorRight _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory O hO) L).IsEquivalence :=
    (isEquivalence_tensorRight_iff O hO L).mpr inferInstance
  obtain ⟨⟨multiplication, leftUnit, rightUnit, rightOne, associativity, commutativity⟩⟩ :=
    @Stacks.MonoidalCategory.nonempty_powCoherence _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory O hO)
    (Stacks.SheafOfModules.Strict.braidedCategory O hO) L this
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L)
    hNativeEquivalence
    (fun X => (tensorSheafMapIso O hO (Iso.refl X) (tensorPowerOneIso O hO L) :))
    (tensorRightFunctor_eq O hO L)
    (heq_of_eq (funext fun X => (tensorSheafMapIso_refl_left O hO X _).trans
      (congrArg (whiskerLeftIso X) (tensorPowerOneIso_eq_powOneIso O hO L))))
    (braiding_symmetry O hO) (braiding_pow_one_self_eq_id O hO L)
  have hr := fun {n m : ℤ} (h : n = m) =>
    powReindexOf_eq_tensorPowerReindex O hO L (hNativeEquivalence := hNativeEquivalence) h
  refine ⟨{ isInvertible := isInvertible_tensorPower O hO L
            mulIso := multiplication
            mul_zero_left := fun n => ?_
            mul_zero_right := fun n => ?_
            mul_one_right := rightOne
            pow_succ_natural := fun n M N f =>
              @tensorPowerSuccIso_natural C _ J O hO _ _ L hNativeEquivalence n M N f
            mul_assoc := fun n m k => ?_
            mul_comm := fun n m => ?_ }⟩
  · have h1 := leftUnit n
    rwa [Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor,
      hr] at h1
  · have h1 := rightUnit n
    rwa [Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor,
      hr] at h1
  · have h1 := associativity n m k
    rwa [← tensorSheafMapIso_refl_right O hO (multiplication n m),
      ← tensorSheafMapIso_refl_left O hO _ (multiplication m k),
      Stacks.SheafOfModules.associator_eq_tensorSheafAssociator,
      hr] at h1
  · have h1 := commutativity n m
    rwa [Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding,
      hr] at h1

end Coherence

end Stacks.SheafOfModules.TensorPower

end
