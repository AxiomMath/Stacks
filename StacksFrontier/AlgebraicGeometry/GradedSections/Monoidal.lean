module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal

/-!
# The graded ring of sections of the tensor powers of an object

Let `C` be a monoidal category and `L` an object of `C`. The "global sections of the `n`-th
tensor power of `L`" are the morphisms `𝟙_ C ⟶ L ^⊗ n` out of the monoidal unit, where
`L ^⊗ n` is `Stacks.TensorPowers.natTensorPow L n`, the left-iterated tensor product
`(⋯ ((𝟙_ C ⊗ L) ⊗ L) ⋯) ⊗ L`. This file makes
`⨁_{n ≥ 0} (𝟙_ C ⟶ L ^⊗ n)`
into a graded ring, hence into a ring. This is the ring-theoretic content of Stacks Tag 01CV,
done once at the level of an arbitrary monoidal category so that the geometric case is an
instantiation.

For a ringed space or a scheme, `𝟙_ C ⟶ F` really is `Γ(X, F)`, by
`SheafOfModules.unitHomEquiv`.

## Main definitions

* `Stacks.GradedSections.powSections`: the degree-`n` piece, `𝟙_ C ⟶ L ^⊗ n`.
* `Stacks.GradedSections.mulMap`: **the multiplication, in its load-bearing form.** For a
  section `s : 𝟙_ C ⟶ L ^⊗ n` this is a morphism of powers `L ^⊗ m ⟶ L ^⊗ (n + m)`, defined by
  recursion on `m` as `s` whiskered on the right by `m` copies of `L`.
* `Stacks.GradedSections.mul`: the product of two sections, `t ≫ mulMap s m`.
* `Stacks.GradedSections.sectionRing`: `⨁_{n ≥ 0} (𝟙_ C ⟶ L ^⊗ n)`, with its ring structure.

## Main results

* `Stacks.GradedSections.mulMap_mul`: **associativity in its strong form** — the `mulMap` of a
  product is the composite of the two `mulMap`s. Everything else about associativity follows.
* `Stacks.GradedSections.instGMonoid`, `Stacks.GradedSections.instGRing`: the graded monoid and
  graded ring structures; `Stacks.GradedSections.instRing` is the resulting ring.

## Implementation notes

**Why there is no monoidal coherence here, and why that is the point.** The expected route to
Stacks Tag 01CV goes through the addition isomorphism
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of Stacks Tag 01CU, whose associativity and commutativity
constraints the source states with the formulation omitted; they are genuinely not formal
consequences of that isomorphism, because it is defined by recursion on its second exponent.
This file does not use the addition isomorphism at all. Instead the product of
`s : 𝟙_ C ⟶ L ^⊗ n` with `t : 𝟙_ C ⟶ L ^⊗ m` is `t ≫ mulMap s m`, where `mulMap s m` is `s`
whiskered on the right by `m` copies of `L`. Two things then come out for free:

* the types match on the nose. `natTensorPow L (n + m)` recurses on `m` exactly as `mulMap s m`
  does, so `mulMap s m : L ^⊗ m ⟶ L ^⊗ (n + m)` needs no transport and no unitor;
* associativity is `mulMap_mul`, whose inductive step is nothing but
  `CategoryTheory.MonoidalCategory.comp_whiskerRight`. No associator, no pentagon, no
  `monoidal` tactic call.

The price is paid in the index bookkeeping that Mathlib's `GradedMonoid` interface forces:
`0 + n` and `n + m` are not definitionally `n` and `m + n`, so the unit and commutativity laws
are equalities of dependent pairs and need `mk_eq`. The associativity and right-unit laws need
nothing: `n + 0` and `n + (m + k)` are definitionally `n` and `(n + m) + k`.

**What commutativity would need, and why it is not here.** See "What is not done".

**The additivity hypothesis.** Distributivity in the first variable asks that `- ▷ L` be an
additive functor, which is the stated hypothesis `(tensorRight L).Additive`; it is the weakest
form that the construction uses. `CategoryTheory.MonoidalPreadditive C` supplies it through
Mathlib's instance `CategoryTheory.tensorRight_additive`, so a caller with a monoidal
preadditive category need not mention it. Distributivity in the second variable asks for
nothing: the product is a composite with `t` on the left, so it is additive in `t` by
preadditivity of `C` alone.

**Transparency.** `Stacks.TensorPowers.natTensorPow` is a plain `def`, so `L ^⊗ 0` and `𝟙_ C`
are equal only at default transparency; `rw` and `simp` work on goals mentioning both only
inside the section's `attribute [local implicit_reducible]`. The `monoidal` tactic is not
helped by that attribute — it fails to recognise `natTensorPow L 0` as the unit whatever the
transparency — which is a second reason the construction above is preferable to one that needs
coherence.

**Universes.** Polymorphic in both category universes, exactly as `natTensorPow` is. The
degree-`n` piece lives in `Type v`, the Hom universe.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What is not done

The ring is not shown to be commutative, and that is not an oversight of this file but a real
gap, with a precise location. Commutativity is false for a general object `L`: at `n = m = 1`
it asserts that the braiding `β_ L L` is the identity, which already fails in a symmetric
monoidal category (an invertible object may have self-braiding `-1`). The correct hypothesis is
that the self-braiding of `L` is trivial, and under it commutativity is a statement about the
braiding of tensor powers that this file does not prove; it needs the addition isomorphism of
Stacks Tag 01CU back again, plus a left-successor formula for it, plus the hexagon. See the
sibling file's "What is not done" for the same obstruction seen from the other side.

Nothing here is stated for negative exponents. Stacks Tag 01CV's graded ring is the
nonnegative-degree one by its own convention, and the graded module
`Γ_*(X, L, F) = ⨁_{n ∈ ℤ} Γ(X, F ⊗ L ^⊗ n)` of the same tag is not constructed.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

open scoped DirectSum

namespace Stacks.GradedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Defs

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The degree-`n` piece of the section ring of `L`: the global sections of the `n`-th tensor
power, read as morphisms out of the monoidal unit. -/
abbrev powSections (L : C) (n : ℕ) : Type v := 𝟙_ C ⟶ natTensorPow L n

/-- **Multiplication by a section, as a morphism of tensor powers.** For a section `s` of the
`n`-th power this is `s` whiskered on the right by `m` copies of `L`. Its codomain is
`natTensorPow L (n + m)` on the nose: that power recurses on `m` just as this definition does,
so no transport and no unitor appear. -/
def mulMap {L : C} {n : ℕ} (s : powSections L n) :
    (m : ℕ) → (natTensorPow L m ⟶ natTensorPow L (n + m))
  | 0 => s
  | m + 1 => mulMap s m ▷ L

/-- Multiplication by `s` on the `0`-th power is `s` itself. -/
@[simp]
theorem mulMap_zero {L : C} {n : ℕ} (s : powSections L n) : mulMap s 0 = s := rfl

/-- Multiplication by `s` on the `(m + 1)`-st power is multiplication by `s` on the `m`-th
power, whiskered on the right by `L`. -/
theorem mulMap_succ {L : C} {n : ℕ} (s : powSections L n) (m : ℕ) :
    mulMap s (m + 1) = mulMap s m ▷ L := rfl

/-- `mulMap_succ` with the exponent in the shape the associativity induction produces. -/
theorem mulMap_add_succ {L : C} {n : ℕ} (s : powSections L n) (m k : ℕ) :
    mulMap s (m + (k + 1)) = mulMap s (m + k) ▷ L := rfl

/-- **The product of two sections.** -/
def mul {L : C} {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    powSections L (n + m) :=
  t ≫ mulMap s m

/-- The product of `s` and `t` is `t` followed by multiplication by `s`. -/
theorem mul_def {L : C} {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    mul s t = t ≫ mulMap s m := rfl

/-- Multiplication by the unit section is the transport along `0 + m = m`. -/
theorem mulMap_id {L : C} (m : ℕ) :
    mulMap (𝟙 (𝟙_ C) : powSections L 0) m =
      eqToHom (congrArg (natTensorPow L) (Nat.zero_add m).symm) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mulMap_succ, ih, eqToHom_whiskerRight]

/-- **Associativity, in the form everything else follows from:** multiplying by a product is
multiplying by each factor in turn. The inductive step is one application of
`CategoryTheory.MonoidalCategory.comp_whiskerRight`. -/
theorem mulMap_mul {L : C} {n m : ℕ} (s : powSections L n) (t : powSections L m) : ∀ k : ℕ,
    mulMap (mul s t) k =
      mulMap t k ≫ mulMap s (m + k) ≫
        eqToHom (congrArg (natTensorPow L) (Nat.add_assoc n m k).symm)
  | 0 => by simp [mul_def]
  | k + 1 => by
      rw [mulMap_succ (mul s t) k, mulMap_mul s t k, mulMap_add_succ s m k, mulMap_succ t k,
        comp_whiskerRight, comp_whiskerRight, eqToHom_whiskerRight]

/-- Reindexing a homogeneous element of the section ring along an equality of degrees. This is
the one place a transport is needed, and `GradedMonoid`'s dependent-pair formulation of the unit
and commutativity laws is what forces it. -/
theorem mk_eq {L : C} {n m : ℕ} (h : n = m) (s : powSections L n) :
    (⟨n, s⟩ : GradedMonoid (powSections L)) =
      ⟨m, s ≫ eqToHom (congrArg (natTensorPow L) h)⟩ := by
  subst h; simp

/-- The unit of the graded section ring is the identity of the monoidal unit, in degree `0`. -/
instance instGOne (L : C) : GradedMonoid.GOne (powSections L) := ⟨𝟙 (𝟙_ C)⟩

/-- The graded multiplication on sections of tensor powers is `mul`. -/
instance instGMul (L : C) : GradedMonoid.GMul (powSections L) := ⟨fun s t => mul s t⟩

/-- The graded multiplication of `s` and `t` is `mul s t`. -/
theorem gMul_def {L : C} {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    GradedMonoid.GMul.mul s t = mul s t := rfl

/-- The graded unit is the identity of the monoidal unit. -/
theorem gOne_def {L : C} : (GradedMonoid.GOne.one : powSections L 0) = 𝟙 (𝟙_ C) := rfl

/-- **The tensor powers of `L` form a graded monoid under multiplication of sections.** -/
noncomputable instance instGMonoid (L : C) : GradedMonoid.GMonoid (powSections L) where
  one_mul a := by
    obtain ⟨m, t⟩ := a
    change (⟨0 + m, mul (𝟙 (𝟙_ C) : powSections L 0) t⟩ : GradedMonoid (powSections L)) = ⟨m, t⟩
    refine (mk_eq (Nat.zero_add m) _).trans ?_
    congr 1
    rw [mul_def, mulMap_id]
    simp
  mul_one a := by
    obtain ⟨n, s⟩ := a
    change (⟨n + 0, mul s (𝟙 (𝟙_ C) : powSections L 0)⟩ : GradedMonoid (powSections L)) = ⟨n, s⟩
    rw [mul_def, mulMap_zero, Category.id_comp]
    rfl
  mul_assoc a b c := by
    obtain ⟨n, s⟩ := a; obtain ⟨m, t⟩ := b; obtain ⟨k, u⟩ := c
    change (⟨n + m + k, mul (mul s t) u⟩ : GradedMonoid (powSections L)) =
      ⟨n + (m + k), mul s (mul t u)⟩
    refine (mk_eq (Nat.add_assoc n m k) _).trans ?_
    congr 1
    rw [mul_def s (mul t u), mul_def (mul s t) u, mulMap_mul s t k, mul_def t u]
    simp

end Defs

section Preadditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable [Preadditive C] {L : C} [(tensorRight L).Additive]

/-- Multiplication by the zero section is zero. -/
theorem mulMap_zero_section {n : ℕ} (m : ℕ) : mulMap (0 : powSections L n) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mulMap_succ, ih]; exact (tensorRight L).map_zero _ _

/-- Multiplication by a section is additive in that section. -/
theorem mulMap_add {n : ℕ} (s t : powSections L n) (m : ℕ) :
    mulMap (s + t) m = mulMap s m + mulMap t m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [mulMap_succ, ih, mulMap_succ s m, mulMap_succ t m]
    exact (tensorRight L).map_add

/-- **The section ring of `L` is a graded ring.** -/
noncomputable instance instGRing : DirectSum.GRing (powSections L) where
  mul_zero _ := Limits.zero_comp
  zero_mul _ := by
    change mul 0 _ = 0
    rw [mul_def, mulMap_zero_section, Limits.comp_zero]
  mul_add s t u := by
    change mul s (t + u) = mul s t + mul s u
    rw [mul_def, mul_def, mul_def, Preadditive.add_comp]
  add_mul s t u := by
    change mul (s + t) u = mul s u + mul t u
    rw [mul_def, mul_def, mul_def, mulMap_add, Preadditive.comp_add]
  natCast n := n • 𝟙 (𝟙_ C)
  natCast_zero := by simp
  natCast_succ n := by rw [succ_nsmul]; rfl
  intCast n := n • 𝟙 (𝟙_ C)
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    change (Int.negSucc n) • 𝟙 (𝟙_ C) = _
    rw [Int.negSucc_eq, neg_smul]
    norm_cast

/-- **The section ring `⨁_{n ≥ 0} (𝟙_ C ⟶ L ^⊗ n)`.** This is Stacks Tag 01CV's `Γ_*(X, L)`
read in an arbitrary monoidal category. -/
abbrev sectionRing (L : C) : Type v := ⨁ n : ℕ, powSections L n

/-- The section ring is a ring. -/
noncomputable instance instRing : Ring (sectionRing L) := inferInstance

end Preadditive

end Stacks.GradedSections
