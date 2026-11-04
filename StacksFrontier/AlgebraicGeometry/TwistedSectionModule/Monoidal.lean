module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.AlgebraicGeometry.GradedSections.Braided

/-!
# The graded module of twisted sections

Let `C` be a monoidal category, `L` an object of `C` and `F` a second object. Stacks Tag 01CV's
section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` is `Stacks.GradedSections.sectionRing`, read
in `C` as `⨁_{n} (𝟙_ C ⟶ L ^⊗ n)`. This file builds the graded module over it that Stacks Tags
0B5L and 01PW need,

`Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)`,

again in an arbitrary monoidal category, as `⨁_{m} (𝟙_ C ⟶ F ⊙ m)` where `F ⊙ m` is `F`
whiskered on the right by `m` copies of `L`.

## Main definitions

* `Stacks.TwistedSections.twistPow`: `F ⊙ m`, defined by the same recursion as
  `Stacks.TensorPowers.natTensorPow` but starting at `F` instead of at `𝟙_ C`.
* `Stacks.TwistedSections.twistSections`: the degree-`m` piece, `𝟙_ C ⟶ F ⊙ m`.
* `Stacks.TwistedSections.actMap`: **the action in its load-bearing form.** For a twisted
  section `t : 𝟙_ C ⟶ F ⊙ m` this is a morphism `L ^⊗ n ⟶ F ⊙ (m + n)`, namely `t` whiskered on
  the right by `n` copies of `L`.
* `Stacks.TwistedSections.gsmul`: the action of a section of `L ^⊗ n` on a twisted section.
* `Stacks.TwistedSections.twistModule`: `⨁_{m} (𝟙_ C ⟶ F ⊙ m)`, with its module structure over
  `Stacks.GradedSections.sectionRing L`.

## Main results

* `Stacks.TwistedSections.actMap_comp`: **associativity in its strong form** — the `actMap` of
  an action is the composite of a `mulMap` and an `actMap`. This is the module counterpart of
  `Stacks.GradedSections.mulMap_mul`.
* `Stacks.TwistedSections.instGmodule`: `DirectSum.Gmodule (powSections L) (twistSections F L)`.
* `Stacks.TwistedSections.instModule`: the resulting
  `Module (Stacks.GradedSections.sectionRing L) (Stacks.TwistedSections.twistModule F L)`.
* `Stacks.TwistedSections.of_smul_of`: the computation rule on homogeneous elements.

## Implementation notes

**Why the whiskering goes on the module and not on the ring, and what that costs.** The
product of `Stacks.GradedSections` is `mul s t = t ≫ mulMap s m`, where `mulMap s m` whiskers the
ring element `s`. The analogous move here is impossible: a morphism `F ⊙ k ⟶ F ⊙ (n + k)` built
from a section of `L ^⊗ n` would need the unitor and the associator, since the `n` new copies of
`L` land between `F` and the `k` old ones. Whiskering the *twisted* section instead gives
`actMap t n : L ^⊗ n ⟶ F ⊙ (m + n)` with the types matching on the nose, exactly as `mulMap`
does, and the action is `a ≫ actMap t n`.

The price is that the natural degree of the result is `m + n`, the module degree first, while
`DirectSum.Gmodule` asks for `n +ᵥ m`, and `VAdd ℕ ℕ` is already `instVAddOfAdd`, i.e. `(+)`.
So `Stacks.TwistedSections.gsmul` transports along `Nat.add_comm`, and `mul_smul` is proved from
*commutativity* of the section ring (`Stacks.GradedSections.mul_comm'`, hence the
`CategoryTheory.BraidedCategory` and `Stacks.GradedSections.HasTrivialSelfBraiding`
hypotheses) rather than from its associativity. For the geometric case both are supplied:
`Stacks.SectionRingGeometric.schemeBraidedCategory` and
`Stacks.SectionRingGeometric.schemeHasTrivialSelfBraiding`.

**No object-level nesting identity is used.** `twistPow (twistPow F L m) L n` and
`twistPow F L (m + n)` are *not* definitionally equal, and neither are `twistPow (𝟙_ C) L n` and
`natTensorPow L n` — so no general right-whiskering operator on morphisms
appears here. Every lemma is stated for `actMap` directly, whose source is `natTensorPow L n` by
construction, and the one associativity statement that would otherwise need the nesting is
`Stacks.TwistedSections.actMap_comp`, proved by induction on the whiskering count.

**Every transport is discharged by `subst`.** `twistCongr` reindexes a twisted section along an
equality of degrees; the three lemmas describing how `actMap` interacts with such a reindexing
are proved by substituting the equality, after which both sides are syntactically equal.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the section ring.
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L) — the consumer: the
  degree-zero localization of this module at a global section of `L`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits DirectSum
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing HasTrivialSelfBraiding powCongr)

universe v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Defs

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **`F` twisted by `m` copies of `L`**: `F ⊙ 0 = F` and `F ⊙ (m + 1) = (F ⊙ m) ⊗ L`. This is
the recursion of `Stacks.TensorPowers.natTensorPow` started at `F` rather than at `𝟙_ C`. -/
def twistPow (F L : C) : ℕ → C
  | 0 => F
  | m + 1 => twistPow F L m ⊗ L

/-- `F` twisted by zero copies of `L` is `F`. -/
theorem twistPow_zero (F L : C) : twistPow F L 0 = F := rfl

/-- `F` twisted by `m + 1` copies of `L` is `(F ⊙ m) ⊗ L`. -/
theorem twistPow_succ (F L : C) (m : ℕ) : twistPow F L (m + 1) = twistPow F L m ⊗ L := rfl

/-- The degree-`m` piece of the graded module of twisted sections: the global sections of
`F ⊗ L ^⊗ m`, read as morphisms out of the monoidal unit. -/
abbrev twistSections (F L : C) (m : ℕ) : Type v := 𝟙_ C ⟶ twistPow F L m

/-- Reindexing a twisted section along an equality of degrees. -/
def twistCongr {F L : C} {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    twistSections F L m' :=
  t ≫ eqToHom (congrArg (twistPow F L) h)

/-- Reindexing along `rfl` is the identity. -/
@[simp] theorem twistCongr_rfl {F L : C} {m : ℕ} (t : twistSections F L m) :
    twistCongr (rfl : m = m) t = t := by simp [twistCongr]

/-- Two reindexings compose. -/
theorem twistCongr_trans {F L : C} {m m' m'' : ℕ} (h : m = m') (h' : m' = m'')
    (t : twistSections F L m) :
    twistCongr h' (twistCongr h t) = twistCongr (h.trans h') t := by
  subst h; subst h'; simp

/-- A reindexed twisted section is the original one, as an element of the sigma type that
`GradedMonoid` uses for the unit and associativity laws. -/
theorem mk_eq {F L : C} {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    (⟨m, t⟩ : GradedMonoid (twistSections F L)) = ⟨m', twistCongr h t⟩ := by
  subst h; simp

/-- **Acting by a twisted section, as a morphism out of a tensor power.** For a twisted section
`t` of degree `m` this is `t` whiskered on the right by `n` copies of `L`. Its codomain is
`F ⊙ (m + n)` on the nose: that object recurses on `n` just as this definition does, so no
transport and no unitor appear. -/
def actMap {F L : C} {m : ℕ} (t : twistSections F L m) :
    (n : ℕ) → (natTensorPow L n ⟶ twistPow F L (m + n))
  | 0 => t
  | n + 1 => actMap t n ▷ L

/-- Acting through the zeroth tensor power is the twisted section itself. -/
@[simp] theorem actMap_zero {F L : C} {m : ℕ} (t : twistSections F L m) : actMap t 0 = t := rfl

/-- `actMap t (n + 1)` is `actMap t n` whiskered on the right by `L`. -/
theorem actMap_succ {F L : C} {m : ℕ} (t : twistSections F L m) (n : ℕ) :
    actMap t (n + 1) = actMap t n ▷ L := rfl

/-- Reindexing commutes with the action. -/
theorem actMap_twistCongr {F L : C} {m m' : ℕ} (h : m = m') (t : twistSections F L m) (n : ℕ) :
    actMap (twistCongr h t) n =
      actMap t n ≫ eqToHom (congrArg (twistPow F L) (congrArg (· + n) h)) := by
  subst h; simp

/-- Reindexing the tensor power commutes with the action. -/
theorem eqToHom_comp_actMap {F L : C} {m : ℕ} (t : twistSections F L m) {p q : ℕ} (h : p = q) :
    eqToHom (congrArg (natTensorPow L) h) ≫ actMap t q =
      actMap t p ≫ eqToHom (congrArg (twistPow F L) (congrArg (m + ·) h)) := by
  subst h; simp

/-- `eqToHom_comp_actMap` in the right-associated shape `rw` meets it in. -/
theorem eqToHom_comp_actMap_assoc {F L : C} {m : ℕ} (t : twistSections F L m) {p q : ℕ}
    (h : p = q) {Z : C} (g : twistPow F L (m + q) ⟶ Z) :
    eqToHom (congrArg (natTensorPow L) h) ≫ actMap t q ≫ g =
      actMap t p ≫ eqToHom (congrArg (twistPow F L) (congrArg (m + ·) h)) ≫ g := by
  subst h; simp

/-- **Associativity in the form everything else follows from:** acting by a ring element on an
already-acted-upon twisted section is acting by the product. The module counterpart of
`Stacks.GradedSections.mulMap_mul`, and the one statement that would otherwise need
`twistPow (twistPow F L m) L n = twistPow F L (m + n)`. -/
theorem actMap_comp {F L : C} {j k : ℕ} (a : powSections L j) (t : twistSections F L k) :
    ∀ n : ℕ, actMap (a ≫ actMap t j) n =
      mulMap a n ≫ actMap t (j + n) ≫
        eqToHom (congrArg (twistPow F L) (Nat.add_assoc k j n).symm)
  | 0 => by simp
  | n + 1 => by
      rw [actMap_succ, actMap_comp a t n, comp_whiskerRight, comp_whiskerRight,
        eqToHom_whiskerRight]
      rfl

/-- **The action of a section of `L ^⊗ n` on a twisted section of degree `m`**, landing in degree
`n + m`. The underlying morphism has codomain `F ⊙ (m + n)`, so the definition transports along
`Nat.add_comm`; see the implementation notes. -/
def gsmul {F L : C} {n m : ℕ} (a : powSections L n) (t : twistSections F L m) :
    twistSections F L (n + m) :=
  twistCongr (Nat.add_comm m n) (a ≫ actMap t n)

/-- `gsmul a t` is `a ≫ actMap t n`, reindexed along `Nat.add_comm`. -/
theorem gsmul_def {F L : C} {n m : ℕ} (a : powSections L n) (t : twistSections F L m) :
    gsmul a t = twistCongr (Nat.add_comm m n) (a ≫ actMap t n) := rfl

/-- Reindexing the twisted section commutes with the action. -/
theorem gsmul_twistCongr {F L : C} {n m m' : ℕ} (a : powSections L n) (h : m = m')
    (t : twistSections F L m) :
    gsmul a (twistCongr h t) = twistCongr (congrArg (n + ·) h) (gsmul a t) := by
  subst h; simp

/-- Reindexing the acting section's degree commutes with the action. -/
theorem gsmul_comp_powCongr {F L : C} {p q m : ℕ} (h : p = q) (a : powSections L p)
    (t : twistSections F L m) :
    gsmul (a ≫ Stacks.GradedSections.powCongr L h) t =
      twistCongr (congrArg (· + m) h) (gsmul a t) := by
  subst h
  rw [Stacks.GradedSections.powCongr_rfl, Category.comp_id]
  exact (twistCongr_rfl _).symm

/-- The graded scalar action of the sections of the tensor powers of `L` on the twisted
sections, given by `gsmul`. -/
instance instGSMul (F L : C) : GradedMonoid.GSMul (powSections L) (twistSections F L) where
  smul a t := gsmul a t

/-- The graded scalar action is `gsmul`. -/
theorem gSMul_def {F L : C} {n m : ℕ} (a : powSections L n) (t : twistSections F L m) :
    GradedMonoid.GSMul.smul a t = gsmul a t := rfl

/-- **The product rule for the action**: acting by `x` on the result of acting by `y` is acting
by the product `x * y`, up to the reindexing the two conventions force. This is the identity that
`mul_smul` is proved from, and the only place commutativity of the section ring is used. -/
theorem actMap_mul [BraidedCategory C] {F L : C} [HasTrivialSelfBraiding L] {i j k : ℕ}
    (x : powSections L i) (y : powSections L j) (t : twistSections F L k) :
    x ≫ actMap (y ≫ actMap t j) i =
      mul x y ≫ actMap t (i + j) ≫
        eqToHom (congrArg (twistPow F L) (by omega : k + (i + j) = k + j + i)) := by
  rw [actMap_comp y t i, ← Category.assoc x (mulMap y i),
    ← Stacks.GradedSections.mul_def y x, ← Stacks.GradedSections.mul_comm' x y,
    Category.assoc, eqToHom_comp_actMap_assoc t (Nat.add_comm i j)]
  simp only [eqToHom_trans]

end Defs

section Preadditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

section Reindex

variable [Preadditive C] {F L : C}

/-- **Reindexing the degree, as a morphism of additive groups.** -/
def twistCongrHom (F L : C) {m m' : ℕ} (h : m = m') :
    twistSections F L m →+ twistSections F L m' where
  toFun := twistCongr h
  map_zero' := Limits.zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- `twistCongrHom F L h` applied to `t` is `twistCongr h t`. -/
@[simp] theorem twistCongrHom_apply {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    twistCongrHom F L h t = twistCongr h t := rfl

/-- A reindexed twisted section has the same image in the direct sum, in the reindexed degree. -/
theorem of_twistCongr {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    DirectSum.of (twistSections F L) m' (twistCongr h t) =
      DirectSum.of (twistSections F L) m t := by
  subst h; rw [twistCongr_rfl]

end Reindex

variable [Preadditive C] {F L : C} [(tensorRight L).Additive]

/-- Acting by the zero twisted section is zero. -/
theorem actMap_zero_section {m : ℕ} (n : ℕ) : actMap (0 : twistSections F L m) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [actMap_succ, ih]; exact (tensorRight L).map_zero _ _

/-- The action is additive in the twisted section. -/
theorem actMap_add {m : ℕ} (t t' : twistSections F L m) (n : ℕ) :
    actMap (t + t') n = actMap t n + actMap t' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [actMap_succ, ih, actMap_succ t n, actMap_succ t' n]
      exact (tensorRight L).map_add

variable [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The twisted sections form a graded module over the section ring.** -/
noncomputable instance instGmodule :
    DirectSum.Gmodule (powSections L) (twistSections F L) where
  one_smul b := by
    obtain ⟨m, t⟩ := b
    change (⟨0 + m, gsmul (𝟙 (𝟙_ C) : powSections L 0) t⟩ :
      GradedMonoid (twistSections F L)) = ⟨m, t⟩
    rw [gsmul_def, actMap_zero, Category.id_comp]
    exact (mk_eq (Nat.add_comm m 0) t).symm
  mul_smul a a' b := by
    obtain ⟨i, x⟩ := a; obtain ⟨j, y⟩ := a'; obtain ⟨k, t⟩ := b
    change (⟨i + j + k, gsmul (mul x y) t⟩ : GradedMonoid (twistSections F L)) =
      ⟨i + (j + k), gsmul x (gsmul y t)⟩
    refine (mk_eq (Nat.add_assoc i j k) _).trans ?_
    congr 1
    rw [gsmul_def x (gsmul y t), gsmul_def y t, twistCongr, actMap_twistCongr,
      ← Category.assoc, actMap_mul x y t]
    simp only [gsmul_def, twistCongr, Category.assoc, eqToHom_trans]
  smul_add a b c := by
    change gsmul a (b + c) = gsmul a b + gsmul a c
    rw [gsmul_def, gsmul_def, gsmul_def, actMap_add, Preadditive.comp_add, twistCongr,
      twistCongr, twistCongr, Preadditive.add_comp]
  smul_zero a := by
    change gsmul a (0 : twistSections F L _) = 0
    rw [gsmul_def, actMap_zero_section, Limits.comp_zero, twistCongr, Limits.zero_comp]
  add_smul a a' b := by
    change gsmul (a + a') b = gsmul a b + gsmul a' b
    rw [gsmul_def, gsmul_def, gsmul_def, Preadditive.add_comp, twistCongr, twistCongr,
      twistCongr, Preadditive.add_comp]
  zero_smul b := by
    change gsmul (0 : powSections L _) b = 0
    rw [gsmul_def, Limits.zero_comp, twistCongr, Limits.zero_comp]

/-- **The graded module of twisted sections `⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)`.** -/
abbrev twistModule (F L : C) : Type v := ⨁ m : ℕ, twistSections F L m

/-- **The degree-`m` component of the graded module of twisted sections**, as a morphism of
additive groups. -/
def componentHom (F L : C) (m : ℕ) : twistModule F L →+ twistSections F L m where
  toFun x := x m
  map_zero' := rfl
  map_add' x y := DFinsupp.add_apply x y m

/-- The degree-`m` component of the image of `t` in degree `m` is `t`. -/
@[simp] theorem componentHom_of (m : ℕ) (t : twistSections F L m) :
    componentHom F L m (DirectSum.of (twistSections F L) m t) = t :=
  DirectSum.of_eq_same m t

/-- **The twisted sections form a module over the section ring of `L`.** -/
noncomputable instance instModule : Module (sectionRing L) (twistModule F L) :=
  DirectSum.Gmodule.module (powSections L) (twistSections F L)

/-- **The action, on homogeneous elements.** -/
theorem of_smul_of {n m : ℕ} (a : powSections L n) (t : twistSections F L m) :
    DirectSum.of (powSections L) n a • DirectSum.of (twistSections F L) m t =
      DirectSum.of (twistSections F L) (n + m) (gsmul a t) :=
  DirectSum.Gmodule.of_smul_of (powSections L) (twistSections F L) a t

end Preadditive

end Stacks.TwistedSections

end
