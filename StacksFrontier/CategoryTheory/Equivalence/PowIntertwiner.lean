module

public import Mathlib.CategoryTheory.Equivalence

/-!
# A functor intertwining two autoequivalences intertwines all their integer iterates

Let `e` be an autoequivalence of `A`, let `e'` be an autoequivalence of `B`, and let `R : A ⥤ B`
be a functor carrying `e` to `e'` in the sense that `R (e M) ≅ e' (R M)` for every object `M`.
This file transports that single comparison to every integer iterate:
`R ((e ^ n) M) ≅ (e' ^ n) (R M)` for all `n : ℤ`.

The negative iterates are the point. Mathlib's `CategoryTheory.Equivalence.pow` sends a negative
exponent to a power of the quasi-inverse, so a comparison for `e` says nothing about
`e ^ (-1) = e.symm` until one is produced for `e.inverse`, and that is
`inverseIntertwineObj` below: it is manufactured from `α` together with the unit of `e'` and the
counit of `e`, with no hypothesis beyond `α` itself.

## Main definitions

* `Stacks.Equivalence.inverseIntertwineObj`: the comparison for the quasi-inverses,
  `R (e⁻¹ N) ≅ e'⁻¹ (R N)`, built from the comparison for the functors.
* `Stacks.Equivalence.powNatIntertwineObj`: the comparison for natural-number iterates.
* `Stacks.Equivalence.powIntertwineObj`: **the comparison for integer iterates.**

## Implementation notes

Everything here is stated **objectwise** — as a family of isomorphisms indexed by an object
rather than as an isomorphism of functors — and this is deliberate. Mathlib's
`Equivalence.powNat` recurses by `e.powNat (n + 2) = e.trans (e.powNat (n + 1))`, so the
functor-level induction step is `e.functor ⋙ (e.powNat (n + 1)).functor` and closing it needs
the two unitors and three whiskerings; at the level of objects the same step is a composite of
two isomorphisms and the recursion is the one `Equivalence.powNat` itself uses. The consumer
this was written for applies the comparison at a single object (the unit of a category of
sheaves of modules), so no naturality statement is needed, and none is proved: naturality of
the result would require naturality of `α`, which is a strictly stronger input than the
objectwise family.

`Stacks.Equivalence.powNatSuccIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPower.lean` compares *one* iterate of a
*single* autoequivalence with its successor. That is a different statement from the one here,
which compares the *same* iterate of *two* autoequivalences across a functor, and neither
implies the other; the two share only the recursion pattern.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace Stacks.Equivalence

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **The comparison for the quasi-inverses.** If `R` carries the functor of `e` to the functor
of `e'`, then it carries the inverse of `e` to the inverse of `e'`: apply the unit of `e'`, undo
the given comparison, then apply `R` to the counit of `e`. -/
noncomputable def inverseIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (N : A) :
    R.obj (e.inverse.obj N) ≅ e'.inverse.obj (R.obj N) :=
  e'.unitIso.app (R.obj (e.inverse.obj N)) ≪≫
    e'.inverse.mapIso ((α (e.inverse.obj N)).symm ≪≫ R.mapIso (e.counitIso.app N))

/-- **The comparison for natural-number iterates.** The exponent `n + 2` is reduced to `n + 1`
at the object `e M`, which is how `Equivalence.powNat` itself recurses, and the remaining
comparison is `α M` pushed through the `(n + 1)`st iterate of `e'`. -/
noncomputable def powNatIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    (n : ℕ) → (M : A) →
      R.obj ((e.powNat n).functor.obj M) ≅ (e'.powNat n).functor.obj (R.obj M)
  | 0, M => Iso.refl (R.obj M)
  | 1, M => α M
  | n + 2, M =>
      powNatIntertwineObj e e' R α (n + 1) (e.functor.obj M) ≪≫
        (e'.powNat (n + 1)).functor.mapIso (α M)

/-- **A functor intertwining two autoequivalences intertwines every integer iterate of them.**
A negative exponent is the corresponding positive iterate of the quasi-inverses, for which the
comparison is `inverseIntertwineObj`. -/
noncomputable def powIntertwineObj (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) :
    (n : ℤ) → (M : A) →
      R.obj ((e ^ n).functor.obj M) ≅ (e' ^ n).functor.obj (R.obj M)
  | Int.ofNat n, M => powNatIntertwineObj e e' R α n M
  | Int.negSucc n, M =>
      powNatIntertwineObj e.symm e'.symm R
        (fun N => inverseIntertwineObj e e' R α N) (n + 1) M

/-- At exponent `0` the integer comparison is the identity. -/
theorem powIntertwineObj_zero (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (M : A) :
    powIntertwineObj e e' R α 0 M = Iso.refl (R.obj M) :=
  rfl

/-- At exponent `1` the integer comparison is the given one. -/
theorem powIntertwineObj_one (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (M : A) :
    powIntertwineObj e e' R α 1 M = α M :=
  rfl

/-- At exponent `-1` the integer comparison is the one built for the quasi-inverses. -/
theorem powIntertwineObj_neg_one (e : A ≌ A) (e' : B ≌ B) (R : A ⥤ B)
    (α : ∀ M : A, R.obj (e.functor.obj M) ≅ e'.functor.obj (R.obj M)) (M : A) :
    powIntertwineObj e e' R α (-1) M = inverseIntertwineObj e e' R α M :=
  rfl

end Stacks.Equivalence
