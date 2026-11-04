module

public import Mathlib.CategoryTheory.Equivalence

/-!
# An autoequivalence objectwise isomorphic to the identity has the same iterates

Let `e` be an autoequivalence of `A` which is objectwise isomorphic to the identity, in the sense
that there is an isomorphism `e M ≅ M` for every object `M`, with no naturality required. Then
`(e ^ n) M ≅ M` for every integer `n` and every object `M`.

## Main definitions

* `Stacks.Equivalence.inverseObjIsoSelf`: the family for the quasi-inverse, `e⁻¹ N ≅ N`, built
  from the family for the functor.
* `Stacks.Equivalence.powNatObjIsoSelf`: the family for natural-number iterates.
* `Stacks.Equivalence.powObjIsoSelf`: the family for integer iterates.

## Main results

* `Stacks.Equivalence.powObjIsoSelf_zero`, `Stacks.Equivalence.powObjIsoSelf_one`,
  `Stacks.Equivalence.powObjIsoSelf_neg_one`: the values at the exponents `0`, `1` and `-1`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.Equivalence

variable {A : Type u} [Category.{v} A]

/-- **The family for the quasi-inverse.** If `e M ≅ M` for every `M`, then `e⁻¹ N ≅ N` for every
`N`, given by the inverse of the isomorphism at `e⁻¹ N` followed by the counit of `e`. -/
noncomputable def inverseObjIsoSelf (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) (N : A) :
    e.inverse.obj N ≅ N :=
  (α (e.inverse.obj N)).symm ≪≫ e.counitIso.app N

/-- **The family for natural-number iterates.** If `e M ≅ M` for every `M`, then
`(e ^ n) M ≅ M` for every natural number `n` and every `M`. -/
noncomputable def powNatObjIsoSelf (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) :
    (n : ℕ) → (M : A) → (e.powNat n).functor.obj M ≅ M
  | 0, M => Iso.refl M
  | 1, M => α M
  | n + 2, M => powNatObjIsoSelf e α (n + 1) (e.functor.obj M) ≪≫ α M

/-- **An autoequivalence objectwise isomorphic to the identity has every integer iterate
objectwise isomorphic to the identity.** If `e M ≅ M` for every `M`, then `(e ^ n) M ≅ M` for
every integer `n` and every `M`. -/
noncomputable def powObjIsoSelf (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) :
    (n : ℤ) → (M : A) → (e ^ n).functor.obj M ≅ M
  | Int.ofNat n, M => powNatObjIsoSelf e α n M
  | Int.negSucc n, M => powNatObjIsoSelf e.symm (inverseObjIsoSelf e α) (n + 1) M

/-- At exponent `0` the family is the identity. -/
theorem powObjIsoSelf_zero (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) (M : A) :
    powObjIsoSelf e α 0 M = Iso.refl M :=
  rfl

/-- At exponent `1` the family is the given one. -/
theorem powObjIsoSelf_one (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) (M : A) :
    powObjIsoSelf e α 1 M = α M :=
  rfl

/-- At exponent `-1` the family is the one built for the quasi-inverse. -/
theorem powObjIsoSelf_neg_one (e : A ≌ A) (α : ∀ M : A, e.functor.obj M ≅ M) (M : A) :
    powObjIsoSelf e α (-1) M = inverseObjIsoSelf e α M :=
  rfl

end Stacks.Equivalence

end
