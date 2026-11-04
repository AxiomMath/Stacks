module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses

/-!
# The Chern class cap products of every rank, as a cap rule

`Stacks.Chow.HigherChernCapRule C r` is the shape of the Chern class operations

  `c_j(ℱ) ∩ - : A_k(T) ⟶ A_{k-j}(T)`,  `0 ≤ j ≤ r`,

for every scheme `T` locally of finite type over the base of chapter 42 and every finite locally
free `𝒪_T`-module `ℱ` of rank `r`. This file supplies the operations themselves: in rank `n + 1`
they are the cap products `Stacks.Chow.bundleChernCap` read off the projective space bundle
formula [Stacks, Tag 02TX] on `𝐏(ℱ)`, the characterization of [Stacks, Tag 02U6]; in rank `0`
the only one is `c_0 = 1`.

## Main definitions

* `Stacks.Chow.GenuineChern.chernCap` — the Chern class cap products in every rank.

## Main results

* `Stacks.Chow.GenuineChern.chernCap_succ` — in rank `n + 1` they are `Stacks.Chow.bundleChernCap`.
* `Stacks.Chow.GenuineChern.chernCap_zero` — in rank `0` the operation is the identity.
* `Stacks.Chow.GenuineChern.chernCap_zero_apply` — `c_0(ℱ) ∩ α = α` in every rank.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- The Chern class cap product of rank `0`: `c_0 = 1` caps as the identity, read in degree
`k - 0`. -/
def chernCapZero : HigherChernCapRule C 0 := by
  intro _T q _ _F _ k j
  exact (chowGroupCast C q (show k = k - ((j : ℕ) : ℤ) by
    rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp)).toAddMonoidHom

/-- The Chern class cap products of rank `n + 1`: the members of the unique family solving the
relation of Stacks 02U6 on the projective bundle. -/
def chernCapSucc (n : ℕ) : HigherChernCapRule C (n + 1) := by
  intro _T q _ F _ k j
  exact bundleChernCap F n C q k j

/-- **The Chern class cap products of Stacks 02U6, in every rank.** In rank `n + 1` the operation
`c_j(ℱ) ∩ -` is the `j`-th member of the unique family solving the relation of Stacks 02U6 on the
projective bundle of `ℱ`; in rank `0` the only Chern class is `c_0 = 1`, which caps as the
identity. -/
def chernCap : (r : ℕ) → HigherChernCapRule C r
  | 0 => chernCapZero C
  | n + 1 => chernCapSucc C n

variable {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F : T.Modules) (k : ℤ)

/-- In rank `n + 1` the Chern class cap products are those of Stacks 02U6 on `𝐏(ℱ)`. -/
theorem chernCap_succ (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)]
    (j : Fin (n + 1 + 1)) :
    chernCap C (n + 1) q F k j = bundleChernCap F n C q k j :=
  rfl

/-- In rank `0` the only Chern class cap product is the identity, read in degree `k - 0`. -/
theorem chernCap_zero [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 0]
    (j : Fin (0 + 1)) (α : chowGroup C q k) :
    chernCap C 0 q F k j α = chowGroupCast C q (by
      rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp) α :=
  rfl

/-- **`c_0(ℱ) ∩ α = α`**, in every rank. -/
theorem chernCap_zero_apply (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    (α : chowGroup C q k) :
    chowGroupCast C q (show k - ((0 : Fin (r + 1)) : ℕ) = k by simp)
      (chernCap C r q F k 0 α) = α := by
  cases r with
  | zero => rw [chernCap_zero, chowGroupCast_chowGroupCast]; rfl
  | succ n => rw [chernCap_succ]; exact bundleChernCapFamily_zero F n C q k α

end Stacks.Chow.GenuineChern

end
