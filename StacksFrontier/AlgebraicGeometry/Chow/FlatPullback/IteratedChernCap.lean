module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# Flat pullback commutes with iterated first Chern class cap products

Let `f : X' ⟶ X` be flat of relative dimension `r`, both schemes locally of finite type over the
base of chapter 42, and let `ℒ₀, …, ℒ_{m-1}` be invertible `𝒪_X`-modules. Stacks 02SS says that
`f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α`; iterating it,

  `f^*(c₁(ℒ₀) ∩ ⋯ ∩ c₁(ℒ_{m-1}) ∩ α) = c₁(f^*ℒ₀) ∩ ⋯ ∩ c₁(f^*ℒ_{m-1}) ∩ f^*α`

in `A_{k+r}(X')`, for `α ∈ A_{k+m}(X)`. This file records both, on Chow groups, with flat
pullback the unconditional `Stacks.Chow.flatPullbackChowOfRelativeDimension` of Stacks 0FVK.

## Main results

* `Stacks.Chow.flatPullbackChowOfRelativeDimension_invCap_capOnChow` — Stacks 02SS for the cap
  operator `Stacks.Chow.invCap` on Chow groups.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_iteratedChernCapOnChow` — the iterated form.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_fundamentalChowClass` — `f^*[X]_k = [X']_{k+r}`
  when `dim_δ X ≤ k`.

## Implementation notes

The two sides of each identity live in degrees that are equal integers but different terms
(`k + 1 + r` and `k + r + 1`, or `k + m + r` and `k + r + m`), so the class on the right is taken
as an arbitrary class heterogeneously equal to the pulled-back one, the convention of
`Stacks.Chow.iteratedChernCapOnChow_cons_eq`.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
  (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)

/-- Flat pullback on Chow groups, at heterogeneously equal arguments in equal degrees. -/
theorem flatPullbackChowOfRelativeDimension_heq {k₁ k₂ : ℤ} (hk : k₁ = k₂)
    {x : chowGroup C sX k₁} {y : chowGroup C sX k₂} (hxy : x ≍ y) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k₁ x ≍
      flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k₂ y := by
  subst hk; cases hxy; rfl

/-- **Stacks 02SS for the cap operator of an invertible module, on Chow groups.** For `f` flat of
relative dimension `r` and `x ∈ A_{k+1}(X)`,

  `f^*(c₁(ℒ) ∩ x) = c₁(f^*ℒ) ∩ f^*x`   in `A_{k+r}(X')`,

the class `y` being `f^*x` read in degree `k + r + 1`. -/
theorem flatPullbackChowOfRelativeDimension_invCap_capOnChow (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (x : chowGroup C sX (k + 1)) (y : chowGroup C sX' (k + r + 1))
    (hxy : flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf (k + 1) x ≍ y) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k
        ((invCap C sX L).capOnChow C sX k x) =
      (invCap C sX' ((Scheme.Modules.pullback f).obj L)).capOnChow C sX' (k + r) y := by
  subst hbase
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  have hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1 := by omega
  have hy : y =
      QuotientAddGroup.mk' _ (hcast ▸ flatPullback C (f ≫ sX) sX f rfl r hf (k + 1) α) := by
    refine chowGroup_eq_of_heq C _ (hxy.symm.trans ?_)
    rw [flatPullbackChowOfRelativeDimension_mk, ← chowGroupCast_mk C _ hcast]
    exact (chowGroupCast_heq C _ hcast _).symm
  rw [hy, invCap_capOnChow_mk, invCap_capOnChow_mk]
  exact flatPullbackChow_firstChernClassCapOfInvertible_of_invertible C sX f r hf k L _ α

/-- **Flat pullback commutes with iterated first Chern class cap products.** For invertible
`ℒ₀, …, ℒ_{m-1}` on `X`, `f` flat of relative dimension `r`, and `x ∈ A_{k+m}(X)`,

  `f^*(c₁(ℒ₀) ∩ ⋯ ∩ c₁(ℒ_{m-1}) ∩ x) = c₁(f^*ℒ₀) ∩ ⋯ ∩ c₁(f^*ℒ_{m-1}) ∩ f^*x`

in `A_{k+r}(X')`, the class `y` being `f^*x` read in degree `k + r + m`. -/
theorem flatPullbackChowOfRelativeDimension_iteratedChernCapOnChow {m : ℕ}
    (L : Fin m → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L i)]
    (k : ℤ) (x : chowGroup C sX (k + ((List.ofFn fun i => invCap C sX (L i)).length : ℤ)))
    (y : chowGroup C sX' (k + r +
      ((List.ofFn fun i => invCap C sX' ((Scheme.Modules.pullback f).obj (L i))).length : ℤ)))
    (hxy : flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf _ x ≍ y) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k
        (iteratedChernCapOnChow C sX (List.ofFn fun i => invCap C sX (L i)) k x) =
      iteratedChernCapOnChow C sX'
        (List.ofFn fun i => invCap C sX' ((Scheme.Modules.pullback f).obj (L i))) (k + r) y := by
  induction m generalizing k with
  | zero =>
    refine chowGroup_eq_of_heq C _ ?_
    refine HEq.trans (flatPullbackChowOfRelativeDimension_heq C sX' sX f hbase r hf (by simp)
      ((iteratedChernCapOnChow_heq_of_eq C sX List.ofFn_zero k (HEq.refl x)).trans
        (iteratedChernCapOnChow_nil_heq C sX k _))) ?_
    refine hxy.trans ?_
    exact ((iteratedChernCapOnChow_heq_of_eq C sX' List.ofFn_zero _ (HEq.refl y)).trans
      (iteratedChernCapOnChow_nil_heq C sX' _ _)).symm
  | succ m ih =>
    have hx : k + ((List.ofFn fun i => invCap C sX (L i)).length : ℤ) =
        k + ((invCap C sX (L 0) :: List.ofFn fun i : Fin m => invCap C sX (L i.succ)).length :
          ℤ) := by simp
    have hy : k + r + ((List.ofFn fun i =>
          invCap C sX' ((Scheme.Modules.pullback f).obj (L i))).length : ℤ) =
        k + r + ((invCap C sX' ((Scheme.Modules.pullback f).obj (L 0)) ::
          List.ofFn fun i : Fin m =>
            invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))).length : ℤ) := by simp
    have hx' : k + ((invCap C sX (L 0) ::
          List.ofFn fun i : Fin m => invCap C sX (L i.succ)).length : ℤ) =
        k + 1 + ((List.ofFn fun i : Fin m => invCap C sX (L i.succ)).length : ℤ) := by
      simp only [List.length_ofFn, List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have hy' : k + r + ((invCap C sX' ((Scheme.Modules.pullback f).obj (L 0)) ::
          List.ofFn fun i : Fin m =>
            invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))).length : ℤ) =
        k + r + 1 + ((List.ofFn fun i : Fin m =>
          invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))).length : ℤ) := by
      simp only [List.length_ofFn, List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    set x₁ := chowGroupCast C sX hx x
    set x₂ := chowGroupCast C sX hx' x₁
    set y₁ := chowGroupCast C sX' hy y
    set y₂ := chowGroupCast C sX' hy' y₁
    have hxx₂ : x ≍ x₂ := ((chowGroupCast_heq C sX hx' x₁).trans (chowGroupCast_heq C sX hx x)).symm
    have hyy₂ : y ≍ y₂ :=
      ((chowGroupCast_heq C sX' hy' y₁).trans (chowGroupCast_heq C sX' hy y)).symm
    have hL : iteratedChernCapOnChow C sX (List.ofFn fun i => invCap C sX (L i)) k x =
        (invCap C sX (L 0)).capOnChow C sX k (iteratedChernCapOnChow C sX
          (List.ofFn fun i : Fin m => invCap C sX (L i.succ)) (k + 1) x₂) := by
      refine (chowGroup_eq_of_heq C sX (iteratedChernCapOnChow_heq_of_eq C sX List.ofFn_succ k
        (chowGroupCast_heq C sX hx x).symm)).trans ?_
      exact iteratedChernCapOnChow_cons_eq C sX _ _ k x₁ x₂ (chowGroupCast_heq C sX hx' x₁).symm
    have hR : iteratedChernCapOnChow C sX'
          (List.ofFn fun i => invCap C sX' ((Scheme.Modules.pullback f).obj (L i))) (k + r) y =
        (invCap C sX' ((Scheme.Modules.pullback f).obj (L 0))).capOnChow C sX' (k + r)
          (iteratedChernCapOnChow C sX' (List.ofFn fun i : Fin m =>
            invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))) (k + r + 1) y₂) := by
      refine (chowGroup_eq_of_heq C sX' (iteratedChernCapOnChow_heq_of_eq C sX' List.ofFn_succ _
        (chowGroupCast_heq C sX' hy y).symm)).trans ?_
      exact iteratedChernCapOnChow_cons_eq C sX' _ _ _ y₁ y₂
        (chowGroupCast_heq C sX' hy' y₁).symm
    rw [hL, hR]
    refine flatPullbackChowOfRelativeDimension_invCap_capOnChow C sX' sX f hbase r hf (L 0) k _ _ ?_
    have hdeg : k + 1 + (r : ℤ) = k + r + 1 := by ring
    have hlen : (k + 1 + (r : ℤ)) + ((List.ofFn fun i : Fin m =>
        invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))).length : ℤ) =
        k + r + 1 + ((List.ofFn fun i : Fin m =>
          invCap C sX' ((Scheme.Modules.pullback f).obj (L i.succ))).length : ℤ) := by ring
    rw [ih (fun i => L i.succ) (k + 1) x₂ (chowGroupCast C sX' hlen.symm y₂)
      ((flatPullbackChowOfRelativeDimension_heq C sX' sX f hbase r hf (hx.trans hx').symm
        hxx₂.symm).trans
        (hxy.trans (hyy₂.trans (chowGroupCast_heq C sX' hlen.symm y₂).symm)))]
    exact iteratedChernCapOnChow_heq C sX' _ hdeg (chowGroupCast_heq C sX' hlen.symm y₂)

/-- **Flat pullback of a fundamental class, on Chow groups**: `f^*[X]_k = [X']_{k+r}` when
`dim_δ X ≤ k`. This is `Stacks.Chow.flatPullbackChow_fundamentalChowClass` with Stacks 02S1
discharged. -/
theorem flatPullbackChowOfRelativeDimension_fundamentalChowClass (k : ℤ)
    (hdim : schemeDeltaDimension C sX ≤ (k : EInt)) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k (fundamentalChowClass C sX k) =
      fundamentalChowClass C sX' (k + (r : ℤ)) :=
  flatPullbackChow_fundamentalChowClass C sX' sX f hbase r hf k _ hdim

end Stacks.Chow

end
