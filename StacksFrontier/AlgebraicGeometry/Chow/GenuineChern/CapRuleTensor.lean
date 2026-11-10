module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleTensorTwist

/-!
# The Chern class cap products of a twist by an invertible module

Let `X` be locally of finite type over the base of chapter 42, `ℰ` finite locally free of rank
`r` and `ℒ` invertible on `X`. Then for every `0 ≤ i ≤ r` and `α ∈ A_k(X)`

  `c_i(ℰ ⊗ ℒ) ∩ α = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) ∩ c₁(ℒ)^j ∩ α`

in `A_{k-i}(X)`, for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6].
This is [Stacks, Tag 02UD] capped with a class, the form to which the source reduces it by
[Stacks, Tag 02UC].

## Main results

* `Stacks.Chow.GenuineChern.chernCap_sheafTensor`: the formula above.

## References

* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Chern class cap products of a twist by an invertible module.** Let `ℰ` be finite
locally free of rank `r` and `ℒ` invertible on `X`. For `0 ≤ i ≤ r` and `α ∈ A_k(X)`,

  `c_i(ℰ ⊗ ℒ) ∩ α = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j}(ℰ) ∩ c₁(ℒ)^j ∩ α`

in `A_{k-i}(X)`, where `c₁(ℒ)^j ∩ -` is the `j`-fold cap `Stacks.Chow.capPow` and the `j`-th
summand, which lies in `A_{(k-j)-(i-j)}(X)`, is read in `A_{k-i}(X)`. -/
theorem chernCap_sheafTensor (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (k : ℤ) (i : Fin (r + 1)) (α : chowGroup C sX k) :
    @chernCap C r X sX inferInstance
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L)
        (isFiniteLocallyFreeOfRank_sheafTensor E r L) k i α =
      ∑ j : Fin ((i : ℕ) + 1), ((r - i + j : ℕ).choose j : ℤ) •
        chowGroupCast C sX (by simp only; omega)
          (chernCap C r sX E (k - (j : ℤ)) ⟨(i : ℕ) - j, by omega⟩
            (capPow C sX (invCap C sX L) j k (k - (j : ℤ)) (by ring) α)) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  @chernCap_eq_sum_of_bundleIso C X sX inferInstance E
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).obj L) r inferInstance
    (isFiniteLocallyFreeOfRank_sheafTensor E r L) L inferInstance
    (exists_bundleTensorIso E L) k i α

end Stacks.Chow.GenuineChern

end
