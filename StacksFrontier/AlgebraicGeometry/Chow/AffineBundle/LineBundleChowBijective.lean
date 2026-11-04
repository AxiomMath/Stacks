module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChowInjective

/-!
# Flat pullback along a line bundle is an isomorphism on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let
`p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X` be the associated line bundle. Then

  `p^* : A_k(X) ⟶ A_{k+1}(L)`

is an isomorphism for every `k` ([Stacks, Tag 0B74]).

The morphism `p` is flat, locally of finite type and of relative dimension one, being Zariski
locally on `X` the projection `𝔸¹_U ⟶ U`
(`Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase`). Surjectivity is then
[Stacks, Tag 02TT] at rank one, `Stacks.Chow.flatPullbackChow_surjective_isAffineSpaceBundle`.
Injectivity is the zero-section argument `o^* ∘ p^* = (p ∘ o)^* = \mathrm{id}` of
[Stacks, Tag 02TR], `Stacks.Chow.flatPullbackChow_totalSpaceToBase_injective`.

## Main results

* `Stacks.Chow.flatPullbackChow_totalSpaceToBase_bijective` — **[Stacks, Tag 0B74]**.
* `Stacks.Chow.lineBundleFlatPullbackChowEquiv` — the flat pullback `A_k(X) ≃+ A_{k+1}(L)` as an
  isomorphism of groups.

## References

* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `ℒ` be an
invertible `𝒪_X`-module and let `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X` be the associated line
bundle. Then

  `p^* : A_k(X) ⟶ A_{k+1}(L)`

is an isomorphism for every `k`. -/
@[stacks 0B74]
theorem flatPullbackChow_totalSpaceToBase_bijective (k : ℤ) :
    Function.Bijective
      (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
        rfl 1 D.relativeDimension_totalSpaceToBase k) :=
  ⟨flatPullbackChow_totalSpaceToBase_injective C D sX D.relativeDimension_totalSpaceToBase k _,
    flatPullbackChow_surjective_isAffineSpaceBundle C sX D.totalSpaceToBase 1
      D.relativeDimension_totalSpaceToBase D.isAffineSpaceBundle_totalSpaceToBase k⟩

/-- The flat pullback `p^* : A_k(X) ≃+ A_{k+1}(L)` along a line bundle, as an isomorphism of
groups ([Stacks, Tag 0B74]). -/
def lineBundleFlatPullbackChowEquiv (k : ℤ) :
    chowGroup C sX k ≃+ chowGroup C (D.totalSpaceToBase ≫ sX) (k + ((1 : ℕ) : ℤ)) :=
  AddEquiv.ofBijective _ (flatPullbackChow_totalSpaceToBase_bijective C D sX k)

/-- The isomorphism `lineBundleFlatPullbackChowEquiv` sends a cycle class `α` to its flat pullback
`p^* α` along the line bundle `p : L ⟶ X`. -/
@[simp]
theorem lineBundleFlatPullbackChowEquiv_apply (k : ℤ) (α : chowGroup C sX k) :
    lineBundleFlatPullbackChowEquiv C D sX k α =
      flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
        rfl 1 D.relativeDimension_totalSpaceToBase k α :=
  rfl

end Stacks.Chow

end
