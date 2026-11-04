module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces

/-!
# Surjectivity of flat pullback from a decomposition of the target into open and closed pieces

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` which is flat of relative dimension `r`. If
`Y` is decomposed into pairwise disjoint open subschemes covering it, and flat pullback in degree
`k` is surjective along the restriction of `f` to each piece, then it is surjective along `f`.

Both `Y` and `X` decompose, Chow groups turn the decompositions into products by
`Stacks.Chow.chowGroupClopenEquiv`, and flat pullback is the product of its restrictions by
Stacks 02RD. So surjectivity is checked factor by factor.

This complements the localization step
`Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap`, which treats an open subscheme
together with its *closed* complement. Here the complement is open as well, which is what makes
the conclusion a bijection of products rather than a five-term exact sequence.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_isClopenDecomposition` — surjectivity of flat
  pullback from the pieces of such a decomposition of the target.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Stacks.Chow

/-- The factor of the product decomposition of `A_k(X)` at a piece is restriction of Chow classes
to that piece: both are the cycle-level restriction read through the quotient. -/
theorem chowGroupClopenRestrict_eq_chowGroupOpensRestrict (C : ChowSituation.{u})
    {X : Scheme.{u}} {I : Type v} {U : I → X.Opens} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (h : IsClopenDecomposition U) (k : ℤ) (hdec : RationalEquivalenceDecomposes C f h k)
    (α : chowGroup C f k) (i : I) :
    chowGroupClopenRestrict C f h k hdec α i =
      chowGroupOpensRestrictOfIsOpenImmersion C f (U i) k α := by
  induction α using QuotientAddGroup.induction_on with
  | H c => rfl

/-- **Surjectivity of flat pullback from a decomposition of the target into open and closed
subschemes.** Let `f : X ⟶ Y` be flat of relative dimension `r` between schemes locally of finite
type over the base of chapter 42, and let `V : I → Y.Opens` be a family of pairwise disjoint open
subschemes covering `Y`. If flat pullback in degree `k` is surjective along every restriction
`f ∣_ V i`, then it is surjective along `f`.

A class `α` on `X` restricts to each piece `f^{-1}(V i)`; by hypothesis those restrictions are
pullbacks of classes `β i` on `V i`, and the `β i` assemble to a class `β` on `Y` because
`A_k(Y) = ∏_i A_k(V i)`. Flat pullback commutes with restriction to a piece by Stacks 02RD, so
`f^* β` and `α` have the same restriction to every piece, hence are equal by the same product
decomposition for `X`. -/
theorem flatPullbackChow_surjective_of_isClopenDecomposition (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) {I : Type u} (V : I → Y.Opens)
    (h : IsClopenDecomposition V)
    (hV : ∀ i, Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((f ⁻¹ᵁ V i).ι ≫ f ≫ sY) ((V i).ι ≫ sY) (f ∣_ (V i))
      (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
      (relativeDimension_morphismRestrict' f (V i) r hf) k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  intro α
  choose β hβ using fun i ↦ hV i (chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY)
    (f ⁻¹ᵁ V i) (k + (r : ℤ)) α)
  have hX : IsClopenDecomposition fun i ↦ f ⁻¹ᵁ V i := h.preimage f
  have hdecY := rationalEquivalenceDecomposes_of_isClopenDecomposition C sY h k
  have hdecX := rationalEquivalenceDecomposes_of_isClopenDecomposition C (f ≫ sY) hX
    (k + (r : ℤ))
  refine ⟨(chowGroupClopenEquiv C sY h k hdecY).symm β, ?_⟩
  refine (chowGroupClopenEquiv C (f ≫ sY) hX (k + (r : ℤ)) hdecX).injective (funext fun i ↦ ?_)
  rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
    chowGroupClopenRestrict_eq_chowGroupOpensRestrict,
    chowGroupClopenRestrict_eq_chowGroupOpensRestrict,
    chowGroupOpensRestrict_flatPullbackChow C sY f r hf k (V i)]
  have hsymm : chowGroupOpensRestrictOfIsOpenImmersion C sY (V i) k
      ((chowGroupClopenEquiv C sY h k hdecY).symm β) = β i := by
    rw [← chowGroupClopenRestrict_eq_chowGroupOpensRestrict C sY h k hdecY]
    exact congrFun ((chowGroupClopenEquiv C sY h k hdecY).apply_symm_apply β) i
  rw [hsymm]
  exact hβ i

end Stacks.Chow

end
