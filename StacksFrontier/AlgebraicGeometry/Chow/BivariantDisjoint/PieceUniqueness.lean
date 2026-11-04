module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksCore.Tactic.StacksAttribute

/-!
# A bivariant class is determined by its restrictions to the pieces

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over the base scheme of chapter 42
of the Stacks Project and let `X = ∐_{i ∈ I} X_i` be a decomposition into open and closed
subschemes. For a test scheme `g : T ⟶ Y` the base change `X ×_Y T` decomposes into the open and
closed pieces `X_i ×_Y T`, the preimages of the `X_i` under the projection to `X`, so

  `CH_k(X ×_Y T) = ∏_{i ∈ I} CH_k(X_i ×_Y T)`.

Consequently a bivariant class of degree `p` for `f` is determined by the restrictions of its cap
operations to those pieces. This is the injectivity half of Stacks 0FDZ: it says that the map from
`A^p(X ⟶ Y)` to the product over the pieces is injective, without reference to the decomposition
of the target or to the construction of that map.

## Main results

* `Stacks.Chow.chowGroupClopenRestrict_eq_chowGroupRestrict` — the components of the decomposition
  of a Chow group along a decomposition into open and closed subschemes are restriction along the
  piece inclusions.
* `Stacks.Chow.BivariantClass.eq_of_clopenRestrict_cap_eq` — **Stacks 0FDZ, injectivity.** Two
  bivariant classes for `f` whose cap operations agree after restriction to every piece of `X` are
  equal.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The components of the decomposition of a Chow group -/

/-- The components of the decomposition `CH_k(Z) = ∏_i CH_k(Z_i)` of the Chow group of a scheme
along a decomposition into open and closed subschemes are restriction of Chow classes along the
inclusions of the pieces. -/
theorem chowGroupClopenRestrict_eq_chowGroupRestrict (C : ChowSituation.{u}) {Z : Scheme.{u}}
    (q : Z ⟶ C.S) [LocallyOfFiniteType q] {I : Type u} {U : I → Z.Opens}
    (hz : IsClopenDecomposition U) (k : ℤ) (hdec : RationalEquivalenceDecomposes C q hz k)
    (α : chowGroup C q k) (i : I) :
    chowGroupClopenRestrict C q hz k hdec α i =
      chowGroupRestrict C q ((U i).ι ≫ q) (U i).ι rfl k α := by
  induction α using QuotientAddGroup.induction_on with
  | H c => rfl

/-! ### Uniqueness -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ) {I : Type u} (UX : I → X.Opens)
  (hX : IsClopenDecomposition UX)

include hX in
/-- **Stacks 0FDZ, injectivity.** Two bivariant classes of degree `p` for `f : X ⟶ Y` are equal as
soon as, for every test scheme `g : T ⟶ Y` and every `k`, their cap operations agree after
restriction to each piece `X_i ×_Y T` of `X ×_Y T`.

The pieces of `X ×_Y T` are the preimages of the pieces of `X` under the projection, a
decomposition into open and closed subschemes by
`Stacks.Chow.IsClopenDecomposition.preimage`, so restriction to them is jointly injective on
`CH_{k-p}(X ×_Y T)` by `Stacks.Chow.chowGroupClopenEquiv`. -/
@[stacks 0FDZ "injectivity: a bivariant class is determined by its restrictions to the pieces"]
theorem BivariantClass.eq_of_clopenRestrict_cap_eq {c d : BivariantClass C G sX sY f hf p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sY) k) (i : I),
      chowGroupRestrict C (pullback.fst f g ≫ sX)
          ((pullback.fst f g ⁻¹ᵁ UX i).ι ≫ (pullback.fst f g ≫ sX))
          (pullback.fst f g ⁻¹ᵁ UX i).ι rfl (k - p) (c.cap g k α) =
        chowGroupRestrict C (pullback.fst f g ≫ sX)
          ((pullback.fst f g ⁻¹ᵁ UX i).ι ≫ (pullback.fst f g ≫ sX))
          (pullback.fst f g ⁻¹ᵁ UX i).ι rfl (k - p) (d.cap g k α)) :
    c = d :=
  BivariantClass.ext C G sX sY f hf p fun {T} g _ k α ↦ by
    have hdec := IsClopenDecomposition.preimage hX (pullback.fst f g)
    refine (chowGroupClopenEquiv C (pullback.fst f g ≫ sX) hdec (k - p)
      (rationalEquivalenceDecomposes_of_isClopenDecomposition C (pullback.fst f g ≫ sX)
        hdec (k - p))).injective (funext fun i ↦ ?_)
    rw [chowGroupClopenEquiv_apply, chowGroupClopenEquiv_apply,
      chowGroupClopenRestrict_eq_chowGroupRestrict,
      chowGroupClopenRestrict_eq_chowGroupRestrict]
    exact h (T := T) g k α i

end Stacks.Chow

end
