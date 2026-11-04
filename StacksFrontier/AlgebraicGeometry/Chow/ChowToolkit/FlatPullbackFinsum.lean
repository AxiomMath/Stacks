module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.CycleFinsumPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence

/-!
# A Chow class as the flat pullback of a locally finite sum of classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be flat of
relative dimension `r` between schemes locally of finite type over `S`, and let `(W_j)_j` be a
locally finite family of closed subschemes of `Y`. Write `f_j : f^{-1}(W_j) ⟶ W_j` for the
restriction of `f`, again flat of relative dimension `r`.

This file assembles the identity the devissage of Stacks 02TT needs: if a `(k+r)`-cycle `α` on `X`
is coefficientwise the locally finite sum of the pushforwards of cycles `d_j` on the inverse images
`f^{-1}(W_j)`, and each `d_j` is rationally equivalent to the flat pullback `f_j^* b_j` of a
`k`-cycle `b_j` on `W_j`, then the class of `α` is the flat pullback of a single class on `Y` —
namely of the locally finite sum of the classes of the `b_j`.

Both halves of the proof are imported. Forming the sum on `Y` is
`Stacks.Chow.exists_cycle_finsum_properPushforward`; that its pullback is again a locally finite
sum of pushforwards is the closed-immersion case of Stacks 02RG on cycles,
`Stacks.Chow.flatPullback_properPushforward_comap`, read coefficientwise; and that the resulting
cycle is rationally equivalent to `α` is Stacks 02RZ at the locally finite family of inverse
images `f^{-1}(W_j)`.

## Main results

* `Stacks.Chow.exists_flatPullbackChow_eq_of_finsum_properPushforward` — the identity above: a
  Chow class on `X` presented as a locally finite sum over the `f^{-1}(W_j)` of pullbacks from the
  `W_j` is in the image of `f^*`.

## Implementation notes

The index type is restricted to `Type u`, the universe of the schemes, because Stacks 02RZ is: see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.CycleFinsumPushforward`.

The two base-change facts for `Stacks.Chow.comapRestrict` — that it is again locally of finite type
and again flat — are local instances here, so that the flat pullbacks along the restrictions `f_j`
can be written without threading them through the statement.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02R9](https://stacks.math.columbia.edu/tag/02R9)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] locallyOfFiniteType_comapRestrict flat_comapRestrict

/-- **A Chow class presented as a locally finite sum of pullbacks over a locally finite family of
closed subschemes is a flat pullback.** Let `f : X ⟶ Y` be flat of relative dimension `r`, let
`(W_j)_j` be a locally finite family of closed subschemes of `Y`, let `b_j` be a `k`-cycle on
`W_j` and let `d_j` be a `(k+r)`-cycle on `f^{-1}(W_j)` rationally equivalent there to the flat
pullback of `b_j`. If the `(k+r)`-cycle `α` on `X` is coefficientwise the locally finite sum of
the pushforwards of the `d_j`, then the class of `α` is the flat pullback of a class on `Y`.

The class on `Y` is that of the locally finite sum of the pushforwards of the `b_j`, which is a
cycle by `Stacks.Chow.exists_cycle_finsum_properPushforward`. Its flat pullback is coefficientwise
the locally finite sum of the pushforwards of the `f_j^* b_j`, because flat pullback multiplies the
coefficient at the image point by a weight and so passes through the sum, and because the
closed-immersion case of Stacks 02RG on cycles
(`Stacks.Chow.flatPullback_properPushforward_comap`) identifies the pullback of each pushed-forward
summand. Stacks 02RZ at the family of inverse images — locally finite by Stacks 02R9 — then
identifies that cycle with `α` up to rational equivalence. -/
theorem exists_flatPullbackChow_eq_of_finsum_properPushforward (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) {J : Type u}
    (W : J → Y.IdealSheafData) (hW : LocallyFinite fun j ↦ ((W j).support : Set Y))
    (b : ∀ j, CycleGroup C ((W j).subschemeι ≫ sY) k)
    (d : ∀ j, CycleGroup C (((W j).comap f).subschemeι ≫ f ≫ sY) (k + (r : ℤ)))
    (hbd : ∀ j, RationallyEquivalent C (((W j).comap f).subschemeι ≫ f ≫ sY) (k + (r : ℤ))
      (flatPullback C (((W j).comap f).subschemeι ≫ f ≫ sY) ((W j).subschemeι ≫ sY)
        (comapRestrict (W j) f) (comapRestrict_comp_base C (f ≫ sY) sY f rfl (W j)) r
        (relativeDimension_comapRestrict (W j) f hf) k (b j)) (d j))
    (α : CycleGroup C (f ≫ sY) (k + (r : ℤ)))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (properPushforward C
      (((W j).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY) ((W j).comap f).subschemeι rfl
      (k + (r : ℤ)) (d j)).1 x) :
    ∃ β : chowGroup C sY k,
      flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k β =
        QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sY) (k + (r : ℤ))) α := by
  obtain ⟨γ, hγ⟩ := exists_cycle_finsum_properPushforward C sY k W hW b
  refine ⟨QuotientAddGroup.mk' (rationalEquivalences C sY k) γ, ?_⟩
  rw [flatPullbackChowOfRelativeDimension_mk]
  refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
  have hTloc : LocallyFinite fun j : J ↦ (((W j).comap f).support : Set X) := by
    simpa only [coe_support_comap] using hW.preimage_continuous f.continuous
  refine rationallyEquivalent_finsum_of_closedSupports C (f ≫ sY) (k + (r : ℤ))
    (fun j ↦ (W j).comap f) hTloc
    (fun j ↦ flatPullback C (((W j).comap f).subschemeι ≫ f ≫ sY) ((W j).subschemeι ≫ sY)
      (comapRestrict (W j) f) (comapRestrict_comp_base C (f ≫ sY) sY f rfl (W j)) r
      (relativeDimension_comapRestrict (W j) f hf) k (b j)) d hbd (fun x ↦ ?_) hα
  rw [flatPullback_apply, hγ (f.base x), finsum_mul]
  refine finsum_congr fun j ↦ ?_
  rw [← flatPullback_apply C (f ≫ sY) sY f rfl r hf k _ x,
    flatPullback_properPushforward_comap C (f ≫ sY) sY f rfl r hf k (W j) (b j)]

end Stacks.Chow

end
