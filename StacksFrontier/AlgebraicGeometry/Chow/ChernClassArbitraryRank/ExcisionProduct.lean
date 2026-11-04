module

public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# Products of classes vanishing on complementary pieces

Let `Y` be locally of finite type over the base of chapter 42, let `U ⊆ Y` be open and let
`ι : Y' ⟶ Y` be a closed immersion onto the complement of `U`. If `a ∈ A^p(Y)` restricts to zero
on `Y'` and `b ∈ A^q(Y)` restricts to zero on `U`, then `a · b = 0` in `A^{p+q}(Y)`.

On a test scheme `g : T ⟶ Y` the class `b ∩ α` restricts to zero on `T_U = g⁻¹(U)`, because the
operation of `b` commutes with flat pullback along the open immersion `T_U ⟶ T` and vanishes on a
test scheme over `U`. By the localization sequence of Stacks 02RX it is therefore the pushforward
of a class on `T ×_Y Y'`, and capping it with `a` commutes with that pushforward (the projection
formula of Stacks 0B76) and vanishes over `Y'`.

## Main results

* `Stacks.Chow.idRule_idRule_eq_zero_of_chowCohomologyRestriction_eq_zero` — the statement on
  every test scheme.
* `Stacks.Chow.mulId_eq_zero_of_chowCohomologyRestriction_eq_zero` — `a · b = 0` in `A^{p+q}(Y)`.
* `Stacks.Chow.TotalChowClass.mul_eq_zero_of_res_eq_zero` — the same for total classes.

## References

* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (ι : Y' ⟶ Y) [IsClosedImmersion ι] (U : Y.Opens)
  (hU : Set.range ι.base = (U : Set Y)ᶜ)

/-- **A class restricting to zero on `U` caps to a class restricting to zero on `g⁻¹(U)`.** -/
theorem chowGroupRestrict_idRule_eq_zero_of_chowCohomologyRestriction_eq_zero {q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q)
    (hb : chowCohomologyRestriction C (gysinSystemOfInvertible C) sY U.ι q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b = 0)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    chowGroupOpensRestrictOfIsOpenImmersion C (g ≫ sY) (g ⁻¹ᵁ U) (k - q)
      (b.idRule C sY (gysinSystemOfInvertible C) g k α) = 0 := by
  set W := g ⁻¹ᵁ U
  have hr := relativeDimension_of_isOpenImmersion W.ι
  have hflat := idRule_flatPullbackChow_heq C sY b g (W.ι ≫ g) W.ι 0 hr rfl k α
  have hzero := idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sY b U.ι hb (W.ι ≫ g)
    (g ∣_ U) (morphismRestrict_ι g U) (k + ((0 : ℕ) : ℤ))
    (flatPullbackChow C ((W.ι ≫ g) ≫ sY) (g ≫ sY) W.ι (by rw [Category.assoc]) 0 hr k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ W.ι _ 0 hr k) α)
  rw [hzero] at hflat
  rw [← chowGroupRestrict_opensι]
  have key : flatPullbackChow C ((W.ι ≫ g) ≫ sY) (g ≫ sY) W.ι (by rw [Category.assoc]) 0 hr
      (k - q) (flatPullbackFactorsThroughRationalEquivalence_general C _ _ W.ι _ 0 hr (k - q))
      (b.idRule C sY (gysinSystemOfInvertible C) g k α) = 0 :=
    eq_of_heq (hflat.symm.trans (chowGroup_zero_heq C _ (by omega)))
  exact (flatPullbackChow_eq_zero_iff_chowGroupRestrict_eq_zero C (g ≫ sY)
    ((W.ι ≫ g) ≫ sY) W.ι (by rw [Category.assoc]) (k - q) _ _).1 key

include hU in
/-- **Stacks 02RX and 0B76 combined, on a test scheme.** If `a ∈ A^p(Y)` restricts to zero along
the closed immersion `ι` and `b ∈ A^q(Y)` restricts to zero on the complementary open `U`, then
`a ∩ (b ∩ α) = 0` for every class `α` on every test scheme. -/
theorem idRule_idRule_eq_zero_of_chowCohomologyRestriction_eq_zero {p q : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (ha : chowCohomologyRestriction C (gysinSystemOfInvertible C) sY ι p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a = 0)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q)
    (hb : chowCohomologyRestriction C (gysinSystemOfInvertible C) sY U.ι q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b = 0)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    a.idRule C sY (gysinSystemOfInvertible C) g (k - q)
      (b.idRule C sY (gysinSystemOfInvertible C) g k α) = 0 := by
  have hrestr := chowGroupRestrict_idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sY U b hb
    g k α
  set i := pullback.snd ι g
  have hi : i ≫ (g ≫ sY) = (pullback.fst ι g ≫ ι) ≫ sY := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  have hcompl : Set.range i.base = (Set.range (g ⁻¹ᵁ U).ι.base)ᶜ := by
    rw [Scheme.Pullback.range_snd, hU, Scheme.Opens.range_ι]
    rfl
  obtain ⟨δ, hδ⟩ := (exact_chowPushforward_chowGroupOpensRestrict C (g ≫ sY)
    ((pullback.fst ι g ≫ ι) ≫ sY) i hi (g ⁻¹ᵁ U) hcompl (k - q) _).1 hrestr
  rw [← hδ]
  have : LocallyOfFiniteType (pullback.fst ι g ≫ ι) := by
    rw [pullback.condition]
    infer_instance
  show a.idRule C sY (gysinSystemOfInvertible C) g (k - q)
    (chowPush C ((pullback.fst ι g ≫ ι) ≫ sY) (g ≫ sY) i hi (k - q) δ) = 0
  rw [idRule_chowPush_of_eq C sY a g (i ≫ g) i rfl ((pullback.fst ι g ≫ ι) ≫ sY)
    (by rw [← pullback.condition]) hi (k - q) δ,
    idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sY a ι ha (i ≫ g) (pullback.fst ι g)
      pullback.condition, map_zero]

include hU in
/-- **The product of two classes vanishing on complementary pieces vanishes.** If `a ∈ A^p(Y)`
restricts to zero along the closed immersion `ι` and `b ∈ A^q(Y)` restricts to zero on the
complementary open `U`, then `a · b = 0` in `A^{p+q}(Y)`. -/
theorem mulId_eq_zero_of_chowCohomologyRestriction_eq_zero {p q : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (ha : chowCohomologyRestriction C (gysinSystemOfInvertible C) sY ι p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) a = 0)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q)
    (hb : chowCohomologyRestriction C (gysinSystemOfInvertible C) sY U.ι q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) b = 0) :
    a.mulId C sY b = 0 := by
  refine BivariantClass.eq_of_idRule_eq C sY _ _ _ fun g _ k α ↦ eq_of_heq ?_
  refine (BivariantClass.idRule_mulId C sY a b g k α).trans ?_
  rw [idRule_idRule_eq_zero_of_chowCohomologyRestriction_eq_zero C sY ι U hU a ha b hb g k α,
    BivariantClass.idRule_zero]
  exact chowGroup_zero_heq C _ (by ring)

include hU in
/-- **The product of two total classes vanishing on complementary pieces vanishes.** -/
theorem TotalChowClass.mul_eq_zero_of_res_eq_zero {a b : TotalChowClass C sY}
    (ha : TotalChowClass.res ι rfl a = 0) (hb : TotalChowClass.res U.ι rfl b = 0) :
    a * b = 0 := by
  refine TotalChowClass.ext fun n ↦ ?_
  rw [TotalChowClass.mul_apply, TotalChowClass.zero_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [TotalChowClass.mulTerm]
  split_ifs
  · rw [mulId_eq_zero_of_chowCohomologyRestriction_eq_zero C sY ι U hU (a (n - j))
      (congrArg (· (n - j)) ha) (b j) (congrArg (· j) hb), map_zero]
  · rfl

end Stacks.Chow

end
