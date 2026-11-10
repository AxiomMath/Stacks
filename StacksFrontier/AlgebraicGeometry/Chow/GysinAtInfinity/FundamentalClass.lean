module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Class
public import StacksFrontier.AlgebraicGeometry.Chow.GysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.InfinityClass
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf

/-!
# The class at infinity on a fundamental class

Let `(π : W ⟶ X, j : U ⟶ W, L, s)` be the data of the general construction of Stacks 0F9J
(`Stacks.Chow.GysinAtInfinity.infinityClass`): `U ⊆ W` is the complement of the zero scheme
`D = Z(s)` of a section of an invertible module, and `U ⟶ X` is flat of relative dimension one.
For a test scheme `g : T ⟶ X` of δ-dimension at most `k`, the class at infinity `C` caps the
fundamental class by

  `C ∩ [T]_k = [D ×_X T]_k`

as soon as `dim_δ(W ×_X T) ≤ k + 1` and the pulled-back divisor is an effective Cartier divisor
of `W ×_X T`. This is the source's computation `C ∩ [X]_n = i_∞^*[W]_{n+1} = [W_∞]_n` in the proof
of Stacks 0FBM: the fundamental class `[W ×_X T]_{k+1}` restricts on `U ×_X T` to the flat
pullback of `[T]_k` (Stacks 02RE), so it is a lift of `[T]_k`, and the Gysin map of the effective
Cartier divisor carries it to the fundamental class of the divisor (Stacks 02TB (1)).

## Main results

* `Stacks.Chow.chowGroupRestrict_fundamentalChowClass` — restriction to an open subscheme carries
  a fundamental class to a fundamental class.
* `Stacks.Chow.gysinSystemOfInvertible_onChow_fundamentalChowClass` — the Gysin map of the Gysin
  system of an invertible module carries `[T]_{k+1}` to the fundamental class of an effective
  Cartier zero scheme.
* `Stacks.Chow.GysinAtInfinity.infinityCap_fundamentalChowClass` — `C ∩ [T]_k = [D ×_X T]_k`.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Restriction to an open subscheme carries a fundamental class to a fundamental class**: for
`X` of δ-dimension at most `k` and `j : U ⟶ X` an open immersion, `[X]_k|_U = [U]_k`. Restriction
is flat pullback of relative dimension zero (Stacks 02RE). -/
theorem chowGroupRestrict_fundamentalChowClass (C : ChowSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)
    (hdim : schemeDeltaDimension C sX ≤ (k : EInt)) :
    chowGroupRestrict C sX sU j hj k (fundamentalChowClass C sX k) =
      fundamentalChowClass C sU k := by
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  rw [← cast_flatPullbackChow_eq_chowGroupRestrict C sX sU j hj k hk
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _),
    flatPullbackChow_fundamentalChowClass C sU sX j hj 0 _ k _ hdim]
  exact eq_of_heq ((eqRec_heq _ _).trans (fundamentalChowClass_heq C sU hk))

/-- **The Gysin map of an effective Cartier zero scheme on a fundamental class** (Stacks 02TB (1)),
for the Gysin system of an invertible module: `i^*[T]_{k+1} = [D]_k` when `T` has δ-dimension at
most `k + 1` and the zero scheme `D` of `s` is an effective Cartier divisor. -/
theorem gysinSystemOfInvertible_onChow_fundamentalChowClass (C : ChowSituation.{u})
    {T : Scheme.{u}} (p : T ⟶ C.S) [LocallyOfFiniteType p] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt))
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme T L s)) :
    (gysinSystemOfInvertible C).onChow p L s k (fundamentalChowClass C p (k + 1)) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ p) k := by
  rw [← gysinChowOfInvertible_fundamentalChowClass C p k L s hdim hC, fundamentalChowClass,
    GysinSystem.onChow_mk, gysinChowOfInvertible_mk]
  rfl

/-- Proper pushforward on Chow groups along an isomorphism over the base carries a fundamental
class to the fundamental class. -/
theorem properChowPushforward_fundamentalChowClass_of_isIso (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u] (hu : u ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k) :
    properChowPushforward C sA sB u hu k hfac (fundamentalChowClass C sA k) =
      fundamentalChowClass C sB k := by
  rw [fundamentalChowClass, properChowPushforward_mk,
    properPushforward_fundamentalCycle_of_isIso C sA sB u hu k]
  rfl

namespace GysinAtInfinity

section Class

variable (C : ChowSituation.{u}) {X W U : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (π : W ⟶ X) [LocallyOfFiniteType π] (j : U ⟶ W) [IsOpenImmersion j] [Flat (j ≫ π)]
  (hU : AlgebraicGeometry.RelativeDimension (j ≫ π) 1) (L : W.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (hcompl : Set.range (Stacks.Divisors.zeroScheme W L s).subschemeι.base = (Set.range j.base)ᶜ)
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme W L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme W L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W L s).subschemeι).obj L))

/-- The fundamental class `[W ×_X T]_{k+1}` is a lift of `[T]_k`: on `U ×_X T` it restricts to
the flat pullback of `[T]_k` along `U ×_X T ⟶ T`, both being the fundamental class there. -/
theorem isLift_fundamentalChowClass {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (hT : schemeDeltaDimension C (g ≫ f) ≤ (k : EInt))
    (hW : schemeDeltaDimension C (testStr C f π g) ≤ ((k + 1 : ℤ) : EInt)) :
    IsLift C f π j hU g k (fundamentalChowClass C (g ≫ f) k)
      (fundamentalChowClass C (testStr C f π g) (k + 1)) := by
  have := isOpenImmersion_openBaseChange π j g
  unfold IsLift
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ _ (k + 1) hW,
    flatPullbackChow_fundamentalChowClass C _ _ _ rfl 1 _ k _ hT]
  rfl

/-- **The class at infinity on a fundamental class**: `C ∩ [T]_k = [D ×_X T]_k`, for a test scheme
`T` of δ-dimension at most `k` with `dim_δ(W ×_X T) ≤ k + 1` and the pulled-back divisor an
effective Cartier divisor of `W ×_X T`. -/
theorem infinityCap_fundamentalChowClass {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) (hT : schemeDeltaDimension C (g ≫ f) ≤ (k : EInt))
    (hW : schemeDeltaDimension C (testStr C f π g) ≤ ((k + 1 : ℤ) : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (gysinTripleDivisor L s (pullback.fst π g))) :
    infinityCap C f π j hU L s hcompl htriv g k (fundamentalChowClass C (g ≫ f) k) =
      fundamentalChowClass C (pullback.fst (gysinTripleInclusion L s ≫ π) g ≫
        (gysinTripleInclusion L s ≫ (π ≫ f))) (k - 0) := by
  rw [infinityCap_eq_of_isLift C f π j hU L s hcompl htriv
    (isLift_fundamentalChowClass C f π j hU g k hT hW), divisorMiddleCap, middleCap_apply]
  change chowGroupDegreeEquiv C _ _ (properChowPushforward C _ _ _ _ _ _
    (gysinBivariantCap C (gysinSystemOfInvertible C) (π ≫ f) L s (pullback.fst π g) (k + 1)
      (fundamentalChowClass C (testStr C f π g) (k + 1)))) = _
  rw [gysinBivariantCap_apply, chowGroupDegreeEquiv_fundamentalChowClass,
    gysinSystemOfInvertible_onChow_fundamentalChowClass C _ _ _ _
      (by rw [show k + 1 - 1 + 1 = k + 1 by ring]; exact hW) hcart,
    chowPushforwardOfIso_fundamentalChowClass, properChowPushforward_fundamentalChowClass_of_isIso,
    chowGroupDegreeEquiv_fundamentalChowClass]

/-- **The class at infinity on the fundamental class of the base**, at the test scheme `𝟙 X`:
`C ∩ [X]_k = [D ×_X X]_k`, for `X` of δ-dimension at most `k` and `W` of δ-dimension at most
`k + 1`, when the divisor `D` is an effective Cartier divisor of `W`. -/
theorem infinityCap_id_fundamentalChowClass (k : ℤ) (hX : schemeDeltaDimension C f ≤ (k : EInt))
    (hW : schemeDeltaDimension C (π ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme W L s)) :
    infinityCap C f π j hU L s hcompl htriv (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ f) k) =
      fundamentalChowClass C (pullback.fst (gysinTripleInclusion L s ≫ π) (𝟙 X) ≫
        (gysinTripleInclusion L s ≫ (π ≫ f))) (k - 0) := by
  refine infinityCap_fundamentalChowClass C f π j hU L s hcompl htriv (𝟙 X) k
    ((schemeDeltaDimension_congr C (Category.id_comp f)).trans_le hX) ?_ ?_
  · exact schemeDeltaDimension_le_of_isClosedImmersion C (π ≫ f) (pullback.fst π (𝟙 X)) hW
  · rw [gysinTripleDivisor, Stacks.Divisors.zeroScheme_pullback]
    exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _ hcart _

end Class

end GysinAtInfinity

end Stacks.Chow

end
