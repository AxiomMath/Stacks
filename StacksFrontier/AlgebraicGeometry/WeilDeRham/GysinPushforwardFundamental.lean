module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison

/-!
# The Gysin map on the pushforward of a fundamental class

Let `f : X ⟶ Y` be a local complete intersection morphism for which the Gysin map exists
(Stacks 0FF3), with `X`, `Y` pure of `δ`-dimensions `n` and `m`, and let `t : T ⟶ Y` be proper
with `T` pure of `δ`-dimension `m'`. If `X ×_Y T` has the expected dimension
`m' - (m - n)` and the local rings of `T` are Cohen–Macaulay where needed, then

  `f^!(t_*[T]) = t'_*[X ×_Y T]`,

`t' : X ×_Y T ⟶ X` being the base change of `t`. This is the combination of three facts: the Gysin
map of `f` is homogeneous of degree `m - n` (the proof of Stacks 0FF7), bivariant classes commute
with proper pushforward (Stacks 0B76 (1)), and `f^![T] = [X ×_Y T]` (Stacks 0FF7, in a single
degree, `Stacks.Chow.cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass`).

For the self-products of smooth projective schemes this computes the Gysin pullback of the class
of a diagonal along a projection (Lemma 0FIL).

## Main results

* `Stacks.WeilDeRham.lciGysinMapComponent_eq_zero_of_ne`: the part of `f^!` of degree `q ≠ m - n`
  vanishes.
* `Stacks.WeilDeRham.lciGysinChow_properChowPushforward_fundamentalChowClass`: `f^!(t_*[T]) =
  t'_*[X ×_Y T]` in `CH_{m' - (m - n)}(X)`.
* `Stacks.WeilDeRham.lciGysinRational_rationalProperChowPushforward_rationalFundamentalClass`: the
  same in `CH_*(X) ⊗ 𝐐`, for schemes smooth over a field.

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Chow

universe u

namespace Stacks.WeilDeRham

section General

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
  {n m : ℤ}
  (hXn : ∀ W : irreducibleComponents X,
    deltaDimension C sX ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩ = n)
  (hYm : ∀ W : irreducibleComponents Y,
    deltaDimension C sY ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set Y) W.2⟩ = m)

include hXn hYm in
/-- **The Gysin map is homogeneous of degree `m - n`**: for `X`, `Y` pure of `δ`-dimensions `n`
and `m`, the part of degree `q ≠ m - n` of `f^! ∈ A^*(X ⟶ Y)^∧` vanishes. -/
theorem lciGysinMapComponent_eq_zero_of_ne {q : ℤ} (hq : q ≠ m - n) :
    lciGysinMapComponent C sX sY hf hlci h q = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨d, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty f).1 h) :
    SmoothFactorization f).exists_hasCapFundamentalFormula_gysinMap C sX sY hf hlci
  have hda : ∀ a, d a = m - n := by
    intro a
    obtain ⟨ξ, hξ, hξa⟩ := exists_mem_genericPoints_mk_eq a
    have hdξ := hdeg ξ hξ m fun W ↦
      deltaDimension_irreducibleComponents_of_isOpenImmersion C sY hYm _ W
    have hξn : relativeDimension C.dimensionFunction sX ξ = n := by
      rw [← hXn ⟨_, hξ⟩, deltaDimension_eq_of_isGenericPoint C _ _ ξ isGenericPoint_closure]
    rw [← hξa, hdξ, hξn]
  change (bivariantConnectedComponentEquiv C _ sX sY f hf q _ _ _).symm
    (fun i => lciGysinMap C sX sY hf hlci h i q) = 0
  rw [show (fun i => lciGysinMap C sX sY hf hlci h i q) = 0 from funext fun w ↦ ?_, map_zero]
  change (Classical.choice ((gysinMapExists_iff_nonempty f).1 h) :
    SmoothFactorization f).gysinMap C sX sY hf hlci w q = 0
  rw [(hd w).1, hda w]
  exact DirectSum.of_eq_of_ne _ _ _ hq

variable {T : Scheme.{u}} (t : T ⟶ Y) [IsProper t] {m' : ℤ}
  (hTm' : ∀ W : irreducibleComponents T,
    deltaDimension C (t ≫ sY)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set T) W.2⟩ = m')
  (hdim : ∀ ξ : (pullback f t : Scheme.{u}),
    relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ ≤ m' - (m - n))
  (hCM : ∀ ξ : (pullback f t : Scheme.{u}),
    relativeDimension C.dimensionFunction (pullback.fst f t ≫ sX) ξ = m' - (m - n) →
    letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
    IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd f t ξ)))

include hXn hYm hTm' hdim hCM in
/-- **`f^!(t_*[T]) = t'_*[X ×_Y T]`** in `CH_{m' - (m - n)}(X)`, for the part of degree `m - n`
of the Gysin map of `f`, `t' : X ×_Y T ⟶ X` the base change of `t`. -/
theorem lciGysinChow_properChowPushforward_fundamentalChowClass :
    lciGysinChow C sX sY hf hlci h (m - n) m'
        (properChowPushforward C (t ≫ sY) sY t rfl m' (properPushforwardDescends C _ _ _ _ _)
          (fundamentalChowClass C (t ≫ sY) m')) =
      properChowPushforward C (pullback.fst f t ≫ sX) sX (pullback.fst f t) rfl (m' - (m - n))
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (pullback.fst f t ≫ sX) (m' - (m - n))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  set c := lciGysinMapComponent C sX sY hf hlci h (m - n)
  set h' : pullback f t ⟶ pullback f (𝟙 Y) := pullback.fst f t ≫ (pullbackIdIso f).hom
  have hfst : h' ≫ pullback.fst f (𝟙 Y) = pullback.fst f t := by simp [h']
  have hsnd : h' ≫ pullback.snd f (𝟙 Y) = pullback.snd f t ≫ t := by
    simp [h', pullback.condition]
  have hcap := BivariantClass.cap_properChowPushforward c (properPushforwardDescends C) (𝟙 Y) t
    t (Category.comp_id t) h' hfst hsnd m' (fundamentalChowClass C (t ≫ sY) m')
  rw [cap_completedBivariantSequenceOfInvertible_lciGysinMap_fundamentalChowClass C sX sY hf hlci h
    t hXn hYm hTm' hdim hCM] at hcap
  have e1 : chowGroupCongr C (Category.id_comp sY).symm m'
      (properChowPushforward C (t ≫ sY) sY t rfl m' (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (t ≫ sY) m')) =
      properChowPushforward C (t ≫ sY) (𝟙 Y ≫ sY) t (by rw [Category.id_comp]) m'
        (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
        (fundamentalChowClass C (t ≫ sY) m') :=
    properChowPushforward_chowGroupCongr C rfl _ t rfl _ m' _ _ _
  rw [lciGysinChow, BivariantClass.capTargetHom_apply, BivariantClass.capTarget, e1]
  change chowPushforwardOfIso C _ sX (pullbackIdIso f).inv _ _ (c.cap (𝟙 Y) m' _) = _
  rw [hcap, chowPushforwardOfIso, ← properChowPushforward_comp_apply C _ _ sX h'
    (pullbackIdIso f).inv (pullback.fst f t) (by simp [h'])]

end General

section Field

open Stacks.WeilCohomology (deltaDimension_irreducibleComponent_of_relativeDimension
  relativeDimension_of_mem_irreducibleComponents_of_relativeDimension)

variable (k : Type u) [Field k] {X Y T : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
  (t : T ⟶ Y) [IsProper t] [Smooth (t ≫ sY)]
  [IsNoetherian T] [IsNoetherian (pullback f t)] [Flat (pullback.fst f t ≫ sX)]
  {n m m' N : ℕ} (hX : RelativeDimension sX n) (hY : RelativeDimension sY m)
  (hT : RelativeDimension (t ≫ sY) m') (hP : RelativeDimension (pullback.fst f t ≫ sX) N)
  (hN : (N : ℤ) = m' - (m - n))

include hX hY hT hP hN in
/-- **`f^!(t_*[T]) = t'_*[X ×_Y T]` in `CH_*(X) ⊗ 𝐐`**, for schemes smooth over a field `k`: `X`,
`Y`, `T` of constant dimensions `n`, `m`, `m'`, `t : T ⟶ Y` proper, and the fibre product
`X ×_Y T` flat of the expected constant dimension `N = m' - (m - n)` over `k`. -/
theorem lciGysinRational_rationalProperChowPushforward_rationalFundamentalClass :
    lciGysinRational (fieldChowSituation k) sX sY hf hlci h
        (rationalProperChowPushforward (fieldChowSituation k) (t ≫ sY) sY (f := t) rfl
          (rationalFundamentalClass (fieldChowSituation k) (t ≫ sY))) =
      rationalProperChowPushforward (fieldChowSituation k) (pullback.fst f t ≫ sX) sX
        (f := pullback.fst f t) rfl
        (rationalFundamentalClass (fieldChowSituation k) (pullback.fst f t ≫ sX)) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (t ≫ sY)
  have hXn := deltaDimension_irreducibleComponent_of_relativeDimension k sX n hX
  have hYm := deltaDimension_irreducibleComponent_of_relativeDimension k sY m hY
  have hTm := deltaDimension_irreducibleComponent_of_relativeDimension k (t ≫ sY) m' hT
  have hgen : ∀ W : irreducibleComponents (pullback f t : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f t ≫ sX)
        W.2.1.genericPoint = N := fun W ↦
    relativeDimension_of_mem_irreducibleComponents_of_relativeDimension k _ N hP _ (by
      rw [(W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)).def]
      exact W.2)
  have hdim : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f t ≫ sX) ξ ≤
        m' - (m - n) := fun ξ ↦ hN ▸ relativeDimension_le_of_forall_genericPoint _ _ hgen ξ
  have hCM : ∀ ξ : (pullback f t : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (pullback.fst f t ≫ sX) ξ =
        m' - (m - n) →
      IsCohenMacaulayLocalRing (T.presheaf.stalk (pullback.snd f t ξ)) := fun ξ _ ↦
    isCohenMacaulayLocalRing_stalk T
      (isCohenMacaulay_of_isRegular (isRegular_of_smooth_over_field (t ≫ sY))) _
  have hsupp : lciGysinSupport (fieldChowSituation k) sX sY hf hlci h ⊆
      (({(m : ℤ) - n} : Finset ℤ) : Set ℤ) := by
    intro q hq
    by_contra hne
    exact hq (lciGysinMapComponent_eq_zero_of_ne _ sX sY hf hlci h hXn hYm (by simpa using hne))
  rw [rationalFundamentalClass_eq_of_relativeDimension k (t ≫ sY) hT,
    rationalFundamentalClass_eq_of_relativeDimension k _ hP, rationalProperChowPushforward_of_tmul,
    rationalProperChowPushforward_of_tmul, lciGysinRational_eq_sum _ _ _ _ _ _ _ hsupp,
    Finset.sum_singleton, lciGysinRationalComponent, rationalChowMap_of_tmul,
    lciGysinChow_properChowPushforward_fundamentalChowClass _ sX sY hf hlci h hXn hYm t hTm hdim
      hCM, ← hN]

end Field

end Stacks.WeilDeRham

end
