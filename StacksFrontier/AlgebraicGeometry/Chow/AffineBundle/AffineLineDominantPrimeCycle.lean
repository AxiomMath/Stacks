module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineGenericPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ClassLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.RankOneUtilities
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.TrivialBundle
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionInduction

/-!
# A prime cycle of the affine line dominating an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be integral and
locally of finite type over `S` of delta-dimension `n`, and let `W ⊆ 𝔸¹_Y` be an integral closed
subscheme dominating `Y`, presented by its generic point `w`. The fourth step of the proof of
Stacks 02TT asserts that the class of `[W]` is a flat pullback from `Y`, granted that flat
pullback along the affine line is surjective over every base of smaller delta-dimension. This
file carries out that assertion from one input: that over some nonempty open subscheme `V ⊆ Y`
the restriction of `[W]` is rationally equivalent to zero.

The source produces that input by exhibiting `W`, over a suitable `V`, as a principal divisor:
the generic fibre of `W → Y` is cut out in `𝔸¹_{R(Y)}` by a monic irreducible polynomial
`P ∈ R(Y)[T]`, and over an open `V` on which the coefficients of `P` are regular and still cut
out `W`, the cycle `[W]|_{𝔸¹_V}` is `div(P)`.

Three cases are distinguished here, exactly as in the source.

* The degree may be wrong. The statement fixes a degree `k` and reads `[W]` in degree `k + 1`;
  if the relative dimension of `w` is not `k + 1` then the cycle in that degree is zero and
  there is nothing to prove.
* `W` may be the whole of `𝔸¹_Y`, that is `w` may be the generic point. Then `[W]` is the
  fundamental cycle, which is the flat pullback of the fundamental cycle of `Y`.
* Otherwise `W` is a prime divisor of `𝔸¹_Y`, and the input is used: the restriction of `[W]` to
  `𝔸¹_V` is zero in the Chow group, so by the localization sequence `[W]` differs from a flat
  pullback by a class supported over the reduced complement of `V`, whose delta-dimension is
  smaller, where flat pullback is surjective by hypothesis.

## Main results

* `Stacks.Chow.mem_range_flatPullbackChow_primeCycle_of_rationallyEquivalentToZero_restrict` —
  the localization half: a prime cycle that becomes rationally equivalent to zero over a nonempty
  open subscheme of the base has its class in the image of flat pullback.
* `Stacks.Chow.mem_range_flatPullbackChow_primeCycle_affineLineOver_of_dominant` — the fourth
  step of the proof of Stacks 02TT for a prime cycle dominating an integral base, from the
  principal-divisor input.

## Implementation notes

No `@[stacks]` attribute is placed here: the hypothesis `hrat` of the second result is the
principal-divisor half of the step it belongs to, and a declaration carrying it proves less than
the tag asserts.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver locallyOfFiniteType_comapRestrict
  flat_comapRestrict

/-- **The localization half of the fourth step of Stacks 02TT.** Let `Y` be integral of
delta-dimension `n`, let `V ⊆ Y` be a nonempty open subscheme and let `w'` be a point of
`𝔸¹_V = f^{-1}(V)`. If the prime cycle of `w'` is rationally equivalent to zero on `f^{-1}(V)`,
and if flat pullback along the affine line is surjective in degree `k` over every base of
delta-dimension smaller than `n`, then the class of the prime cycle of the image of `w'` in
`𝔸¹_Y` lies in the image of flat pullback along `f`.

The restriction of the class to `f^{-1}(V)` is the class of the prime cycle of `w'`, which
vanishes; the reduced complement of `V` has strictly smaller delta-dimension, and the base change
of the affine line over it is again a trivial bundle, so
`Stacks.Chow.mem_range_flatPullbackChow_of_opens_of_comap` applies. -/
theorem mem_range_flatPullbackChow_primeCycle_of_rationallyEquivalentToZero_restrict
    (C : ChowSituation.{u}) {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (k : ℤ) {n : ℤ} (hn : schemeDeltaDimension C sY = (n : EInt))
    (hsmaller : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
      schemeDeltaDimension C sB < (n : EInt) →
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
        (relativeDimension_affineSpaceOver B 1) k))
    (V : Y.Opens) (hVne : ((V : Set Y)).Nonempty)
    (w' : ↥((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V))
    (hrat : IsRationallyEquivalentToZero C
      (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
      (k + ((1 : ℕ) : ℤ))
      (cycleAssociatedToClosedSubscheme C
        (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
        (integralComponentAt w').subschemeι (k + ((1 : ℕ) : ℤ)))) :
    (QuotientAddGroup.mk' (rationalEquivalences C
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (k + ((1 : ℕ) : ℤ)))
      (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
        (integralComponentAt (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι.base w')).subschemeι
        (k + ((1 : ℕ) : ℤ)))) ∈
    (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1 (relativeDimension_affineSpaceOver Y 1) k).range := by
  have hcomplement : Set.range (Scheme.IdealSheafData.vanishingIdeal
      (X := Y) ⟨((V : Set Y))ᶜ, V.2.isClosed_compl⟩).subschemeι.base =
      (Set.range V.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  refine mem_range_flatPullbackChow_of_opens_of_comap C sY (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) 1
    (relativeDimension_affineSpaceOver Y 1) k V _ hcomplement _ ?_ ?_
  · refine ⟨0, ?_⟩
    rw [map_zero, chowGroupOpensRestrictOfIsOpenImmersion_mk_primeCycle C
      ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V)
      (k + ((1 : ℕ) : ℤ)) w']
    exact ((QuotientAddGroup.eq_zero_iff _).mpr hrat).symm
  · have hlt : schemeDeltaDimension C ((Scheme.IdealSheafData.vanishingIdeal
        (X := Y) ⟨((V : Set Y))ᶜ, V.2.isClosed_compl⟩).subschemeι ≫ sY) < (n : EInt) := by
      rw [← hn]
      exact schemeDeltaDimension_lt_of_range_eq_compl C sY _ V hcomplement hVne hn
    exact flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle_of_base C 1 _ _
      (comapRestrict _ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))
      (comapRestrict_comp_base C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
        (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl _)
      (relativeDimension_comapRestrict _ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)
        (relativeDimension_affineSpaceOver Y 1)) k
      (isTrivialAffineSpaceBundle_of_isPullback
        (isPullback_comapRestrict _ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) 1
        (isTrivialAffineSpaceBundle_affineSpaceOver Y 1))
      (hsmaller _ _ hlt)

/-- **The fourth step of the proof of Stacks 02TT for a prime cycle dominating an integral
base.** Let `Y` be integral of delta-dimension `n`, let `w` be a point of `𝔸¹_Y` lying over the
generic point of `Y`, and assume flat pullback along the affine line is surjective in degree `k`
over every base of smaller delta-dimension. Then the class of the prime cycle of `w` in degree
`k + 1` is a flat pullback from `Y`.

The hypothesis `hrat` is the principal-divisor half of the step: a point of `𝔸¹_Y` over the
generic point of `Y` other than the generic point of `𝔸¹_Y` has, over some nonempty open
subscheme of `Y`, its prime cycle rationally equivalent to zero. It is the one thing not proved
here. -/
theorem mem_range_flatPullbackChow_primeCycle_affineLineOver_of_dominant
    (C : ChowSituation.{u}) {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (k : ℤ) {n : ℤ} (hn : schemeDeltaDimension C sY = (n : EInt))
    (hsmaller : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB],
      schemeDeltaDimension C sB < (n : EInt) →
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin 1); B) ↘ B) rfl 1
        (relativeDimension_affineSpaceOver B 1) k))
    (hrat : ∀ w : ↥𝔸(ULift.{u} (Fin 1); Y),
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y →
      w ≠ genericPoint ↥𝔸(ULift.{u} (Fin 1); Y) →
      ∃ (V : Y.Opens) (_ : ((V : Set Y)).Nonempty)
        (w' : ↥((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V)),
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι.base w' = w ∧
        IsRationallyEquivalentToZero C
          (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
          (k + ((1 : ℕ) : ℤ))
          (cycleAssociatedToClosedSubscheme C
            (((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ⁻¹ᵁ V).ι ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
            (integralComponentAt w').subschemeι (k + ((1 : ℕ) : ℤ))))
    (w : ↥𝔸(ULift.{u} (Fin 1); Y))
    (hdom : (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y) :
    (QuotientAddGroup.mk' (rationalEquivalences C
        ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (k + ((1 : ℕ) : ℤ)))
      (cycleAssociatedToClosedSubscheme C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
        (integralComponentAt w).subschemeι (k + ((1 : ℕ) : ℤ)))) ∈
    (flatPullbackChowOfRelativeDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1 (relativeDimension_affineSpaceOver Y 1) k).range := by
  by_cases hdeg : relativeDimension C.dimensionFunction
      ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w = k + ((1 : ℕ) : ℤ)
  · by_cases hgen : w = genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)
    · -- `W = 𝔸¹_Y`: the prime cycle is the fundamental cycle
      subst hgen
      have hdim := schemeDeltaDimension_affineSpaceOver C sY 1 hn
      have hgp : relativeDimension C.dimensionFunction
          ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
          (genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)) = n + ((1 : ℕ) : ℤ) := by
        refine WithBotTop.coe_injective ?_
        rw [← schemeDeltaDimension_eq_genericPoint C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY),
          hdim]
      have hnk : n = k := by rw [hgp] at hdeg; omega
      subst hnk
      exact mem_range_flatPullbackChow_primeCycle_genericPoint_affineSpaceOver C sY 1 hn
    · -- `W` is a prime divisor: the principal-divisor input
      obtain ⟨V, hVne, w', hw'eq, hw'rat⟩ := hrat w hdom hgen
      have h := mem_range_flatPullbackChow_primeCycle_of_rationallyEquivalentToZero_restrict
        C sY k hn hsmaller V hVne w' hw'rat
      rwa [hw'eq] at h
  · -- the wrong degree: the cycle itself is zero
    rw [cycleAssociatedToClosedSubscheme_integralComponentAt_eq_zero_of_ne C
      ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) (k + ((1 : ℕ) : ℤ)) w hdeg, map_zero]
    exact ⟨0, map_zero _⟩

end Stacks.Chow

end
