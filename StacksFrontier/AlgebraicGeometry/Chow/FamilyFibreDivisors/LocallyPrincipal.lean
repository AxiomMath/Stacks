module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.InfinityCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.SplitClosedImmersionIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic

/-!
# The two distinguished divisors of an integral family over the projective line are Cartier

Let `f : X ⟶ S` and let `W ⊆ X ×_S ℙ¹_S` be a closed subscheme of the family of projective lines
over `X` which is contained in neither the image of the zero section nor the image of the
infinity section. Part (1) of Stacks Tag 02S4 says that when `W` is integral the two closed
subschemes `W₀ = W ∩ D₀` and `W_∞ = W ∩ D_∞` are effective Cartier divisors on `W`. This file
proves that, by supplying the local principality which
`StacksFrontier/AlgebraicGeometry/Chow/FamilyFibreDivisors/EffectiveCartier.lean` takes as a
hypothesis.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Chow.isLocallyPrincipal_zeroDivisor` and
  `Stacks.Chow.isLocallyPrincipal_infinityDivisor`: for reduced `W` the two divisors are locally
  principal, with no nondegeneracy hypothesis.
* `Stacks.Chow.zeroDivisor_isEffectiveCartierDivisor` and
  `Stacks.Chow.infinityDivisor_isEffectiveCartierDivisor`: **part (1) of Stacks Tag 02S4.**

## Implementation notes

The two divisors are cut out by the *reduced* structure on the image of a section, by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, and that reduced structure is not
locally principal on `X ×_S ℙ¹_S` when `X` is non-reduced: on a chart with ring `A[T]` the
vanishing ideal of `V(T)` is `{g : g(0) nilpotent}`, which for `A = k[ε]/(ε²)` is `(T, ε)`. What
makes the divisors on `W` locally principal is therefore a comparison of two closed subscheme
structures on the image of the section, carried out in
`StacksFrontier/AlgebraicGeometry/Divisors/SplitClosedImmersionIdeal.lean`: because the section has
the first projection as a retraction, the reduced structure on its image is its kernel ideal sheaf
together with the nilradical of the ambient family, so over the reduced scheme `W` the two
structures have the same inverse image
(`Stacks.IdealSheaf.comap_vanishingIdeal_closure_range_of_split`). Reducedness of `W` is all that
step needs, and `AlgebraicGeometry.isReduced_of_isIntegral` supplies it from the integrality the
tag assumes.

The kernel ideal sheaf itself is locally principal for a reason already in the repository: a
section of `X ×_S ℙ¹_S ⟶ X` is the base change of the corresponding section of `ℙ¹_S ⟶ S`, so its
kernel is the inverse image of `D₀` resp. `D_∞` under the second projection
(`AlgebraicGeometry.ker_eq_comap_ker_of_isPullback`), those two are effective Cartier divisors on
`ℙ¹_S` by `Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor` and
`Stacks.Chow.lineInfinityDivisor_isEffectiveCartierDivisor`, and local principality survives both
inverse images by Tag 053P (`Stacks.Divisors.isLocallyPrincipal_comap`). So no chart of
`X ×_S ℙ¹_S` is identified with a polynomial ring here; the one place where the coordinate of a
chart appears is inside the separate computation of `D₀` on `𝔸¹_S`.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 053P](https://stacks.math.columbia.edu/tag/053P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (W : (projectiveLineProduct f).IdealSheafData)

/-! ### The zero section -/

/-- The zero section of `X ×_S ℙ¹_S ⟶ X` is the base change of the zero section of `ℙ¹_S ⟶ S`
along the second projection. -/
theorem isPullback_zeroSection :
    IsPullback (zeroSection f) f (pullback.snd f (relativeProjectiveLine S ↘ S))
      (lineZeroSection S) := by
  refine IsPullback.of_right ?_ (zeroSection_comp_snd f) (IsPullback.of_hasPullback _ _)
  rw [zeroSection_comp_fst, lineZeroSection_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The scheme-theoretic image of the zero section of `X ×_S ℙ¹_S ⟶ X` is the inverse image of
`D₀ ⊆ ℙ¹_S`. -/
theorem ker_zeroSection :
    (zeroSection f).ker =
      (lineZeroDivisor S).comap (pullback.snd f (relativeProjectiveLine S ↘ S)) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_zeroSection f)

/-- The scheme-theoretic image of the zero section of `X ×_S ℙ¹_S ⟶ X` is locally principal,
being the inverse image of an effective Cartier divisor on `ℙ¹_S`. -/
theorem isLocallyPrincipal_ker_zeroSection :
    Stacks.Divisors.IsLocallyPrincipal (zeroSection f).ker := by
  rw [ker_zeroSection]
  exact Stacks.Divisors.isLocallyPrincipal_comap _ _
    (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _
      (lineZeroDivisor_isEffectiveCartierDivisor S))

/-- For reduced `W` the zero divisor of `W` is cut out by the scheme-theoretic image of the zero
section, not merely by its reduced structure. -/
theorem zeroDivisor_eq_comap_ker [IsReduced W.subscheme] :
    zeroDivisor f W = (zeroSection f).ker.comap W.subschemeι :=
  Stacks.IdealSheaf.comap_vanishingIdeal_closure_range_of_split (zeroSection f)
    (pullback.fst f (relativeProjectiveLine S ↘ S)) (zeroSection_comp_fst f) W.subschemeι

/-- For reduced `W` the zero divisor of `W` is locally principal. -/
theorem isLocallyPrincipal_zeroDivisor [IsReduced W.subscheme] :
    Stacks.Divisors.IsLocallyPrincipal (zeroDivisor f W) := by
  rw [zeroDivisor_eq_comap_ker f W]
  exact Stacks.Divisors.isLocallyPrincipal_comap _ _ (isLocallyPrincipal_ker_zeroSection f)

/-- **Stacks Project, Tag 02S4, part (1), for the zero divisor.** If `W` is integral and is not
contained in the image of the zero section, then the zero divisor of `W` is an effective Cartier
divisor on `W`. -/
@[stacks 02S4 "part (1): zero divisor"]
theorem zeroDivisor_isEffectiveCartierDivisor [IsIntegral W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroDivisor f W) :=
  zeroDivisor_isEffectiveCartierDivisor_of_isLocallyPrincipal f W h
    (isLocallyPrincipal_zeroDivisor f W)

/-! ### The infinity section -/

/-- The infinity section of `X ×_S ℙ¹_S ⟶ X` is the base change of the infinity section of
`ℙ¹_S ⟶ S` along the second projection. -/
theorem isPullback_infinitySection :
    IsPullback (infinitySection f) f (pullback.snd f (relativeProjectiveLine S ↘ S))
      (lineInfinitySection S) := by
  refine IsPullback.of_right ?_ (infinitySection_comp_snd f) (IsPullback.of_hasPullback _ _)
  rw [infinitySection_comp_fst, lineInfinitySection_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The scheme-theoretic image of the infinity section of `X ×_S ℙ¹_S ⟶ X` is the inverse image
of `D_∞ ⊆ ℙ¹_S`. -/
theorem ker_infinitySection :
    (infinitySection f).ker =
      (lineInfinityDivisor S).comap (pullback.snd f (relativeProjectiveLine S ↘ S)) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_infinitySection f)

/-- The scheme-theoretic image of the infinity section of `X ×_S ℙ¹_S ⟶ X` is locally principal,
being the inverse image of an effective Cartier divisor on `ℙ¹_S`. -/
theorem isLocallyPrincipal_ker_infinitySection :
    Stacks.Divisors.IsLocallyPrincipal (infinitySection f).ker := by
  rw [ker_infinitySection]
  exact Stacks.Divisors.isLocallyPrincipal_comap _ _
    (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _
      (lineInfinityDivisor_isEffectiveCartierDivisor S))

/-- For reduced `W` the infinity divisor of `W` is cut out by the scheme-theoretic image of the
infinity section, not merely by its reduced structure. -/
theorem infinityDivisor_eq_comap_ker [IsReduced W.subscheme] :
    infinityDivisor f W = (infinitySection f).ker.comap W.subschemeι :=
  Stacks.IdealSheaf.comap_vanishingIdeal_closure_range_of_split (infinitySection f)
    (pullback.fst f (relativeProjectiveLine S ↘ S)) (infinitySection_comp_fst f) W.subschemeι

/-- For reduced `W` the infinity divisor of `W` is locally principal. -/
theorem isLocallyPrincipal_infinityDivisor [IsReduced W.subscheme] :
    Stacks.Divisors.IsLocallyPrincipal (infinityDivisor f W) := by
  rw [infinityDivisor_eq_comap_ker f W]
  exact Stacks.Divisors.isLocallyPrincipal_comap _ _ (isLocallyPrincipal_ker_infinitySection f)

/-- **Stacks Project, Tag 02S4, part (1), for the infinity divisor.** If `W` is integral and is
not contained in the image of the infinity section, then the infinity divisor of `W` is an
effective Cartier divisor on `W`. -/
@[stacks 02S4 "part (1): infinity divisor"]
theorem infinityDivisor_isEffectiveCartierDivisor [IsIntegral W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (infinityDivisor f W) :=
  infinityDivisor_isEffectiveCartierDivisor_of_isLocallyPrincipal f W h
    (isLocallyPrincipal_infinityDivisor f W)

end Stacks.Chow

end
