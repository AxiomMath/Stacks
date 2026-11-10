module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral

/-!
# Restricting prime cycles to an open subscheme, and the affine line over an integral base

This file collects three ingredients used in the fourth step of the proof of Stacks 02TT, where
the surjectivity of flat pullback along an affine-line bundle over an integral base is reduced to
a computation on the generic fibre.

The first two are about an open subscheme `U ⊆ X`. Restriction of cycles to `U` (Stacks 02RC,
`Stacks.Chow.cycleGroupOpensRestrict`) takes the prime cycle of a point of `U` — read in `X` — to
the prime cycle of that point read in `U`: the two coefficient functions agree point by point,
because the relative dimension does not see the passage to an open subscheme and because the
integral closed subscheme attached to a point has its single generic point at that point. The
same statement on Chow classes follows at once, both restriction maps being induced on the
quotient by rational equivalence. Alongside this sits the elementary fact that a nonempty open
subscheme of an integral scheme is integral, in the form in which the point is supplied as an
element of `U`.

The third is the relative-dimension computation on the affine line. If `Y` is integral of
delta-dimension `n` over the base and `w` is a point of `𝔸^1_Y` lying over the generic point of
`Y` but distinct from the generic point of `𝔸^1_Y`, then `w` has relative dimension exactly `n`.
The projection `𝔸^1_Y ⟶ Y` is flat of relative dimension one, so `𝔸^1_Y` has delta-dimension
`n + 1`, attained at its generic point; the relative dimension at `w` is therefore strictly less
than `n + 1`, while dominance of `w` over the generic point of `Y` bounds it below by `n`.

## Main results

* `Stacks.Chow.cycleGroupOpensRestrict_cycleAssociatedToClosedSubscheme_integralComponentAt` —
  restricting the prime cycle of a point of an open subscheme `U ⊆ X` to `U` gives the prime
  cycle of that point computed in `U`.
* `Stacks.Chow.chowGroupOpensRestrictOfIsOpenImmersion_mk_primeCycle` — the same statement for
  the classes of these cycles in the Chow groups.
* `Stacks.Chow.isIntegral_opens_of_mem` — an open subscheme of an integral scheme that contains a
  point is integral.
* `Stacks.Chow.relativeDimension_eq_of_dominant_of_ne_genericPoint` — a non-generic point of the
  affine line over an integral base of delta-dimension `n`, lying over the generic point of the
  base, has relative dimension `n`.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT) — surjectivity of flat
  pullback along an affine-space bundle, the statement these ingredients serve.
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC) — flat pullback of
  cycles, of which restriction to an open subscheme is the relative-dimension-zero case.
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU) — the cycle associated to
  a closed subscheme, whose coefficients are compared here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Prime cycles and restriction to an open subscheme -/

/-- **Stacks 02RC for a prime cycle.** Restricting the prime cycle of a point `x'` of an open
subscheme `U ⊆ X`, formed in `X`, to `U` gives the prime cycle of `x'` formed in `U`.

Both sides are compared coefficientwise. At a point `z ≠ x'` both vanish, the integral closed
subscheme attached to a point having that point as its only generic point. At `z = x'` both
coefficients are one if the relative dimension there is `k` — which is the same condition on
either side, the relative dimension not seeing the open subscheme — and both vanish if not. -/
theorem cycleGroupOpensRestrict_cycleAssociatedToClosedSubscheme_integralComponentAt
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (U : X.Opens) (k : ℤ) (x' : U) :
    cycleGroupOpensRestrict C p U k
        (cycleAssociatedToClosedSubscheme C p
          (integralComponentAt (U.ι.base x')).subschemeι k) =
      cycleAssociatedToClosedSubscheme C (U.ι ≫ p) (integralComponentAt x').subschemeι k := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  change (cycleAssociatedToClosedSubscheme C p
      (integralComponentAt (U.ι.base x')).subschemeι k).1 (U.ι.base z) =
    (cycleAssociatedToClosedSubscheme C (U.ι ≫ p) (integralComponentAt x').subschemeι k).1 z
  by_cases hz : z = x'
  · subst hz
    have hrel := relativeDimension_opensι_comp C.dimensionFunction p U z
    by_cases hdim : relativeDimension C.dimensionFunction (U.ι ≫ p) z = k
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C p (U.ι.base z)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C p _
            (hrel.symm.trans hdim)),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C (U.ι ≫ p) z
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C (U.ι ≫ p) _ hdim)]
    · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C p _ k
          (fun h ↦ hdim (hrel.trans h)),
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C (U.ι ≫ p) _ k
          hdim]
  · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k (U.ι.base x')
        (fun h ↦ hz (U.ι.isOpenEmbedding.injective h)),
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C (U.ι ≫ p) k x' hz]

/-- **Stacks 02RC for a prime cycle, on Chow groups.** Restricting the class of the prime cycle of
a point of an open subscheme `U ⊆ X` to `U` gives the class of the prime cycle of that point
formed in `U`.

Both restriction maps are induced on the quotient by rational equivalence by
`Stacks.Chow.cycleGroupOpensRestrict`, so this is the cycle-level statement
`Stacks.Chow.cycleGroupOpensRestrict_cycleAssociatedToClosedSubscheme_integralComponentAt` read
on representatives. -/
theorem chowGroupOpensRestrictOfIsOpenImmersion_mk_primeCycle
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (U : X.Opens) (k : ℤ) (x' : U) :
    chowGroupOpensRestrictOfIsOpenImmersion C p U k
        (QuotientAddGroup.mk' (rationalEquivalences C p k)
          (cycleAssociatedToClosedSubscheme C p
            (integralComponentAt (U.ι.base x')).subschemeι k)) =
      QuotientAddGroup.mk' (rationalEquivalences C (U.ι ≫ p) k)
        (cycleAssociatedToClosedSubscheme C (U.ι ≫ p) (integralComponentAt x').subschemeι k) := by
  rw [chowGroupOpensRestrictOfIsOpenImmersion_mk,
    cycleGroupOpensRestrict_cycleAssociatedToClosedSubscheme_integralComponentAt]

/-! ### Open subschemes of an integral scheme -/

/-- An open subscheme of an integral scheme which contains a point is integral: it is nonempty,
and an open immersion into an integral scheme with nonempty source has integral source. -/
theorem isIntegral_opens_of_mem {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : U) :
    IsIntegral U.toScheme :=
  have : Nonempty U.toScheme := ⟨x⟩
  isIntegral_of_isOpenImmersion U.ι

/-! ### The affine line over an integral base -/

attribute [local instance] flat_affineSpaceOver

/-- The relative dimension of a non-generic point of the affine line over an integral base of
delta-dimension `n`, lying over the generic point of the base, is `n`.

The projection `f : 𝔸^1_Y ⟶ Y` is flat of relative dimension one, so `𝔸^1_Y` has
delta-dimension `n + 1`; being irreducible, it attains that value at its generic point. Hence the
relative dimension at `w` is strictly smaller than `n + 1`, the relative dimension being a
dimension function and `w` a nontrivial specialization of the generic point. On the other hand it
is the relative dimension of `f w = ` the generic point of `Y`, namely `n`, plus a transcendence
degree, hence at least `n`. -/
theorem relativeDimension_eq_of_dominant_of_ne_genericPoint (C : ChowSituation.{u})
    {Y : Scheme.{u}} [IsIntegral Y] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {n : ℤ}
    (hn : schemeDeltaDimension C sY = (n : EInt)) (w : ↥𝔸(ULift.{u} (Fin 1); Y))
    (hdom : (𝔸(ULift.{u} (Fin 1); Y) ↘ Y).base w = genericPoint ↥Y)
    (hne : w ≠ genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)) :
    relativeDimension C.dimensionFunction ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w = n := by
  have hA : schemeDeltaDimension C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
      = ((n + 1 : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_eq_add_of_flat C
      ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) sY (𝔸(ULift.{u} (Fin 1); Y) ↘ Y) rfl 1
      (relativeDimension_affineSpaceOver Y 1) hn
  have hgen : relativeDimension C.dimensionFunction ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)
      (genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)) = n + 1 :=
    WithBotTop.coe_injective
      ((schemeDeltaDimension_eq_genericPoint C ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY)).symm.trans hA)
  have hclos : closure {genericPoint ↥𝔸(ULift.{u} (Fin 1); Y)} = Set.univ :=
    genericPoint_spec _
  have hlt : relativeDimension C.dimensionFunction ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w
      < n + 1 := by
    rw [← hgen]
    exact relativeDimension_lt_of_mem_closure_of_ne C _ (hclos ▸ Set.mem_univ w) hne
  have hYgen : relativeDimension C.dimensionFunction sY (genericPoint ↥Y) = n :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sY).symm.trans hn)
  have hge : n ≤ relativeDimension C.dimensionFunction ((𝔸(ULift.{u} (Fin 1); Y) ↘ Y) ≫ sY) w := by
    rw [relativeDimension_comp_eq_add_trdeg, hdom, hYgen]
    omega
  omega

end Stacks.Chow

end
