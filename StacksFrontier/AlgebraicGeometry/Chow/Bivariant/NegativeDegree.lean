module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Bivariant classes of negative degree for a closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. A bivariant class
`c ∈ A^p(Z ⟶ X)` of negative degree `p < 0` is zero. This is the fact Remark 0FA0 of the
Stacks Project uses to see that the sums appearing there are finite: "the negative degree groups
vanish for a closed immersion". In particular, taking `f = id_X`, the groups `A^p(X)` of Chow
cohomology vanish in negative degrees.

The argument is the source's. By Stacks 02UC it suffices that `c ∩ [Y']_k = 0` for every integral
scheme `Y'` locally of finite type over `X` and every `k`. The fundamental class `[Y']_k` is zero
unless `k` is the delta-dimension of the generic point of `Y'`. In that case `c ∩ [Y']_k` lies
in `CH_{k - p}(Y' ×_X Z)` with `k - p > k`, while `Y' ×_X Z` is a closed subscheme of `Y'`, so
its points have delta-dimension at most `k`: the delta-dimension of a point of a closed
subscheme is that of its image, and it does not increase along the specialization from the
generic point of `Y'`. So that Chow group is zero.

## Main results

* `Stacks.Chow.BivariantClass.eq_zero_of_relativeDimension_le` — the general form: if for each
  integral test scheme `T ⟶ X` every point of `T ×_X Z` has delta-dimension at most `q` more
  than the generic point of `T`, then every bivariant class of degree `p < -q` is zero.
* `Stacks.Chow.BivariantClass.eq_zero_of_isClosedImmersion_of_neg` — **the fact used in
  Stacks 0FA0**: for a closed immersion `f`, `A^p(Z ⟶ X) = 0` when `p < 0`.
* `Stacks.Chow.chowCohomologyComponent_eq_zero_of_neg` — `A^p(X) = 0` when `p < 0`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Bivariant classes below a fibre-dimension bound vanish.** Let `f : Z ⟶ X` be such that,
for every integral scheme `T` locally of finite type over `X`, every point of `T ×_X Z` has
delta-dimension at most `q` more than the generic point of `T`. Then every bivariant class
`c ∈ A^p(Z ⟶ X)` with `p < -q` is zero.

By Stacks 02UC it suffices to cap with fundamental classes `[T]_k` of integral `T`; such a class
is zero unless `k` is the delta-dimension of the generic point of `T`, and then the cap product
lies in `CH_{k - p}(T ×_X Z)`, where `k - p > k + q` exceeds the delta-dimension of every point,
so that group is zero. -/
theorem BivariantClass.eq_zero_of_relativeDimension_le (f : Z ⟶ X) [LocallyOfFiniteType f]
    (hf : f ≫ sX = sZ) (q : ℤ)
    (hdim : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] [IsIntegral T]
      (w : ↥(pullback f g)), relativeDimension C.dimensionFunction (pullback.fst f g ≫ sZ) w ≤
        relativeDimension C.dimensionFunction (g ≫ sX) (genericPoint T) + q)
    {p : ℤ} (hp : p < -q) (c : BivariantClass C G sZ sX f hf p) : c = 0 := by
  rw [BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero]
  intro T g _ _ k
  by_cases hk : relativeDimension C.dimensionFunction (g ≫ sX) (genericPoint T) = k
  · refine chowGroup_eq_zero C _ (fun w hw ↦ ?_) _
    have := hdim g w
    omega
  · rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C _ genericPoints_eq_singleton hk,
      map_zero, map_zero]

omit [LocallyOfFiniteType sZ] in
/-- A point of the base change `T ×_X Z` of a closed immersion `Z ⟶ X` along a morphism from an
integral scheme `T` has delta-dimension at most that of the generic point of `T`: the base change
is a closed immersion into `T`, which preserves delta-dimensions of points, and the generic point
of `T` specializes to every point. -/
theorem relativeDimension_pullback_fst_le_genericPoint (f : Z ⟶ X) [IsClosedImmersion f]
    (hf : f ≫ sX = sZ) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] [IsIntegral T]
    (w : ↥(pullback f g)) :
    relativeDimension C.dimensionFunction (pullback.fst f g ≫ sZ) w ≤
      relativeDimension C.dimensionFunction (g ≫ sX) (genericPoint T) := by
  have hcomp : pullback.fst f g ≫ sZ = pullback.snd f g ≫ (g ≫ sX) := by
    rw [← hf, ← Category.assoc, pullback.condition, Category.assoc]
  rw [hcomp, relativeDimension_comp_closedImmersion]
  exact relativeDimension_le_of_specializes C (g ≫ sX) (genericPoint_specializes _)

/-- **Stacks 0FA0, the vanishing it uses.** For a closed immersion `f : Z ⟶ X` of schemes
locally of finite type over the base, every bivariant class `c ∈ A^p(Z ⟶ X)` of negative degree
`p < 0` is zero. -/
theorem BivariantClass.eq_zero_of_isClosedImmersion_of_neg (f : Z ⟶ X) [IsClosedImmersion f]
    (hf : f ≫ sX = sZ) {p : ℤ} (hp : p < 0) (c : BivariantClass C G sZ sX f hf p) : c = 0 :=
  BivariantClass.eq_zero_of_relativeDimension_le C G sZ sX f hf 0
    (fun g _ _ w ↦ by
      rw [add_zero]
      exact relativeDimension_pullback_fst_le_genericPoint C sZ sX f hf g w)
    (by rwa [neg_zero]) c

/-- **Chow cohomology vanishes in negative degrees.** For a scheme `X` locally of finite type
over the base, `A^p(X) = A^p(X ⟶ X)` is zero when `p < 0`; this is the case `f = id_X` of
`Stacks.Chow.BivariantClass.eq_zero_of_isClosedImmersion_of_neg`. -/
theorem chowCohomologyComponent_eq_zero_of_neg {p : ℤ} (hp : p < 0)
    (c : chowCohomologyComponent C G sX p) : c = 0 :=
  BivariantClass.eq_zero_of_isClosedImmersion_of_neg C G sX sX (𝟙 X) (Category.id_comp sX) hp c

end Stacks.Chow

end
