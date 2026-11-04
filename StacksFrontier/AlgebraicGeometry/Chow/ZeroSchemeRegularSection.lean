module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralLocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral

/-!
# Zero schemes of sections on integral schemes

On an integral scheme a nonzero global section of an invertible module is a nonzerodivisor, so its
zero scheme is an effective Cartier divisor. The same holds for the restriction of such a zero
scheme to an integral closed subscheme not contained in it, the restricted section being nonzero
exactly because of the non-containment.

## Main results

* `Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero`: on an integral
  scheme the zero scheme of a nonzero global section of an invertible module is an effective
  Cartier divisor.
* `Stacks.Divisors.comap_eq_bot_iff_le`: the scheme-theoretic inverse image of an ideal sheaf
  along the closed immersion of another is the zero ideal sheaf exactly when the second closed
  subscheme is contained in the first.
* `Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral`: the restriction of
  such a zero scheme to an integral closed subscheme not contained in it is an effective Cartier
  divisor on that subscheme.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

/-- On an integral scheme the zero scheme of a nonzero global section of an invertible module is
an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0) :
    IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
  (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr
    (isRegularSection_of_eval_top_ne_zero L s hs)

/-- A closed subscheme is contained in another exactly when the scheme-theoretic inverse image of
the second along the closed immersion of the first is the zero ideal sheaf. -/
theorem comap_eq_bot_iff_le {X : Scheme.{u}} (I W : X.IdealSheafData) :
    I.comap W.subschemeι = ⊥ ↔ I ≤ W := by
  rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- The restriction of the zero scheme of a global section of an invertible module to an integral
closed subscheme not contained in it is an effective Cartier divisor on that subscheme. -/
theorem isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hle : ¬ zeroScheme X L s ≤ W) :
    IsEffectiveCartierDivisor ((zeroScheme X L s).comap W.subschemeι) := by
  have : IsIntegral W.subscheme := hW
  have hbot : (zeroScheme X L s).comap W.subschemeι ≠ ⊥ :=
    fun h0 ↦ hle ((comap_eq_bot_iff_le _ W).mp h0)
  rw [← zeroScheme_pullback W.subschemeι L s] at hbot ⊢
  exact isEffectiveCartierDivisor_of_isLocallyPrincipal _ hbot
    (isLocallyPrincipal_zeroScheme _ _ _)

end Stacks.Divisors

end
