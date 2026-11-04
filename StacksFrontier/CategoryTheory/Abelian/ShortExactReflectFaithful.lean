module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# A faithful exact functor reflects short exactness

A functor between abelian categories which is faithful and preserves finite limits and finite
colimits reflects short exactness: if the image of a short complex is short exact, so is the
short complex.

This is the converse of `CategoryTheory.ShortComplex.ShortExact.map_of_exact`, which carries
short exactness forward along the same hypotheses.

## Main results

* `CategoryTheory.ShortComplex.shortExact_of_shortExact_map` — the reflection statement.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

/-- **A faithful functor between abelian categories which preserves finite limits and finite
colimits reflects short exactness.** -/
theorem ShortComplex.shortExact_of_shortExact_map {A : Type u₁} {B : Type u₂} [Category.{v₁} A]
    [Category.{v₂} B] [Abelian A] [Abelian B] (F : A ⥤ B) [F.Faithful]
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    ⦃S : ShortComplex A⦄ (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := (S.exact_map_iff_of_faithful F).mp hS.exact
  mono_f := F.mono_of_mono_map hS.mono_f
  epi_g := F.epi_of_epi_map hS.epi_g

end CategoryTheory

end
