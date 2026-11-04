module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals

/-!
# The closed subschemes cut out by the Fitting ideals of a module

Let `F` be a finite type quasi-coherent module on a scheme `S`. Its Fitting ideal sheaves
`Fit_r(F)` cut out a family of closed subschemes of `S`, indexed by an integer `r`; at a negative
index the subscheme is the whole of `S`.

Each member is recorded as an object of `Over S`, which retains both the subscheme and its
canonical closed immersion into `S`.

## Main definitions

* `AlgebraicGeometry.fittingClosedSubscheme`: the closed subscheme cut out by the `r`-th Fitting
  ideal of `F`, as an object of `Over S`, the whole of `S` at negative `r`.

## Main results

* `AlgebraicGeometry.fittingClosedSubscheme_of_nonneg` and
  `AlgebraicGeometry.fittingClosedSubscheme_ofNat`: at a nonnegative index the structural
  morphism is the inclusion of the subscheme of the corresponding Fitting ideal sheaf.
* `AlgebraicGeometry.fittingClosedSubscheme_neg`: at a negative index — in particular at `-1` —
  the subscheme is the whole base scheme.
* `AlgebraicGeometry.fittingClosedSubscheme_isClosedImmersion`: the structural morphism is a
  closed immersion at every index.

## References

* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The closed subscheme of `S` cut out by the `r`-th Fitting ideal of a finite type
quasi-coherent module `F`, recorded together with its closed immersion into `S` as an object of
`Over S`. At a negative index, in particular at `r = -1`, this is the whole of `S`. -/
@[implicit_reducible]
noncomputable def fittingClosedSubscheme {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℤ) : Over S :=
  if r < 0 then Over.mk (𝟙 S) else Over.mk (fittingIdeal F r).subschemeι

/-- At a negative index, in particular at `-1`, the Fitting closed subscheme is the whole base
scheme. -/
@[simp]
theorem fittingClosedSubscheme_neg {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℤ) (hr : r < 0) :
    fittingClosedSubscheme F r = Over.mk (𝟙 S) := by
  simp [fittingClosedSubscheme, hr]

/-- At a nonnegative index the Fitting closed subscheme is the subscheme cut out by the
corresponding Fitting ideal sheaf. -/
theorem fittingClosedSubscheme_of_nonneg {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] {r : ℤ} (hr : 0 ≤ r) :
    fittingClosedSubscheme F r = Over.mk (fittingIdeal F r).subschemeι := by
  simp [fittingClosedSubscheme, not_lt.mpr hr]

/-- At an index coming from a natural number the Fitting closed subscheme is the subscheme cut
out by the corresponding Fitting ideal sheaf. -/
@[simp]
theorem fittingClosedSubscheme_ofNat {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    fittingClosedSubscheme F (r : ℤ) = Over.mk (fittingIdeal F (r : ℤ)).subschemeι :=
  fittingClosedSubscheme_of_nonneg F (Int.natCast_nonneg r)

/-- The structural morphism of a Fitting closed subscheme is a closed immersion. -/
instance fittingClosedSubscheme_isClosedImmersion {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℤ) :
    IsClosedImmersion (fittingClosedSubscheme F r).hom := by
  by_cases hr : r < 0
  · rw [fittingClosedSubscheme_neg F r hr]
    exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  · rw [fittingClosedSubscheme_of_nonneg F (not_lt.mp hr)]
    exact inferInstanceAs (IsClosedImmersion (fittingIdeal F r).subschemeι)

end AlgebraicGeometry

end
