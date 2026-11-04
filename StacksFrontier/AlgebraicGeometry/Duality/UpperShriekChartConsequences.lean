module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.UpperShriekCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
import StacksCore.Tactic.StacksAttribute

/-!
# Gorenstein and Cohen–Macaulay morphisms through `f^!𝒪_Y`

Let `S` be Noetherian and `f : X ⟶ Y` a morphism of `AlgebraicGeometry.FTS S`, with `f^!` computed
at any compactification `j`. This file characterizes Gorenstein and Cohen–Macaulay morphisms in
terms of `f^!𝒪_Y`, through its affine chart description
`Stacks.Duality.upperShriekStructureSheafCharts` ([Stacks, Tag 0BV2]).

## Main results

* `Stacks.Duality.isGorensteinAt_iff_exists_isInvertible_upperShriek` — a flat `f` is Gorenstein
  at `x` if and only if `f^!𝒪_Y` is invertible near `x`; the Gorenstein locus is open.
* `Stacks.Duality.exists_isCoherent_isFlatOver_iso_shift_upperShriek` — for a Cohen–Macaulay `f`,
  `f^!𝒪_Y = ω_{X/Y}[d]` with `ω_{X/Y}` coherent and flat over `Y`.
* `Stacks.Duality.isCohenMacaulayAt_iff_exists_unique_nonzero_homology_upperShriek` — a flat `f`
  is Cohen–Macaulay at `x` if and only if `f^!𝒪_Y` has a unique nonzero cohomology sheaf near `x`.

## References

* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
* [Stacks Project, Tag 0C08](https://stacks.math.columbia.edu/tag/0C08)
* [Stacks Project, Tag 0C0Z](https://stacks.math.columbia.edu/tag/0C0Z)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- Let `S` be Noetherian, `f : X ⟶ Y` a flat morphism of `FTS S` and `x ∈ X`. Then `f` is
Gorenstein at `x` if and only if `f^!𝒪_Y` is isomorphic to an invertible object in a
neighbourhood of `x`. In particular the set of points where `f` is Gorenstein is open in `X`.
Here `f^!` is computed at any compactification `j`. -/
@[stacks 0C08]
theorem isGorensteinAt_iff_exists_isInvertible_upperShriek [Flat f.left] :
    (∀ x : X.left, f.left.IsGorensteinAt (isLocallyNoetherian_fiber_left f) x ↔
      ∃ W : X.left.Opens, x ∈ W ∧
        letI := Scheme.Modules.derivedMonoidal W.toScheme
        MonoidalCategory.IsInvertible
          ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj
            (relativeDualizingComplexObj f j))) ∧
      IsOpen {x : X.left | f.left.IsGorensteinAt (isLocallyNoetherian_fiber_left f) x} :=
  ⟨isGorensteinAt_iff_exists_isInvertible_of_charts (upperShriekStructureSheafCharts f j),
    Scheme.Hom.isOpen_setOf_isGorensteinAt f.left⟩

/-- Let `S` be Noetherian and `f : X ⟶ Y` a Cohen–Macaulay morphism of `FTS S`. Then
`f^!𝒪_Y = ω_{X/Y}[d]` for a coherent `𝒪_X`-module `ω_{X/Y}` flat over `Y`, where `d` is the
locally constant relative dimension of `X` over `Y`: on the open where the relative dimension is
`d`, `f^!𝒪_Y` is `ω_{X/Y}` placed in degree `-d`. -/
@[stacks 0BV8]
theorem exists_isCoherent_isFlatOver_iso_shift_upperShriek
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) :
    letI h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
    letI : Flat f.left := h.1
    letI := locallyOfFinitePresentation_left f
    ∃ ω : X.left.Modules, ω.IsCoherent ∧ IsFlatOver f.left.toLRSHom.toShHom ω ∧
      ∀ d : ℕ, Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left h.2 d).ι
          ).mapDerivedCategory.obj (relativeDualizingComplexObj f j) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left h.2 d).ι).obj ω))⟦
            (d : ℤ)⟧) :=
  exists_isCoherent_isFlatOver_iso_shift_of_charts (upperShriekStructureSheafCharts f j) hCM

/-- Let `S` be Noetherian, `f : X ⟶ Y` a flat morphism of `FTS S` and `x ∈ X`. Then `f` is
Cohen–Macaulay at `x` if and only if `f^!𝒪_Y` has a unique nonzero cohomology sheaf in a
neighbourhood of `x`. -/
@[stacks 0C0Z]
theorem isCohenMacaulayAt_iff_exists_unique_nonzero_homology_upperShriek [Flat f.left]
    (x : X.left) :
    f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x ↔
      ∃ W : X.left.Opens, x ∈ W ∧ ∃ n : ℤ,
        ¬ IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
          ((DerivedCategory.homologyFunctor X.left.Modules n).obj
            (relativeDualizingComplexObj f j))) ∧
        ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
          ((DerivedCategory.homologyFunctor X.left.Modules i).obj
            (relativeDualizingComplexObj f j))) :=
  isCohenMacaulayAt_iff_exists_unique_nonzero_homology_of_charts
    (upperShriekStructureSheafCharts f j) x

end Stacks.Duality
