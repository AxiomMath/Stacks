module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlat
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatDualizing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitude
import all StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlat

/-!
# The bounds of Tag 0BV6 for the relative dualizing complex of a flat morphism, unconditionally

`Stacks.Duality.fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat` proves the
bounds `-dim_x(X_y) ≤ i ≤ 0` on the nonzero stalks of `H^i(f^!𝒪_Y)`, `f` flat, granted the
affine-chart description of `f^!𝒪_Y` at a chart through `x`. That description is
`Stacks.Duality.upperShriekStructureSheafCharts`, and this file discharges it; it also proves the
Tor amplitude statement of [Stacks, Tag 0BV6].

## Main results

* `Stacks.Duality.exists_mem_primeIdealOf_eq` — every prime of `Γ(Z, U)` for an affine open
  `U` is the prime of a point of `U`.
* `Stacks.Duality.fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat_unconditional`
  — the bounds of [Stacks, Tag 0BV6].
* `Stacks.Duality.hasTorAmplitude_derivedScalarRestriction_upperShriek` — the Tor amplitude of
  `f^!𝒪_Y` over `f^{-1}𝒪_Y`.

## References

* [Stacks Project, Tag 0BV6](https://stacks.math.columbia.edu/tag/0BV6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

universe u

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace Stacks.Duality

open DerivedPushforward

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0BV6 (Lemma 48.21.4), the first assertion.** In Situation 48.16.1 let
`f : X ⟶ Y` be a flat morphism of `FTS S` and let `x ∈ X` with image `y ∈ Y`. Then

  `H^i(f^!𝒪_Y)_x ≠ 0  ⟹  -dim_x(X_y) ≤ i ≤ 0`,

for every compactification `j` defining `f^!`, the local dimension `dim_x(X_y)` being named by
`hd`. On a chart of `Stacks.Duality.upperShriekStructureSheafCharts` this is the ring-level
[Stacks, Tag 0E9Q]. -/
@[stacks 0BV6 "first assertion: the bounds -dim_x(X_y) <= i <= 0 on nonzero stalks"]
theorem fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat_unconditional
    [Flat f.left] (x : X.left) (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := by
  obtain ⟨U, hU, V, hV, hUV, hxU, -, he⟩ := exists_chart_of_upperShriekStructureSheafCharts f j
    (upperShriekStructureSheafCharts f j) x ⊤ trivial
  exact fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat f j x
    ⟨U, hU, V, hV, hUV, hxU, he⟩ d hd i hi

end Shriek

end Stacks.Duality

end Geometric

section TorAmplitude

open AlgebraicGeometry CategoryTheory TopologicalSpace StacksDraft.TorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0BV6 (Lemma 48.21.4), the second assertion.** In Situation 48.16.1 let
`f : X ⟶ Y` be a flat morphism of `FTS S` all of whose fibres have dimension at most `d`. Then
`f^!𝒪_Y` has Tor amplitude in `[-d, 0]` as an object of `D(X, f^{-1}𝒪_Y)`, for every
compactification `j` defining `f^!`.

By [Stacks, Tag 09U9] this is a statement about the derived stalks read over the local rings of
`Y`; on a chart of `Stacks.Duality.upperShriekStructureSheafCharts` it is the Tor amplitude clause
of the ring-level [Stacks, Tag 0E9Q]. -/
@[stacks 0BV6 "second assertion: Tor amplitude in [-d, 0] over f^{-1}O_Y when all fibres have \
dimension at most d"]
theorem hasTorAmplitude_derivedScalarRestriction_upperShriek [Flat f.left] (d : ℕ)
    (hd : ∀ y : Y.left, topologicalKrullDim (f.left.fiber y) ≤ (d : WithBot ℕ∞)) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude
      (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base)
      ((Scheme.Hom.derivedScalarRestriction f.left).obj (relativeDualizingComplexObj f j))
      (-(d : ℤ)) 0 := by
  refine (Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff
    (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base).sheaf _ _ _).2 fun x => ?_
  refine (Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff f.left x _ _ _).2 ?_
  obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ :=
    isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j
      (upperShriekStructureSheafCharts f j) x
  refine hasTorAmplitudeCanonical_stalk_base_of_modulesStalk f.left _ x _ _ ?_
  refine hasTorAmplitudeCanonical_stalk_of_chart f hU hV hUV p _ he _ _ ?_ x hxU
  have hLN (Z : AlgebraicGeometry.FTS S) : IsLocallyNoetherian Z.left := by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have := hLN X
  have := hLN Y
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have : Module.Flat Γ(Y.left, V) Γ(X.left, U) := f.left.flat_appLE hV hU hUV
  have hdim : Algebra.relativeDimension Γ(Y.left, V) Γ(X.left, U) ≤ (d : WithBot ℕ∞) := by
    refine iSup_le fun r => ?_
    obtain ⟨w, hw, hwr⟩ := exists_mem_primeIdealOf_eq hU r
    subst hwr
    exact (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV w hw).symm.trans_le
        ((topologicalKrullDimAt_le_topologicalKrullDim _).trans (hd _))
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso (Iso.refl _) _ _
    ((hasTorAmplitudeIn_canonicalCertified_iff _ _ _ _).1
      (Dualizing.upperShriekFunctor_hasTorAmplitude_of_relativeDimension_le p d hdim))

end Stacks.Duality

end TorAmplitude

end
