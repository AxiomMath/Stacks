module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlat
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
import StacksCore.Tactic.StacksAttribute

/-!
# The upper shriek of a perfect morphism

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a perfect morphism of
`AlgebraicGeometry.FTS S` (for example a flat one). [Stacks, Tag 0B6U] (Lemma 48.17.9) asserts:

* (a) `f^!𝒪_Y ∈ D^b_Coh(𝒪_X)`;
* (b) `f^!𝒪_Y` has finite tor dimension in `D(f⁻¹𝒪_Y)`;
* (c) `𝒪_X ⟶ R𝓗om(f^!𝒪_Y, f^!𝒪_Y)` is an isomorphism;
* (d) `f^!` maps `D^b_Coh(𝒪_Y)` into `D^b_Coh(𝒪_X)`;
* (e) `μ_{f,K} : Lf^*K ⊗ᴸ f^!𝒪_Y ⟶ f^!K` is an isomorphism for `K ∈ D⁺_QCoh(𝒪_Y)`.

## Main results

* `Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_perfect` — part (a).
* `Stacks.Duality.hasFiniteTorDimension_derivedScalarRestriction_upperShriek` — part (b).
* `Stacks.Duality.isIso_derivedSheafHomothety_upperShriek` — part (c).

Part (d) is `Stacks.Duality.derivedCategoryBBounded_upperShriek`
(`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekCoherent.lean`) and part (e) is
`Stacks.Duality.isIso_upperShriekCompareWithPullback`
(`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekPerfectComparison.lean`).

## References

* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0B6U (Lemma 48.17.9), part (a).** In Situation 48.16.1 let
`f : X ⟶ Y` be a perfect morphism of `FTS S`. Then `f^!𝒪_Y` lies in `D^b_Coh(𝒪_X)`: it is
cohomologically bounded and its cohomology sheaves are coherent. Here `f^!` is computed at an
arbitrary compactification `j`. -/
@[stacks 0B6U "part (a)"]
theorem derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_perfect [Perfect f.left] :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) :=
  derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_charts f j fun x => by
    obtain ⟨U, hU, V, hV, hUV, hxU, -, he⟩ := exists_chart_of_upperShriekStructureSheafCharts f j
      (upperShriekStructureSheafCharts f j) x ⊤ trivial
    exact ⟨U, hU, V, hV, hUV, hxU, he⟩

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0B6U (Lemma 48.17.9), part (b).** In Situation 48.16.1 let
`f : X ⟶ Y` be a perfect morphism of `FTS S`. Then `f^!𝒪_Y` has finite tor dimension in
`D(f⁻¹𝒪_Y)`: read on the ringed space `(X, f⁻¹𝒪_Y)`, it has Tor amplitude in some interval.
Here `f^!` is computed at an arbitrary compactification `j`. -/
@[stacks 0B6U "part (b)"]
theorem hasFiniteTorDimension_derivedScalarRestriction_upperShriek [Perfect f.left] :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base)
      ((Scheme.Hom.derivedScalarRestriction f.left).obj (relativeDualizingComplexObj f j)) := by
  have hw := isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j
    (upperShriekStructureSheafCharts f j)
  choose U hU V hV hUV hxU p he using hw
  choose a b hab using fun x => exists_hasTorAmplitudeCanonical_stalk_of_chart f (hU x) (hV x)
    (hUV x) (p x) _ (he x)
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X.left)).elim_finite_subcover
      (fun x : X.left => (U x : Set X.left)) (fun x => (U x).isOpen)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨-∑ x ∈ t, |a x|, ∑ x ∈ t, |b x|, ?_⟩
  refine (Stacks.SheafOfModules.DerivedTensorStalk.hasTorAmplitudeCanonical_forall_stalk_iff
    (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base).sheaf _ _ _).2 fun y => ?_
  refine (Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff f.left y _ _ _).2 ?_
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  have hs (c : X.left → ℤ) : |c x| ≤ ∑ x ∈ t, |c x| :=
    Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hxt
  exact hasTorAmplitudeCanonical_stalk_base_of_modulesStalk f.left _ y _ _
    (hab x _ _ (abs_le.mp (hs a)).1 (abs_le.mp (hs b)).2 y hyx)

/-- **Stacks Project, Tag 0B6U (Lemma 48.17.9), part (c).** In Situation 48.16.1 let
`f : X ⟶ Y` be a perfect morphism of `FTS S`. Then the homothety
`𝒪_X ⟶ R𝓗om_{𝒪_X}(f^!𝒪_Y, f^!𝒪_Y)` is an isomorphism. Here `f^!` is computed at an arbitrary
compactification `j`. -/
@[stacks 0B6U "part (c)"]
theorem isIso_derivedSheafHomothety_upperShriek [Perfect f.left] :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.left.sheaf
      (relativeDualizingComplexObj f j)) :=
  isIso_derivedSheafHomothety_of_isShriekOfStructureSheafOnCharts f _
    (isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j
      (upperShriekStructureSheafCharts f j))

end Standard

end Stacks.Duality

end
