module

public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The level sets of the weighted fibre sum of a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and let `w : X → ℤ` be a weighting of `f`.
Then the weighted fibre sum `∫_f w = separableDegreeWeightedFiberSum f w` is locally constant
on `Y`, and consequently each of its level sets is locally constructible.

## Main results

* `AlgebraicGeometry.IsWeighting.isLocallyConstant_separableDegreeWeightedFiberSum`: the
  weighted fibre sum of a finite morphism carrying a weighting is locally constant.
* `AlgebraicGeometry.isLocallyConstructible_separableDegreeWeightedFiberSum_levelSet_of_isFinite`:
  the level sets of that fibre sum are locally constructible.

## References

* [Stacks Project, Tag 0F3H](https://stacks.math.columbia.edu/tag/0F3H)
* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- A level set of a locally constant function is locally constructible. -/
private theorem isLocallyConstructible_levelSet_of_isLocallyConstant
    {Z β : Type*} [TopologicalSpace Z] {g : Z → β} (hg : IsLocallyConstant g) (n : β) :
    IsLocallyConstructible {z : Z | g z = n} := by
  intro z
  refine ⟨{y | g y = g z}, (hg.isOpen_fiber (g z)).mem_nhds rfl, hg.isOpen_fiber (g z), ?_⟩
  by_cases h : g z = n
  · convert IsConstructible.univ using 1
    simp [Set.eq_univ_iff_forall, h]
  · convert IsConstructible.empty using 1
    simp +contextual [Set.eq_empty_iff_forall_notMem, h]

/-- The weighted fibre sum of a **finite** morphism carrying a weighting is locally constant. -/
theorem IsWeighting.isLocallyConstant_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsFinite f] {w : X → ℤ} (hw : IsWeighting f w) :
    IsLocallyConstant (separableDegreeWeightedFiberSum f w) := by
  have : LocallyQuasiFinite f := inferInstance
  set h : pullback f (𝟙 Y) ⟶ X := pullback.fst f (𝟙 Y) with hh
  set π : pullback f (𝟙 Y) ⟶ Y := pullback.snd f (𝟙 Y) with hπ
  have hsquare : IsPullback h π f (𝟙 Y) := IsPullback.of_hasPullback f (𝟙 Y)
  have hlift : pullback.lift h π pullback.condition = 𝟙 (pullback f (𝟙 Y)) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, Category.id_comp]
  have hsum : IsLocallyConstant (separableDegreeWeightedFiberSum π (w ∘ h)) := by
    refine hw h π (𝟙 Y) pullback.condition inferInstance ?_ inferInstance
    rw [hlift]
    infer_instance
  have hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite := fun y => f.finite_preimage_singleton y
  have hbase :=
    separableDegreeWeightedFiberSum_comp_of_isPullback f h π (𝟙 Y) hsquare hfinite w
  have heq : separableDegreeWeightedFiberSum f w =
      separableDegreeWeightedFiberSum π (w ∘ h) := by
    funext y
    simpa [Function.comp] using congrFun hbase y
  rw [heq]
  exact hsum

/-- The level sets of the weighted fibre sum `∫_f w` of a weighting `w` of a **finite** morphism
`f : X ⟶ Y` are locally constructible in `Y`. -/
theorem isLocallyConstructible_separableDegreeWeightedFiberSum_levelSet_of_isFinite
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsFinite f] {w : X → ℤ} (hw : IsWeighting f w) (n : ℤ) :
    IsLocallyConstructible {y : Y | separableDegreeWeightedFiberSum f w y = n} :=
  isLocallyConstructible_levelSet_of_isLocallyConstant
    hw.isLocallyConstant_separableDegreeWeightedFiberSum n

end AlgebraicGeometry

end
