module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationIntegralComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A square of open immersions that is cartesian

For open immersions `t : X ⟶ X̄` and `j : X ⟶ X̄'` and a morphism `g : X̄ ⟶ X̄'` with `t ≫ g = j`,
the square `𝟙 ≫ j = t ≫ g` is a pullback as soon as `g⁻¹(j(X)) ⊆ t(X)`: every map into `X̄` whose
composite with `g` factors through `j` then factors through `t`. This is how a compactification
lying over another is seen to be cartesian over the interior.

## Main results

* `AlgebraicGeometry.isPullback_id_of_preimage_range_subset`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A square of open immersions over an open immersion is cartesian when the preimage of the
image is the image.**  For open immersions `t : X ⟶ X̄`, `j : X ⟶ X̄'` and a morphism
`g : X̄ ⟶ X̄'` with `t ≫ g = j` and `g⁻¹(j(X)) ⊆ t(X)`, the square `𝟙 ≫ j = t ≫ g` is a
pullback. -/
theorem isPullback_id_of_preimage_range_subset {X Xb Xb' : Scheme.{u}} (t : X ⟶ Xb)
    [IsOpenImmersion t] (j : X ⟶ Xb') [IsOpenImmersion j] (g : Xb ⟶ Xb') (htg : t ≫ g = j)
    (hsub : g.base ⁻¹' Set.range j.base ⊆ Set.range t.base) :
    IsPullback (𝟙 X) t j g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp [htg]) (fun s ↦ s.fst)
    (fun s ↦ by simp) (fun s ↦ ?_) (fun s m h₁ _ ↦ by simpa using h₁))
  have hr : Set.range s.snd.base ⊆ Set.range t.base := by
    rintro _ ⟨a, rfl⟩
    refine hsub ⟨s.fst.base a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, s.condition]
  have hl : IsOpenImmersion.lift t s.snd hr = s.fst := by
    rw [← cancel_mono j]
    calc IsOpenImmersion.lift t s.snd hr ≫ j = (IsOpenImmersion.lift t s.snd hr ≫ t) ≫ g := by
          rw [Category.assoc, htg]
      _ = s.fst ≫ j := by rw [IsOpenImmersion.lift_fac, s.condition]
  rw [← hl, IsOpenImmersion.lift_fac]

end AlgebraicGeometry

end
